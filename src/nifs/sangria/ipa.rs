use std::sync::Arc;

use crate::ff::{Field, FromUniformBytes, PrimeField};
use crate::group::Curve;
use crate::nifs::sangria::VerifyError;
use halo2_proofs::arithmetic::{best_multiexp, CurveAffine, CurveExt};

use crate::{commitment::CommitmentKey, constants::NUM_CHALLENGE_BITS, poseidon::ROTrait};

// =====================================================================
// IPA proof structure
// =====================================================================

#[derive(Clone, Debug)]
pub struct IpaProof<C: CurveAffine> {
    /// The (L, R) pairs from each of the log₂(n) rounds.
    pub rounds: Vec<(C, C)>,
    /// The final folded scalar (the length-1 `a` vector).
    pub a_final: C::ScalarExt,
}

// =====================================================================
// Helpers for "extract a fresh independent generator U"
//
// In Halo2, this is the auxiliary generator W = params.w.  We need an
// extra group element independent of ck.ck.  The cleanest way is to
// commit to a known fixed vector (e.g., all-zeros except a 1 in some
// reserved slot beyond ck.len()) — but Sirius's CommitmentKey doesn't
// reserve such a slot.
//
// Practical alternative: hash-to-curve a fixed string at IPA setup,
// store the resulting point alongside CommitmentKey (or in the
// decider's verifier param).  Below I assume an extra field
// `aux_generator: C` is added to whatever vp/pp the decider holds.
// =====================================================================
#[derive(Clone, Debug)]
pub struct IpaParams<C: CurveAffine> {
    pub ck: Arc<CommitmentKey<C>>,   // generators live here
    pub aux: C,               // the U — separate, independent point
}

impl<C: CurveAffine> IpaParams<C> {
    /// Build from a CommitmentKey by hashing a fixed label to get U.
    pub fn from_ck(ck: &Arc<CommitmentKey<C>>) -> Self {
        // Use the same hash-to-curve approach as CommitmentKey::setup
        // but with a distinguishing label so U ≠ any G_i.
        use sha3::{
            digest::{ExtendableOutput, Update, XofReader},
            Shake256,
        };

        let mut reader = Shake256::default()
            .chain(b"sirius-ipa-aux-generator")
            .finalize_xof();
        let mut buf = [0u8; 32];
        reader.read(&mut buf);
        let aux = C::CurveExt::hash_to_curve("from_uniform_bytes")(&buf).to_affine();

        IpaParams {
            ck: ck.clone(),
            aux,
        }
    }
}

// =====================================================================
// Prover: single-point opening of a single polynomial
//
// Statement: C = <a, G>, claimed v = <a, b> where b_i = ζ^i.
// =====================================================================

pub fn ipa_prove_single<C: CurveAffine, RO>(
    params: &IpaParams<C>,
    a: &[C::Scalar],      // the polynomial in whatever basis
    b: &[C::Scalar],      // the basis vector evaluated at the point
    transcript: &mut RO,
) -> IpaProof<C>
where
    RO: ROTrait<C::Base>,
    C::Base: FromUniformBytes<64>,
{
    let n = a.len();
    assert!(n.is_power_of_two(), "IPA requires power-of-2 length");
    assert!(
        n <= params.ck.len(), 
        "polynomial longer than generators"
    );

    let k = n.trailing_zeros() as usize;

    // Working state — gets halved each round.
    let mut a: Vec<C::ScalarExt> = a.to_vec();
    let mut b: Vec<C::ScalarExt> = b.to_vec();
    let mut g: Vec<C> = params.ck[..n].to_vec();

    let mut rounds = Vec::with_capacity(k);

    for _round in 0..k {
        println!("ROUND: {}", _round);
        let half = a.len() / 2;
        let (a_L, a_R) = a.split_at(half);
        let (b_L, b_R) = b.split_at(half);
        let (g_L, g_R) = g.split_at(half);

        // L = <a_L, G_R> + <a_L, b_R> · U
        let inner_LR = inner_product(a_L, b_R);
        let l_point = msm_with_aux(a_L, g_R, &params.aux, inner_LR);

        // R = <a_R, G_L> + <a_R, b_L> · U
        let inner_RL = inner_product(a_R, b_L);
        let r_point = msm_with_aux(a_R, g_L, &params.aux, inner_RL);

        // Absorb L and R into the transcript.
        transcript.absorb_point(&l_point);
        transcript.absorb_point(&r_point);

        // Squeeze challenge u from C::ScalarExt; need to absorb via
        // scalar-to-base helper for both prover and verifier consistency.
        let u: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        let u_inv = u
            .invert()
            .expect("challenge nonzero with overwhelming probability");

        rounds.push((l_point, r_point));

        // Update vectors for next round:
        //   a' = a_L + u_inv · a_R
        //   b' = b_L + u · b_R
        //   G' = G_L + u · G_R
        let new_a: Vec<C::ScalarExt> = a_L
            .iter()
            .zip(a_R.iter())
            .map(|(l, r)| *l + u_inv * r)
            .collect();
        let new_b: Vec<C::ScalarExt> = b_L
            .iter()
            .zip(b_R.iter())
            .map(|(l, r)| *l + u * r)
            .collect();
        let new_g: Vec<C> = g_L
            .iter()
            .zip(g_R.iter())
            .map(|(l, r)| (l.to_curve() + r.to_curve() * u).to_affine())
            .collect();

        a = new_a;
        b = new_b;
        g = new_g;
    }

    debug_assert_eq!(a.len(), 1);
    IpaProof {
        rounds,
        a_final: a[0],
    }
}

// =====================================================================
// Verifier: single-point opening
//
// Given commitment C, claimed evaluation v, point ζ, and proof, check.
//
// Verifier work: O(log n) field/group ops for the round folding, plus
// O(n) MSM at the end to reconstruct the final folded generator.
// (The amortized "Halo trick" defers this MSM; for a single decider we
// just do it.)
// =====================================================================

pub fn ipa_verify_single<C: CurveAffine, RO>(
    params: &IpaParams<C>,
    commitment: C,
    claimed_eval: C::ScalarExt,
    b: &[C::Scalar],      // the basis vector evaluated at the point
    proof: &IpaProof<C>,
    transcript: &mut RO,
) -> Result<(), VerifyError>
where
    RO: ROTrait<C::Base>,
    C::Base: FromUniformBytes<64>,
{
    let k = proof.rounds.len();
    let n = 1 << k;

    // Modified commitment: C' = C + v · U
    let mut c_prime = (commitment.to_curve() + params.aux.to_curve() * claimed_eval).to_affine();

    // Collect challenges, mirroring the prover's transcript.
    let mut challenges = Vec::with_capacity(k);
    let mut challenges_inv = Vec::with_capacity(k);

    for (l, r) in &proof.rounds {
        transcript.absorb_point(l);
        transcript.absorb_point(r);
        let u: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        let u_inv = u.invert().expect("nonzero challenge");
        challenges.push(u);
        challenges_inv.push(u_inv);

        // Update C': C' += u² · L + u⁻² · R
        let u_sq = u.square();
        let u_inv_sq = u_inv.square();
        c_prime = (c_prime.to_curve() + l.to_curve() * u_sq + r.to_curve() * u_inv_sq).to_affine();
    }

    // Reconstruct the folded generator G_final = Σ s_i · G_i
    // where s_i is determined by the binary expansion of i and the u's.
    // s_i = Π_{j: bit_j(i)=1} u_j   (with the right indexing convention)
    //
    // This is the O(n) MSM.  See "compute_s" below.
    let s = compute_s(&challenges, &challenges_inv, n);
    let g_final = best_multiexp(&s, &params.ck[..n]).to_affine();

    // Reconstruct b_final = <s, [1, ζ, ζ², ...]>
    // This can be done in O(log n) via a closed form, see below.
    let b_final = compute_b_after_rounds(&b, &challenges);

    // Final check: C' == a_final · G_final + (a_final · b_final) · U
    let expected = (g_final.to_curve() * proof.a_final
        + params.aux.to_curve() * (proof.a_final * b_final))
        .to_affine();

    if c_prime == expected {
        Ok(())
    } else {
        Err(VerifyError::OpeningFailed { error: format!("c': {:?}, expected: {:?}", c_prime, expected) })
    }
}

// =====================================================================
// Closed-form helpers
// =====================================================================

/// Compute s_i for i in 0..n.
///
/// s_i = Π_{j=0}^{k-1}  ( u_{k-1-j}        if bit_j(i) = 1 )
///                     ( u_{k-1-j}^{-1}    if bit_j(i) = 0 )
///
/// (Indexing convention matches Halo2.  Double-check against halo2
/// reference if hooking into an existing transcript order.)
fn compute_s<F: PrimeField>(challenges: &[F], challenges_inv: &[F], n: usize) -> Vec<F> {
    let k = challenges.len();
    debug_assert_eq!(1 << k, n);

    let mut s = vec![F::ONE; n];
    for i in 0..n {
        for j in 0..k {
            let bit = (i >> j) & 1;
            if bit == 1 {
                s[i] *= challenges[k - 1 - j];
            } else {
                s[i] *= challenges_inv[k - 1 - j];
            }
        }
    }
    s
}

/// Compute b_final = <s, [1, ζ, ζ², ..., ζ^{n-1}]> in closed form.
///
/// b_final = Π_{j=0}^{k-1}  (u_{k-1-j}⁻¹ + u_{k-1-j} · ζ^{2^j})
///
/// This is O(log n) because of the product structure.
fn compute_b_final<F: PrimeField>(challenges: &[F], zeta: F) -> F {
    let k = challenges.len();
    let mut result = F::ONE;
    let mut zeta_pow = zeta; // ζ^{2^0} = ζ

    for j in 0..k {
        let u = challenges[k - 1 - j];
        let u_inv = u.invert().unwrap();
        result *= u_inv + u * zeta_pow;
        zeta_pow = zeta_pow.square(); // ζ^{2^(j+1)}
    }
    result
}

// =====================================================================
// Trivial helpers
// =====================================================================

fn powers_of<F: PrimeField>(x: F, n: usize) -> Vec<F> {
    let mut result = Vec::with_capacity(n);
    let mut cur = F::ONE;
    for _ in 0..n {
        result.push(cur);
        cur *= x;
    }
    result
}

fn inner_product<F: PrimeField>(a: &[F], b: &[F]) -> F {
    a.iter().zip(b.iter()).map(|(a, b)| *a * b).sum()
}

/// Compute <coeffs, generators> + extra · U  via best_multiexp.
fn msm_with_aux<C: CurveAffine>(
    coeffs: &[C::ScalarExt],
    generators: &[C],
    aux: &C,
    extra: C::ScalarExt,
) -> C {
    let main = best_multiexp(coeffs, generators);
    (main + aux.to_curve() * extra).to_affine()
}

fn compute_b_after_rounds<F: Field>(b: &[F], challenges: &[F]) -> F {
    let mut b = b.to_vec();
    for u in challenges {
        let half = b.len() / 2;
        let u_inv = u.invert().unwrap();
        let new_b: Vec<F> = b[..half].iter().zip(b[half..].iter())
            .map(|(l, r)| *l * u_inv + *r * u)
            .collect();
        b = new_b;
    }
    debug_assert_eq!(b.len(), 1);
    b[0]
}