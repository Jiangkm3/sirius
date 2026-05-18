use std::sync::Arc;

use crate::ff::{Field, FromUniformBytes, PrimeField};
use crate::group::Curve;
use crate::nifs::sangria::VerifyError;
use halo2_proofs::arithmetic::{best_multiexp, CurveAffine, CurveExt};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator,
};

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
    pub ck: Arc<CommitmentKey<C>>, // generators live here
    pub aux: C,                    // the U — separate, independent point
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
    a: &[C::Scalar], // the polynomial in whatever basis
    b: &[C::Scalar], // the basis vector evaluated at the point
    transcript: &mut RO,
) -> IpaProof<C>
where
    RO: ROTrait<C::Base>,
    C::Base: FromUniformBytes<64>,
{
    ipa_prove_single_with_generators(&params.ck[..], &params.aux, a, b, transcript)
}

// Core implementation that takes generators explicitly.
pub fn ipa_prove_single_with_generators<C: CurveAffine>(
    generators: &[C],   // length L (any power of 2)
    aux: &C,            // auxiliary generator for v · H
    f: &[C::ScalarExt], // length L
    b: &[C::ScalarExt], // length L
    transcript: &mut impl ROTrait<C::Base>,
) -> IpaProof<C>
where
    C::Base: FromUniformBytes<64>,
{
    debug_assert_eq!(f.len(), b.len());
    debug_assert_eq!(f.len(), generators.len());
    debug_assert!(f.len().is_power_of_two());
    let n = f.len();
    assert!(n.is_power_of_two(), "IPA requires power-of-2 length");
    assert!(n <= generators.len(), "polynomial longer than generators");

    let k = n.trailing_zeros() as usize;

    // Working state — gets halved each round.
    let mut a: Vec<C::ScalarExt> = f.to_vec();
    let mut b: Vec<C::ScalarExt> = b.to_vec();
    let mut g: Vec<C> = generators[..n].to_vec();

    let mut rounds = Vec::with_capacity(k);

    for _round in 0..k {
        let half = a.len() / 2;
        let (a_L, a_R) = a.split_at(half);
        let (b_L, b_R) = b.split_at(half);
        let (g_L, g_R) = g.split_at(half);

        // L = <a_L, G_R> + <a_L, b_R> · U
        let inner_LR = inner_product(a_L, b_R);
        let l_point = msm_with_aux(a_L, g_R, aux, inner_LR);

        // R = <a_R, G_L> + <a_R, b_L> · U
        let inner_RL = inner_product(a_R, b_L);
        let r_point = msm_with_aux(a_R, g_L, aux, inner_RL);

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
            .par_iter()
            .zip(a_R.par_iter())
            .map(|(l, r)| *l * u + u_inv * r)
            .collect();
        let new_b: Vec<C::ScalarExt> = b_L
            .par_iter()
            .zip(b_R.par_iter())
            .map(|(l, r)| *l * u_inv + u * r)
            .collect();
        // Compute new g in projective form, in parallel.
        let new_g_curve: Vec<C::CurveExt> = g_L
            .par_iter()
            .zip(g_R.par_iter())
            .map(|(l, r)| double_scalar_mul(u_inv, &l.to_curve(), u, &r.to_curve()))
            .collect();

        // Batch convert to affine.
        let mut new_g = vec![C::identity(); new_g_curve.len()];
        C::CurveExt::batch_normalize(&new_g_curve, &mut new_g);

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
    expected_v: C::ScalarExt,
    b: &[C::Scalar], // the basis vector evaluated at the point
    proof: &IpaProof<C>,
    transcript: &mut RO,
) -> Result<(), VerifyError>
where
    RO: ROTrait<C::Base>,
    C::Base: FromUniformBytes<64>,
{
    ipa_verify_single_with_generators(
        &params.ck[..],
        &params.aux,
        commitment,
        expected_v,
        b,
        proof,
        transcript,
    )
}

pub fn ipa_verify_single_with_generators<C: CurveAffine>(
    generators: &[C],
    aux: &C,
    commitment: C,
    expected_v: C::ScalarExt,
    b: &[C::ScalarExt],
    proof: &IpaProof<C>,
    transcript: &mut impl ROTrait<C::Base>,
) -> Result<(), VerifyError>
where
    C::Base: FromUniformBytes<64>,
{
    debug_assert_eq!(b.len(), generators.len());
    debug_assert!(b.len().is_power_of_two());
    let k = proof.rounds.len();
    let n = 1 << k;

    // Modified commitment: C' = C + v · U
    let mut c_prime = (commitment.to_curve() + aux.to_curve() * expected_v).to_affine();

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
    let g_final = best_multiexp(&s, &generators[..n]).to_affine();

    // Reconstruct b_final = <s, [1, ζ, ζ², ...]>
    // This can be done in O(log n) via a closed form, see below.
    let b_final = compute_b_after_rounds(&b, &challenges);

    // Final check: C' == a_final · G_final + (a_final · b_final) · U
    let expected = (g_final.to_curve() * proof.a_final
        + aux.to_curve() * (proof.a_final * b_final))
        .to_affine();

    if c_prime == expected {
        Ok(())
    } else {
        Err(VerifyError::OpeningFailed {
            error: format!("c': {:?}, expected: {:?}", c_prime, expected),
        })
    }
}

// =====================================================================
// Closed-form helpers
// =====================================================================

/// Compute s_i for i in 0..n in O(n) field operations.
///
/// Recursive doubling: starts with s = [1], doubles in size each iteration
/// by multiplying existing entries by challenges_inv (the "bit = 0" extension)
/// and creating new entries via multiplication by challenges (the "bit = 1"
/// extension).
///
/// Indexing convention: bit j of i (j ∈ [0, k)) selects challenges[k-1-j].
/// This matches the naive O(n log n) version.
fn compute_s<F: PrimeField + Send + Sync>(
    challenges: &[F],
    challenges_inv: &[F],
    n: usize,
) -> Vec<F> {
    let k = challenges.len();
    debug_assert_eq!(1 << k, n);
    debug_assert_eq!(challenges_inv.len(), k);

    let mut s = vec![F::ONE; n];
    let mut half_size = 1;
    for j in (0..k).rev() {
        let u = challenges[j];
        let u_inv = challenges_inv[j];

        let (lower, upper) = s[..2 * half_size].split_at_mut(half_size);
        lower
            .par_iter_mut()
            .zip(upper.par_iter_mut())
            .for_each(|(s_lo, s_hi)| {
                *s_hi = *s_lo * u;
                *s_lo *= u_inv;
            });

        half_size *= 2;
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
    a.par_iter().zip(b.par_iter()).map(|(a, b)| *a * b).sum()
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
        let new_b: Vec<F> = b[..half]
            .iter()
            .zip(b[half..].iter())
            .map(|(l, r)| *l * u_inv + *r * u)
            .collect();
        b = new_b;
    }
    debug_assert_eq!(b.len(), 1);
    b[0]
}

/// Compute `a * P + b * Q` using simultaneous scalar multiplication
/// with 2-bit windowing.
///
/// Expected cost: ~256 doublings + ~64 additions (vs ~512 doublings + ~256 additions
/// for two separate scalar muls).
pub fn double_scalar_mul<C: CurveExt>(a: C::ScalarExt, p: &C, b: C::ScalarExt, q: &C) -> C
where
    C::ScalarExt: PrimeField,
{
    // Precompute lookup table for window size 2.
    // Index = (high_bit_a, low_bit_a, high_bit_b, low_bit_b) → 4 bits → 16 entries.
    let p2 = p.double();
    let q2 = q.double();

    let table: [C; 16] = [
        C::identity(),     // 0000
        *p,                // 0001 -> a=01, b=00 -> 1·P
        p2,                // 0010 -> a=10, b=00 -> 2·P
        p2 + p,            // 0011 -> a=11, b=00 -> 3·P
        *q,                // 0100 -> a=00, b=01 -> 1·Q
        *p + *q,           // 0101
        p2 + *q,           // 0110
        p2 + *p + *q,      // 0111
        q2,                // 1000 -> a=00, b=10 -> 2·Q
        *p + q2,           // 1001
        p2 + q2,           // 1010
        p2 + *p + q2,      // 1011
        q2 + *q,           // 1100 -> a=00, b=11 -> 3·Q
        *p + q2 + *q,      // 1101
        p2 + q2 + *q,      // 1110
        p2 + *p + q2 + *q, // 1111
    ];

    // Get scalar bytes.
    let a_repr = a.to_repr();
    let b_repr = b.to_repr();
    let a_bytes: &[u8] = a_repr.as_ref();
    let b_bytes: &[u8] = b_repr.as_ref();

    let mut result = C::identity();

    // Iterate MSB to LSB, 2 bits at a time.
    // Field is 256 bits = 32 bytes = 128 windows of 2 bits.
    for byte_idx in (0..a_bytes.len()).rev() {
        let a_byte = a_bytes[byte_idx];
        let b_byte = b_bytes[byte_idx];

        // Process 4 windows per byte (each window is 2 bits).
        for window in (0..4).rev() {
            // Double twice (2 bits per window).
            result = result.double().double();

            let a_window = (a_byte >> (window * 2)) & 0b11;
            let b_window = (b_byte >> (window * 2)) & 0b11;
            let idx = ((b_window << 2) | a_window) as usize;

            if idx != 0 {
                result += table[idx];
            }
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use crate::poseidon::{PoseidonRO, ROPair};

    use super::*;
    use halo2_proofs::halo2curves::{
        bn256::{Fr, G1Affine},
        ff::PrimeFieldBits,
        group::prime::PrimeCurveAffine,
    };
    use rand::{rngs::OsRng, RngCore};
    use serde::Serialize;

    const T: usize = 5;
    const RATE: usize = 4;

    type RO<F> = <PoseidonRO<T, RATE> as ROPair<F>>::OffCircuit;
    type ROArgs<F> = <RO<F> as ROTrait<F>>::Constants;

    // Helper: build a CommitmentKey with n generators by hash-to-curve.
    fn setup_ck(n: usize) -> Arc<CommitmentKey<G1Affine>> {
        let ck = CommitmentKey::setup(n, b"sirius-ipa-test");
        Arc::new(ck)
    }

    // Helper: build a fresh transcript.
    fn fresh_transcript<F>() -> RO<F>
    where
        F: PrimeField + PrimeFieldBits + FromUniformBytes<64> + Serialize,
    {
        let constants = ROArgs::<F>::new(/* r_f */ 10, /* r_p */ 60);
        RO::<F>::new(constants)
    }

    // Helper: compute the Lagrange basis at zeta for a domain of size n.
    fn lagrange_basis_at(zeta: Fr, n: usize, omega: Fr) -> Vec<Fr> {
        // Naive O(n²) for testing — just for correctness.
        let mut lagrange = Vec::with_capacity(n);
        for i in 0..n {
            let omega_i = omega.pow_vartime([i as u64]);
            let zeta_minus_omega_i = zeta - omega_i;
            // L_i(zeta) = (omega^i · (zeta^n - 1)) / (n · (zeta - omega^i))
            let zeta_n = zeta.pow_vartime([n as u64]);
            let numerator = omega_i * (zeta_n - Fr::ONE);
            let denominator = Fr::from(n as u64) * zeta_minus_omega_i;
            lagrange.push(numerator * denominator.invert().unwrap());
        }
        lagrange
    }

    #[test]
    fn ipa_basic_roundtrip_coefficient_basis() {
        // Test: open a polynomial in coefficient basis at a random point.
        // b = [1, ζ, ζ², ..., ζ^{n-1}].
        let n = 16;
        let ck = setup_ck(n);
        let params = IpaParams::from_ck(&ck);

        let mut rng = OsRng;
        let a: Vec<Fr> = (0..n).map(|_| Fr::from(rng.next_u64())).collect();
        let zeta = Fr::from(rng.next_u64());
        let b: Vec<Fr> = powers_of(zeta, n);

        // Compute commitment and claimed eval.
        let commitment = best_multiexp(&a, &params.ck[..n]).to_affine();
        let expected_v: Fr = a.iter().zip(b.iter()).map(|(x, y)| *x * y).sum();

        // Prove.
        let mut prover_transcript = fresh_transcript();
        let proof = ipa_prove_single(&params, &a, &b, &mut prover_transcript);

        // Verify.
        let mut verifier_transcript = fresh_transcript();
        let result = ipa_verify_single(
            &params,
            commitment,
            expected_v,
            &b,
            &proof,
            &mut verifier_transcript,
        );

        assert!(result.is_ok(), "honest proof should verify");
    }

    #[test]
    fn ipa_basic_roundtrip_lagrange_basis() {
        // Test: open a polynomial in Lagrange basis at a random point.
        // b = [L_0(ζ), L_1(ζ), ..., L_{n-1}(ζ)].
        let n = 16;
        let ck = setup_ck(n);
        let params = IpaParams::from_ck(&ck);

        let omega = Fr::ROOT_OF_UNITY;
        let mut rng = OsRng;
        let a: Vec<Fr> = (0..n).map(|_| Fr::from(rng.next_u64())).collect();
        let zeta = Fr::from(rng.next_u64());
        let b: Vec<Fr> = lagrange_basis_at(zeta, n, omega);

        let commitment = best_multiexp(&a, &params.ck[..n]).to_affine();
        let expected_v: Fr = a.iter().zip(b.iter()).map(|(x, y)| *x * y).sum();

        let mut prover_transcript = fresh_transcript();
        let proof = ipa_prove_single(&params, &a, &b, &mut prover_transcript);

        let mut verifier_transcript = fresh_transcript();
        let result = ipa_verify_single(
            &params,
            commitment,
            expected_v,
            &b,
            &proof,
            &mut verifier_transcript,
        );

        assert!(result.is_ok(), "honest Lagrange-basis proof should verify");
    }

    #[test]
    fn ipa_rejects_wrong_eval() {
        // Same as basic test, but with a deliberately wrong claimed eval.
        let n = 16;
        let ck = setup_ck(n);
        let params = IpaParams::from_ck(&ck);

        let mut rng = OsRng;
        let a: Vec<Fr> = (0..n).map(|_| Fr::from(rng.next_u64())).collect();
        let zeta = Fr::from(rng.next_u64());
        let b: Vec<Fr> = powers_of(zeta, n);
        let commitment = best_multiexp(&a, &params.ck[..n]).to_affine();
        let real_eval: Fr = a.iter().zip(b.iter()).map(|(x, y)| *x * y).sum();
        let wrong_eval = real_eval + Fr::ONE;

        let mut prover_transcript = fresh_transcript();
        // Even if we prove against the wrong claim, the prover doesn't error
        // (the prover doesn't check correctness, just proves what's stated).
        let proof = ipa_prove_single(&params, &a, &b, &mut prover_transcript);

        let mut verifier_transcript = fresh_transcript();
        let result = ipa_verify_single(
            &params,
            commitment,
            wrong_eval, // ← LIE
            &b,
            &proof,
            &mut verifier_transcript,
        );

        assert!(result.is_err(), "wrong claim should be rejected");
    }

    #[test]
    fn ipa_size_2_smallest_case() {
        // Smallest non-trivial size: n=2, k=1 (one round).
        // This is easiest to debug if the IPA is broken.
        let n = 2;
        let ck = setup_ck(n);
        let params = IpaParams::from_ck(&ck);

        let a = vec![Fr::from(3), Fr::from(7)];
        let zeta = Fr::from(11);
        let b = vec![Fr::ONE, zeta]; // coefficient basis

        let commitment = best_multiexp(&a, &params.ck[..n]).to_affine();
        let expected_v = a[0] + a[1] * zeta; // = 3 + 7 · 11 = 80
        assert_eq!(expected_v, Fr::from(80));

        let mut prover_transcript = fresh_transcript();
        let proof = ipa_prove_single(&params, &a, &b, &mut prover_transcript);
        assert_eq!(proof.rounds.len(), 1);

        let mut verifier_transcript = fresh_transcript();
        let result = ipa_verify_single(
            &params,
            commitment,
            expected_v,
            &b,
            &proof,
            &mut verifier_transcript,
        );

        assert!(result.is_ok(), "n=2 should verify");
    }

    #[test]
    fn compute_s_matches_iterative_g_folding() {
        // Test that compute_s produces the same g_final as the prover's
        // iterative g folding.
        let n = 8;
        let k = 3;
        let ck = setup_ck(n);

        // Pick arbitrary challenges.
        let challenges: Vec<Fr> = (1..=k as u64).map(Fr::from).collect();
        let challenges_inv: Vec<Fr> = challenges.iter().map(|u| u.invert().unwrap()).collect();

        // Method 1: closed form via compute_s.
        let s = compute_s(&challenges, &challenges_inv, n);
        let g_from_s = best_multiexp(&s, &ck[..n]).to_affine();

        // Method 2: iterative folding (mimicking the prover).
        let mut g: Vec<G1Affine> = ck[..n].to_vec();
        for u in &challenges {
            let u_inv = u.invert().unwrap();
            let half = g.len() / 2;
            let new_g: Vec<G1Affine> = g[..half]
                .iter()
                .zip(g[half..].iter())
                .map(|(l, r)| (l.to_curve() * u_inv + r.to_curve() * u).to_affine())
                .collect();
            g = new_g;
        }
        assert_eq!(g.len(), 1);
        let g_from_folding = g[0];

        assert_eq!(
            g_from_s, g_from_folding,
            "compute_s and iterative folding must agree on g_final"
        );
    }

    #[test]
    fn compute_b_after_rounds_matches_iterative_b_folding() {
        // Same test for b.
        let n = 8;
        let k = 3;
        let zeta = Fr::from(13);
        let b_initial: Vec<Fr> = powers_of(zeta, n);

        let challenges: Vec<Fr> = (1..=k as u64).map(Fr::from).collect();

        // Method 1: compute_b_after_rounds.
        let b_final = compute_b_after_rounds(&b_initial, &challenges);

        // Method 2: closed form (assuming coefficient basis, b = powers of zeta).
        let b_final_closed = compute_b_final(&challenges, zeta);

        assert_eq!(
            b_final, b_final_closed,
            "iterative folding and closed form must agree for coefficient basis"
        );
    }

    #[test]
    fn compute_s_doubling_matches_naive() {
        let k = 10;
        let n = 1 << k;
        let challenges: Vec<Fr> = (1..=k as u64).map(Fr::from).collect();
        let challenges_inv: Vec<Fr> = challenges.iter().map(|u| u.invert().unwrap()).collect();

        let s_doubling = compute_s(&challenges, &challenges_inv, n);

        // Naive version for comparison.
        let mut s_naive = vec![Fr::ONE; n];
        for i in 0..n {
            for j in 0..k {
                let bit = (i >> j) & 1;
                if bit == 1 {
                    s_naive[i] *= challenges[k - 1 - j];
                } else {
                    s_naive[i] *= challenges_inv[k - 1 - j];
                }
            }
        }

        assert_eq!(s_doubling, s_naive, "doubling must match naive");
    }
}
