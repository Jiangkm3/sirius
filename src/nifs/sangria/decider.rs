use std::collections::BTreeMap;
use std::sync::Arc;

use crate::ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits};
use crate::fft::best_fft;
use crate::nifs::sangria::ipa::{ipa_prove_single, ipa_verify_single, IpaParams, IpaProof};
use crate::{
    commitment::CommitmentKey,
    constants::NUM_CHALLENGE_BITS,
    halo2_proofs::arithmetic::CurveAffine,
    nifs::sangria::{
        accumulator::{RelaxedPlonkInstance, RelaxedPlonkTrace},
        Error, VanillaFS, VerifyError,
    },
    plonk::PlonkStructure,
    polynomial::{Expression, Query},
    poseidon::ROTrait,
};
use halo2_proofs::arithmetic::best_multiexp;
use halo2_proofs::{
    halo2curves::{
        ff::WithSmallOrderMulGroup,
        group::{Curve, Group},
    },
    poly::{EvaluationDomain, ExtendedLagrangeCoeff, Polynomial},
};
use rayon::prelude::*;

// =====================================================================
// Decider proof structures
// =====================================================================

#[derive(Clone, Debug)]
pub struct GateDeciderProof<C: CurveAffine> {
    pub t_commitments: Vec<C>,
    pub advice_column_commitments: Vec<C>,
    pub evals: GateEvaluations<C::ScalarExt>,
    pub opening_proof: IpaProof<C>,
}

// =====================================================================
// One entry per polynomial being opened.
// =====================================================================

struct OpeningEntry<'a, C: CurveAffine> {
    /// The polynomial in coefficient form (length = ipa_params.generators.len()).
    /// For columns stored as evaluations on H, this is the iFFT'd coefficient vector.
    coeffs: &'a [C::ScalarExt],
    /// Its commitment (already a Pedersen MSM in coefficient form, since
    /// ck.commit(c) = Σ cᵢ Gᵢ).
    commitment: C,
    /// Its claimed evaluation at ζ.
    eval: C::ScalarExt,
    generator_offset: usize,
}

/// Evaluations of all polynomials at the challenge point `ζ` (and `ζω` for
/// polynomials with non-zero rotations referenced by the gate expression).
#[derive(Clone, Debug)]
pub struct GateEvaluations<F: PrimeField> {
    /// Per-query evaluations. Indexed identically to how `Query::index` is
    /// laid out in the gate expression. For each query that has rotation r,
    /// this is the evaluation of the corresponding polynomial at ζ · ωʳ.
    pub queries: Vec<F>,

    /// Evaluation of E(X) at ζ.
    pub e_eval: F,

    /// Evaluations of each quotient chunk t_i(X) at ζ.
    pub t_chunks: Vec<F>,
}

/// Prover parameters for the gate-identity decider check.
pub struct GateDeciderProverParam<C: CurveAffine> {
    pub S: PlonkStructure<C::ScalarExt>,
    pub pp_digest: (C::Base, C::Base),

    /// Commitments to fixed columns, one per column.
    pub fixed_commitments: Vec<C>,
    /// Commitments to selector columns, one per column.
    pub selector_commitments: Vec<C>,
    /// IPA setup parameters.
    pub ipa_params: IpaParams<C>,
}

/// Verifier parameters for the gate-identity decider check.
/// Computed once at setup and reused across decides.
pub struct GateDeciderVerifierParam<C: CurveAffine> {
    pub pp_digest: (C::Base, C::Base),
    pub k: usize,
    pub omega: C::ScalarExt,
    pub gate_expression: Expression<C::ScalarExt>,
    pub query_layout: QueryLayout,
    pub gate_degree: usize,

    pub fixed_commitments: Vec<C>,
    pub selector_commitments: Vec<C>,
    pub ipa_params: IpaParams<C>,
}

/// Index-range layout for Query::index resolution.
/// **VERIFY THIS AGAINST YOUR CONSTRAINT-SYSTEM COMPILER**.
#[derive(Clone, Debug)]
pub struct QueryLayout {
    pub num_selectors: usize,
    pub num_fixed: usize,
    pub num_advice: usize,
    // Convention assumed below: selectors, then fixed, then advice.
    // Adjust if your codebase uses a different order.
}

impl QueryLayout {
    fn resolve(&self, index: usize) -> ResolvedQuery {
        if index < self.num_selectors {
            ResolvedQuery::Selector(index)
        } else if index < self.num_selectors + self.num_fixed {
            ResolvedQuery::Fixed(index - self.num_selectors)
        } else if index < self.num_selectors + self.num_fixed + self.num_advice {
            ResolvedQuery::Advice(index - self.num_selectors - self.num_fixed)
        } else {
            panic!("Query index {} out of range", index)
        }
    }
}

enum ResolvedQuery {
    Selector(usize),
    Fixed(usize),
    Advice(usize),
}

// =====================================================================
// Setup
// =====================================================================

pub fn setup_decider_params<C: CurveAffine>(
    pp_digest: C,
    S: PlonkStructure<C::ScalarExt>,
    ck: &Arc<CommitmentKey<C>>,
    layout: QueryLayout,
) -> Result<(GateDeciderProverParam<C>, GateDeciderVerifierParam<C>), Error>
where
    C::ScalarExt: PrimeField + WithSmallOrderMulGroup<3>,
{
    let pp_digest_xy = {
        let c = pp_digest.coordinates().unwrap();
        (*c.x(), *c.y())
    };

    // Commit each fixed column.
    let fixed_commitments: Vec<C> = S
        .fixed_columns
        .iter()
        .map(|col| ck.commit(col))
        .collect::<Result<_, _>>()?;

    // Convert each selector to field elements, then commit.
    let selector_commitments: Vec<C> = S
        .selectors
        .iter()
        .map(|sel| {
            let as_field = selector_as_field::<C::ScalarExt>(sel);
            ck.commit(&as_field)
        })
        .collect::<Result<_, _>>()?;

    let ipa_params = IpaParams::from_ck(ck);

    // Compute ω for the verifier (the n-th root of unity).
    let domain = EvaluationDomain::<C::ScalarExt>::new(
        S.custom_gates_lookup_compressed.homogeneous_degree() as u32,
        S.k as u32,
    );
    let omega = domain.get_omega();

    let gate_expression = S.custom_gates_lookup_compressed.homogeneous().clone();
    let gate_degree = S.custom_gates_lookup_compressed.homogeneous_degree();
    let k = S.k;

    let pp = GateDeciderProverParam {
        S,
        pp_digest: pp_digest_xy,
        fixed_commitments: fixed_commitments.clone(),
        selector_commitments: selector_commitments.clone(),
        ipa_params: ipa_params.clone(),
    };

    let vp = GateDeciderVerifierParam {
        pp_digest: pp_digest_xy,
        k,
        omega,
        gate_expression,
        query_layout: layout,
        gate_degree,
        fixed_commitments,
        selector_commitments,
        ipa_params,
    };

    Ok((pp, vp))
}

pub fn setup_decider_params_from_digest<C: CurveAffine>(
    pp_digest_xy: (C::Base, C::Base),
    S: PlonkStructure<C::ScalarExt>,
    ck: &Arc<CommitmentKey<C>>,
    layout: QueryLayout,
) -> Result<(GateDeciderProverParam<C>, GateDeciderVerifierParam<C>), Error>
where
    C::ScalarExt: PrimeField + WithSmallOrderMulGroup<3>,
{
    // Same body as setup_decider_params, but skip the coordinate extraction
    // since the caller already did it.
    let fixed_commitments: Vec<C> = S
        .fixed_columns
        .iter()
        .map(|col| ck.commit(col))
        .collect::<Result<_, _>>()?;

    let selector_commitments: Vec<C> = S
        .selectors
        .iter()
        .map(|sel| {
            let as_field = selector_as_field::<C::ScalarExt>(sel);
            ck.commit(&as_field)
        })
        .collect::<Result<_, _>>()?;

    let ipa_params = IpaParams::from_ck(ck);

    let gate_degree = S.custom_gates_lookup_compressed.homogeneous_degree();

    let domain = EvaluationDomain::<C::ScalarExt>::new(gate_degree as u32, S.k as u32);
    let omega = domain.get_omega();

    let gate_expression = S.custom_gates_lookup_compressed.homogeneous().clone();
    let gate_degree = S.custom_gates_lookup_compressed.homogeneous_degree();
    let k = S.k;

    let pp = GateDeciderProverParam {
        S,
        pp_digest: pp_digest_xy,
        fixed_commitments: fixed_commitments.clone(),
        selector_commitments: selector_commitments.clone(),
        ipa_params: ipa_params.clone(),
    };

    let vp = GateDeciderVerifierParam {
        pp_digest: pp_digest_xy,
        k,
        omega,
        gate_expression,
        query_layout: layout,
        gate_degree,
        fixed_commitments,
        selector_commitments,
        ipa_params,
    };

    Ok((pp, vp))
}

// =====================================================================
// Prover side
// =====================================================================

impl<C: CurveAffine, const MARKERS_LEN: usize> VanillaFS<C, MARKERS_LEN>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C::ScalarExt: PrimeFieldBits + FromUniformBytes<64>,
{
    /// Produce the gate-identity portion of a decider proof.
    ///
    /// This replaces the row-by-row work of `is_sat_accumulation` with a
    /// polynomial identity check at a single random point ζ, supported by
    /// a quotient polynomial commitment and IPA batch opening.
    pub fn prove_decider_gate_part(
        pp: &GateDeciderProverParam<C>,
        layout: &QueryLayout,
        acc: &RelaxedPlonkTrace<C, MARKERS_LEN>,
        transcript: &mut impl ROTrait<C::Base>,
    ) -> Result<GateDeciderProof<C>, Error> {
        println!("Prover CK_LEN: {}", pp.ipa_params.ck.len());

        let RelaxedPlonkTrace { U, W } = acc;
        let n = 1usize << pp.S.k;
        let gate_expr = pp.S.custom_gates_lookup_compressed.homogeneous();
        let gate_degree = pp.S.custom_gates_lookup_compressed.homogeneous_degree();

        let domain = EvaluationDomain::<C::ScalarExt>::new(gate_degree as u32, pp.S.k as u32);
        transcript.absorb(U);

        // ----------------------------------------------------------------
        // Phase A: build the quotient polynomial t(X)
        // ----------------------------------------------------------------

        let advice_columns = split_rounds_into_columns(&W.W, &pp.S.round_sizes, n);
        let selector_field: Vec<Vec<C::ScalarExt>> =
            pp.S.selectors
                .iter()
                .map(|sel| selector_as_field::<C::ScalarExt>(sel))
                .collect();

        let advice_coset: Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>> = advice_columns
            .iter()
            .map(|col| lift_to_coset(col, &domain))
            .collect();
        let fixed_coset: Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>> =
            pp.S.fixed_columns
                .iter()
                .map(|col| lift_to_coset(col, &domain))
                .collect();
        let selector_coset: Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>> = selector_field
            .iter()
            .map(|sel| lift_to_coset(sel, &domain))
            .collect();
        let e_coset = lift_to_coset(&W.E, &domain);

        let all_challenges: Vec<C::ScalarExt> = U
            .challenges
            .iter()
            .copied()
            .chain(std::iter::once(U.u))
            .collect();

        let ext_n = domain.extended_len();
        let rotation_step = ext_n / n;

        let mut g_on_coset = domain.empty_extended();
        g_on_coset.par_iter_mut().enumerate().for_each(|(i, slot)| {
            let gate_at_i = evaluate_expression_on_coset_row(
                gate_expr,
                layout,
                i,
                &advice_coset,
                &fixed_coset,
                &selector_coset,
                &all_challenges,
                rotation_step,
                ext_n,
            );
            *slot = gate_at_i - e_coset[i];
        });

        let t_on_coset = domain.divide_by_vanishing_poly(g_on_coset);
        let t_coeffs = domain.extended_to_coeff(t_on_coset);
        let num_chunks = domain.get_quotient_poly_degree();
        let t_chunks_coeffs = split_into_chunks(&t_coeffs, n, num_chunks);

        // convert each chunk to evaluation form *before* committing.
        let omega = domain.get_omega();
        let t_chunks_evals: Vec<Vec<_>> = t_chunks_coeffs
            .iter()
            .map(|chunk| coeffs_to_evals_via_fft(chunk, omega, pp.S.k as u32))
            .collect();

        // CHANGED: commit the evaluation form, not the coefficient form.
        let t_commitments: Vec<C> = t_chunks_evals
            .iter()
            .map(|evals| pp.ipa_params.ck.commit(evals))
            .collect::<Result<_, _>>()?;

        for c in &t_commitments {
            transcript.absorb_point(c);
        }

        // ----------------------------------------------------------------
        // Phase B: compute all claimed evaluations.
        // ----------------------------------------------------------------

        let queries = collect_queries(gate_expr);

        // Commit each column using the slice of generators that corresponds
        // to its position in the stacked layout.
        let advice_commitments_per_column: Vec<C> = advice_columns
            .iter()
            .enumerate()
            .map(|(col_idx, col_evals)| {
                let gen_start = col_idx * n;
                let gen_end = gen_start + n;
                let generators_slice = &pp.ipa_params.ck[gen_start..gen_end];
                best_multiexp(col_evals, generators_slice).to_affine()
            })
            .collect();
        for c in &advice_commitments_per_column {
            transcript.absorb_point(c);
        }

        // ----------------------------------------------------------------
        // Phase C: derive ζ and compute related evaluations.
        // ----------------------------------------------------------------

        let zeta: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        let lagrange_at_zeta = compute_lagrange_basis_at(&domain, zeta, n);
        println!(
            "Prover L0: {:?}, LN-1: {:?}",
            lagrange_at_zeta[0],
            lagrange_at_zeta[n - 1]
        );

        // Evaluate at ζ in lagrange form
        let query_evals: Vec<_> = queries
            .iter()
            .map(|q| {
                let evals = match layout.resolve(q.index) {
                    ResolvedQuery::Advice(i) => &advice_columns[i],
                    ResolvedQuery::Fixed(i) => &pp.S.fixed_columns[i],
                    ResolvedQuery::Selector(i) => &selector_field[i],
                };
                eval_lagrange_at(evals, &lagrange_at_zeta)
            })
            .collect();

        let e_eval = eval_lagrange_at(&W.E, &lagrange_at_zeta);
        let t_chunks_eval: Vec<C::ScalarExt> = t_chunks_evals
            .iter()
            .map(|evals| eval_lagrange_at(evals, &lagrange_at_zeta))
            .collect();

        // Absorb evaluations.  Each is a scalar, absorbed via the
        // scalar-to-base helper.
        for e in &query_evals {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }
        absorb_scalar_as_base::<C, _>(transcript, e_eval);
        for e in &t_chunks_eval {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }

        // ----------------------------------------------------------------
        // Phase D: combine and open via IPA.
        // ----------------------------------------------------------------

        // Squeeze the batching challenge α.
        let alpha: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        println!("Prover alpha: {:?}", alpha);

        // Convert t_chunks to evaluation form for unified IPA
        let omega = domain.get_omega();
        let t_chunks_evals: Vec<Vec<_>> = t_chunks_coeffs
            .iter()
            .map(|chunk| coeffs_to_evals_via_fft(chunk, omega, pp.S.k as u32))
            .collect();

        // Gather openings using evaluation form throughout
        let openings = gather_openings_for_prover(
            &queries,
            layout,
            &advice_columns,
            &pp.S.fixed_columns,
            &selector_field,
            &advice_commitments_per_column,
            &pp.fixed_commitments,
            &pp.selector_commitments,
            &W.E,
            &U.E_commitment,
            &t_chunks_evals,
            &t_commitments,
            &query_evals,
            e_eval,
            &t_chunks_eval,
            n,
        );

        // Combine: f_coeffs = Σ α^i · p_i(X)
        let total_len = pp.ipa_params.ck.len();
        let f_embedded = combine_evals_embedded(&openings, alpha, total_len);
        let mut b_embedded = Vec::with_capacity(total_len);
        let num_blocks = total_len / n;
        for _ in 0..num_blocks {
            b_embedded.extend_from_slice(&lagrange_at_zeta);
        }
        debug_assert_eq!(b_embedded.len(), total_len);
        println!(
            "Prover b[0], b[n], b[2n], b[total_len-1]: {:?}, {:?}, {:?}, {:?}",
            b_embedded[0],
            b_embedded[n],
            b_embedded[2 * n],
            b_embedded[total_len - 1]
        );

        let f_commit =
            best_multiexp(&f_embedded, &pp.ipa_params.ck[..f_embedded.len()]).to_affine();

        let c_combined_prover: C = openings
            .iter()
            .enumerate()
            .fold(C::CurveExt::identity(), |acc, (i, o)| {
                let alpha_pow = alpha.pow_vartime([i as u64]);
                acc + o.commitment.to_curve() * alpha_pow
            })
            .to_affine();

        println!("f_commit = {:?}", f_commit);
        println!("c_combined_prover = {:?}", c_combined_prover);

        let inner_product: C::ScalarExt = f_embedded
            .iter()
            .zip(b_embedded.iter())
            .map(|(a, b)| *a * b)
            .fold(C::ScalarExt::ZERO, |acc, x| acc + x);

        let v_combined_prover: C::ScalarExt =
            openings
                .iter()
                .enumerate()
                .fold(C::ScalarExt::ZERO, |acc, (i, o)| {
                    let alpha_pow = alpha.pow_vartime([i as u64]);
                    acc + alpha_pow * o.eval
                });

        println!("inner_product = {:?}", inner_product);
        println!("v_combined_prover = {:?}", v_combined_prover);

        // Run IPA on (f, ζ).
        // The IPA prover doesn't need C_f or v_f as inputs — it just commits
        // to the polynomial f and proves the inner product.  The verifier
        // will reconstruct C_f from public data and check.
        let opening_proof = ipa_prove_single(&pp.ipa_params, &f_embedded, &b_embedded, transcript);
        println!("IPA proof generated");

        Ok(GateDeciderProof {
            t_commitments,
            advice_column_commitments: advice_commitments_per_column,
            evals: GateEvaluations {
                queries: query_evals,
                e_eval,
                t_chunks: t_chunks_eval,
            },
            opening_proof,
        })
    }

    // =================================================================
    // Verifier side
    // =================================================================

    /// Verify the gate-identity portion of a decider proof.
    ///
    /// Replaces `is_sat_accumulation` with a constant-work check:
    ///   1. Symbolic evaluation of the gate expression at ζ using the
    ///      prover's claimed evaluations.
    ///   2. Quotient relation: gate_hom(ζ) - E(ζ) == Z_H(ζ) · t(ζ).
    ///   3. IPA batch opening verification tying the claimed evaluations
    ///      to column commitments, U.E_commitment, and proof.t_commitments
    ///      (plus the preprocessed fixed/selector commitments in vp).
    pub fn verify_decider_gate_part(
        vp: &GateDeciderVerifierParam<C>,
        U: &RelaxedPlonkInstance<C, MARKERS_LEN>,
        proof: &GateDeciderProof<C>,
        transcript: &mut impl ROTrait<C::Base>,
    ) -> Result<(), VerifyError> {
        println!("Verifier CK_LEN: {}", vp.ipa_params.ck.len());

        let n = 1usize << vp.k;
        let n_u64 = n as u64;

        let expected_num_chunks = vp.gate_degree.saturating_sub(1).max(1);
        if proof.evals.t_chunks.len() != expected_num_chunks
            || proof.t_commitments.len() != expected_num_chunks
        {
            return Err(VerifyError::ProofShapeMismatch);
        }

        // consistency of column commitments against W
        let reconstructed_round_commitment: C = proof
            .advice_column_commitments
            .iter()
            .map(|c| c.to_curve())
            .fold(C::Curve::identity(), |acc, c| acc + c)
            .to_affine();

        if reconstructed_round_commitment != U.W_commitments[0] {
            return Err(VerifyError::OpeningFailed {
                error: "Reconstructed round commitment does not match U.W_commitments[0]".into(),
            });
        }

        transcript.absorb(U);

        // Re-derive ζ from the transcript (mirroring the prover).
        for c in &proof.t_commitments {
            transcript.absorb_point(c);
        }

        for c in &proof.advice_column_commitments {
            transcript.absorb_point(c);
        }

        let zeta: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        let domain = EvaluationDomain::<C::ScalarExt>::new(vp.gate_degree as u32, vp.k as u32);
        let lagrange_at_zeta = compute_lagrange_basis_at(&domain, zeta, 1 << vp.k);
        println!(
            "Verifier L0: {:?}, LN-1: {:?}",
            lagrange_at_zeta[0],
            lagrange_at_zeta[n - 1]
        );

        // ----------------------------------------------------------------
        // Step 1: symbolic gate-identity check at ζ.
        //
        // Verifier reconstructs gate_hom(W(ζ), u, ...) using the prover's
        // claimed evaluations, subtracts E(ζ), and checks against
        // Z_H(ζ) · t(ζ).
        // ----------------------------------------------------------------
        let queries = collect_queries(&vp.gate_expression);
        if queries.len() != proof.evals.queries.len() {
            return Err(VerifyError::ProofShapeMismatch);
        }

        let all_challenges: Vec<C::ScalarExt> = U
            .challenges
            .iter()
            .copied()
            .chain(std::iter::once(U.u))
            .collect();

        let query_eval_pairs: Vec<(Query, C::ScalarExt)> = queries
            .iter()
            .copied()
            .zip(proof.evals.queries.iter().copied())
            .collect();

        let gate_at_zeta =
            evaluate_expression_symbolic(&vp.gate_expression, &query_eval_pairs, &all_challenges);

        let z_h_at_zeta = zeta.pow_vartime([n_u64]) - C::ScalarExt::ONE;
        let t_at_zeta = combine_quotient_chunks(&proof.evals.t_chunks, zeta, n_u64);

        let lhs = gate_at_zeta - proof.evals.e_eval;
        let rhs = z_h_at_zeta * t_at_zeta;

        if lhs != rhs {
            return Err(VerifyError::GateIdentityMismatch);
        }

        // ----------------------------------------------------------------
        // Step 2: re-derive α (the batching challenge for the IPA).
        // ----------------------------------------------------------------

        for e in &proof.evals.queries {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }
        absorb_scalar_as_base::<C, _>(transcript, proof.evals.e_eval);
        for e in &proof.evals.t_chunks {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }

        let alpha: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        println!("Verifier alpha: {:?}", alpha);

        // ----------------------------------------------------------------
        // Step 3: combine commitments and evaluations.
        //
        // Verifier knows:
        //   - column_commitments
        //   - vp.fixed_commitments
        //   - vp.selector_commitments
        //   - U.E_commitment
        //   - proof.t_commitments
        //
        // For each query (in the same order as the prover), resolve to a
        // commitment.  Then compute C_f = Σ α^i · C_i and v_f = Σ α^i · v_i.
        // ----------------------------------------------------------------

        let commitments_in_order = gather_commitments_for_verifier(
            &queries,
            &vp.query_layout,
            &proof.advice_column_commitments,
            &vp.fixed_commitments,
            &vp.selector_commitments,
            &U.E_commitment,
            &proof.t_commitments,
        );

        let evals_in_order: Vec<C::ScalarExt> = proof
            .evals
            .queries
            .iter()
            .copied()
            .chain(std::iter::once(proof.evals.e_eval))
            .chain(proof.evals.t_chunks.iter().copied())
            .collect();

        debug_assert_eq!(commitments_in_order.len(), evals_in_order.len());

        // Compute C_f and v_f via Horner-style accumulation with α.
        let (c_combined, v_combined) =
            combine_for_ipa(&commitments_in_order, &evals_in_order, alpha);

        // ----------------------------------------------------------------
        // Step 4: verify the IPA opening of (c_combined, v_combined) at ζ.
        // ----------------------------------------------------------------
        let total_len = vp.ipa_params.ck.len();
        let mut b_embedded = Vec::with_capacity(total_len);
        let num_blocks = total_len / n;
        for _ in 0..num_blocks {
            b_embedded.extend_from_slice(&lagrange_at_zeta);
        }
        println!(
            "Verifier b[0], b[n], b[2n], b[total_len-1]: {:?}, {:?}, {:?}, {:?}",
            b_embedded[0],
            b_embedded[n],
            b_embedded[2 * n],
            b_embedded[total_len - 1]
        );

        ipa_verify_single(
            &vp.ipa_params,
            c_combined,
            v_combined,
            &b_embedded,
            &proof.opening_proof,
            transcript,
        )?;

        Ok(())
    }
}

// IPA HELPERS
// Prover side: gather (coeffs, commitment, eval) triples in a deterministic order.
fn gather_openings_for_prover<'a, C: CurveAffine>(
    queries: &'a [Query],
    layout: &QueryLayout,
    advice_evals: &'a [Vec<C::ScalarExt>],
    fixed_evals: &'a [Vec<C::ScalarExt>],
    selector_evals: &'a [Vec<C::ScalarExt>],
    advice_commitments: &'a [C],
    fixed_commitments: &'a [C],
    selector_commitments: &'a [C],
    e_evals: &'a [C::ScalarExt],
    e_commitment: &'a C,
    t_chunks_evals: &'a [Vec<C::ScalarExt>],
    t_commitments: &'a [C],
    query_evals: &'a [C::ScalarExt],
    e_eval: C::ScalarExt,
    t_chunks_eval: &'a [C::ScalarExt],
    n: usize,
) -> Vec<OpeningEntry<'a, C>> {
    let mut out = Vec::new();

    for (i, q) in queries.iter().enumerate() {
        let (evals, commitment, generator_offset): (&[C::ScalarExt], C, usize) = match layout
            .resolve(q.index)
        {
            ResolvedQuery::Advice(idx) => (&advice_evals[idx], advice_commitments[idx], idx * n),
            ResolvedQuery::Fixed(idx) => (&fixed_evals[idx], fixed_commitments[idx], 0),
            ResolvedQuery::Selector(idx) => (&selector_evals[idx], selector_commitments[idx], 0),
        };
        out.push(OpeningEntry {
            coeffs: evals,
            commitment,
            eval: query_evals[i],
            generator_offset,
        });
    }

    out.push(OpeningEntry {
        coeffs: e_evals,
        commitment: *e_commitment,
        eval: e_eval,
        generator_offset: 0,
    });

    for (i, t) in t_chunks_evals.iter().enumerate() {
        out.push(OpeningEntry {
            coeffs: t,
            commitment: t_commitments[i],
            eval: t_chunks_eval[i],
            generator_offset: 0,
        });
    }
    out
}

// Verifier side: just the commitments, in the same order.
fn gather_commitments_for_verifier<C: CurveAffine>(
    queries: &[Query],
    layout: &QueryLayout,
    advice_commitments: &[C],
    fixed_commitments: &[C],
    selector_commitments: &[C],
    e_commitment: &C,
    t_commitments: &[C],
) -> Vec<C> {
    let mut out = Vec::with_capacity(queries.len() + 1 + t_commitments.len());

    for q in queries {
        let c = match layout.resolve(q.index) {
            ResolvedQuery::Advice(i) => advice_commitments[i],
            ResolvedQuery::Fixed(i) => fixed_commitments[i],
            ResolvedQuery::Selector(i) => selector_commitments[i],
        };
        out.push(c);
    }
    out.push(*e_commitment);
    out.extend_from_slice(t_commitments);

    out
}

// Combine evaluation vectors into f = Σ α^i · p_i.
// All polynomials must have the same length (pad with zeros if shorter).
fn combine_evals<C: CurveAffine>(
    openings: &[OpeningEntry<'_, C>],
    alpha: C::ScalarExt,
) -> Vec<C::ScalarExt> {
    let max_len = openings.iter().map(|o| o.coeffs.len()).max().unwrap_or(0);
    let mut result = vec![C::ScalarExt::ZERO; max_len];

    let mut alpha_pow = C::ScalarExt::ONE;
    for o in openings {
        for (r, c) in result.iter_mut().zip(o.coeffs.iter()) {
            *r += alpha_pow * c;
        }
        alpha_pow *= alpha;
    }
    result
}

fn combine_evals_embedded<C: CurveAffine>(
    openings: &[OpeningEntry<'_, C>],
    alpha: C::ScalarExt,
    total_len: usize,
) -> Vec<C::ScalarExt> {
    let mut result = vec![C::ScalarExt::ZERO; total_len];
    let mut alpha_pow = C::ScalarExt::ONE;
    for opening in openings {
        for (j, val) in opening.coeffs.iter().enumerate() {
            result[opening.generator_offset + j] += alpha_pow * val;
        }
        alpha_pow *= alpha;
    }
    result
}

// Combine commitments and evaluations on the verifier side.
fn combine_for_ipa<C: CurveAffine>(
    commitments: &[C],
    evals: &[C::ScalarExt],
    alpha: C::ScalarExt,
) -> (C, C::ScalarExt) {
    debug_assert_eq!(commitments.len(), evals.len());

    let mut c_acc = C::CurveExt::identity();
    let mut v_acc = C::ScalarExt::ZERO;
    let mut alpha_pow = C::ScalarExt::ONE;

    for (c, v) in commitments.iter().zip(evals.iter()) {
        c_acc += c.to_curve() * alpha_pow;
        v_acc += alpha_pow * v;
        alpha_pow *= alpha;
    }

    (c_acc.to_affine(), v_acc)
}

// HELPERS
// =====================================================================
// 1. collect_queries
// =====================================================================

/// Collect all distinct (index, rotation) pairs referenced by Polynomial
/// leaves in the expression, in a deterministic order.
pub fn collect_queries<F: PrimeField>(expr: &Expression<F>) -> Vec<Query> {
    // Use BTreeMap to deduplicate and maintain canonical ordering by (index, rotation).
    let mut seen: BTreeMap<(usize, i32), Query> = BTreeMap::new();
    collect_queries_inner(expr, &mut seen);
    seen.into_values().collect()
}

fn collect_queries_inner<F: PrimeField>(
    expr: &Expression<F>,
    out: &mut BTreeMap<(usize, i32), Query>,
) {
    match expr {
        Expression::Constant(_) => {}
        Expression::Challenge(_) => {}
        Expression::Polynomial(q) => {
            out.entry((q.index, q.rotation.0)).or_insert_with(|| *q);
        }
        Expression::Negated(inner) => collect_queries_inner(inner, out),
        Expression::Sum(a, b) | Expression::Product(a, b) => {
            collect_queries_inner(a, out);
            collect_queries_inner(b, out);
        }
        Expression::Scaled(inner, _) => collect_queries_inner(inner, out),
    }
}

// =====================================================================
// 2. evaluate_expression_symbolic
// =====================================================================

/// Walk the expression tree, returning the scalar value when:
/// - each Polynomial(query) leaf is substituted by the corresponding claimed eval
/// - each Challenge(i) leaf is substituted by `challenges[i]`
///
/// `query_evals` must be in the same order as `collect_queries` produces.
pub fn evaluate_expression_symbolic<F: PrimeField>(
    expr: &Expression<F>,
    query_evals: &[(Query, F)],
    challenges: &[F],
) -> F {
    // Build a lookup: (index, rotation) -> eval.
    let lookup: BTreeMap<(usize, i32), F> = query_evals
        .iter()
        .map(|(q, e)| ((q.index, q.rotation.0), *e))
        .collect();

    eval_symbolic_inner(expr, &lookup, challenges)
}

fn eval_symbolic_inner<F: PrimeField>(
    expr: &Expression<F>,
    lookup: &BTreeMap<(usize, i32), F>,
    challenges: &[F],
) -> F {
    match expr {
        Expression::Constant(c) => *c,
        Expression::Challenge(i) => challenges[*i],
        Expression::Polynomial(q) => *lookup
            .get(&(q.index, q.rotation.0))
            .expect("query missing from claimed evals"),
        Expression::Negated(inner) => -eval_symbolic_inner(inner, lookup, challenges),
        Expression::Sum(a, b) => {
            eval_symbolic_inner(a, lookup, challenges) + eval_symbolic_inner(b, lookup, challenges)
        }
        Expression::Product(a, b) => {
            eval_symbolic_inner(a, lookup, challenges) * eval_symbolic_inner(b, lookup, challenges)
        }
        Expression::Scaled(inner, s) => eval_symbolic_inner(inner, lookup, challenges) * s,
    }
}

// =====================================================================
// 3. evaluate_expression_on_coset_row
// =====================================================================

/// Evaluate the expression at a single row of the extended (coset) domain.
/// `row` is the index into the extended domain.
/// Polynomial leaves are resolved through `layout` and indexed into the
/// corresponding coset evaluation table at row `(row + rotation_shift) mod ext_n`.
pub fn evaluate_expression_on_coset_row<F: PrimeField>(
    expr: &Expression<F>,
    layout: &QueryLayout,
    row: usize,
    advice_coset: &[Polynomial<F, ExtendedLagrangeCoeff>],
    fixed_coset: &[Polynomial<F, ExtendedLagrangeCoeff>],
    selector_coset: &[Polynomial<F, ExtendedLagrangeCoeff>],
    challenges: &[F],
    rotation_step: usize, // = ext_n / n  (extended-domain rows per H-row)
    ext_n: usize,
) -> F {
    match expr {
        Expression::Constant(c) => *c,
        Expression::Challenge(i) => challenges[*i],
        Expression::Polynomial(q) => {
            // Rotation r on H corresponds to rotation r * rotation_step on
            // the extended domain.  Work modulo ext_n to handle negative r.
            //
            // ⚠ FIX: apply rem_euclid AFTER multiplying by rotation_step,
            // because both ω^r (on H) and extended_omega^(r·rotation_step)
            // (on H_ext) have period ext_n in their integer exponents.
            let shift_signed = q.rotation.0 as i64 * rotation_step as i64;
            let shift = shift_signed.rem_euclid(ext_n as i64) as usize;
            let r = (row + shift) % ext_n;

            match layout.resolve(q.index) {
                ResolvedQuery::Advice(i) => advice_coset[i][r],
                ResolvedQuery::Fixed(i) => fixed_coset[i][r],
                ResolvedQuery::Selector(i) => selector_coset[i][r],
            }
        }
        Expression::Negated(inner) => -evaluate_expression_on_coset_row(
            inner,
            layout,
            row,
            advice_coset,
            fixed_coset,
            selector_coset,
            challenges,
            rotation_step,
            ext_n,
        ),
        Expression::Sum(a, b) => {
            evaluate_expression_on_coset_row(
                a,
                layout,
                row,
                advice_coset,
                fixed_coset,
                selector_coset,
                challenges,
                rotation_step,
                ext_n,
            ) + evaluate_expression_on_coset_row(
                b,
                layout,
                row,
                advice_coset,
                fixed_coset,
                selector_coset,
                challenges,
                rotation_step,
                ext_n,
            )
        }
        Expression::Product(a, b) => {
            evaluate_expression_on_coset_row(
                a,
                layout,
                row,
                advice_coset,
                fixed_coset,
                selector_coset,
                challenges,
                rotation_step,
                ext_n,
            ) * evaluate_expression_on_coset_row(
                b,
                layout,
                row,
                advice_coset,
                fixed_coset,
                selector_coset,
                challenges,
                rotation_step,
                ext_n,
            )
        }
        Expression::Scaled(inner, s) => {
            evaluate_expression_on_coset_row(
                inner,
                layout,
                row,
                advice_coset,
                fixed_coset,
                selector_coset,
                challenges,
                rotation_step,
                ext_n,
            ) * s
        }
    }
}

// =====================================================================
// 5. split_into_chunks
// =====================================================================

/// Split a coefficient vector into `num_chunks` consecutive slices of
/// length `n` (the last chunk may be shorter; padded with zeros if so).
pub fn split_into_chunks<F: PrimeField>(coeffs: &[F], n: usize, num_chunks: usize) -> Vec<Vec<F>> {
    (0..num_chunks)
        .map(|i| {
            let start = i * n;
            let end = ((i + 1) * n).min(coeffs.len());
            let mut chunk = if start < coeffs.len() {
                coeffs[start..end].to_vec()
            } else {
                Vec::new()
            };
            chunk.resize(n, F::ZERO);
            chunk
        })
        .collect()
}

// =====================================================================
// 6. combine_quotient_chunks  (verifier side)
// =====================================================================

/// Reconstruct t(ζ) from per-chunk evaluations t_0(ζ), t_1(ζ), ..., t_{k-1}(ζ).
/// Convention: t(X) = t_0(X) + X^n · t_1(X) + X^{2n} · t_2(X) + ...
/// So t(ζ) = Σ_i ζ^{i·n} · t_i(ζ), computed via Horner:
///        t(ζ) = ((... t_{k-1} · ζ^n + t_{k-2}) · ζ^n + ...) · ζ^n + t_0
pub fn combine_quotient_chunks<F: PrimeField>(chunk_evals: &[F], zeta: F, n: u64) -> F {
    let zeta_n = zeta.pow_vartime([n]);
    chunk_evals
        .iter()
        .rev()
        .fold(F::ZERO, |acc, t_i| acc * zeta_n + t_i)
}

// =====================================================================
// 7. split_rounds_into_columns
// =====================================================================

pub fn split_rounds_into_columns<F: PrimeField>(
    w_rounds: &[Vec<F>],
    round_sizes: &[usize],
    n: usize,
) -> Vec<Vec<F>> {
    let mut columns = Vec::new();
    for (round, round_size) in w_rounds.iter().zip(round_sizes.iter()) {
        // round.len() should equal *round_size, and round_size should be
        // a multiple of n: round_size = num_cols_in_round * n.
        debug_assert_eq!(round.len(), *round_size);
        debug_assert_eq!(round_size % n, 0);

        // Stacked layout: chunks of n.
        for col in round.chunks_exact(n) {
            columns.push(col.to_vec());
        }
    }
    columns
}

// =====================================================================
// 8. selector_as_field  (helper for treating bool selectors as field elements)
// =====================================================================

pub fn selector_as_field<F: PrimeField>(sel: &[bool]) -> Vec<F> {
    sel.iter()
        .map(|b| if *b { F::ONE } else { F::ZERO })
        .collect()
}

// =====================================================================
// 9. Polynomial domain operations
//
// In Halo2 these are:
//   - domain.lagrange_to_coeff(evals) -> Polynomial<F, Coeff>
//   - domain.coeff_to_extended(coeffs) -> Polynomial<F, ExtendedLagrangeCoeff>
//   - domain.extended_to_coeff(extended) -> Polynomial<F, Coeff>
// =====================================================================

/// Lift a column from its row evaluations on H to coset evaluations on ζ·H_ext.
pub fn lift_to_coset<F: PrimeField + WithSmallOrderMulGroup<3>>(
    col_evals_on_H: &[F],
    domain: &EvaluationDomain<F>,
) -> Polynomial<F, ExtendedLagrangeCoeff> {
    let n = 1usize << domain.k();
    assert_eq!(
        col_evals_on_H.len(),
        n,
        "column must have length 2^k = {}, got {}",
        n,
        col_evals_on_H.len()
    );

    // Build a LagrangeCoeff Polynomial
    let lagrange_poly = domain.lagrange_from_vec(col_evals_on_H.to_vec());
    // iFFT: LagrangeCoeff --> Coeff
    let coeff_poly = domain.lagrange_to_coeff(lagrange_poly);
    // Coset-FFT: Coeff --> ExtendedLagrangeCoeff
    let extended_poly = domain.coeff_to_extended(coeff_poly);
    extended_poly
}

/// Takes a polynomial g(X) given as coset evaluations, divides by Z_H(X)
/// on the coset, and returns t(X) as coefficients (truncated to its
/// actual length n * quotient_poly_degree).
pub fn divide_and_recover_coeffs<F>(
    g_on_coset: Polynomial<F, ExtendedLagrangeCoeff>,
    domain: &EvaluationDomain<F>,
) -> Vec<F>
where
    F: PrimeField + WithSmallOrderMulGroup<3>,
{
    let t_on_coset = domain.divide_by_vanishing_poly(g_on_coset);
    domain.extended_to_coeff(t_on_coset)
}

/// Evaluate a polynomial given in coefficient form at an arbitrary point,
/// via Horner's rule.
pub fn eval_coeffs_at<F: PrimeField>(coeffs: &[F], point: F) -> F {
    coeffs.iter().rev().fold(F::ZERO, |acc, c| acc * point + c)
}

fn absorb_scalar_as_base<C, RO>(transcript: &mut RO, x: C::ScalarExt)
where
    C: CurveAffine,
    C::Base: FromUniformBytes<64>,
    C::ScalarExt: PrimeField,
    RO: ROTrait<C::Base>,
{
    let repr = x.to_repr();
    let repr_bytes: &[u8] = repr.as_ref();

    let mut buf = [0u8; 64];
    debug_assert!(
        repr_bytes.len() <= 64,
        "scalar repr should fit in 64 bytes; got {}",
        repr_bytes.len()
    );
    buf[..repr_bytes.len()].copy_from_slice(repr_bytes);

    let as_base = C::Base::from_uniform_bytes(&buf);
    transcript.absorb_field(as_base);
}

// LAGRANGE HELERS
/// Compute the Lagrange basis values L_i(ζ) for i = 0, ..., n-1.
///
/// Using the closed form:
///     L_i(ζ) = (ω^i · (ζ^n - 1)) / (n · (ζ - ω^i))
///
/// This is O(n) field ops including one batch inversion.
pub fn compute_lagrange_basis_at<F: PrimeField + WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    zeta: F,
    n: usize,
) -> Vec<F> {
    let omega = domain.get_omega();
    let n_inv = F::from(n as u64).invert().unwrap();
    let zeta_n_minus_one = zeta.pow_vartime([n as u64]) - F::ONE;

    // Compute denominators (ζ - ω^i) for all i, then batch invert.
    let mut denominators = Vec::with_capacity(n);
    let mut omega_pow_i = F::ONE;
    for _ in 0..n {
        denominators.push(zeta - omega_pow_i);
        omega_pow_i *= omega;
    }

    // Batch invert the denominators.
    let inv_denominators = batch_invert(denominators);

    // Compute L_i(ζ) = (ω^i · (ζ^n - 1)) / (n · (ζ - ω^i))
    let mut lagrange = Vec::with_capacity(n);
    let mut omega_pow_i = F::ONE;
    for inv_den in inv_denominators.iter() {
        lagrange.push(omega_pow_i * zeta_n_minus_one * n_inv * inv_den);
        omega_pow_i *= omega;
    }

    lagrange
}

/// Evaluate a polynomial given in Lagrange (evaluation) form at ζ.
/// `evals[i]` is the polynomial's value at ω^i; `lagrange_at_zeta[i]` is L_i(ζ).
pub fn eval_lagrange_at<F: PrimeField>(evals: &[F], lagrange_at_zeta: &[F]) -> F {
    debug_assert_eq!(evals.len(), lagrange_at_zeta.len());
    evals
        .iter()
        .zip(lagrange_at_zeta.iter())
        .map(|(e, l)| *e * l)
        .fold(F::ZERO, |acc, x| acc + x)
}

/// Standard batch inversion: invert a Vec<F> using Montgomery's trick.
/// O(n) multiplications + 1 inversion.
pub fn batch_invert<F: PrimeField>(mut vals: Vec<F>) -> Vec<F> {
    let n = vals.len();
    let mut prefix = vec![F::ONE; n];
    let mut acc = F::ONE;
    for i in 0..n {
        prefix[i] = acc;
        acc *= vals[i];
    }
    let acc_inv = acc.invert().unwrap();
    let mut acc = acc_inv;
    for i in (0..n).rev() {
        let val_inv = acc * prefix[i];
        acc *= vals[i];
        vals[i] = val_inv;
    }
    vals
}

pub fn coeffs_to_evals_via_fft<F: PrimeField>(coeffs: &[F], omega: F, k: u32) -> Vec<F> {
    let mut evals = coeffs.to_vec();
    best_fft(&mut evals, omega, k);
    evals
}
