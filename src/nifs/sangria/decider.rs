use std::collections::BTreeMap;
use std::sync::Arc;

use crate::ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits};
use crate::fft::best_fft;
use crate::nifs::sangria::ipa::{ipa_prove_single, ipa_verify_single, IpaParams, IpaProof};
use crate::nifs::sangria::permutation::{
    build_permutation_grand_product, build_permutation_params, gather_commitments_with_permutation,
    gather_openings_with_permutation, l_0_evals, PermutationParams,
};
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
    pub z_commitment: C,
    pub evals: GateEvaluations<C::ScalarExt>,
    pub opening_proof: IpaProof<C>,
    pub opening_proof_zw: IpaProof<C>,
}

// =====================================================================
// One entry per polynomial being opened.
// =====================================================================

pub(crate) struct OpeningEntry<'a, C: CurveAffine> {
    /// The polynomial in coefficient form (length = ipa_params.generators.len()).
    /// For columns stored as evaluations on H, this is the iFFT'd coefficient vector.
    pub(crate) coeffs: &'a [C::ScalarExt],
    /// Its commitment (already a Pedersen MSM in coefficient form, since
    /// ck.commit(c) = Σ cᵢ Gᵢ).
    pub(crate) commitment: C,
    /// Its claimed evaluation at ζ.
    pub(crate) eval: C::ScalarExt,
    pub(crate) generator_offset: usize,
}

/// Evaluations of all polynomials at the challenge point `ζ` (and `ζω` for
/// polynomials with non-zero rotations referenced by the gate expression).
#[derive(Clone, Debug)]
pub struct GateEvaluations<F: PrimeField> {
    pub queries: Vec<F>,
    pub e_eval: F,
    pub t_chunks: Vec<F>,
    pub z_at_zeta: F,
    pub z_at_zeta_omega: F,
    pub s_at_zeta: Vec<F>,
    pub id_at_zeta: Vec<F>,
}

/// Prover parameters for the gate-identity decider check.
pub struct GateDeciderProverParam<C: CurveAffine> {
    pub S: PlonkStructure<C::ScalarExt>,
    pub pp_digest: (C::Base, C::Base),
    pub fixed_commitments: Vec<C>,
    pub fixed_columns_coset: Arc<Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>>>,
    pub selector_commitments: Vec<C>,
    pub ipa_params: IpaParams<C>,
    pub perm_params: PermutationParams<C>,
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
    pub perm_params: PermutationParams<C>,
}

/// Index-range layout for Query::index resolution.
/// **VERIFY THIS AGAINST YOUR CONSTRAINT-SYSTEM COMPILER**.
#[derive(Clone, Debug)]
pub struct QueryLayout {
    pub num_selectors: usize,
    pub num_fixed: usize,
    pub num_advice: usize,
}

impl QueryLayout {
    pub(crate) fn resolve(&self, index: usize) -> ResolvedQuery {
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

#[derive(Clone, Debug)]
pub(crate) enum ResolvedQuery {
    Selector(usize),
    Fixed(usize),
    Advice(usize),
}

// =====================================================================
// Setup
// =====================================================================
pub fn setup_decider_params_from_digest<C: CurveAffine, const MARKERS_LEN: usize>(
    pp_digest_xy: (C::Base, C::Base),
    S: PlonkStructure<C::ScalarExt>,
    ck: &Arc<CommitmentKey<C>>,
    layout: QueryLayout,
) -> Result<(GateDeciderProverParam<C>, GateDeciderVerifierParam<C>), Error>
where
    C::ScalarExt: PrimeField + WithSmallOrderMulGroup<3>,
{
    let fixed_commitments: Vec<C> = S
        .fixed_columns
        .iter()
        .map(|col| ck.commit(col))
        .collect::<Result<_, _>>()?;
    let fixed_columns_coset: Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>> = S
        .fixed_columns
        .iter()
        .map(|col| lift_to_coset(col, &EvaluationDomain::new(S.k as u32, S.k as u32)))
        .collect();

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
    let num_advice = S.num_advice_columns;
    let num_active = 1 + num_advice;
    let perm_recur_degree_bound = num_active + 2;
    let combined_j = std::cmp::max(gate_degree, perm_recur_degree_bound);

    let domain = EvaluationDomain::<C::ScalarExt>::new(combined_j as u32, S.k as u32);
    let omega = domain.get_omega();

    let gate_expression = S.custom_gates_lookup_compressed.homogeneous().clone();
    let k = S.k;

    // build permutation preprocessing.
    let perm_params =
        build_permutation_params::<C, MARKERS_LEN>(&S, ck, omega, &domain, S.num_advice_columns)?;

    let pp = GateDeciderProverParam {
        S,
        pp_digest: pp_digest_xy,
        fixed_commitments: fixed_commitments.clone(),
        fixed_columns_coset: fixed_columns_coset.into(),
        selector_commitments: selector_commitments.clone(),
        ipa_params: ipa_params.clone(),
        perm_params: perm_params.clone(),
    };

    let vp = GateDeciderVerifierParam {
        pp_digest: pp_digest_xy,
        k,
        omega,
        gate_expression,
        query_layout: layout,
        gate_degree: combined_j,
        fixed_commitments,
        selector_commitments,
        ipa_params,
        perm_params,
    };

    Ok((pp, vp))
}

impl<C: CurveAffine, const MARKERS_LEN: usize> VanillaFS<C, MARKERS_LEN>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C::ScalarExt: PrimeFieldBits + FromUniformBytes<64> + WithSmallOrderMulGroup<3>,
{
    // =====================================================================
    // Prover side
    // =====================================================================

    /// Produce a decider proof covering both the gate identity and
    /// the permutation argument.
    pub fn prove_decider_gate_part(
        pp: &GateDeciderProverParam<C>,
        layout: &QueryLayout,
        perm_params: &PermutationParams<C>,
        acc: &RelaxedPlonkTrace<C, MARKERS_LEN>,
        transcript: &mut impl ROTrait<C::Base>,
    ) -> Result<GateDeciderProof<C>, Error> {
        let prover_start = std::time::Instant::now();

        let RelaxedPlonkTrace { U, W } = acc;
        let n = 1usize << pp.S.k;
        let gate_expr = pp.S.custom_gates_lookup_compressed.homogeneous();
        let gate_degree = pp.S.custom_gates_lookup_compressed.homogeneous_degree();
        let num_active = perm_params.num_active;
        let perm_recur_degree_bound = num_active + 2;
        let combined_j = std::cmp::max(gate_degree, perm_recur_degree_bound);

        let domain = EvaluationDomain::<C::ScalarExt>::new(combined_j as u32, pp.S.k as u32);
        let omega = domain.get_omega();

        transcript.absorb(U);

        // ----------------------------------------------------------------
        // Phase A: split witness, build evaluation-form columns.
        // ----------------------------------------------------------------
        let advice_columns = split_rounds_into_columns(&W.W, &pp.S.round_sizes, n);
        let selector_field: Vec<Vec<C::ScalarExt>> =
            pp.S.selectors
                .iter()
                .map(|sel| selector_as_field::<C::ScalarExt>(sel))
                .collect();

        // ----------------------------------------------------------------
        // Phase B: per-column commitments of advice using offset generators.
        //
        // These will be summed by the verifier and checked against
        // U.W_commitments[0], binding the proof to the folded accumulator.
        // ----------------------------------------------------------------
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
        // Phase C: derive β, γ for the permutation argument.
        //
        // These come AFTER advice commitments so the witness is bound
        // before challenges are chosen.
        // ----------------------------------------------------------------
        let beta: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        absorb_scalar_as_base::<C, _>(transcript, beta);
        let gamma: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        absorb_scalar_as_base::<C, _>(transcript, gamma);

        // ----------------------------------------------------------------
        // Phase D: build the grand product polynomial Z.
        //
        // Active columns for the permutation:
        //   - Column 0: markers (virtual, built from U.consistency_markers).
        //   - Columns 1..num_advice+1: advice columns.
        //
        // Build the virtual markers polynomial: length n, first MARKERS_LEN
        // slots hold the markers, rest are zero.
        // ----------------------------------------------------------------
        let mut markers_poly = vec![C::ScalarExt::ZERO; n];
        for (j, m) in U.consistency_markers.iter().enumerate() {
            markers_poly[j] = *m;
        }

        let mut active_witness_refs: Vec<&[C::ScalarExt]> =
            Vec::with_capacity(perm_params.num_active);
        active_witness_refs.push(&markers_poly);
        for col_idx in 0..pp.S.num_advice_columns {
            active_witness_refs.push(&advice_columns[col_idx]);
        }
        debug_assert_eq!(active_witness_refs.len(), perm_params.num_active);

        let z_evals = build_permutation_grand_product(
            &active_witness_refs,
            &perm_params.id_polys,
            &perm_params.s_polys,
            beta,
            gamma,
            n,
        );

        let z_commitment = pp.ipa_params.ck.commit(&z_evals)?;
        transcript.absorb_point(&z_commitment);

        // ----------------------------------------------------------------
        // Phase E: derive λ — the weight for combining the gate identity
        // and the permutation identity into a single quotient.
        // ----------------------------------------------------------------
        let lambda: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        absorb_scalar_as_base::<C, _>(transcript, lambda);

        // ----------------------------------------------------------------
        // Phase F: build the combined quotient polynomial.
        //
        // Combined identity:
        //   g_combined(X) = (gate_hom(W, u)(X) - E(X))            // gate identity
        //                 + λ   · perm_recurrence(X)              // permutation rec.
        //                 + λ²  · perm_boundary(X)                // Z(ω⁰) = 1
        //
        // where:
        //   perm_recurrence(X) = Z(ω · X) · denom(X) - Z(X) · num(X)
        //   perm_boundary(X)   = L_0(X) · (Z(X) - 1)
        //
        //   num(X)   = Π_i (w_i(X) + β · id_i(X) + γ)
        //   denom(X) = Π_i (w_i(X) + β · s_i(X)  + γ)
        //
        // Each term must vanish on H. Dividing by Z_H(X) gives t(X).
        // ----------------------------------------------------------------

        // Lift everything to the coset.
        let advice_coset: Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>> = advice_columns
            .iter()
            .map(|col| lift_to_coset(col, &domain))
            .collect();
        let fixed_coset: &Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>> =
            &pp.fixed_columns_coset;
        let selector_coset: Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>> = selector_field
            .iter()
            .map(|sel| lift_to_coset(sel, &domain))
            .collect();
        let e_coset = lift_to_coset(&W.E, &domain);

        // Lift markers once.
        let markers_coset = lift_to_coset(&markers_poly, &domain);
        let active_witness_coset = |k: usize, i: usize| {
            if k == 0 {
                markers_coset[i]
            } else {
                advice_coset[k - 1][i]
            }
        };

        // Permutation polynomials on coset.
        let s_coset: &Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>> =
            &perm_params.s_polys_coset;
        let id_coset: &Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>> =
            &perm_params.id_polys_coset;

        // Z and Z shifted on coset.
        let z_coset = lift_to_coset(&z_evals, &domain);

        // L_0 on coset (1 at row 0, 0 elsewhere on H).
        let l_0_coset = lift_to_coset(&l_0_evals::<C::ScalarExt>(n), &domain);

        let ext_n = domain.extended_len();
        let rotation_step = ext_n / n;
        let all_challenges: Vec<C::ScalarExt> = U
            .challenges
            .iter()
            .copied()
            .chain(std::iter::once(U.u))
            .collect();

        let lambda_sq = lambda.square();

        // construct the polynomial (X - ω^{n-1}) in coefficient form,
        // lift to the coset, and use it as a factor.

        let mut factor_coeffs = vec![C::ScalarExt::ZERO; n];
        factor_coeffs[0] = -omega.pow_vartime([(n - 1) as u64]);
        factor_coeffs[1] = C::ScalarExt::ONE;

        // Convert from Coeff to ExtendedLagrangeCoeff.
        let factor_poly_coeff = domain.coeff_from_vec(factor_coeffs);
        let factor_coset = domain.coeff_to_extended(factor_poly_coeff);

        let mut g_combined = domain.empty_extended();
        g_combined.par_iter_mut().enumerate().for_each(|(i, slot)| {
            // --- Gate identity at coset row i ---
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
            let gate_part = gate_at_i - e_coset[i];

            // --- Permutation recurrence at coset row i ---
            let mut num = C::ScalarExt::ONE;
            let mut denom = C::ScalarExt::ONE;
            for k in 0..perm_params.num_active {
                let w_at_i = active_witness_coset(k, i);
                num *= w_at_i + beta * id_coset[k][i] + gamma;
                denom *= w_at_i + beta * s_coset[k][i] + gamma;
            }
            let z_shifted_coset = |i: usize| z_coset[(i + rotation_step) % ext_n];
            let perm_recur = z_shifted_coset(i) * denom - z_coset[i] * num;
            let perm_recur_with_factor = perm_recur * factor_coset[i];

            // --- Permutation boundary at coset row i ---
            let perm_boundary = l_0_coset[i] * (z_coset[i] - C::ScalarExt::ONE);

            // --- Combine ---
            *slot = gate_part + lambda * perm_recur_with_factor + lambda_sq * perm_boundary;
        });

        // Divide by Z_H(X) and split into chunks.
        let t_on_coset = domain.divide_by_vanishing_poly(g_combined);
        let t_coeffs = domain.extended_to_coeff(t_on_coset);
        let num_chunks = domain.get_quotient_poly_degree();
        let t_chunks_coeffs = split_into_chunks(&t_coeffs, n, num_chunks);

        // Convert t-chunks to evaluation form for the unified IPA.
        let t_chunks_evals: Vec<Vec<C::ScalarExt>> = t_chunks_coeffs
            .iter()
            .map(|chunk| coeffs_to_evals_via_fft(chunk, omega, pp.S.k as u32))
            .collect();

        let t_commitments: Vec<C> = t_chunks_evals
            .iter()
            .map(|evals| pp.ipa_params.ck.commit(evals))
            .collect::<Result<_, _>>()?;

        for c in &t_commitments {
            transcript.absorb_point(c);
        }

        // ----------------------------------------------------------------
        // Phase G: derive ζ and compute Lagrange bases at ζ and ζω.
        // ----------------------------------------------------------------
        let zeta: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        absorb_scalar_as_base::<C, _>(transcript, zeta);
        let zeta_omega = zeta * omega;

        let lagrange_at_zeta = compute_lagrange_basis_at(&domain, zeta, n);
        let lagrange_at_zeta_omega = compute_lagrange_basis_at(&domain, zeta_omega, n);

        // ----------------------------------------------------------------
        // Phase H: compute all claimed evaluations.
        // ----------------------------------------------------------------
        let queries = collect_queries(gate_expr);

        let query_evals: Vec<C::ScalarExt> = queries
            .iter()
            .map(|q| {
                debug_assert_eq!(q.rotation.0, 0);
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

        // Permutation-related evaluations.
        let z_at_zeta = eval_lagrange_at(&z_evals, &lagrange_at_zeta);
        let z_at_zeta_omega = eval_lagrange_at(&z_evals, &lagrange_at_zeta_omega);

        let s_at_zeta: Vec<C::ScalarExt> = perm_params
            .s_polys
            .iter()
            .map(|p| eval_lagrange_at(p, &lagrange_at_zeta))
            .collect();
        let id_at_zeta: Vec<C::ScalarExt> = perm_params
            .id_polys
            .iter()
            .map(|p| eval_lagrange_at(p, &lagrange_at_zeta))
            .collect();

        // Absorb all evaluations into transcript.
        for e in &query_evals {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }
        absorb_scalar_as_base::<C, _>(transcript, e_eval);
        for e in &t_chunks_eval {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }
        absorb_scalar_as_base::<C, _>(transcript, z_at_zeta);
        absorb_scalar_as_base::<C, _>(transcript, z_at_zeta_omega);
        for e in &s_at_zeta {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }
        for e in &id_at_zeta {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }

        // ----------------------------------------------------------------
        // Phase I: main IPA at ζ.
        //
        // All polynomials except shifted-Z open at ζ:
        //   - advice columns (per-column, with offsets)
        //   - fixed columns
        //   - selector columns
        //   - E
        //   - t-chunks
        //   - Z (at ζ)
        //   - s_i for each active column
        //   - id_i for each active column
        // ----------------------------------------------------------------
        let alpha: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        absorb_scalar_as_base::<C, _>(transcript, alpha);

        let openings = gather_openings_with_permutation(
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
            &z_evals,
            &z_commitment,
            &perm_params.s_polys,
            &perm_params.s_commitments,
            &perm_params.id_polys,
            &perm_params.id_commitments,
            &query_evals,
            e_eval,
            &t_chunks_eval,
            z_at_zeta,
            &s_at_zeta,
            &id_at_zeta,
            n,
        );

        let total_len = pp.ipa_params.ck.len();
        let f_embedded = combine_evals_embedded(&openings, alpha, total_len);

        // b_embedded: tile lagrange_at_zeta across the full generator range.
        let num_blocks = total_len / n;
        let mut b_embedded = Vec::with_capacity(total_len);
        for _ in 0..num_blocks {
            b_embedded.extend_from_slice(&lagrange_at_zeta);
        }

        let opening_proof = ipa_prove_single(&pp.ipa_params, &f_embedded, &b_embedded, transcript);

        // ----------------------------------------------------------------
        // Phase J: separate IPA for Z at ζω.
        //
        // Z is the only polynomial that opens at a shifted point.
        // We prove it separately to keep the main IPA's b vector uniform.
        // ----------------------------------------------------------------
        let mut z_embedded = vec![C::ScalarExt::ZERO; total_len];
        z_embedded[..n].copy_from_slice(&z_evals);

        let mut b_embedded_zw = Vec::with_capacity(total_len);
        for _ in 0..num_blocks {
            b_embedded_zw.extend_from_slice(&lagrange_at_zeta_omega);
        }

        let opening_proof_zw =
            ipa_prove_single(&pp.ipa_params, &z_embedded, &b_embedded_zw, transcript);

        let prover_elapsed = prover_start.elapsed();
        println!(
            "Prover time for gate decider: {} s",
            prover_elapsed.as_millis() / 1000
        );

        Ok(GateDeciderProof {
            t_commitments,
            advice_column_commitments: advice_commitments_per_column,
            z_commitment,
            evals: GateEvaluations {
                queries: query_evals,
                e_eval,
                t_chunks: t_chunks_eval,
                z_at_zeta,
                z_at_zeta_omega,
                s_at_zeta,
                id_at_zeta,
            },
            opening_proof,
            opening_proof_zw,
        })
    }

    // =================================================================
    // Verifier side
    // =================================================================

    /// Verify the gate-identity and permutation portions of a decider proof.
    pub fn verify_decider_gate_part(
        vp: &GateDeciderVerifierParam<C>,
        perm_params: &PermutationParams<C>,
        U: &RelaxedPlonkInstance<C, MARKERS_LEN>,
        proof: &GateDeciderProof<C>,
        transcript: &mut impl ROTrait<C::Base>,
    ) -> Result<(), VerifyError> {
        let n = 1usize << vp.k;
        let n_u64 = n as u64;

        // ----------------------------------------------------------------
        // Step 1: reconstruction check on advice commitments.
        //
        // The per-column commitments in the proof must sum to U.W_commitments[0],
        // binding the proof to the folded accumulator.
        // ----------------------------------------------------------------
        let expected_num_chunks = vp.gate_degree.saturating_sub(1).max(1);
        if proof.evals.t_chunks.len() != expected_num_chunks
            || proof.t_commitments.len() != expected_num_chunks
        {
            return Err(VerifyError::ProofShapeMismatch);
        }

        let reconstructed: C = proof
            .advice_column_commitments
            .iter()
            .fold(C::CurveExt::identity(), |acc, c| acc + c.to_curve())
            .to_affine();

        if U.W_commitments.len() != 1 || reconstructed != U.W_commitments[0] {
            return Err(VerifyError::OpeningFailed {
                error: "round commitment reconstruction mismatch".into(),
            });
        }

        // ----------------------------------------------------------------
        // Step 2: mirror the prover's transcript exactly.
        // ----------------------------------------------------------------
        transcript.absorb(U);

        for c in &proof.advice_column_commitments {
            transcript.absorb_point(c);
        }

        let beta: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        absorb_scalar_as_base::<C, _>(transcript, beta);
        let gamma: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        absorb_scalar_as_base::<C, _>(transcript, gamma);

        transcript.absorb_point(&proof.z_commitment);

        let lambda: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        absorb_scalar_as_base::<C, _>(transcript, lambda);
        let lambda_sq = lambda.square();

        for c in &proof.t_commitments {
            transcript.absorb_point(c);
        }

        let zeta: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        absorb_scalar_as_base::<C, _>(transcript, zeta);
        let zeta_omega = zeta * vp.omega;

        // Build a verifier-side domain for Lagrange basis computation.
        // j=1 is sufficient — we only need iFFT-related machinery.
        let domain = EvaluationDomain::<C::ScalarExt>::new(1, vp.k as u32);
        let lagrange_at_zeta = compute_lagrange_basis_at(&domain, zeta, n);
        let lagrange_at_zeta_omega = compute_lagrange_basis_at(&domain, zeta_omega, n);

        // ----------------------------------------------------------------
        // Step 3: gate identity at ζ.
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

        // ----------------------------------------------------------------
        // Step 4: permutation identity at ζ.
        //
        // Reconstruct the values of active columns at ζ:
        //   - Active column 0: markers polynomial, evaluated by verifier
        //     directly from U.consistency_markers (no commitment needed).
        //   - Active columns 1..num_active: advice columns, extracted
        //     from proof.evals.queries by matching the Query layout.
        // ----------------------------------------------------------------
        let mut markers_poly = vec![C::ScalarExt::ZERO; n];
        for (j, m) in U.consistency_markers.iter().enumerate() {
            markers_poly[j] = *m;
        }
        let markers_at_zeta = eval_lagrange_at(&markers_poly, &lagrange_at_zeta);

        let mut w_active_at_zeta = Vec::with_capacity(perm_params.num_active);
        w_active_at_zeta.push(markers_at_zeta);

        for col_idx in 0..vp.query_layout.num_advice {
            let q_idx = queries.iter().position(|q| {
                matches!(
                    vp.query_layout.resolve(q.index),
                    ResolvedQuery::Advice(c) if c == col_idx
                ) && q.rotation.0 == 0
            });
            match q_idx {
                Some(idx) => w_active_at_zeta.push(proof.evals.queries[idx]),
                None => {
                    // Advice column doesn't appear in the gate at rotation 0.
                    // For the current implementation we require it to.
                    return Err(VerifyError::ProofShapeMismatch);
                }
            }
        }
        debug_assert_eq!(w_active_at_zeta.len(), perm_params.num_active);

        // Sanity-check that the proof's s_at_zeta and id_at_zeta have the
        // right shape.
        if proof.evals.s_at_zeta.len() != perm_params.num_active
            || proof.evals.id_at_zeta.len() != perm_params.num_active
        {
            return Err(VerifyError::ProofShapeMismatch);
        }

        // Compute the recurrence at ζ.
        let mut num_at_zeta = C::ScalarExt::ONE;
        let mut denom_at_zeta = C::ScalarExt::ONE;
        for i in 0..perm_params.num_active {
            num_at_zeta *= w_active_at_zeta[i] + beta * proof.evals.id_at_zeta[i] + gamma;
            denom_at_zeta *= w_active_at_zeta[i] + beta * proof.evals.s_at_zeta[i] + gamma;
        }

        let perm_recur_at_zeta =
            proof.evals.z_at_zeta_omega * denom_at_zeta - proof.evals.z_at_zeta * num_at_zeta;

        // Boundary at ζ: L_0(ζ) · (Z(ζ) - 1).
        let l_0_at_zeta = lagrange_at_zeta[0];
        let perm_boundary_at_zeta = l_0_at_zeta * (proof.evals.z_at_zeta - C::ScalarExt::ONE);

        // ----------------------------------------------------------------
        // Step 5: combined identity check.
        //
        //   (gate_at_zeta - e_eval) + λ · perm_recur + λ² · perm_boundary
        //     ==  Z_H(ζ) · t(ζ)
        // ----------------------------------------------------------------
        let zeta_minus_omega_n_minus_1 = zeta - vp.omega.pow_vartime([(n - 1) as u64]);
        let combined_lhs = (gate_at_zeta - proof.evals.e_eval)
            + lambda * perm_recur_at_zeta * zeta_minus_omega_n_minus_1
            + lambda_sq * perm_boundary_at_zeta;

        let z_h_at_zeta = zeta.pow_vartime([n_u64]) - C::ScalarExt::ONE;
        let t_at_zeta = combine_quotient_chunks(&proof.evals.t_chunks, zeta, n_u64);
        let combined_rhs = z_h_at_zeta * t_at_zeta;

        if combined_lhs != combined_rhs {
            return Err(VerifyError::GateIdentityMismatch);
        }

        // ----------------------------------------------------------------
        // Step 6: absorb evaluations and derive α (mirroring prover).
        // ----------------------------------------------------------------
        for e in &proof.evals.queries {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }
        absorb_scalar_as_base::<C, _>(transcript, proof.evals.e_eval);
        for e in &proof.evals.t_chunks {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }
        absorb_scalar_as_base::<C, _>(transcript, proof.evals.z_at_zeta);
        absorb_scalar_as_base::<C, _>(transcript, proof.evals.z_at_zeta_omega);
        for e in &proof.evals.s_at_zeta {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }
        for e in &proof.evals.id_at_zeta {
            absorb_scalar_as_base::<C, _>(transcript, *e);
        }

        let alpha: C::ScalarExt = transcript.squeeze(NUM_CHALLENGE_BITS);
        absorb_scalar_as_base::<C, _>(transcript, alpha);

        // ----------------------------------------------------------------
        // Step 7: combine commitments and evaluations for the main IPA.
        // ----------------------------------------------------------------
        let commitments_in_order = gather_commitments_with_permutation(
            &queries,
            &vp.query_layout,
            &proof.advice_column_commitments,
            &vp.fixed_commitments,
            &vp.selector_commitments,
            &U.E_commitment,
            &proof.t_commitments,
            &proof.z_commitment,
            &perm_params.s_commitments,
            &perm_params.id_commitments,
        );

        let evals_in_order: Vec<C::ScalarExt> = proof
            .evals
            .queries
            .iter()
            .copied()
            .chain(std::iter::once(proof.evals.e_eval))
            .chain(proof.evals.t_chunks.iter().copied())
            .chain(std::iter::once(proof.evals.z_at_zeta))
            .chain(proof.evals.s_at_zeta.iter().copied())
            .chain(proof.evals.id_at_zeta.iter().copied())
            .collect();

        debug_assert_eq!(commitments_in_order.len(), evals_in_order.len());

        let (c_combined, v_combined) =
            combine_for_ipa(&commitments_in_order, &evals_in_order, alpha);

        // ----------------------------------------------------------------
        // Step 8: verify the main IPA at ζ.
        // ----------------------------------------------------------------
        let total_len = vp.ipa_params.ck.len();
        let num_blocks = total_len / n;
        let mut b_embedded = Vec::with_capacity(total_len);
        for _ in 0..num_blocks {
            b_embedded.extend_from_slice(&lagrange_at_zeta);
        }

        ipa_verify_single(
            &vp.ipa_params,
            c_combined,
            v_combined,
            &b_embedded,
            &proof.opening_proof,
            transcript,
        )?;

        // ----------------------------------------------------------------
        // Step 9: verify the separate IPA for Z at ζω.
        // ----------------------------------------------------------------
        let mut b_embedded_zw = Vec::with_capacity(total_len);
        for _ in 0..num_blocks {
            b_embedded_zw.extend_from_slice(&lagrange_at_zeta_omega);
        }

        ipa_verify_single(
            &vp.ipa_params,
            proof.z_commitment,
            proof.evals.z_at_zeta_omega,
            &b_embedded_zw,
            &proof.opening_proof_zw,
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

// Build a function that evaluates expr at H row j, NOT coset.
fn eval_expr_at_H_row<F: PrimeField>(
    expr: &Expression<F>,
    layout: &QueryLayout,
    row: usize,
    advice_evals_on_H: &[Vec<F>],
    fixed_evals_on_H: &[Vec<F>],
    selector_evals_on_H: &[Vec<F>],
    challenges: &[F],
    n: usize,
) -> F {
    match expr {
        Expression::Constant(c) => *c,
        Expression::Challenge(i) => challenges[*i],
        Expression::Polynomial(q) => {
            // Rotation r on H: row (r + row) mod n.
            let r = ((row as i64 + q.rotation.0 as i64).rem_euclid(n as i64)) as usize;
            match layout.resolve(q.index) {
                ResolvedQuery::Advice(i) => advice_evals_on_H[i][r],
                ResolvedQuery::Fixed(i) => fixed_evals_on_H[i][r],
                ResolvedQuery::Selector(i) => selector_evals_on_H[i][r],
            }
        }
        Expression::Negated(inner) => -eval_expr_at_H_row(
            inner,
            layout,
            row,
            advice_evals_on_H,
            fixed_evals_on_H,
            selector_evals_on_H,
            challenges,
            n,
        ),
        Expression::Sum(a, b) => {
            eval_expr_at_H_row(
                a,
                layout,
                row,
                advice_evals_on_H,
                fixed_evals_on_H,
                selector_evals_on_H,
                challenges,
                n,
            ) + eval_expr_at_H_row(
                b,
                layout,
                row,
                advice_evals_on_H,
                fixed_evals_on_H,
                selector_evals_on_H,
                challenges,
                n,
            )
        }
        Expression::Product(a, b) => {
            eval_expr_at_H_row(
                a,
                layout,
                row,
                advice_evals_on_H,
                fixed_evals_on_H,
                selector_evals_on_H,
                challenges,
                n,
            ) * eval_expr_at_H_row(
                b,
                layout,
                row,
                advice_evals_on_H,
                fixed_evals_on_H,
                selector_evals_on_H,
                challenges,
                n,
            )
        }
        Expression::Scaled(inner, s) => {
            eval_expr_at_H_row(
                inner,
                layout,
                row,
                advice_evals_on_H,
                fixed_evals_on_H,
                selector_evals_on_H,
                challenges,
                n,
            ) * s
        }
    }
}
