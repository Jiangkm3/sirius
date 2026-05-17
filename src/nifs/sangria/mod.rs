use std::sync::Arc;
use std::{marker::PhantomData, num::NonZeroUsize};

use count_to_non_zero::CountToNonZeroExt;
use itertools::Itertools;
use rayon::prelude::*;
use some_to_err::ErrOr;
use tracing::*;

pub use self::accumulator::{
    FoldablePlonkInstance, FoldablePlonkTrace, RelaxedPlonkInstance, RelaxedPlonkTrace,
};
pub use self::decider::{
    GateDeciderProof, GateDeciderProverParam, GateDeciderVerifierParam, QueryLayout,
};
pub use crate::plonk::PlonkInstance;
use crate::{
    commitment::{self, CommitmentKey},
    concat_vec,
    constants::NUM_CHALLENGE_BITS,
    ff::Field,
    halo2_proofs::{
        arithmetic::CurveAffine,
        halo2curves::ff::{FromUniformBytes, PrimeField, PrimeFieldBits, WithSmallOrderMulGroup},
        plonk::Error as Halo2Error,
    },
    ivc::{sangria::instances_accumulator_computation, Instances},
    nifs::sangria::accumulator::RelaxedPlonkWitness,
    plonk::{
        self,
        eval::{Error as EvalError, GetDataForEval, PlonkEvalDomain},
        PlonkStructure, PlonkWitness,
    },
    polynomial::{graph_evaluator::GraphEvaluator, sparse::SparseMatrix},
    poseidon::ROTrait,
    sps::{Error as SpsError, SpecialSoundnessVerifier},
};

pub mod accumulator;
pub mod decider;
pub mod ipa;
pub mod permutation;

// =====================================================================
// Cross-term types
// =====================================================================

pub type CrossTerms<C> = Vec<Box<[<C as CurveAffine>::ScalarExt]>>;
pub type CrossTermCommits<C> = Vec<C>;

// =====================================================================
// VanillaFS struct and per-step folding API
// =====================================================================

#[derive(Clone, Debug)]
pub struct VanillaFS<C: CurveAffine, const MARKERS_LEN: usize = CONSISTENCY_MARKERS_COUNT> {
    _marker: PhantomData<C>,
}

pub struct ProverParam<C: CurveAffine> {
    pub(crate) S: PlonkStructure<C::ScalarExt>,
    /// digest of public parameter of IVC circuit
    pub pp_digest: (C::Base, C::Base),
}

impl<C: CurveAffine, const MARKERS_LEN: usize> VanillaFS<C, MARKERS_LEN>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    // commit_cross_terms
    #[instrument(skip_all)]
    pub fn commit_cross_terms(
        ck: &CommitmentKey<C>,
        S: &PlonkStructure<C::ScalarExt>,
        U1: &RelaxedPlonkInstance<C, MARKERS_LEN>,
        W1: &RelaxedPlonkWitness<C::ScalarExt>,
        U2: &PlonkInstance<C>,
        W2: &PlonkWitness<C::ScalarExt>,
    ) -> Result<(CrossTerms<C>, CrossTermCommits<C>), Error> {
        let data = PlonkEvalDomain {
            num_advice: S.num_advice_columns,
            num_lookup: S.num_lookups(),
            challenges: &concat_vec!(
                &U1.challenges,
                &[U1.u],
                &U2.challenges,
                &[RelaxedPlonkInstance::<C, MARKERS_LEN>::DEFAULT_u]
            ),
            selectors: &S.selectors,
            fixed: &S.fixed_columns,
            W1s: &W1.W,
            W2s: &W2.W,
        };

        let row_size = data.row_size();

        let evaluation_span = info_span!("evaluation").entered();
        let cross_terms = {
            S.custom_gates_lookup_compressed
                .grouped()
                .iter_cross_terms()
                .map(|optional_expr| match optional_expr {
                    Some(expr) => {
                        let evaluator = GraphEvaluator::new(expr);
                        let n_chunks = rayon::current_num_threads();
                        let chunk_sz = (row_size + n_chunks - 1) / n_chunks;
                        let ranges: Vec<(usize, usize)> = (0..n_chunks)
                            .map(|i| {
                                let start = i * chunk_sz;
                                let end = ((i + 1) * chunk_sz).min(row_size);
                                (start, end)
                            })
                            .filter(|(s, e)| s < e)
                            .collect();

                        let parts: Vec<Vec<_>> = ranges
                            .into_par_iter()
                            .map(|(start, end)| {
                                let mut scratch = evaluator.instance();
                                let mut out = Vec::with_capacity(end - start);
                                for row in start..end {
                                    let v = evaluator.evaluate_with_scratch(
                                        &data,
                                        row,
                                        &mut scratch,
                                    )?;
                                    out.push(v);
                                }
                                Ok::<Vec<<C as CurveAffine>::ScalarExt>, EvalError>(out)
                            })
                            .collect::<Result<Vec<Vec<C::ScalarExt>>, EvalError>>()?;

                        let flat: Vec<_> = parts.into_iter().flatten().collect();
                        let boxed: Box<[_]> = flat.into_boxed_slice();
                        Ok::<Box<[<C as CurveAffine>::ScalarExt]>, EvalError>(boxed)
                    }
                    None => Ok(vec![C::ScalarExt::ZERO; row_size].into_boxed_slice()),
                })
                .collect::<Result<CrossTerms<C>, _>>()?
        };
        evaluation_span.exit();

        let commit_span = info_span!("commit").entered();
        let cross_term_commits: Vec<C> = cross_terms
            .iter()
            .map(|v| ck.commit(v))
            .collect::<Result<Vec<_>, _>>()?;
        commit_span.exit();

        Ok((cross_terms, cross_term_commits))
    }

    // generate_challenge
    #[instrument(skip_all)]
    pub(crate) fn generate_challenge(
        pp_digest: &(C::Base, C::Base),
        ro_acc: &mut impl ROTrait<C::Base>,
        U1: &RelaxedPlonkInstance<C, MARKERS_LEN>,
        U2: &PlonkInstance<C>,
        cross_term_commits: &[C],
    ) -> Result<<C as CurveAffine>::ScalarExt, Error> {
        let _span = info_span!("sangria_cha").entered();
        Ok(ro_acc
            .absorb_field(pp_digest.0)
            .absorb_field(pp_digest.1)
            .absorb(U1)
            .absorb(U2)
            .absorb_point_iter(cross_term_commits.iter())
            .inspect(|buf| debug!("buf before: {buf:?}"))
            .squeeze::<C::ScalarExt>(NUM_CHALLENGE_BITS))
    }
}

// =====================================================================
// Error types — extended with decider-specific variants
// =====================================================================

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("parameter not setup")]
    ParamNotSetup,
    #[error(transparent)]
    Eval(#[from] EvalError),
    #[error(transparent)]
    Sps(#[from] SpsError),
    #[error(transparent)]
    Plonk(#[from] Halo2Error),
    #[error(transparent)]
    Commitment(#[from] commitment::Error),
    #[error("In the traces that are folded by this scheme the first column with two elements is expected")]
    NoConsistencyMarkers,
}

pub struct VerifierParam<C: CurveAffine> {
    pp_digest: (C::Base, C::Base),
}

impl<C: CurveAffine> From<(C::Base, C::Base)> for VerifierParam<C> {
    fn from(pp_digest: (C::Base, C::Base)) -> Self {
        Self { pp_digest }
    }
}

impl<C: CurveAffine> VerifierParam<C> {
    /// Accessor used by the decider setup, which inherits pp_digest
    /// from the per-step verifier param.
    pub fn pp_digest(&self) -> (C::Base, C::Base) {
        self.pp_digest
    }
}

// =====================================================================
// Per-step setup / prove / verify
// =====================================================================

impl<C: CurveAffine, const MARKERS_LEN: usize> VanillaFS<C, MARKERS_LEN>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn setup_params(
        pp_digest: C,
        S: PlonkStructure<C::ScalarExt>,
    ) -> Result<(ProverParam<C>, VerifierParam<C>), Error> {
        let pp_digest = {
            let c = pp_digest.coordinates().unwrap();
            (*c.x(), *c.y())
        };
        Ok((ProverParam { S, pp_digest }, VerifierParam { pp_digest }))
    }

    #[instrument(skip_all)]
    pub fn generate_plonk_trace(
        ck: &CommitmentKey<C>,
        instances: &[Vec<C::ScalarExt>],
        witness: &[Vec<C::ScalarExt>],
        pp: &ProverParam<C>,
        ro_nark: &mut impl ROTrait<C::Base>,
    ) -> Result<FoldablePlonkTrace<C, MARKERS_LEN>, Error> {
        pp.S.run_sps_protocol(ck, instances, witness, ro_nark)
            .map(FoldablePlonkTrace::new)?
            .ok_or(Error::NoConsistencyMarkers)
    }

    #[instrument(skip_all)]
    pub fn prove(
        ck: &CommitmentKey<C>,
        pp: &ProverParam<C>,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: RelaxedPlonkTrace<C, MARKERS_LEN>,
        incoming: &[FoldablePlonkTrace<C, MARKERS_LEN>; 1],
    ) -> Result<(RelaxedPlonkTrace<C, MARKERS_LEN>, CrossTermCommits<C>), Error> {
        let incoming = &incoming[0];
        let U1 = &accumulator.U;
        let W1 = &accumulator.W;
        let U2 = &incoming.u;
        let W2 = &incoming.w;

        let (cross_terms, cross_term_commits) =
            Self::commit_cross_terms(ck, &pp.S, U1, W1, U2, W2)?;

        let r = VanillaFS::generate_challenge(&pp.pp_digest, ro_acc, U1, U2, &cross_term_commits)?;
        debug!("sangria_cha: {r:?}");

        let U = U1.fold(U2, &cross_term_commits, &r);
        let W = W1.fold(W2, &cross_terms, &r);

        Ok((RelaxedPlonkTrace { U, W }, cross_term_commits))
    }

    pub fn verify(
        vp: &VerifierParam<C>,
        ro_nark: &mut impl ROTrait<C::Base>,
        ro_acc: &mut impl ROTrait<C::Base>,
        U1: &RelaxedPlonkInstance<C>,
        U2: &[FoldablePlonkInstance<C>; 1],
        cross_term_commits: &CrossTermCommits<C>,
    ) -> Result<RelaxedPlonkInstance<C>, Error> {
        let U2 = &U2[0];
        U2.sps_verify(ro_nark)?;
        let r = VanillaFS::generate_challenge(&vp.pp_digest, ro_acc, U1, U2, cross_term_commits)?;
        Ok(U1.fold(U2, cross_term_commits, &r))
    }
}

// =====================================================================
// VerifyError — extended with decider-specific variants
// =====================================================================

#[derive(Debug, thiserror::Error)]
pub enum VerifyError {
    #[error(transparent)]
    Plonk(#[from] plonk::Error),
    #[error(transparent)]
    Eval(#[from] plonk::eval::Error),
    #[error("Manually accumulation instance columns does not return same as stored")]
    InstancesHashMismatch,
    #[error("(Relaxed) plonk relation not satisfied: commitment of E")]
    ECommitmentMismatch,
    #[error("Permutation check fail: mismatch_count {mismatch_count}")]
    PermCheckFail { mismatch_count: usize },
    #[error("Instance mismatch")]
    InstanceMismatch,
    #[error("Proof shape mismatch")]
    ProofShapeMismatch,
    #[error("Gate identity mismatch")]
    GateIdentityMismatch,
    #[error("Opening failed: {error}")]
    OpeningFailed { error: String },
}

// =====================================================================
// is_sat_* family — kept for debugging/tests
//
// is_sat_pub_instances refactored to delegate to an instance-only variant
// that the decider verifier can call directly.
// =====================================================================

impl<C: CurveAffine, const MARKERS_LEN: usize> VanillaFS<C, MARKERS_LEN>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn is_sat_accumulation(
        S: &PlonkStructure<C::ScalarExt>,
        acc: &RelaxedPlonkTrace<C, MARKERS_LEN>,
    ) -> Result<(), VerifyError> {
        let RelaxedPlonkTrace { U, W } = acc;
        let total_row = 1 << S.k;
        let data = PlonkEvalDomain {
            num_advice: S.num_advice_columns,
            num_lookup: S.num_lookups(),
            challenges: &concat_vec!(&U.challenges, &[U.u]),
            selectors: &S.selectors,
            fixed: &S.fixed_columns,
            W1s: &W.W,
            W2s: &[],
        };

        let evaluator = GraphEvaluator::new(S.custom_gates_lookup_compressed.homogeneous());
        (0..total_row)
            .into_par_iter()
            .map(|row| {
                evaluator.evaluate(&data, row).map(|eval_of_row| {
                    let expected = W.E[row];
                    if eval_of_row.eq(&expected) {
                        0
                    } else {
                        warn!("row {row} invalid: expected {expected:?}, but {eval_of_row:?}");
                        1
                    }
                })
            })
            .try_reduce(
                || 0,
                |mismatch_count, is_missed| Ok(mismatch_count + is_missed),
            )
            .map(|mismatch_count| {
                Some(plonk::Error::EvaluationMismatch {
                    mismatch_count: NonZeroUsize::new(mismatch_count)?,
                    total_row,
                })
            })?
            .err_or(())?;

        if !S.is_sat_log_derivative(&W.W) {
            return Err(plonk::Error::LogDerivativeNotSat.into());
        }
        Ok(())
    }

    pub fn is_sat_permutation(
        S: &PlonkStructure<C::ScalarExt>,
        acc: &RelaxedPlonkTrace<C, MARKERS_LEN>,
    ) -> Result<(), VerifyError> {
        fn permutation_data_without_step_circuit_instances<F: PrimeField>(
            S: &PlonkStructure<F>,
        ) -> SparseMatrix<F> {
            S.permutation_data
                .clone()
                .rm_copy_constraints(1..S.num_io.len())
                .matrix(S.k, &S.num_io, S.num_advice_columns)
        }

        let RelaxedPlonkTrace { U, W } = acc;
        let nrow = 1usize << S.k;
        let inst_total_len: usize = S.num_io.iter().sum();
        let wit_len = nrow * S.num_advice_columns;
        let z_len = inst_total_len + wit_len;

        let z_at = |idx: usize| -> C::ScalarExt {
            if idx < MARKERS_LEN {
                U.consistency_markers[idx]
            } else if idx < inst_total_len {
                C::ScalarExt::ZERO
            } else {
                let j = idx - inst_total_len;
                W.W[0].get(j).copied().unwrap_or(C::ScalarExt::ZERO)
            }
        };

        let P = permutation_data_without_step_circuit_instances(S);
        let mut result = vec![C::ScalarExt::ZERO; z_len];

        for (row, col, value) in P.iter() {
            if *row >= z_len {
                panic!(
                    "invalid matrix multiply: row {} out of bounds {}",
                    row, z_len
                );
            }
            if *col >= z_len {
                panic!(
                    "invalid matrix multiply: col {} out of bounds {}",
                    col, z_len
                );
            }
            result[*row] += *value * z_at(*col);
        }

        let mismatch_count = result
            .into_iter()
            .enumerate()
            .filter(|(row, y)| {
                let z = z_at(*row);
                let diff = *y - z;
                if diff.is_zero().into() {
                    false
                } else {
                    warn!("permutation mismatch at {row} with: {y:?} - {z:?} = {diff:?}");
                    true
                }
            })
            .count();

        if mismatch_count == 0 {
            Ok(())
        } else {
            Err(VerifyError::PermCheckFail { mismatch_count })
        }
    }

    pub fn is_sat_witness_commit(
        ck: &CommitmentKey<C>,
        acc: &RelaxedPlonkTrace<C, MARKERS_LEN>,
    ) -> Result<(), VerifyError> {
        let RelaxedPlonkTrace { U, W } = acc;
        U.W_commitments
            .iter()
            .zip_eq(W.W.iter())
            .filter_map(|(Ci, Wi)| ck.commit(Wi).unwrap().ne(Ci).then_some(()))
            .count_to_non_zero()
            .map(|mismatch_count| plonk::Error::CommitmentMismatch { mismatch_count })
            .err_or(())?;

        if ck.commit(&W.E).unwrap().ne(&U.E_commitment) {
            return Err(VerifyError::ECommitmentMismatch);
        }
        Ok(())
    }

    /// Public-instance check that takes a `RelaxedPlonkInstance` directly,
    /// for use by the decider verifier (which doesn't have the witness).
    ///
    /// `is_sat_pub_instances` (which takes the full trace) is preserved as
    /// a thin wrapper for backwards compatibility and test usage.
    pub fn is_sat_pub_instances_with_instance(
        U: &RelaxedPlonkInstance<C, MARKERS_LEN>,
        pub_instances: &[Vec<Vec<C::ScalarExt>>],
    ) -> Result<(), VerifyError> {
        match U.step_circuit_instances_hash_accumulator {
            accumulator::SCInstancesHashAcc::None => {
                assert!(pub_instances
                    .iter()
                    .all(|instances| instances.get_step_circuit_instances().is_empty()));
                Ok(())
            }
            accumulator::SCInstancesHashAcc::Hash(stored_hash) => pub_instances
                .iter()
                .fold(
                    instances_accumulator_computation::get_initial_sc_instances_accumulator::<C>(),
                    |acc, instances| {
                        instances_accumulator_computation::absorb_in_sc_instances_accumulator::<C>(
                            &acc,
                            instances.get_step_circuit_instances(),
                        )
                    },
                )
                .ne(&stored_hash)
                .then_some(VerifyError::InstanceMismatch)
                .err_or(()),
        }
    }

    /// Backwards-compatible wrapper: takes a trace, delegates to the
    /// instance-only variant.
    pub fn is_sat_pub_instances(
        acc: &RelaxedPlonkTrace<C, MARKERS_LEN>,
        pub_instances: &[Vec<Vec<C::ScalarExt>>],
    ) -> Result<(), VerifyError> {
        Self::is_sat_pub_instances_with_instance(&acc.U, pub_instances)
    }

    pub fn is_sat(
        ck: &CommitmentKey<C>,
        S: &PlonkStructure<C::ScalarExt>,
        acc: &RelaxedPlonkTrace<C, MARKERS_LEN>,
        pub_instances: &[Vec<Vec<C::ScalarExt>>],
    ) -> Result<(), Vec<VerifyError>> {
        let mut errors = vec![];
        if let Err(err) = Self::is_sat_accumulation(S, acc) {
            errors.push(err);
        }
        if let Err(err) = Self::is_sat_permutation(S, acc) {
            errors.push(err);
        }
        if let Err(err) = Self::is_sat_witness_commit(ck, acc) {
            errors.push(err);
        }
        if let Err(err) = Self::is_sat_pub_instances(acc, pub_instances) {
            errors.push(err);
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

// =====================================================================
// Decider entry points
//
// These are the production verification path.  The folding scheme
// produces RelaxedPlonkTraces at every step; once IVC finishes, the
// final accumulator is "decided" — a succinct proof is produced that
// it satisfies the relaxed Plonk relation, and the public instances
// are checked against the hash accumulator.
//
// is_sat remains as a debug-time cross-check.
// =====================================================================

impl<C: CurveAffine, const MARKERS_LEN: usize> VanillaFS<C, MARKERS_LEN>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
    C::ScalarExt: PrimeFieldBits + FromUniformBytes<64> + WithSmallOrderMulGroup<3>,
{
    /// Set up the decider's preprocessed parameters.
    ///
    /// Computes commitments to the circuit's fixed and selector columns
    /// (one-time per circuit), constructs IPA setup from the existing
    /// commitment key, and packages everything into prover and verifier
    /// params for the decider.
    ///
    /// Takes the existing per-step `ProverParam` and `VerifierParam` to
    /// inherit `S` and `pp_digest`, avoiding duplication.
    pub fn setup_decider_params(
        pp: &ProverParam<C>,
        ck: &Arc<CommitmentKey<C>>,
        layout: QueryLayout,
    ) -> Result<(GateDeciderProverParam<C>, GateDeciderVerifierParam<C>), Error> {
        decider::setup_decider_params_from_digest::<C, MARKERS_LEN>(
            pp.pp_digest,
            pp.S.clone(),
            ck,
            layout,
        )
    }

    /// Produce a decider proof on the final accumulator.
    ///
    /// Currently runs only the gate-identity portion.  When the
    /// permutation argument is added, this function will compose the
    /// gate proof and the permutation proof into a unified proof object.
    #[instrument(skip_all)]
    pub fn prove_decider(
        decider_pp: &GateDeciderProverParam<C>,
        layout: &QueryLayout,
        final_acc: &RelaxedPlonkTrace<C, MARKERS_LEN>,
        transcript: &mut impl ROTrait<C::Base>,
    ) -> Result<GateDeciderProof<C>, Error> {
        Self::prove_decider_gate_part(
            decider_pp,
            layout,
            &decider_pp.perm_params,
            final_acc,
            transcript,
        )
    }

    /// Verify a decider proof against the final accumulator's instance
    /// and the user's claimed public instances.
    ///
    /// Combines:
    ///   1. The gate-identity check (verify_decider_gate_part)
    ///   2. The public-instance hash check (is_sat_pub_instances_with_instance)
    ///
    /// When the permutation argument is added, this function will also
    /// invoke verify_decider_permutation_part.
    ///
    /// Note: this is the *full* verification path replacing `is_sat`.
    /// The verifier does not need the witness — only the instance, the
    /// proof, and the claimed public instances.
    pub fn verify_decider(
        decider_vp: &GateDeciderVerifierParam<C>,
        U_final: &RelaxedPlonkInstance<C, MARKERS_LEN>,
        pub_instances: &[Vec<Vec<C::ScalarExt>>],
        proof: &GateDeciderProof<C>,
        transcript: &mut impl ROTrait<C::Base>,
    ) -> Result<(), VerifyError> {
        Self::verify_decider_gate_part(
            decider_vp,
            &decider_vp.perm_params,
            U_final,
            proof,
            transcript,
        )?;
        Self::is_sat_pub_instances_with_instance(U_final, pub_instances)?;
        Ok(())
    }
}

// =====================================================================
// Consistency markers + step-circuit-instance helpers
// =====================================================================

pub const CONSISTENCY_MARKERS_COUNT: usize = 2;

pub trait GetConsistencyMarkers<const MARKERS: usize, F> {
    fn get_consistency_markers(&self) -> [F; MARKERS];
}

impl<C: CurveAffine, const MARKERS: usize> GetConsistencyMarkers<MARKERS, C::ScalarExt>
    for FoldablePlonkInstance<C, MARKERS>
{
    fn get_consistency_markers(&self) -> [C::ScalarExt; MARKERS] {
        match self.instances.first() {
            Some(instance) if instance.len() == MARKERS => instance.clone().try_into().unwrap(),
            _ => unreachable!("folded plonk instance always have markers"),
        }
    }
}

impl<C: CurveAffine, const MARKERS: usize> GetConsistencyMarkers<MARKERS, C::ScalarExt>
    for RelaxedPlonkInstance<C, MARKERS>
{
    fn get_consistency_markers(&self) -> [C::ScalarExt; MARKERS] {
        self.consistency_markers
    }
}

pub trait GetStepCircuitInstances<F> {
    fn get_step_circuit_instances(&self) -> &[Vec<F>];
}

impl<C: CurveAffine> GetStepCircuitInstances<C::ScalarExt> for PlonkInstance<C> {
    fn get_step_circuit_instances(&self) -> &[Vec<C::ScalarExt>] {
        &self.instances[1..]
    }
}

impl<F: PrimeField> GetStepCircuitInstances<F> for Instances<F> {
    fn get_step_circuit_instances(&self) -> &[Vec<F>] {
        &self[1..]
    }
}

#[cfg(test)]
mod tests;
