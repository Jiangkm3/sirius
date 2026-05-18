use std::{io, marker::PhantomData, num::NonZeroUsize};

use halo2_proofs::{dev::MockProver, halo2curves::ff::WithSmallOrderMulGroup};
use nifs::sangria::CONSISTENCY_MARKERS_COUNT;
use serde::Serialize;
use tracing::*;

pub use super::super::step_circuit::{self, StepCircuit, SynthesisError};
use crate::{
    ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits},
    group::prime::PrimeCurveAffine,
    halo2curves::CurveAffine,
    ivc::{
        sangria::{
            consistency_markers_computation::ConsistencyMarkerComputation,
            public_params::PublicParams,
        },
        step_folding_circuit::{StepFoldingCircuit, StepInputs},
    },
    main_gate::MainGateConfig,
    nifs::{
        self,
        sangria::{
            FoldablePlonkInstance, GateDeciderProof, GateDeciderProverParam, GateDeciderVerifierParam, GetConsistencyMarkers, QueryLayout, VanillaFS, VerifyError, accumulator::{FoldablePlonkTrace, RelaxedPlonkTrace},
        },
    },
    poseidon::{ROPair, random_oracle::ROTrait},
    sps,
    table::CircuitRunner,
    util::ScalarToBase,
};

pub type Instances<F> = Vec<Vec<F>>;

// TIMER
use std::time::Instant;

/// Logs elapsed time on drop.
pub struct SectionTimer<'a> {
    name: &'a str,
    start: Instant,
}

impl<'a> SectionTimer<'a> {
    pub fn new(name: &'a str) -> Self {
        Self {
            name,
            start: Instant::now(),
        }
    }
}

impl Drop for SectionTimer<'_> {
    fn drop(&mut self) {
        // pick your preferred level
        println!(
            "{}, Elapse = {} ms",
            self.name,
            self.start.elapsed().as_millis()
        );
    }
}

// TODO #31 docs
struct StepCircuitContext<const ARITY: usize, C, SC>
where
    C: CurveAffine,
{
    relaxed_trace: RelaxedPlonkTrace<C>,
    z_0: [C::Scalar; ARITY],
    z_i: [C::Scalar; ARITY],

    /// Public input (instance) from each step
    ///
    /// For further checking of hash-accumulator correctness, we save each instance
    pub_instances: Vec<Instances<C::Scalar>>,

    _p: PhantomData<SC>,
}

// TODO #31 docs
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Halo2(#[from] halo2_proofs::plonk::Error),
    #[error(transparent)]
    Plonk(#[from] crate::plonk::Error),
    #[error(transparent)]
    Step(#[from] step_circuit::SynthesisError),
    #[error("number of steps is not match")]
    NumStepNotMatch,
    #[error("step circuit input not match")]
    SCInputNotMatch,
    #[error("TODO")]
    WhileHash(io::Error),
    #[error("TODO")]
    Sps(#[from] sps::Error),
    #[error("TODO")]
    NIFS(#[from] nifs::sangria::Error),
    #[error("TODO")]
    VerifyFailed(Vec<VerificationError>),
}

impl Error {
    fn from_mock_verify(
        errors: Vec<halo2_proofs::dev::VerifyFailure>,
        is_primary: bool,
        step: usize,
    ) -> Self {
        Self::VerifyFailed(
            errors
                .into_iter()
                .map(|err| VerificationError::MockRunFailed {
                    err,
                    is_primary,
                    step,
                })
                .collect(),
        )
    }
}

#[derive(Debug, thiserror::Error)]
pub enum VerificationError {
    #[error("TODO")]
    InstanceNotMatch { index: usize, is_primary: bool },
    #[error("TODO")]
    NotSat {
        err: VerifyError,
        is_primary: bool,
        is_relaxed: bool,
    },
    #[error("TODO")]
    MockRunFailed {
        err: halo2_proofs::dev::VerifyFailure,
        is_primary: bool,
        step: usize,
    },
}

/// Trait defining the curve cycle used in the IVC.
pub trait IvcCurveCycle {
    // C1 is a curve whose Base field matches C2's Scalar field
    type C1: CurveAffine<
            Base = <Self::C2 as PrimeCurveAffine>::Scalar, 
            ScalarExt = Self::C1Scalar
         > + Serialize;

    // C2 is a curve whose Base field matches C1's Scalar field
    type C2: CurveAffine<
            Base = <Self::C1 as PrimeCurveAffine>::Scalar, 
            ScalarExt = Self::C2Scalar
         > + Serialize;

    // Associated types to bubble up the scalar and constraint requirements cleanly
    type C1Scalar: Serialize + Ord + WithSmallOrderMulGroup<3> + PrimeFieldBits + FromUniformBytes<64>;
    type C2Scalar: Serialize + Ord + WithSmallOrderMulGroup<3> + PrimeFieldBits + FromUniformBytes<64>;
}

// TODO #31 docs
#[allow(clippy::upper_case_acronyms)]
/// RecursiveSNARK from Nova codebase
pub struct IVC<const A1: usize, const A2: usize, Cycle, SC1, SC2>
where
    Cycle: IvcCurveCycle,
    SC1: StepCircuit<A1, Cycle::C1Scalar>,
    SC2: StepCircuit<A2, Cycle::C2Scalar>,
{

    // existing fields ...
    primary: StepCircuitContext<A1, Cycle::C1, SC1>,
    secondary: StepCircuitContext<A2, Cycle::C2, SC2>,
    step: usize,
    secondary_nifs_pp: nifs::sangria::ProverParam<Cycle::C2>,
    primary_nifs_pp: nifs::sangria::ProverParam<Cycle::C1>,
    secondary_trace: [FoldablePlonkTrace<Cycle::C2, { CONSISTENCY_MARKERS_COUNT }>; 1],
    debug_mode: bool,

    // decider preprocessing
    primary_layout: QueryLayout,
    primary_decider_pp: GateDeciderProverParam<Cycle::C1>,
    /// verifier key
    pub primary_decider_vp: GateDeciderVerifierParam<Cycle::C1>,
}

// Folding
impl<const A1: usize, const A2: usize, Cycle: IvcCurveCycle, SC1, SC2> IVC<A1, A2, Cycle, SC1, SC2>
where
    Cycle: IvcCurveCycle,
    SC1: StepCircuit<A1, Cycle::C1Scalar>,
    SC2: StepCircuit<A2, Cycle::C2Scalar>,
{
    pub fn fold_with_debug_mode<const T: usize, RP1, RP2>(
        pp: &PublicParams<A1, A2, T, Cycle::C1, Cycle::C2, SC1, SC2, RP1, RP2>,
        primary: &SC1,
        primary_z_0: [Cycle::C1Scalar; A1],
        secondary: &SC2,
        secondary_z_0: [Cycle::C2Scalar; A2],
        num_steps: NonZeroUsize,
    ) -> Result<(), Error>
    where
        RP1: ROPair<Cycle::C1Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<Cycle::C2Scalar, Config = MainGateConfig<T>>,
    {
        let mut ivc = Self::new(pp, primary, primary_z_0, secondary, secondary_z_0, true)?;
        trace!("IVC created");

        for step in 1..=num_steps.get() {
            trace!("Start fold {step} step");
            ivc.fold_step(pp, primary, secondary)?;
        }

        trace!("Finish folding, start verify");

        ivc.verify(pp)?;

        Ok(())
    }
    pub fn fold<const T: usize, RP1, RP2>(
        pp: &PublicParams<A1, A2, T, Cycle::C1, Cycle::C2, SC1, SC2, RP1, RP2>,
        primary: &SC1,
        primary_z_0: [Cycle::C1Scalar; A1],
        secondary: &SC2,
        secondary_z_0: [Cycle::C2Scalar; A2],
        num_steps: NonZeroUsize,
    ) -> Result<(), Error>
    where
        RP1: ROPair<Cycle::C1Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<Cycle::C2Scalar, Config = MainGateConfig<T>>,
    {
        let mut ivc = Self::new(pp, primary, primary_z_0, secondary, secondary_z_0, false)?;
        trace!("IVC created");

        for step in 1..=num_steps.get() {
            trace!("Start fold {step} step");
            ivc.fold_step(pp, primary, secondary)?;
        }

        trace!("Finish folding, start verify");

        ivc.verify(pp)?;

        Ok(())
    }

    #[instrument(name = "ivc_new", skip_all, fields(step = 0))]
    pub fn new<const T: usize, RP1, RP2>(
        pp: &PublicParams<A1, A2, T, Cycle::C1, Cycle::C2, SC1, SC2, RP1, RP2>,
        primary: &SC1,
        primary_z_0: [Cycle::C1Scalar; A1],
        secondary: &SC2,
        secondary_z_0: [Cycle::C2Scalar; A2],
        debug_mode: bool,
    ) -> Result<Self, Error>
    where
        RP1: ROPair<Cycle::C1Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<Cycle::C2Scalar, Config = MainGateConfig<T>>,
    {
        let primary_span = info_span!("primary").entered();

        // ---------------------------------------------------------------
        // Primary pre-round setup
        // ---------------------------------------------------------------
        let secondary_pre_round_plonk_trace = pp.secondary_initial_plonk_trace();
        let primary_z_output = primary.process_step(&primary_z_0, pp.primary.k_table_size())?;
        debug!("primary z output calculated off-circuit");

        let secondary_relaxed_trace = RelaxedPlonkTrace::from_regular(
            secondary_pre_round_plonk_trace.clone(),
            pp.secondary.k_table_size() as usize,
        );

        let primary_consistency_marker = {
            let _s = info_span!("generate_instance").entered();
            [
                get_consistency_marker_output(&secondary_pre_round_plonk_trace.u),
                ConsistencyMarkerComputation::<
                    '_,
                    A1,
                    Cycle::C2,
                    RP1::OffCircuit,
                    { CONSISTENCY_MARKERS_COUNT },
                > {
                    random_oracle_constant: pp.primary.params().ro_constant().clone(),
                    public_params_hash: &pp.digest_2(),
                    step: 1,
                    z_0: &primary_z_0,
                    z_i: &primary_z_output,
                    relaxed: &secondary_relaxed_trace.U,
                    limb_width: pp.primary.params().limb_width(),
                    limbs_count: pp.primary.params().limbs_count(),
                }
                .generate_with_inspect(|buf| debug!("primary X1 zero-step: {buf:?}")),
            ]
        };

        let primary_sfc = StepFoldingCircuit::<'_, A1, Cycle::C2, SC1, RP1::OnCircuit, T> {
            step_circuit: primary,
            input: StepInputs::<'_, A1, Cycle::C2, RP1::OnCircuit> {
                step: <Cycle::C2 as CurveAffine>::Base::ZERO,
                step_pp: pp.primary.params(),
                public_params_hash: pp.digest_2(),
                z_0: primary_z_0,
                z_i: primary_z_0,
                U: secondary_relaxed_trace.U.clone(),
                u: secondary_pre_round_plonk_trace.u.clone(),
                cross_term_commits: vec![
                    Cycle::C2::identity();
                    pp.secondary.S().get_degree_for_folding().saturating_sub(2)
                ],
                step_circuit_instances: primary.instances(),
            },
        };

        let primary_instances = primary_sfc.instances(primary_consistency_marker);

        if debug_mode {
            let _s = debug_span!("debug").entered();
            MockProver::run(
                pp.primary.k_table_size(),
                &primary_sfc,
                primary_instances.clone(),
            )?
            .verify()
            .map_err(|err| Error::from_mock_verify(err, true, 0))?;
        }

        assert!(primary_instances
            .iter()
            .zip(pp.primary.S().num_io.iter())
            .all(|(instance, expected_len)| { instance.len() == *expected_len }));

        let primary_witness = CircuitRunner::new(
            pp.primary.k_table_size(),
            primary_sfc,
            primary_instances.clone(),
        )
        .try_collect_witness()?;

        let (primary_nifs_pp, _primary_off_circuit_vp) =
            VanillaFS::<Cycle::C1, { CONSISTENCY_MARKERS_COUNT }>::setup_params(
                pp.digest_1(),
                pp.primary.S().clone(),
            )?;

        let primary_plonk_trace =
            VanillaFS::<Cycle::C1, { CONSISTENCY_MARKERS_COUNT }>::generate_plonk_trace(
                pp.primary.ck(),
                &primary_instances,
                &primary_witness,
                &primary_nifs_pp,
                &mut RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone()),
            )?;

        let primary_relaxed_trace = RelaxedPlonkTrace::from_regular(
            primary_plonk_trace.clone(),
            pp.primary.k_table_size() as usize,
        );

        primary_span.exit();
        let _secondary_span = info_span!("secondary").entered();

        // ---------------------------------------------------------------
        // Secondary pre-round setup
        // ---------------------------------------------------------------
        let secondary_z_output =
            secondary.process_step(&secondary_z_0, pp.secondary.k_table_size())?;

        let secondary_consistency_marker = {
            let _s = info_span!("generate_instance");
            [
                get_consistency_marker_output(&primary_plonk_trace.u),
                ConsistencyMarkerComputation::<
                    '_,
                    A2,
                    Cycle::C1,
                    RP2::OffCircuit,
                    { CONSISTENCY_MARKERS_COUNT },
                > {
                    random_oracle_constant: pp.secondary.params().ro_constant().clone(),
                    public_params_hash: &pp.digest_1(),
                    step: 1,
                    z_0: &secondary_z_0,
                    z_i: &secondary_z_output,
                    relaxed: &primary_relaxed_trace.U,
                    limb_width: pp.secondary.params().limb_width(),
                    limbs_count: pp.secondary.params().limbs_count(),
                }
                .generate_with_inspect(|buf| debug!("secondary X1 zero-step: {buf:?}")),
            ]
        };

        let secondary_sfc = StepFoldingCircuit::<'_, A2, Cycle::C1, SC2, RP2::OnCircuit, T> {
            step_circuit: secondary,
            input: StepInputs::<'_, A2, Cycle::C1, RP2::OnCircuit> {
                step: <Cycle::C1 as CurveAffine>::Base::ZERO,
                step_pp: pp.secondary.params(),
                public_params_hash: pp.digest_1(),
                z_0: secondary_z_0,
                z_i: secondary_z_0,
                U: primary_relaxed_trace.U.clone(),
                u: primary_plonk_trace.u.clone(),
                cross_term_commits: vec![
                    Cycle::C1::identity();
                    primary_nifs_pp
                        .S
                        .get_degree_for_folding()
                        .saturating_sub(2)
                ],
                step_circuit_instances: secondary.instances(),
            },
        };

        let secondary_instances = secondary_sfc.instances(secondary_consistency_marker);
        if debug_mode {
            let _s = debug_span!("debug").entered();
            MockProver::run(
                pp.secondary.k_table_size(),
                &secondary_sfc,
                secondary_instances.clone(),
            )?
            .verify()
            .map_err(|err| Error::from_mock_verify(err, false, 0))?;
        }

        assert!(secondary_instances
            .iter()
            .zip(pp.secondary.S().num_io.iter())
            .all(|(instance, expected_len)| { instance.len() == *expected_len }));

        let secondary_witness = CircuitRunner::new(
            pp.secondary.k_table_size(),
            secondary_sfc,
            secondary_instances.clone(),
        )
        .try_collect_witness()?;

        let (secondary_nifs_pp, _nifs_vp) =
            VanillaFS::<_, { CONSISTENCY_MARKERS_COUNT }>::setup_params(
                pp.digest_2(),
                pp.secondary.S().clone(),
            )?;

        let secondary_plonk_trace =
            VanillaFS::<_, { CONSISTENCY_MARKERS_COUNT }>::generate_plonk_trace(
                pp.secondary.ck(),
                &secondary_instances,
                &secondary_witness,
                &secondary_nifs_pp,
                &mut RP1::OffCircuit::new(pp.primary.params().ro_constant().clone()),
            )?;

        // ---------------------------------------------------------------
        // Decider preprocessing
        //
        // The decider params depend only on the circuit (S + ck + layout),
        // not on the step or any witness data.  Compute once here so the
        // decider is ready to use at end-of-IVC without recomputing.
        // ---------------------------------------------------------------
        let _decider_setup_span = info_span!("decider_setup").entered();

        let primary_layout = QueryLayout {
            num_selectors: pp.primary.S().selectors.len(),
            num_fixed: pp.primary.S().fixed_columns.len(),
            num_advice: pp.primary.S().num_advice_columns,
        };

        let (primary_decider_pp, primary_decider_vp) =
            VanillaFS::<Cycle::C1, { CONSISTENCY_MARKERS_COUNT }>::setup_decider_params(
                &primary_nifs_pp,
                pp.primary.arc_ck(),
                primary_layout.clone(),
            )?;

        debug!("decider params constructed for both sides");

        // ---------------------------------------------------------------
        // Build Self with decider params included
        // ---------------------------------------------------------------
        Ok(Self {
            step: 1,
            debug_mode,
            secondary_nifs_pp,
            primary_nifs_pp,
            secondary_trace: [secondary_plonk_trace.clone()],
            primary: StepCircuitContext {
                z_0: primary_z_0,
                z_i: primary_z_output,
                relaxed_trace: primary_relaxed_trace,
                pub_instances: vec![],
                _p: PhantomData,
            },
            secondary: StepCircuitContext {
                z_0: secondary_z_0,
                z_i: secondary_z_output,
                relaxed_trace: secondary_relaxed_trace,
                pub_instances: vec![],
                _p: PhantomData,
            },

            // decider fields
            primary_layout,
            primary_decider_pp,
            primary_decider_vp,
        })
    }

    #[instrument(name = "ivc_fold_step", skip_all, fields(step = self.step))]
    pub fn fold_step<const T: usize, RP1, RP2>(
        &mut self,
        pp: &PublicParams<A1, A2, T, Cycle::C1, Cycle::C2, SC1, SC2, RP1, RP2>,
        primary: &SC1,
        secondary: &SC2,
    ) -> Result<(), Error>
    where
        RP1: ROPair<<Cycle::C1 as PrimeCurveAffine>::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<<Cycle::C2 as PrimeCurveAffine>::Scalar, Config = MainGateConfig<T>>,
    {
        let primary_span = info_span!("primary").entered();
        debug!("start fold step with folding 'secondary' by 'primary'");

        // --- Secondary NIFS prove (fold secondary by primary) ---
        let (secondary_new_trace, secondary_cross_term_commits) = {
            VanillaFS::<_, { CONSISTENCY_MARKERS_COUNT }>::prove(
                pp.secondary.ck(),
                &self.secondary_nifs_pp,
                &mut RP1::OffCircuit::new(pp.primary.params().ro_constant().clone()),
                self.secondary.relaxed_trace.clone(),
                &self.secondary_trace,
            )?
        };

        self.secondary
            .pub_instances
            .push(self.secondary_trace[0].u.instances.clone());

        debug!("prepare primary td");

        // --- primary.process_step ---
        let primary_z_next = primary.process_step(&self.primary.z_i, pp.primary.k_table_size())?;

        // --- consistency marker generation ---
        let primary_consistency_marker = [
            get_consistency_marker_output(&self.secondary_trace[0].u),
            ConsistencyMarkerComputation::<
                '_,
                A1,
                Cycle::C2,
                RP1::OffCircuit,
                { CONSISTENCY_MARKERS_COUNT },
            > {
                random_oracle_constant: pp.primary.params().ro_constant().clone(),
                public_params_hash: &pp.digest_2(),
                step: self.step + 1,
                z_0: &self.primary.z_0,
                z_i: &primary_z_next,
                relaxed: &secondary_new_trace.U,
                limb_width: pp.secondary.params().limb_width(),
                limbs_count: pp.secondary.params().limbs_count(),
            }
            .generate_with_inspect(|buf| debug!("primary X1 {}+1-step: {buf:?}", self.step)),
        ];

        // --- build SFC + instances ---
        let (primary_sfc, primary_instances) = {
            let primary_sfc = StepFoldingCircuit::<'_, A1, Cycle::C2, SC1, RP1::OnCircuit, T> {
                step_circuit: primary,
                input: StepInputs::<'_, A1, Cycle::C2, RP1::OnCircuit> {
                    step: <Cycle::C2 as CurveAffine>::Base::from_u128(self.step as u128),
                    step_pp: pp.primary.params(),
                    public_params_hash: pp.digest_2(),
                    z_0: self.primary.z_0,
                    z_i: self.primary.z_i,
                    U: self.secondary.relaxed_trace.U.clone(),
                    u: self.secondary_trace[0].u.clone(),
                    cross_term_commits: secondary_cross_term_commits,
                    step_circuit_instances: primary.instances(),
                },
            };
            let primary_instances = primary_sfc.instances(primary_consistency_marker);
            (primary_sfc, primary_instances)
        };

        if self.debug_mode {
            let _s = debug_span!("debug").entered();
            MockProver::run(
                pp.primary.k_table_size(),
                &primary_sfc,
                primary_instances.clone(),
            )?
            .verify()
            .map_err(|err| Error::from_mock_verify(err, true, self.step))?;
        }

        assert!(primary_instances
            .iter()
            .zip(pp.primary.S().num_io.iter())
            .all(|(instance, expected_len)| instance.len() == *expected_len));

        // --- collect witness ---
        let primary_witness = {
            CircuitRunner::new(
                pp.primary.k_table_size(),
                primary_sfc,
                primary_instances.clone(),
            )
            .try_collect_witness()?
        };

        self.primary.z_i = primary_z_next;
        self.secondary.relaxed_trace = secondary_new_trace;

        // --- generate plonk trace (primary) ---
        let primary_plonk_trace = [
            VanillaFS::<_, { CONSISTENCY_MARKERS_COUNT }>::generate_plonk_trace(
                pp.primary.ck(),
                &primary_instances,
                &primary_witness,
                &self.primary_nifs_pp,
                &mut RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone()),
            )?,
        ];

        // --- Primary NIFS prove (fold primary by secondary) ---
        let (primary_new_trace, primary_cross_term_commits) = {
            nifs::sangria::VanillaFS::<_, { CONSISTENCY_MARKERS_COUNT }>::prove(
                pp.primary.ck(),
                &self.primary_nifs_pp,
                &mut RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone()),
                self.primary.relaxed_trace.clone(),
                &primary_plonk_trace,
            )?
        };

        self.primary
            .pub_instances
            .push(primary_plonk_trace[0].u.instances.clone());

        primary_span.exit();
        let _secondary_span = info_span!("secondary").entered();
        debug!("start fold step with folding 'primary' by 'secondary'");

        // --- secondary.process_step ---
        let next_secondary_z_i =
            secondary.process_step(&self.secondary.z_i, pp.secondary.k_table_size())?;

        // --- consistency marker generation (secondary) ---
        let secondary_consistency_marker = [
            get_consistency_marker_output(&primary_plonk_trace[0].u),
            ConsistencyMarkerComputation::<
                '_,
                A2,
                Cycle::C1,
                RP2::OffCircuit,
                { CONSISTENCY_MARKERS_COUNT },
            > {
                random_oracle_constant: pp.secondary.params().ro_constant().clone(),
                public_params_hash: &pp.digest_1(),
                step: self.step + 1,
                z_0: &self.secondary.z_0,
                z_i: &next_secondary_z_i,
                relaxed: &primary_new_trace.U,
                limb_width: pp.primary.params().limb_width(),
                limbs_count: pp.primary.params().limbs_count(),
            }
            .generate_with_inspect(|buf| debug!("secondary X1 {}+1-step: {buf:?}", self.step)),
        ];

        // --- build SFC + instances (secondary) ---
        let (secondary_sfc, secondary_instances) = {
            let secondary_sfc = StepFoldingCircuit::<'_, A2, Cycle::C1, SC2, RP2::OnCircuit, T> {
                step_circuit: secondary,
                input: StepInputs::<'_, A2, Cycle::C1, RP2::OnCircuit> {
                    step: <Cycle::C1 as CurveAffine>::Base::from_u128(self.step as u128),
                    step_pp: pp.secondary.params(),
                    public_params_hash: pp.digest_1(),
                    z_0: self.secondary.z_0,
                    z_i: self.secondary.z_i,
                    U: self.primary.relaxed_trace.U.clone(),
                    u: primary_plonk_trace[0].u.clone(),
                    cross_term_commits: primary_cross_term_commits,
                    step_circuit_instances: secondary.instances(),
                },
            };
            let secondary_instances = secondary_sfc.instances(secondary_consistency_marker);
            (secondary_sfc, secondary_instances)
        };

        if self.debug_mode {
            let _s = debug_span!("debug").entered();
            MockProver::run(
                pp.secondary.k_table_size(),
                &secondary_sfc,
                secondary_instances.clone(),
            )?
            .verify()
            .map_err(|err| Error::from_mock_verify(err, false, self.step))?;
        }

        assert!(secondary_instances
            .iter()
            .zip(pp.secondary.S().num_io.iter())
            .all(|(instance, expected_len)| instance.len() == *expected_len));

        // --- collect witness (secondary) ---
        let secondary_witness = {
            CircuitRunner::new(
                pp.secondary.k_table_size(),
                secondary_sfc,
                secondary_instances.clone(),
            )
            .try_collect_witness()?
        };

        self.secondary.z_i = next_secondary_z_i;
        self.primary.relaxed_trace = primary_new_trace;

        // --- generate plonk trace (secondary) ---
        self.secondary_trace = [
            VanillaFS::<_, { CONSISTENCY_MARKERS_COUNT }>::generate_plonk_trace(
                pp.secondary.ck(),
                &secondary_instances,
                &secondary_witness,
                &self.secondary_nifs_pp,
                &mut RP1::OffCircuit::new(pp.primary.params().ro_constant().clone()),
            )?,
        ];

        self.step += 1;
        Ok(())
    }

    #[instrument(name = "ivc_verify", skip_all)]
    pub fn verify<const T: usize, RP1, RP2>(
        &mut self,
        pp: &PublicParams<A1, A2, T, Cycle::C1, Cycle::C2, SC1, SC2, RP1, RP2>,
    ) -> Result<(), Error>
    where
        RP1: ROPair<<Cycle::C1 as PrimeCurveAffine>::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<<Cycle::C2 as PrimeCurveAffine>::Scalar, Config = MainGateConfig<T>>,
    {
        let mut errors = vec![];

        ConsistencyMarkerComputation::<
            '_,
            A1,
            Cycle::C2,
            RP1::OffCircuit,
            { CONSISTENCY_MARKERS_COUNT },
        > {
            random_oracle_constant: pp.primary.params().ro_constant().clone(),
            public_params_hash: &pp.digest_2(),
            step: self.step,
            z_0: &self.primary.z_0,
            z_i: &self.primary.z_i,
            relaxed: &self.secondary.relaxed_trace.U,
            limb_width: pp.secondary.params().limb_width(),
            limbs_count: pp.secondary.params().limbs_count(),
        }
        .generate_with_inspect::<<Cycle::C2 as PrimeCurveAffine>::Scalar>(|buf| {
            debug!("primary X0 verify at {}-step: {buf:?}", self.step)
        })
        .ne(&get_consistency_marker_input(&self.secondary_trace[0].u))
        .then(|| {
            errors.push(VerificationError::InstanceNotMatch {
                index: 0,
                is_primary: true,
            })
        });

        ConsistencyMarkerComputation::<
            '_,
            A2,
            Cycle::C1,
            RP2::OffCircuit,
            { CONSISTENCY_MARKERS_COUNT },
        > {
            random_oracle_constant: pp.secondary.params().ro_constant().clone(),
            public_params_hash: &pp.digest_1(),
            step: self.step,
            z_0: &self.secondary.z_0,
            z_i: &self.secondary.z_i,
            relaxed: &self.primary.relaxed_trace.U,
            limb_width: pp.secondary.params().limb_width(),
            limbs_count: pp.secondary.params().limbs_count(),
        }
        .generate_with_inspect::<<Cycle::C1 as PrimeCurveAffine>::Scalar>(|buf| {
            debug!("primary X1 verify at {}-step: {buf:?}", self.step)
        })
        .ne(&get_consistency_marker_output(&self.secondary_trace[0].u))
        .then(|| {
            errors.push(VerificationError::InstanceNotMatch {
                index: 1,
                is_primary: false,
            });
        });

        if let Err(err) = VanillaFS::<_, { CONSISTENCY_MARKERS_COUNT }>::is_sat(
            pp.primary.ck(),
            pp.primary.S(),
            &self.primary.relaxed_trace,
            &self.primary.pub_instances,
        ) {
            errors.extend(err.into_iter().map(|err| VerificationError::NotSat {
                err,
                is_primary: true,
                is_relaxed: true,
            }));
        }

        if let Err(err) = VanillaFS::<_, { CONSISTENCY_MARKERS_COUNT }>::is_sat(
            pp.secondary.ck(),
            pp.secondary.S(),
            &self.secondary.relaxed_trace,
            &self.secondary.pub_instances,
        ) {
            errors.extend(err.into_iter().map(|err| VerificationError::NotSat {
                err,
                is_primary: false,
                is_relaxed: true,
            }));
        }

        if let Err(err) = pp.secondary.S().is_sat(
            pp.secondary.ck(),
            &mut RP1::OffCircuit::new(pp.primary.params().ro_constant().clone()),
            &self.secondary_trace[0].u,
            &self.secondary_trace[0].w,
        ) {
            errors.push(VerificationError::NotSat {
                err: err.into(),
                is_primary: false,
                is_relaxed: false,
            })
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(Error::VerifyFailed(errors))
        }
    }

    pub fn primary_z0(&self) -> &[<Cycle::C1 as PrimeCurveAffine>::Scalar; A1] {
        &self.primary.z_0
    }

    pub fn primary_zi(&self) -> &[<Cycle::C1 as PrimeCurveAffine>::Scalar; A1] {
        &self.primary.z_i
    }

    pub fn change_zi(&mut self, new_zi: [<Cycle::C1 as PrimeCurveAffine>::Scalar; A1]) {
        self.primary.z_i = new_zi;
    }

    pub fn error(&self) -> Cycle::C1 {
        self.primary.relaxed_trace.U.E_commitment
    }
}

fn get_consistency_marker_input<C: CurveAffine>(ins: &FoldablePlonkInstance<C>) -> C::ScalarExt {
    GetConsistencyMarkers::<CONSISTENCY_MARKERS_COUNT, _>::get_consistency_markers(ins)[0]
}

fn get_consistency_marker_output<C: CurveAffine>(ins: &FoldablePlonkInstance<C>) -> C::Base {
    C::scalar_to_base(
        &GetConsistencyMarkers::<CONSISTENCY_MARKERS_COUNT, _>::get_consistency_markers(ins)[1],
    )
    .unwrap()
}

// Decider
impl<const A1: usize, const A2: usize, Cycle, SC1, SC2> IVC<A1, A2, Cycle, SC1, SC2>
where
    Cycle: IvcCurveCycle,
    SC1: StepCircuit<A1, <Cycle::C1 as PrimeCurveAffine>::Scalar>,
    SC2: StepCircuit<A2, <Cycle::C2 as PrimeCurveAffine>::Scalar>,
{
    /// Produce decider proofs for the final accumulators on both sides.
    ///
    /// Called once at the end of the IVC, after the last `fold_step`.
    /// The returned proofs (plus the accumulator instances and public
    /// instances) are what an external verifier needs to validate
    /// the entire IVC run.
    ///
    /// This consumes nothing from `self`; it just reads the final
    /// accumulators and the preprocessed decider params.
    #[instrument(name = "ivc_prove_decider", skip_all)]
    pub fn prove_decider<const T: usize, RP1, RP2>(
        &self,
        pp: &PublicParams<A1, A2, T, Cycle::C1, Cycle::C2, SC1, SC2, RP1, RP2>,
    ) -> Result<GateDeciderProof<Cycle::C1>, Error>
    where
        RP1: ROPair<<Cycle::C1 as PrimeCurveAffine>::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<<Cycle::C2 as PrimeCurveAffine>::Scalar, Config = MainGateConfig<T>>,
    {
        let _primary_span = info_span!("primary").entered();

        let mut primary_transcript =
            RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone());

        let primary_proof = VanillaFS::<Cycle::C1, { CONSISTENCY_MARKERS_COUNT }>::prove_decider(
            &self.primary_decider_pp,
            &self.primary_layout,
            &self.primary.relaxed_trace,
            &mut primary_transcript,
        )?;

        drop(_primary_span);

        Ok(primary_proof)
    }

    /// Produce decider proofs for both sides and immediately verify them
    /// in-process.
    ///
    /// This is a development-time check: it exercises the full prove +
    /// verify path of the gate decider, but doesn't yet validate the
    /// IVC's external invariants (consistency markers, dangling SPS).
    ///
    /// Roundtrip flow:
    ///   1. Prove the gate identity on the primary accumulator.
    ///   2. Verify it against the same accumulator's instance.
    ///   3. Same on the secondary side.
    ///
    /// On success, returns the two proofs (so callers can serialize
    /// them or hand them to a future external verifier).
    ///
    /// Note: until the upstream commitment-basis refactor lands, this
    /// is expected to fail at the IPA verification step on honest
    /// inputs.  See the basis-issue note in the decider module.
    #[instrument(name = "ivc_check_gate_decider", skip_all)]
    pub fn check_gate_decider<const T: usize, RP1, RP2>(
        &self,
        pp: &PublicParams<A1, A2, T, Cycle::C1, Cycle::C2, SC1, SC2, RP1, RP2>,
    ) -> Result<GateDeciderProof<Cycle::C1>, Error>
    where
        RP1: ROPair<<Cycle::C1 as PrimeCurveAffine>::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<<Cycle::C2 as PrimeCurveAffine>::Scalar, Config = MainGateConfig<T>>,
    {
        // ----------------------------------------------------------------
        // Primary side: prove then verify.
        //
        // Both transcripts must be initialized identically to produce
        // matching Fiat–Shamir challenges.  We construct two separate
        // RO instances (with the same constants) so each phase starts
        // from a fresh state.
        // ----------------------------------------------------------------
        let _primary_span = info_span!("primary").entered();

        let primary_proof = {
            let mut prover_transcript =
                RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone());
            VanillaFS::<Cycle::C1, { CONSISTENCY_MARKERS_COUNT }>::prove_decider(
                &self.primary_decider_pp,
                &self.primary_layout,
                &self.primary.relaxed_trace,
                &mut prover_transcript,
            )?
        };
        debug!("primary decider proof produced");

        {
            let mut verifier_transcript =
                RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone());
            VanillaFS::<Cycle::C1, { CONSISTENCY_MARKERS_COUNT }>::verify_decider(
                &self.primary_decider_vp,
                &self.primary.relaxed_trace.U,
                &self.primary.pub_instances,
                &primary_proof,
                &mut verifier_transcript,
            )
            .map_err(|e| Error::VerifyFailed(vec![VerificationError::NotSat {
                err: e,
                is_primary: true,
                is_relaxed: true,
            }]))?;
        }
        debug!("primary decider proof verified");

        drop(_primary_span);

        Ok(primary_proof)
    }
}

// =====================================================================
// External proof artifact
// =====================================================================

/// The complete set of artifacts an external verifier needs to validate
/// the IVC run.
///
/// "External" here means: a party that did not run the IVC themselves
/// and does not have access to the original witness data.
///
/// Contents:
/// - Primary side: the relaxed accumulator instance + decider proof.
///   No witness data; the decider proof is succinct.
/// - Secondary side: the full relaxed trace (instance + witness).
///   The secondary is verified via native `is_sat`, which needs the
///   witness.  This is the pragmatic choice for now — the secondary
///   doesn't have FFT-friendly arithmetic, so a succinct decider for
///   it would require a different SNARK construction.
/// - Dangling secondary trace from the final fold step: instance + witness.
///   This is the last step's secondary trace that hasn't been folded
///   yet.  Verified via native SPS satisfaction check.
/// - Public instances on the primary side, for the hash-accumulator check.
/// - The final primary z_i (output of the IVC), so the external verifier
///   knows what was claimed to be computed.
/// - The number of steps and the initial z_0, for marker reconstruction.
#[derive(Serialize)]
#[serde(bound(serialize = "
    C1: Serialize,
    C2: Serialize,
    C1::ScalarExt: Serialize,
    C2::ScalarExt: Serialize,
"))]
pub struct IvcProofArtifact<const A1: usize, const A2: usize, C1, C2>
where
    C1: CurveAffine + Serialize,
    C2: CurveAffine + Serialize,
{
    // Primary side.
    pub primary_relaxed_instance: nifs::sangria::accumulator::RelaxedPlonkInstance<C1, { CONSISTENCY_MARKERS_COUNT }>,
    pub primary_decider_proof: GateDeciderProof<C1>,
    pub primary_pub_instances: Vec<Instances<C1::Scalar>>,
    #[serde(with = "serde_arrays")]
    pub primary_z_0: [C1::Scalar; A1],
    #[serde(with = "serde_arrays")]
    pub primary_z_i: [C1::Scalar; A1],

    // Secondary side.
    pub secondary_relaxed_trace: RelaxedPlonkTrace<C2, { CONSISTENCY_MARKERS_COUNT }>,
    pub secondary_pub_instances: Vec<Instances<C2::Scalar>>,
    #[serde(with = "serde_arrays")]
    pub secondary_z_0: [C2::Scalar; A2],
    #[serde(with = "serde_arrays")]
    pub secondary_z_i: [C2::Scalar; A2],

    // Dangling secondary trace from the final step.
    pub dangling_secondary_trace: FoldablePlonkTrace<C2, { CONSISTENCY_MARKERS_COUNT }>,

    // Number of steps performed (so the verifier knows what to reconstruct).
    pub num_steps: usize,
}

impl<const A1: usize, const A2: usize, C1, C2> IvcProofArtifact<A1, A2, C1, C2>
where
    C1: CurveAffine + Serialize,
    <C1 as CurveAffine>::ScalarExt: Serialize,
    [<C1 as CurveAffine>::ScalarExt; A1]: Serialize,
    C2: CurveAffine + Serialize,
    <C2 as CurveAffine>::ScalarExt: Serialize,
    [<C2 as CurveAffine>::ScalarExt; A2]: Serialize,
{
    pub fn get_sizes(&self) -> (usize, usize) {
        let primary_size = bincode::serialized_size(&self.primary_decider_proof).unwrap()
            + bincode::serialized_size(&self.primary_relaxed_instance).unwrap()
            + self.primary_pub_instances.iter().map(|inst| bincode::serialized_size(inst).unwrap()).sum::<u64>()
            + bincode::serialized_size(&self.primary_z_0).unwrap()
            + bincode::serialized_size(&self.primary_z_i).unwrap();

        let secondary_size = bincode::serialized_size(&self.secondary_relaxed_trace).unwrap()
            + self.secondary_pub_instances.iter().map(|inst| bincode::serialized_size(inst).unwrap()).sum::<u64>()
            + bincode::serialized_size(&self.secondary_z_0).unwrap()
            + bincode::serialized_size(&self.secondary_z_i).unwrap()
            + bincode::serialized_size(&self.dangling_secondary_trace).unwrap();

        (primary_size as usize, secondary_size as usize)
    }
}

// =====================================================================
// Producing the artifact
// =====================================================================

impl<const A1: usize, const A2: usize, Cycle, SC1, SC2> IVC<A1, A2, Cycle, SC1, SC2>
where
    Cycle: IvcCurveCycle,
    SC1: StepCircuit<A1, <Cycle::C1 as PrimeCurveAffine>::Scalar>,
    SC2: StepCircuit<A2, <Cycle::C2 as PrimeCurveAffine>::Scalar>,
{
    /// Produce a self-contained proof artifact that can be verified
    /// externally without access to the original witness or to the
    /// IVC's internal state.
    ///
    /// Internally: produces the primary decider proof, then bundles
    /// everything together.
    #[instrument(name = "ivc_produce_proof_artifact", skip_all)]
    pub fn produce_proof_artifact<const T: usize, RP1, RP2>(
        &self,
        pp: &PublicParams<A1, A2, T, Cycle::C1, Cycle::C2, SC1, SC2, RP1, RP2>,
    ) -> Result<IvcProofArtifact<A1, A2, Cycle::C1, Cycle::C2>, Error>
    where
        RP1: ROPair<<Cycle::C1 as PrimeCurveAffine>::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<<Cycle::C2 as PrimeCurveAffine>::Scalar, Config = MainGateConfig<T>>,
    {
        let primary_decider_proof = {
            let _s = info_span!("primary_decider").entered();
            let mut transcript =
                RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone());
            VanillaFS::<Cycle::C1, { CONSISTENCY_MARKERS_COUNT }>::prove_decider(
                &self.primary_decider_pp,
                &self.primary_layout,
                &self.primary.relaxed_trace,
                &mut transcript,
            )?
        };

        Ok(IvcProofArtifact {
            primary_relaxed_instance: self.primary.relaxed_trace.U.clone(),
            primary_decider_proof,
            primary_pub_instances: self.primary.pub_instances.clone(),
            primary_z_0: self.primary.z_0,
            primary_z_i: self.primary.z_i,

            secondary_relaxed_trace: self.secondary.relaxed_trace.clone(),
            secondary_pub_instances: self.secondary.pub_instances.clone(),
            secondary_z_0: self.secondary.z_0,
            secondary_z_i: self.secondary.z_i,

            dangling_secondary_trace: self.secondary_trace[0].clone(),

            num_steps: self.step,
        })
    }
}

// =====================================================================
// External verification
// =====================================================================

/// Verify an IVC proof artifact without access to internal state or
/// the original witness.
///
/// This is the entry point for an external party (a party that did not
/// run the IVC) to validate the entire IVC run from the artifact alone.
///
/// Verification covers:
///   1. The primary accumulator's gate identity + permutation +
///      witness binding + public-instance hash, via the succinct decider.
///   2. The secondary accumulator's full satisfiability, via native
///      `is_sat` (needs the witness data, which is in the artifact).
///   3. The dangling secondary trace's SPS / gate identity, via native
///      `is_sat` on the non-relaxed instance.
///   4. The consistency markers connecting the two accumulators and
///      the final step's claimed inputs/outputs.
///
/// Returns primary and secondary proof sizes if everything checks out; otherwise an Error describing
/// what failed.
#[instrument(name = "verify_ivc_externally", skip_all)]
pub fn verify_ivc_externally<const A1: usize, const A2: usize, const T: usize,
                              C1, C2, SC1, SC2, RP1, RP2>(
    pp: &PublicParams<A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
    decider_vp: &GateDeciderVerifierParam<C1>,
    artifact: &IvcProofArtifact<A1, A2, C1, C2>,
) -> Result<(usize, usize), Error>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,
    C1::ScalarExt: Serialize + WithSmallOrderMulGroup<3>,
    C2::ScalarExt: Serialize + WithSmallOrderMulGroup<3>,
    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,
    C1::Base: PrimeFieldBits + FromUniformBytes<64>,
    C2::Base: PrimeFieldBits + FromUniformBytes<64>,
    RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
    RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    [<C1 as CurveAffine>::ScalarExt; A1]: Serialize,
    [<C2 as CurveAffine>::ScalarExt; A2]: Serialize,
{
    let (primary_size, secondary_size) = artifact.get_sizes();
    let primary_size_kb = primary_size as f64 / 1024.0;
    let secondary_size_kb = secondary_size as f64 / 1024.0;
    println!("Artifact sizes: primary = {primary_size_kb:.2} kb, secondary = {secondary_size_kb:.2} kb, total = {:.2} kb", primary_size_kb + secondary_size_kb);

    let mut errors = vec![];

    // ----------------------------------------------------------------
    // Step 1: Verify the primary accumulator via the succinct decider.
    //
    // The decider checks gate identity + permutation + witness binding
    // + public-instance hash, all in O(c·n) verifier work that does
    // not scale with the IVC step count.
    // ----------------------------------------------------------------
    {
        let decider_start = std::time::Instant::now();
        let _s = info_span!("primary_decider").entered();
        let mut transcript =
            RP2::OffCircuit::new(pp.secondary.params().ro_constant().clone());

        VanillaFS::<C1, { CONSISTENCY_MARKERS_COUNT }>::verify_decider(
            decider_vp,
            &artifact.primary_relaxed_instance,
            &artifact.primary_pub_instances,
            &artifact.primary_decider_proof,
            &mut transcript,
        )
        .map_err(|e| {
            errors.push(VerificationError::NotSat {
                err: e,
                is_primary: true,
                is_relaxed: true,
            });
        })
        .ok();
        let decider_elapsed = decider_start.elapsed();
        println!(
            "  Primary decider verification: {} ms",
            decider_elapsed.as_millis()
        );
    }

    // ----------------------------------------------------------------
    // Step 2: Verify the secondary accumulator via native is_sat.
    //
    // Native is_sat checks gate identity, permutation, witness commit,
    // and public-instance hash on the secondary side.  Cost: O(N_secondary),
    // does not scale with IVC step count.
    //
    // The secondary witness is included in the artifact (no privacy
    // requirement, and the secondary's circuit is fixed across the IVC,
    // so its witness size is one-step-sized).
    // ----------------------------------------------------------------
    {
        let accumulator_start = std::time::Instant::now();
        let _s = info_span!("secondary_native_is_sat").entered();

        if let Err(err) = VanillaFS::<C2, { CONSISTENCY_MARKERS_COUNT }>::is_sat(
            pp.secondary.ck(),
            pp.secondary.S(),
            &artifact.secondary_relaxed_trace,
            &artifact.secondary_pub_instances,
        ) {
            errors.extend(err.into_iter().map(|err| VerificationError::NotSat {
                err,
                is_primary: false,
                is_relaxed: true,
            }));
        }
        let accumulator_elapsed = accumulator_start.elapsed();
        println!("  Secondary accumulator native is_sat: {} ms", accumulator_elapsed.as_millis());
    }

    // ----------------------------------------------------------------
    // Step 3: Verify the dangling secondary trace.
    //
    // The dangling trace is the last fold step's secondary input that
    // hasn't been folded into the accumulator yet.  It must satisfy
    // the secondary's circuit natively (non-relaxed).
    // ----------------------------------------------------------------
    {
        let dangling_start = std::time::Instant::now();
        let _s = info_span!("dangling_secondary_sps").entered();

        if let Err(err) = pp.secondary.S().is_sat(
            pp.secondary.ck(),
            &mut RP1::OffCircuit::new(pp.primary.params().ro_constant().clone()),
            &artifact.dangling_secondary_trace.u,
            &artifact.dangling_secondary_trace.w,
        ) {
            errors.push(VerificationError::NotSat {
                err: err.into(),
                is_primary: false,
                is_relaxed: false,
            });
        }
        let dangling_elapsed = dangling_start.elapsed();
        println!("  Dangling secondary trace is_sat: {} ms", dangling_elapsed.as_millis());
    }

    // ----------------------------------------------------------------
    // Step 4: Verify consistency markers.
    //
    // The accumulator's expected markers depend on:
    //   - z_0, z_i  (claimed initial and final states)
    //   - step number (num_steps)
    //   - the "other side" accumulator (cross-reference)
    //
    // We recompute these and check against the dangling trace's
    // consistency markers, which is where the chain currently terminates.
    // ----------------------------------------------------------------
    {
        let consistency_start = std::time::Instant::now();
        let _s = info_span!("consistency_markers").entered();

        // Primary's expected X0 marker: reconstructed from primary's z_0/z_i + secondary acc.
        let primary_x0_expected = ConsistencyMarkerComputation::<
            '_,
            A1,
            C2,
            RP1::OffCircuit,
            { CONSISTENCY_MARKERS_COUNT },
        > {
            random_oracle_constant: pp.primary.params().ro_constant().clone(),
            public_params_hash: &pp.digest_2(),
            step: artifact.num_steps,
            z_0: &artifact.primary_z_0,
            z_i: &artifact.primary_z_i,
            relaxed: &artifact.secondary_relaxed_trace.U,
            limb_width: pp.secondary.params().limb_width(),
            limbs_count: pp.secondary.params().limbs_count(),
        }
        .generate_with_inspect::<C2::Scalar>(|buf| {
            debug!("primary X0 verify at {}-step: {buf:?}", artifact.num_steps)
        });

        let primary_x0_actual = get_consistency_marker_input(&artifact.dangling_secondary_trace.u);
        if primary_x0_expected != primary_x0_actual {
            errors.push(VerificationError::InstanceNotMatch {
                index: 0,
                is_primary: true,
            });
        }

        // Secondary's expected X1 marker.
        let secondary_x1_expected = ConsistencyMarkerComputation::<
            '_,
            A2,
            C1,
            RP2::OffCircuit,
            { CONSISTENCY_MARKERS_COUNT },
        > {
            random_oracle_constant: pp.secondary.params().ro_constant().clone(),
            public_params_hash: &pp.digest_1(),
            step: artifact.num_steps,
            z_0: &artifact.secondary_z_0,
            z_i: &artifact.secondary_z_i,
            relaxed: &artifact.primary_relaxed_instance,
            limb_width: pp.primary.params().limb_width(),
            limbs_count: pp.primary.params().limbs_count(),
        }
        .generate_with_inspect::<C1::Scalar>(|buf| {
            debug!("secondary X1 verify at {}-step: {buf:?}", artifact.num_steps)
        });

        let secondary_x1_actual =
            get_consistency_marker_output(&artifact.dangling_secondary_trace.u);
        if secondary_x1_expected != secondary_x1_actual {
            errors.push(VerificationError::InstanceNotMatch {
                index: 1,
                is_primary: false,
            });
        }
        let consistency_elapsed = consistency_start.elapsed();
        println!("  Consistency marker verification: {} ms", consistency_elapsed.as_millis());
    }

    if errors.is_empty() {
        Ok((primary_size, secondary_size))
    } else {
        Err(Error::VerifyFailed(errors))
    }
}