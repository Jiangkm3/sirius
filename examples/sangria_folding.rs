use std::array;
use halo2_proofs::{circuit::Value, plonk::{Advice, Column, Fixed}, poly::Rotation};
use sirius::{
    ivc::{
        step_circuit::{trivial, AssignedCell, ConstraintSystem, Layouter},
        SangriaIVC, StepCircuit, SynthesisError,
    },
    sangria_prelude::{
        bn256::{new_default_pp, C1Affine, C1Scalar, C2Affine, C2Scalar},
        CommitmentKey, PrimeField,
    },
};

// ARITY is now 2: We pass two values (e.g., a 'sum' and a 'product') across steps.
const ARITY: usize = 2;
const TABLE_SIZE: usize = 17;
const COMMITMENT_KEY_SIZE: usize = 21;

#[derive(Debug, Clone)]
struct StandardPlonkConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    q_l: Column<Fixed>,
    q_r: Column<Fixed>,
    q_o: Column<Fixed>,
    q_m: Column<Fixed>,
    q_c: Column<Fixed>,
}

/// Now holds multiple private inputs unique to this specific step.
struct MyStepCircuit<F: PrimeField> {
    pub private_inputs: [F; 2],
}

impl<const A: usize, F: PrimeField> StepCircuit<A, F> for MyStepCircuit<F> {
    type Config = StandardPlonkConfig;

    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        let [a, b, c] = array::from_fn(|_| cs.advice_column());
        let [q_l, q_r, q_o, q_m, q_c] = array::from_fn(|_| cs.fixed_column());

        [a, b, c].iter().for_each(|col| cs.enable_equality(*col));

        cs.create_gate("universal gate", |vc| {
            let a = vc.query_advice(a, Rotation::cur());
            let b = vc.query_advice(b, Rotation::cur());
            let c = vc.query_advice(c, Rotation::cur());
            let ql = vc.query_fixed(q_l, Rotation::cur());
            let qr = vc.query_fixed(q_r, Rotation::cur());
            let qo = vc.query_fixed(q_o, Rotation::cur());
            let qm = vc.query_fixed(q_m, Rotation::cur());
            let qc = vc.query_fixed(q_c, Rotation::cur());

            vec![ql * a.clone() + qr * b.clone() + qo * c.clone() + qm * a * b + qc]
        });

        StandardPlonkConfig { a, b, c, q_l, q_r, q_o, q_m, q_c }
    }

    fn synthesize_step(
        &self,
        config: Self::Config,
        layouter: &mut impl Layouter<F>,
        z_i: &[AssignedCell<F, F>; A],
    ) -> Result<[AssignedCell<F, F>; A], SynthesisError> {
        layouter.assign_region(
            || "complex-multi-input-step",
            |mut region| {
                let mut offset = 0;

                // --- Row 0: State[0] update ---
                // Logic: z0_next = z_i[0] + private_inputs[0]
                z_i[0].copy_advice(|| "state_0", &mut region, config.a, offset)?;
                let w0 = Value::known(self.private_inputs[0]);
                region.assign_advice(|| "private_0", config.b, offset, || w0)?;
                
                let val_z0_next = z_i[0].value().cloned() + w0;
                let z0_next_cell = region.assign_advice(|| "z0_next", config.c, offset, || val_z0_next)?;

                region.assign_fixed(|| "qL", config.q_l, offset, || Value::known(F::ONE))?;
                region.assign_fixed(|| "qR", config.q_r, offset, || Value::known(F::ONE))?;
                region.assign_fixed(|| "qO", config.q_o, offset, || Value::known(-F::ONE))?;
                region.assign_fixed(|| "qM", config.q_m, offset, || Value::known(F::ZERO))?;
                region.assign_fixed(|| "qC", config.q_c, offset, || Value::known(F::ZERO))?;

                offset += 1;

                // --- Row 1: State[1] update ---
                // Logic: z1_next = z_i[1] * private_inputs[1]
                z_i[1].copy_advice(|| "state_1", &mut region, config.a, offset)?;
                let w1 = Value::known(self.private_inputs[1]);
                region.assign_advice(|| "private_1", config.b, offset, || w1)?;

                let val_z1_next = z_i[1].value().cloned() * w1;
                let z1_next_cell = region.assign_advice(|| "z1_next", config.c, offset, || val_z1_next)?;

                region.assign_fixed(|| "qM", config.q_m, offset, || Value::known(F::ONE))?;
                region.assign_fixed(|| "qO", config.q_o, offset, || Value::known(-F::ONE))?;
                
                for q in [&config.q_l, &config.q_r, &config.q_c] {
                    region.assign_fixed(|| "zero", *q, offset, || Value::known(F::ZERO))?;
                }

                let mut z_out = z_i.clone();
                z_out[0] = z0_next_cell;
                z_out[1] = z1_next_cell;
                Ok(z_out)
            },
        ).map_err(SynthesisError::from)
    }
}

fn main() {
    tracing_subscriber::fmt().with_env_filter("info,sirius=warn").init();

    let sc1_template = MyStepCircuit { private_inputs: [C1Scalar::from(0); 2] };
    let sc2 = trivial::Circuit::<1, C2Scalar>::default();

    let pk = CommitmentKey::<C1Affine>::setup(COMMITMENT_KEY_SIZE, b"bn256");
    let sk = CommitmentKey::<C2Affine>::setup(COMMITMENT_KEY_SIZE, b"grumpkin");

    let pp = new_default_pp::<ARITY, _, 1, _>(
        TABLE_SIZE as u32, &pk, &sc1_template,
        TABLE_SIZE as u32, &sk, &sc2,
    );

    // Initial Public State: [Sum=0, Product=1]
    let z0_primary = [C1Scalar::from(0), C1Scalar::from(1)];
    let z0_secondary = [C2Scalar::from(0)];

    // Data for 3 steps: Each row has 2 private values
    let inputs = vec![
        [C1Scalar::from(5), C1Scalar::from(2)],   // Step 1
        [C1Scalar::from(10), C1Scalar::from(3)],  // Step 2
        [C1Scalar::from(1), C1Scalar::from(10)],  // Step 3
    ];

    let mut ivc = SangriaIVC::new(&pp, &sc1_template, z0_primary, &sc2, z0_secondary, true).unwrap();

    for (i, val) in inputs.into_iter().enumerate() {
        let step_circuit = MyStepCircuit { private_inputs: val };
        ivc.fold_step(&pp, &step_circuit, &sc2).unwrap();
        
        println!("Step {} output state: {:?}", i + 1, ivc.primary_zi());
    }

    // Additionally: check z0 and zi
    ivc.verify(&pp).expect("Verification failed");
}