use std::array;
use halo2_proofs::{circuit::Value, plonk::{Advice, Column, Fixed}, poly::Rotation};
use sirius::{
    // Use the cyclefold_prelude for core types
    cyclefold_prelude::{
        bn256::{C1Affine, C1Scalar, C2Affine},
        PublicParams, IVC,
    },
    ivc::{
        step_circuit::{AssignedCell, ConstraintSystem, Layouter},
        StepCircuit, SynthesisError,
    },
    sangria_prelude::{CommitmentKey, PrimeField},
};

// Cyclefold typically requires slightly larger table and key sizes
const TABLE_SIZE: usize = 20; 
const COMMITMENT_KEY_SIZE: usize = 24;

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

                // --- Row 0: z0_next = z_i[0] + private_inputs[0] ---
                z_i[0].copy_advice(|| "state_0", &mut region, config.a, offset)?;
                let w0 = Value::known(self.private_inputs[0]);
                region.assign_advice(|| "private_0", config.b, offset, || w0)?;
                
                let val_z0_next = z_i[0].value().cloned() + w0;
                let z0_next_cell = region.assign_advice(|| "z0_next", config.c, offset, || val_z0_next)?;

                region.assign_fixed(|| "qL", config.q_l, offset, || Value::known(F::ONE))?;
                region.assign_fixed(|| "qR", config.q_r, offset, || Value::known(F::ONE))?;
                region.assign_fixed(|| "qO", config.q_o, offset, || Value::known(-F::ONE))?;
                region.assign_fixed(|| "qC", config.q_c, offset, || Value::known(F::ZERO))?;

                offset += 1;

                // --- Row 1: z1_next = z_i[1] * private_inputs[1] ---
                z_i[1].copy_advice(|| "state_1", &mut region, config.a, offset)?;
                let w1 = Value::known(self.private_inputs[1]);
                region.assign_advice(|| "private_1", config.b, offset, || w1)?;

                let val_z1_next = z_i[1].value().cloned() * w1;
                let z1_next_cell = region.assign_advice(|| "z1_next", config.c, offset, || val_z1_next)?;

                region.assign_fixed(|| "qM", config.q_m, offset, || Value::known(F::ONE))?;
                region.assign_fixed(|| "qO", config.q_o, offset, || Value::known(-F::ONE))?;
                
                let mut z_out = z_i.clone();
                z_out[0] = z0_next_cell;
                z_out[1] = z1_next_cell;
                Ok(z_out)
            },
        ).map_err(SynthesisError::from)
    }
}

fn main() {
    tracing_subscriber::fmt().init();

    // 1. Setup keys for both curves
    let primary_key = CommitmentKey::<C1Affine>::setup(COMMITMENT_KEY_SIZE, b"bn256");
    let secondary_key = CommitmentKey::<C2Affine>::setup(COMMITMENT_KEY_SIZE, b"grumpkin");

    let sc_template = MyStepCircuit { private_inputs: [C1Scalar::from(0); 2] };

    // 2. Initialize PublicParams (Note the mutability)
    let mut pp = PublicParams::new(
        &sc_template,
        primary_key,
        secondary_key,
        TABLE_SIZE as u32,
    ).unwrap();

    // 3. Initial state z0 = [0, 1]
    let z0 = [C1Scalar::from(0), C1Scalar::from(1)];

    let inputs = vec![
        [C1Scalar::from(5), C1Scalar::from(2)],
        [C1Scalar::from(10), C1Scalar::from(3)],
        [C1Scalar::from(1), C1Scalar::from(10)],
    ];

    // 4. Initialize IVC
    let mut ivc = IVC::new(&mut pp, &sc_template, z0).expect("IVC Init Failed");

    // 5. Fold through inputs
    for (i, val) in inputs.into_iter().enumerate() {
        let step_circuit = MyStepCircuit { private_inputs: val };
        
        // .next() consumes the old ivc and returns a new one
        ivc = ivc.next(&pp, &step_circuit).expect("Folding failed");
        
        // Print current state (zi)
        println!("Step {} state: {:?}", i + 1, ivc.zi());
    }

    // 6. Verify
    // Manual checks for z0 and zi
    assert_eq!(ivc.z0().clone(), z0, "Initial state mismatch");
    println!("Final verified state: {:?}", ivc.zi());
    ivc.verify(&pp).expect("Verification failed");
}