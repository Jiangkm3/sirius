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

const ARITY: usize = 1;
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

/// Our Circuit Struct now holds the private witness for the current step
struct MyStepCircuit<F: PrimeField> {
    pub private_input: F,
}

impl<const A: usize, F: PrimeField> StepCircuit<A, F> for MyStepCircuit<F> {
    type Config = StandardPlonkConfig;

    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        let [a, b, c] = array::from_fn(|_| cs.advice_column());
        let [q_l, q_r, q_o, q_m, q_c] = array::from_fn(|_| cs.fixed_column());

        [a, b, c].iter().for_each(|col| cs.enable_equality(*col));

        cs.create_gate("standard plonk gate", |vc| {
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
        Ok(layouter.assign_region(
            || "multi-row step",
            |mut region| {
                let mut offset = 0;

                // --- Row 0: temp = z_i * private (qM=1, qO=-1) ---
                z_i[0].copy_advice(|| "copy z_i to a", &mut region, config.a, offset)?;
                let val_private = Value::known(self.private_input);
                region.assign_advice(|| "copy private_input to b", config.b, 0, || val_private)?;
                
                let val_temp = z_i[0].value().cloned().map(|v| v * self.private_input);
                let temp_cell = region.assign_advice(|| "temp", config.c, offset, || val_temp)?;

                region.assign_fixed(|| "qM", config.q_m, offset, || Value::known(F::ONE))?;
                region.assign_fixed(|| "qO", config.q_o, offset, || Value::known(-F::ONE))?;
                
                // Clear other selectors for this row
                for q in [&config.q_l, &config.q_r, &config.q_c] {
                    region.assign_fixed(|| "zero", *q, offset, || Value::known(F::ZERO))?;
                }

                offset += 1;

                // --- Row 1: res = temp + 5 (qL=1, qC=5, qO=-1) ---
                temp_cell.copy_advice(|| "copy temp to a", &mut region, config.a, offset)?;
                
                let val_res = val_temp.map(|v| v + F::from(5));
                let res_cell = region.assign_advice(|| "res", config.c, offset, || val_res)?;

                region.assign_fixed(|| "qL", config.q_l, offset, || Value::known(F::ONE))?;
                region.assign_fixed(|| "qC", config.q_c, offset, || Value::known(F::from(5)))?;
                region.assign_fixed(|| "qO", config.q_o, offset, || Value::known(-F::ONE))?;
                
                for q in [&config.q_r, &config.q_m] {
                    region.assign_fixed(|| "zero", *q, offset, || Value::known(F::ZERO))?;
                }

                offset += 1;

                // --- Row 2: z_out = res * 2 (qL=2, qO=-1) ---
                res_cell.copy_advice(|| "copy res to a", &mut region, config.a, offset)?;

                let val_final = val_res.map(|v| v * F::from(2));
                let out_cell = region.assign_advice(|| "final_out", config.c, offset, || val_final)?;

                region.assign_fixed(|| "qL", config.q_l, offset, || Value::known(F::from(2)))?;
                region.assign_fixed(|| "qO", config.q_o, offset, || Value::known(-F::ONE))?;

                for q in [&config.q_r, &config.q_m, &config.q_c] {
                    region.assign_fixed(|| "zero", *q, offset, || Value::known(F::ZERO))?;
                }

                let mut z_out = z_i.clone();
                z_out[0] = out_cell;
                Ok(z_out)
            },
        )?)
    }
}

fn main() {
    tracing_subscriber::fmt().with_env_filter("info,sirius=warn").init();

    let sc1 = MyStepCircuit { private_input: C1Scalar::from(0) };
    let sc2 = trivial::Circuit::<1, C2Scalar>::default();

    let pk = CommitmentKey::<C1Affine>::setup(COMMITMENT_KEY_SIZE, b"bn256");
    let sk = CommitmentKey::<C2Affine>::setup(COMMITMENT_KEY_SIZE, b"grumpkin");

    let pp = new_default_pp::<ARITY, _, 1, _>(
        TABLE_SIZE as u32, &pk, &sc1,
        TABLE_SIZE as u32, &sk, &sc2,
    );

    let z0_primary = [C1Scalar::from(1)];
    let z0_secondary = [C2Scalar::from(0)];
    // Private inputs for 3 steps
    let inputs = vec![
        // Initialization:              2 * (1 * 0 + 5) = 10
        C1Scalar::from(5),   // Step 1: 2 * (10 * 5 + 5) = 110
        C1Scalar::from(100), // Step 2: 2 * (110 * 100 + 5) = 22010
        C1Scalar::from(1),   // Step 3: 2 * (22010 * 1 + 5) = 44030
    ];

    let mut ivc = SangriaIVC::new(&pp, &sc1, z0_primary, &sc2, z0_secondary, true).unwrap();

    for (i, val) in inputs.into_iter().enumerate() {
        // Create circuit instance with the unique private witness
        let step_circuit = MyStepCircuit { private_input: val };
        
        ivc.fold_step(&pp, &step_circuit, &sc2).unwrap();
        let next_z = ivc.primary_zi();
        println!("Fold Step {} finished: output = {:?}", i + 1, next_z);
    }

    ivc.verify(&pp).unwrap();
    println!("IVC verification successful.");
}