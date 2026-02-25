use halo2_proofs::{
    circuit::{Value, Layouter},
    plonk::{
        Advice, Challenge, Column, ConstraintSystem,
        FirstPhase, SecondPhase, Selector,
    },
    poly::Rotation,
};
use sirius::{
    cyclefold_prelude::{
        bn256::{C1Affine, C1Scalar, C2Affine},
        PublicParams, IVC,
    },
    ivc::{StepCircuit, SynthesisError, step_circuit::AssignedCell},
    sangria_prelude::{CommitmentKey, PrimeField},
};

const TABLE_SIZE: usize = 20; 
const COMMITMENT_KEY_SIZE: usize = 24; 
const BATCH_SIZE: usize = 10;

#[derive(Debug, Clone)]
struct GrandProductConfig {
    inputs: Column<Advice>,      // FirstPhase
    gamma: Challenge,            // The Challenge
    product_acc: Column<Advice>, // SecondPhase
    selector: Selector,
}

struct MyGrandProductCircuit<F: PrimeField> {
    pub private_inputs: [F; BATCH_SIZE],
}

impl<const A: usize, F: PrimeField> StepCircuit<A, F> for MyGrandProductCircuit<F> {
    type Config = GrandProductConfig;

    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        // Phase 1: Inputs
        let inputs = cs.advice_column_in(FirstPhase);
        
        // Phase 2: Accumulator (must be SecondPhase to use gamma)
        let product_acc = cs.advice_column_in(SecondPhase);

        // Challenge: Usable after FirstPhase is committed
        let gamma = cs.challenge_usable_after(FirstPhase);

        let selector = cs.selector();

        cs.enable_equality(inputs);
        cs.enable_equality(product_acc);

        cs.create_gate("grand_product_step", |vc| {
            let sel = vc.query_selector(selector);
            let input = vc.query_advice(inputs, Rotation::cur());
            let acc_curr = vc.query_advice(product_acc, Rotation::cur());
            let acc_next = vc.query_advice(product_acc, Rotation::next());
            let gamma_val = vc.query_challenge(gamma);

            // acc_next = acc_curr * (input + gamma)
            vec![sel * (acc_next - (acc_curr * (input + gamma_val)))]
        });

        GrandProductConfig { inputs, gamma, product_acc, selector }
    }

    fn synthesize_step(
        &self,
        config: Self::Config,
        layouter: &mut impl Layouter<F>,
        z_i: &[AssignedCell<F, F>; A],
    ) -> Result<[AssignedCell<F, F>; A], SynthesisError> {
        // FIX: Get challenge from Layouter, not Region
        // This returns a Value<F> that is "Unknown" during Phase 1 witness generation
        // but becomes "Known" during Phase 2.
        let gamma_value = layouter.get_challenge(config.gamma);

        layouter.assign_region(
            || "grand_product_region",
            |mut region| {
                // --- PHASE 1: Assign Inputs ---
                for (i, &val) in self.private_inputs.iter().enumerate() {
                    region.assign_advice(
                        || format!("input row {}", i),
                        config.inputs,
                        i, 
                        || Value::known(val)
                    )?;
                    config.selector.enable(&mut region, i)?;
                }

                // --- PHASE 2: Assign Product ---
                // We capture 'gamma_value' from the outer scope.
                
                let mut current_acc = z_i[0].value().cloned();
                
                // Copy previous step's output to current step's start
                let mut prev_cell = z_i[0].copy_advice(
                    || "z_in copy", 
                    &mut region, 
                    config.product_acc, 
                    0
                )?;

                for (i, &input_val) in self.private_inputs.iter().enumerate() {
                    let input_cell_value = Value::known(input_val);
                    
                    // Calculation: acc * (input + gamma)
                    // The .and_then chaining handles the fact that gamma might be unknown 
                    // during the first pass of the prover.
                    let next_val = current_acc.and_then(|acc| 
                        input_cell_value.and_then(|inp| 
                            gamma_value.map(|g| acc * (inp + g))
                        )
                    );

                    let next_cell = region.assign_advice(
                        || format!("acc row {}", i+1),
                        config.product_acc,
                        i + 1,
                        || next_val
                    )?;

                    current_acc = next_val;
                    prev_cell = next_cell;
                }

                let mut z_out = z_i.clone();
                z_out[0] = prev_cell;
                Ok(z_out)
            },
        ).map_err(SynthesisError::from)
    }
}

fn main() {
    tracing_subscriber::fmt().init();

    // 1. Setup Keys
    println!("Generating keys...");
    let primary_key = CommitmentKey::<C1Affine>::setup(COMMITMENT_KEY_SIZE, b"bn256");
    let secondary_key = CommitmentKey::<C2Affine>::setup(COMMITMENT_KEY_SIZE, b"grumpkin");

    let sc_template = MyGrandProductCircuit { private_inputs: [C1Scalar::from(0); BATCH_SIZE] };

    // 2. Setup Public Params
    let mut pp = PublicParams::new(
        &sc_template,
        primary_key,
        secondary_key,
        TABLE_SIZE as u32,
    ).unwrap();

    // 3. Initial State z0 = 1
    let z0 = [C1Scalar::from(1)];

    // 4. Run Steps
    // Step 1: Inputs [2, 2...]. Product should be 1 * (2+gamma)^10
    let inputs_step_1 = [C1Scalar::from(2); BATCH_SIZE];
    
    let mut ivc = IVC::new(&mut pp, &sc_template, z0).expect("IVC Init");

    println!("Folding Step 1...");
    let circuit_1 = MyGrandProductCircuit { private_inputs: inputs_step_1 };
    ivc = ivc.next(&pp, &circuit_1).expect("Fold 1 Failed");
    
    // Note: The printed state here might look like "0x..." 
    // It depends on the random gamma chosen by the transcript!
    println!("Step 1 Output State (Accumulator): {:?}", ivc.zi());

    println!("Verifying...");
    ivc.verify(&pp).expect("Verification Failed");
    println!("Success!");
}