//! PlonkUp circuit benchmark example.
//!
//! This example benchmarks the on-chain verifier for PlonkUp circuits as described in the PlonkUp paper.
//! PlonkUp circuits have the following characteristics:
//! - Lookups for 3-element tuples (e.g., XOR table: (a, b, a XOR b))
//! - Polynomial Plonk constraints (a * b = c)
//! - Accumulator constraint for computing sum of XOR results (public input)
//! - No references to neighboring rows (only Rotation::cur())
//!
//! ## Circuit Parameters
//!
//! - k (log2 of rows): 9 (512 rows)
//! - XOR lookup inputs: 8 tuples
//! - Polynomial constraint inputs: 4 tuples
//! - Max bits for lookup table: 4 (256 entries in XOR table)
//! - Public input: Sum of XOR results = 61 (0x3d)
//!
//! ## Performance Metrics
//!
//! - Proof size: 1792 bytes
//! - Verifier script size: ~28 KB (Aiken source)
//!
//! To run Plutus benchmarks, build the Aiken verifier and use the profiling tools
//! in the `profiling_setup` directory. See `profiling_setup/README.md` for details.
//!
//! ## Usage
//!
//! - Run with default KZG: `cargo run --example plonkup`
//! - Run with GWC KZG: `cargo run --example plonkup gwc_kzg`

use anyhow::{Context as _, Result, anyhow, bail};
use blstrs::{Bls12, G1Projective, Scalar};
use halo2_proofs::{
    plonk::{
        ProvingKey, VerifyingKey, create_proof, k_from_circuit, keygen_pk, keygen_vk, prepare,
    },
    poly::{
        commitment::Guard, commitment::PolynomialCommitmentScheme, gwc_kzg::GwcKZGCommitmentScheme,
        kzg::KZGCommitmentScheme, kzg::params::ParamsKZG, kzg::params::ParamsVerifierKZG,
    },
    transcript::{CircuitTranscript, Transcript},
};
use log::info;
use plutus_halo2_verifier_gen::plutus_gen::generate_aiken_verifier;
use plutus_halo2_verifier_gen::plutus_gen::proof_serialization::export_proof;
use plutus_halo2_verifier_gen::{
    circuits::plonkup_circuit::PlonkUpCircuit,
    kzg_params::get_or_create_kzg_params,
    plutus_gen::{
        adjusted_types::CardanoFriendlyBlake2b, extraction::ExtractKZG, generate_plinth_verifier,
        proof_serialization::export_public_inputs, proof_serialization::serialize_proof,
    },
};
use rand::rngs::StdRng;
use rand_core::SeedableRng;
use std::env;
use std::fs::File;

fn main() -> Result<()> {
    env_logger::init_from_env(env_logger::Env::default().filter_or("RUST_LOG", "info"));
    let args: Vec<String> = env::args().collect();

    // Parse arguments: [gwc_kzg] [--instances N]
    let mut use_gwc = false;
    let mut num_instances: usize = 1;
    
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "gwc_kzg" => use_gwc = true,
            "--instances" => {
                i += 1;
                if i >= args.len() {
                    bail!("--instances requires a number argument");
                }
                num_instances = args[i].parse().context("--instances must be a positive integer")?;
                if num_instances == 0 {
                    bail!("--instances must be at least 1");
                }
            }
            _ => {
                println!("Usage:");
                println!("  cargo run --example plonkup [gwc_kzg] [--instances N]");
                println!();
                println!("Options:");
                println!("  gwc_kzg        Use GWC19 version of multi-open KZG");
                println!("  --instances N  Number of circuit instances to batch (default: 1)");
                bail!("Invalid command line argument: {}", args[i]);
            }
        }
        i += 1;
    }

    info!("Running with {} circuit instance(s)", num_instances);

    if use_gwc {
        compile_plonkup_circuit::<GwcKZGCommitmentScheme<Bls12>>(num_instances)
    } else {
        compile_plonkup_circuit::<KZGCommitmentScheme<Bls12>>(num_instances)
    }
}

pub fn compile_plonkup_circuit<
    S: PolynomialCommitmentScheme<
            Scalar,
            Commitment = G1Projective,
            Parameters = ParamsKZG<Bls12>,
            VerifierParameters = ParamsVerifierKZG<Bls12>,
        > + ExtractKZG,
>(num_instances: usize) -> Result<()> {
    let seed = [0u8; 32]; // UNSAFE, constant seed is used for testing purposes
    let mut rng: StdRng = SeedableRng::from_seed(seed);

    // Generate circuits and public inputs for each instance
    // Each instance uses slightly different inputs to create distinct proofs
    let mut circuits = Vec::with_capacity(num_instances);
    let mut public_inputs_scalars = Vec::with_capacity(num_instances);

    for instance_idx in 0..num_instances {
        // Create XOR lookup inputs - vary by instance to get different public inputs
        let offset = instance_idx as u64;
        let xor_inputs = vec![
            (5 + offset, 10),     // (5+offset) XOR 10
            (15, 15),             // 15 XOR 15 = 0
            (8, 7),               // 8 XOR 7 = 15
            (12, 3),              // 12 XOR 3 = 15
            (0, 0),               // 0 XOR 0 = 0
            (1, 1),               // 1 XOR 1 = 0
            (2, 3),               // 2 XOR 3 = 1
            (7, 8),               // 7 XOR 8 = 15
        ];

        // Create polynomial constraint inputs (a * b = c)
        let poly_inputs = vec![
            (2, 3),  // 2 * 3 = 6
            (4, 5),  // 4 * 5 = 20
            (10, 2), // 10 * 2 = 20
            (3, 7),  // 3 * 7 = 21
        ];

        let circuit = PlonkUpCircuit::<Scalar>::new(xor_inputs, poly_inputs, 4);
        let public_input = circuit.public_input();
        
        info!("Instance {}: public input = {:?}", instance_idx + 1, public_input);
        
        circuits.push(circuit);
        public_inputs_scalars.push(public_input);
    }

    let k: u32 = k_from_circuit(&circuits[0]);
    info!("PlonkUp circuit k: {}", k);
    
    let kzg_params: ParamsKZG<Bls12> = get_or_create_kzg_params(k, rng.clone())?;
    let vk: VerifyingKey<Scalar, S> = keygen_vk(&kzg_params, &circuits[0])?;
    let pk: ProvingKey<Scalar, S> = keygen_pk(vk.clone(), &circuits[0])?;

    // Build instances array: &[&[&[Scalar]]] with shape [num_circuits][num_columns][num_values]
    // For PlonkUp, each circuit has 1 instance column with 1 public input
    let instances_per_circuit: Vec<Vec<Scalar>> = public_inputs_scalars
        .iter()
        .map(|&pi| vec![pi])
        .collect();
    
    let instances_refs: Vec<&[Scalar]> = instances_per_circuit
        .iter()
        .map(|v| v.as_slice())
        .collect();
    
    let instances_per_circuit_refs: Vec<&[&[Scalar]]> = instances_refs
        .iter()
        .map(|s| std::slice::from_ref(s))
        .collect();
    
    let instances: &[&[&[Scalar]]] = &instances_per_circuit_refs
        .iter()
        .map(|s| *s)
        .collect::<Vec<_>>();
    
    info!("Number of circuit instances: {}", instances.len());

    let instances_file =
        "./plinth-verifier/plutus-halo2/test/Generic/serialized_public_input.hex".to_string();
    let mut output = File::create(instances_file).context("failed to create instances file")?;
    export_public_inputs(instances, &mut output).context("Failed to export the public inputs")?;

    let mut transcript: CircuitTranscript<CardanoFriendlyBlake2b> =
        CircuitTranscript::<CardanoFriendlyBlake2b>::init();

    create_proof(
        &kzg_params,
        &pk,
        &circuits,
        instances,
        &mut rng,
        &mut transcript,
    )
    .context("proof generation should not fail")?;

    let proof = transcript.finalize();
    info!("proof size {:?}", proof.len());

    let mut transcript_verifier: CircuitTranscript<CardanoFriendlyBlake2b> =
        CircuitTranscript::<CardanoFriendlyBlake2b>::init_from_bytes(&proof);

    let verifier = prepare::<_, _, CircuitTranscript<CardanoFriendlyBlake2b>>(
        &vk,
        instances,
        &mut transcript_verifier,
    )
    .context("prepare verification failed")?;

    verifier
        .verify(&kzg_params.verifier_params())
        .map_err(|e| anyhow!("{e:?}"))
        .context("verify failed")?;

    serialize_proof(
        "./plinth-verifier/plutus-halo2/test/Generic/serialized_proof.json".to_string(),
        proof.clone(),
    )
    .context("json proof serialization failed")?;

    export_proof(
        "./plinth-verifier/plutus-halo2/test/Generic/serialized_proof.hex".to_string(),
        proof.clone(),
    )
    .context("hex proof serialization failed")?;

    generate_plinth_verifier(&kzg_params, &vk, instances)
        .context("Plinth verifier generation failed")?;

    // Create an invalid proof by flipping some bytes in the valid proof
    // This approach ensures the circuit structure is the same
    let mut invalid_proof = proof.clone();
    // Flip a byte in the middle of the proof (away from curve point encoding to avoid deserialization errors)
    // The circuit has lookup and accumulator constraints, so proof structure includes:
    // commitments + evaluations + opening proof
    let flip_index = invalid_proof.len() / 2;
    invalid_proof[flip_index] = !invalid_proof[flip_index];

    generate_aiken_verifier(
        &kzg_params,
        &vk,
        instances,
        Some((proof.clone(), invalid_proof)),
    )
    .context("Aiken verifier generation failed")?;
    
    export_proof(
        "./aiken-verifier/submitter/serialized_proof.hex".to_string(),
        proof,
    )
    .context("hex proof serialization failed")?;

    let instances_file = "./aiken-verifier/submitter/serialized_public_input.hex".to_string();
    let mut output = File::create(instances_file).context("failed to create instances file")?;
    export_public_inputs(instances, &mut output).context("Failed to export the public inputs")?;

    Ok(())
}
