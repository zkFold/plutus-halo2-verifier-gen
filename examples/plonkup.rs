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

    match &args[1..] {
        [] => compile_plonkup_circuit::<KZGCommitmentScheme<Bls12>>(),
        [command] if command == "gwc_kzg" => {
            compile_plonkup_circuit::<GwcKZGCommitmentScheme<Bls12>>()
        }
        _ => {
            println!("Usage:");
            println!("- to run the example: `cargo run --example plonkup`");
            println!(
                "- to run the example using the GWC19 version of multi-open KZG, run: `cargo run --example plonkup gwc_kzg`"
            );

            bail!("Invalid command line arguments")
        }
    }
}

pub fn compile_plonkup_circuit<
    S: PolynomialCommitmentScheme<
            Scalar,
            Commitment = G1Projective,
            Parameters = ParamsKZG<Bls12>,
            VerifierParameters = ParamsVerifierKZG<Bls12>,
        > + ExtractKZG,
>() -> Result<()> {
    let seed = [0u8; 32]; // UNSAFE, constant seed is used for testing purposes
    let mut rng: StdRng = SeedableRng::from_seed(seed);

    // Create XOR lookup inputs (3-element tuples as per PlonkUp)
    // Using 4-bit values to keep table size manageable
    let xor_inputs = vec![
        (5, 10),  // 5 XOR 10 = 15
        (15, 15), // 15 XOR 15 = 0
        (8, 7),   // 8 XOR 7 = 15
        (12, 3),  // 12 XOR 3 = 15
        (0, 0),   // 0 XOR 0 = 0
        (1, 1),   // 1 XOR 1 = 0
        (2, 3),   // 2 XOR 3 = 1
        (7, 8),   // 7 XOR 8 = 15
    ];

    // Create polynomial constraint inputs (a * b = c)
    let poly_inputs = vec![
        (2, 3),  // 2 * 3 = 6
        (4, 5),  // 4 * 5 = 20
        (10, 2), // 10 * 2 = 20
        (3, 7),  // 3 * 7 = 21
    ];

    let circuit = PlonkUpCircuit::<Scalar>::new(xor_inputs, poly_inputs, 4);

    let k: u32 = k_from_circuit(&circuit);
    info!("PlonkUp circuit k: {}", k);
    
    let kzg_params: ParamsKZG<Bls12> = get_or_create_kzg_params(k, rng.clone())?;
    let vk: VerifyingKey<Scalar, S> = keygen_vk(&kzg_params, &circuit)?;
    let pk: ProvingKey<Scalar, S> = keygen_pk(vk.clone(), &circuit)?;

    // Public input: sum of XOR results
    let public_input = circuit.public_input();
    let instances: &[&[&[Scalar]]] = &[&[&[public_input]]];
    info!("Public inputs (sum of XOR results): {:?}", instances);

    let instances_file =
        "./plinth-verifier/plutus-halo2/test/Generic/serialized_public_input.hex".to_string();
    let mut output = File::create(instances_file).context("failed to create instances file")?;
    export_public_inputs(instances, &mut output).context("Failed to export the public inputs")?;

    let mut transcript: CircuitTranscript<CardanoFriendlyBlake2b> =
        CircuitTranscript::<CardanoFriendlyBlake2b>::init();

    create_proof(
        &kzg_params,
        &pk,
        &[circuit.clone()],
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
