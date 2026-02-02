pub use crate::plutus_gen::code_emitters_aiken::{
    emit_verifier_code as emit_verifier_code_aiken, emit_vk_code as emit_vk_code_aiken,
};
use crate::plutus_gen::code_emitters_plinth::{
    emit_verifier_code as emit_verifier_code_plinth, emit_vk_code,
};
use crate::plutus_gen::extraction::data::RotationDescription;
use crate::plutus_gen::extraction::{ExtractKZG, KzgType, extract_circuit};
use anyhow::{Context as _, Result};
use blstrs::{Bls12, G1Projective, Scalar};
use halo2_proofs::plonk::VerifyingKey;
use halo2_proofs::poly::commitment::PolynomialCommitmentScheme;
use halo2_proofs::poly::kzg::params::ParamsKZG;
use std::path::Path;

pub mod adjusted_types;
mod code_emitters_aiken;
mod code_emitters_plinth;
pub mod extraction;
pub mod proof_serialization;

/// Generates a Plinth verifier for a specific circuit and saves the generated code
/// to the specified file paths. Uses different KZG type based on used PolynomialCommitmentScheme
///
/// # Arguments
/// * `params` - Parameters for the KZG polynomial commitment scheme
/// * `vk` - Verifying key for the circuit, it can have either GWC19, or halo2 based KZG
/// * `instances` - Public inputs to the circuit
/// * `g2_encoder` - Encoding function for G2Affine points
///
/// # Returns
/// * `Result<(), String>` - Ok(()) if the generation is successful, Err(String) otherwise
pub fn generate_plinth_verifier<S>(
    params: &ParamsKZG<Bls12>,
    vk: &VerifyingKey<Scalar, S>,
    instances: &[&[&[Scalar]]],
) -> Result<()>
where
    S: PolynomialCommitmentScheme<Scalar, Commitment = G1Projective> + ExtractKZG,
{
    // static locations of files in plutus directory
    let verifier_template_file = match S::kzg_type() {
        KzgType::GWC19 => Path::new("plinth-verifier/templates/verification_gwc19_kzg.hbs"),
        KzgType::Halo2MultiOpen => {
            Path::new("plinth-verifier/templates/verification_halo2_kzg.hbs")
        }
    };

    let vk_template_file = Path::new("plinth-verifier/templates/vk_constants.hbs");
    let verifier_generated_file =
        Path::new("plinth-verifier/plutus-halo2/src/Plutus/Crypto/Halo2/Generic/Verifier.hs");
    let vk_generated_file =
        Path::new("plinth-verifier/plutus-halo2/src/Plutus/Crypto/Halo2/Generic/VKConstants.hs");

    // Step 1: extract circuit representation
    let circuit_representation = extract_circuit(params, vk, instances)
        .context("Failed to extract the circuit representation")?;

    // Step 2: extract KZG steps specific to used commitment scheme
    let circuit_representation = S::extract_kzg_steps(circuit_representation);

    // Step 3: Based on the circuit repr generate Plinth verifier and verification key constants
    // using Handlebars templates
    emit_verifier_code_plinth(
        verifier_template_file,
        verifier_generated_file,
        &circuit_representation,
    )
    .context("Failed to emit the verifier code for plutus")?;
    emit_vk_code(vk_template_file, vk_generated_file, &circuit_representation)
        .context("Failed to emit the verifier key constants")?;

    Ok(())
}

pub fn generate_aiken_verifier<S>(
    params: &ParamsKZG<Bls12>,
    vk: &VerifyingKey<Scalar, S>,
    instances: &[&[&[Scalar]]],
    test_proofs: Option<(Vec<u8>, Vec<u8>)>,
) -> Result<()>
where
    S: PolynomialCommitmentScheme<Scalar, Commitment = G1Projective> + ExtractKZG,
{
    let circuit_representation = extract_circuit(params, vk, instances)
        .context("Failed to extract the circuit representation")?;
    let circuit_representation = S::extract_kzg_steps(circuit_representation);

    // static locations of files in aiken directory
    let verifier_template_file = match S::kzg_type() {
        KzgType::GWC19 => Path::new("aiken-verifier/templates/verification_gwc19.hbs"),
        KzgType::Halo2MultiOpen => Path::new("aiken-verifier/templates/verification_h2.hbs"),
    };

    emit_verifier_code_aiken(
        verifier_template_file,
        Path::new("aiken-verifier/aiken_halo2/lib/proof_verifier.ak"),
        Some(Path::new("aiken-verifier/templates/profiler.hbs")),
        &circuit_representation,
        test_proofs.map(|(p, invalid_p)| {
            // Collect all public inputs from all instances for test generation
            let all_public_inputs: Vec<Scalar> = instances
                .iter()
                .flat_map(|inst| inst.iter().flat_map(|col| col.iter().copied()))
                .collect();
            (p, invalid_p, all_public_inputs)
        }),
    )
    .context("Failed to emit the verifier code for aiken")?;
    emit_vk_code_aiken(
        Path::new("aiken-verifier/templates/vk_constants.hbs"),
        Path::new("aiken-verifier/aiken_halo2/lib/verifier_key.ak"),
        &circuit_representation,
    )
    .context("Failed to emit the verifier key constants for aiken")?;

    // Generate the validator file with the correct number of instances
    emit_validator_aiken(
        Path::new("aiken-verifier/aiken_halo2/validators/verifier.ak"),
        &circuit_representation,
    )
    .context("Failed to emit the validator for aiken")?;

    Ok(())
}

/// Generate the Aiken validator file based on the number of instances
fn emit_validator_aiken(
    output_file: &Path,
    circuit: &extraction::data::CircuitRepresentation,
) -> Result<()> {
    use std::io::Write;

    let num_instances = circuit.instantiation_data.num_circuit_instances.max(1);
    let instance_counts = &circuit.instantiation_data.instance_counts;

    // Calculate total number of public input fields
    let total_fields: usize = if num_instances == 1 {
        circuit.instantiation_data.public_inputs_count
    } else {
        instance_counts.iter().flat_map(|cols| cols.iter()).sum()
    };

    // Generate instance field names
    let instance_fields: Vec<String> = if num_instances == 1 {
        (1..=total_fields).map(|i| format!("instance_{}", i)).collect()
    } else {
        let mut fields = Vec::new();
        for (circuit_idx, cols) in instance_counts.iter().enumerate() {
            for (col_idx, &count) in cols.iter().enumerate() {
                for val_idx in 1..=count {
                    fields.push(format!("instance_{}_{}_{}", circuit_idx + 1, col_idx + 1, val_idx));
                }
            }
        }
        fields
    };

    // Generate redeemer type fields
    let redeemer_fields = instance_fields.iter()
        .map(|_| "ByteArray")
        .collect::<Vec<_>>()
        .join(", ");

    // Generate redeemer pattern
    let redeemer_pattern = std::iter::once("proof".to_string())
        .chain(instance_fields.iter().cloned())
        .collect::<Vec<_>>()
        .join(", ");

    // Generate for_hashing nested appends
    let for_hashing = if instance_fields.len() == 1 {
        format!("append_bytearray(proof, {})", instance_fields[0])
    } else {
        let mut expr = "proof".to_string();
        for field in &instance_fields {
            expr = format!("append_bytearray({}, {})", expr, field);
        }
        expr
    };

    // Generate verifier call arguments
    let verifier_args = instance_fields.iter()
        .map(|f| format!("      from_bytes({})", f))
        .collect::<Vec<_>>()
        .join(",\n");

    let validator_code = format!(r#"use aiken/builtin.{{append_bytearray}}
use aiken/crypto.{{blake2b_256}}
use aiken/crypto/bls12_381/scalar.{{from_bytes}}
use cardano/assets.{{PolicyId, has_nft_strict}}
use cardano/transaction.{{Transaction}}
use proof_verifier.{{verifier}}

type Redeemer =
  (ByteArray, {})

validator halo2 {{
  mint(redeemer: Redeemer, policy_id: PolicyId, transaction: Transaction) {{
    let ({}) = redeemer

    let for_hashing =
      {}

    let expected_nft_name = blake2b_256(for_hashing)

    expect has_nft_strict(transaction.mint, policy_id, expected_nft_name)

    verifier(
      proof,
{}
    )
  }}

  else(_) {{
    fail
  }}
}}
"#, redeemer_fields, redeemer_pattern, for_hashing, verifier_args);

    let mut file = std::fs::File::create(output_file)
        .with_context(|| format!("Failed to create validator file: {:?}", output_file))?;
    file.write_all(validator_code.as_bytes())
        .with_context(|| format!("Failed to write validator file: {:?}", output_file))?;

    Ok(())
}

fn decode_rotation(rotation: &RotationDescription) -> String {
    match rotation {
        RotationDescription::Last => "x_last".to_string(),
        RotationDescription::Previous => "x_prev".to_string(),
        RotationDescription::Current => "x_current".to_string(),
        RotationDescription::Next => "x_next".to_string(),
    }
}
