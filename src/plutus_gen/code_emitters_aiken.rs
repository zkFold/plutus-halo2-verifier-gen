use crate::plutus_gen::code_emitters_aiken::ScalarOperation::{Mul, Power};
use crate::plutus_gen::decode_rotation;
use crate::plutus_gen::extraction::data::{
    CommitmentData, Commitments, Evaluations, Query, RotationDescription,
};
use crate::plutus_gen::extraction::{
    AikenExpression, combine_aiken_expressions,
    data::{CircuitRepresentation, ProofExtractionSteps},
    precompute_intermediate_sets,
};
use blstrs::Scalar;
use ff::Field;
use halo2_proofs::halo2curves::group::GroupEncoding;

use handlebars::{Handlebars, RenderError};
use itertools::Itertools;
use log::debug;
use regex::Regex;
use std::ops::Neg;
use std::{collections::HashMap, fs::File, iter::once, path::Path};

/// Transform an expression string to use instance-specific variable names.
/// For example: advice_eval_1 -> advice_eval_I_1
/// This is used for multi-instance verification where each instance has its own evaluations.
/// 
/// For permutation delta powers, the function also adjusts scale(scalarDelta, N) to account
/// for the cumulative column offset across instances.
/// For instance: scale(scalarDelta, 0) in instance 2 becomes scale(scalarDelta, 6) if there are 6 columns per instance.
fn transform_expression_for_instance(expr: &str, instance: usize, columns_per_instance: usize) -> String {
    // List of patterns that need instance prefixing (per-instance evaluations)
    // These match the variable names generated in proof extraction
    // Use ${1}, ${2}, etc. for unambiguous backreferences in replacement strings
    let patterns = [
        // advice evaluations: advice_eval_N -> advice_eval_I_N
        (r"advice_eval_(\d+)", format!("advice_eval_{}_${{1}}", instance)),
        // permutation evaluations: permutations_evaluated_X_N -> permutations_evaluated_I_X_N
        (r"permutations_evaluated_([a-z])_(\d+)", format!("permutations_evaluated_{}_${{1}}_${{2}}", instance)),
        // lookup product: product_eval_N -> product_eval_I_N
        (r"product_eval_(\d+)", format!("product_eval_{}_${{1}}", instance)),
        // lookup product next: product_next_eval_N -> product_next_eval_I_N
        (r"product_next_eval_(\d+)", format!("product_next_eval_{}_${{1}}", instance)),
        // lookup permuted input: permuted_input_eval_N -> permuted_input_eval_I_N
        (r"permuted_input_eval_(\d+)", format!("permuted_input_eval_{}_${{1}}", instance)),
        // lookup permuted input inv: permuted_input_inv_eval_N -> permuted_input_inv_eval_I_N
        (r"permuted_input_inv_eval_(\d+)", format!("permuted_input_inv_eval_{}_${{1}}", instance)),
        // lookup permuted table: permuted_table_eval_N -> permuted_table_eval_I_N
        (r"permuted_table_eval_(\d+)", format!("permuted_table_eval_{}_${{1}}", instance)),
        // instance evaluations: instance_eval_N -> instance_eval_I_N (Note: instance_eval_circuit_column)
        (r"instance_eval_1_(\d+)", format!("instance_eval_{}_${{1}}", instance)),
    ];
    
    let mut result = expr.to_string();
    for (pattern, replacement) in patterns {
        let re = Regex::new(pattern).unwrap();
        // Use regex replace_all with backreferences (${1}, ${2}, etc.)
        result = re.replace_all(&result, replacement.as_str()).to_string();
    }
    
    // Adjust delta powers for multi-instance permutation
    // scale(scalarDelta, N) -> scale(scalarDelta, N + (instance - 1) * columns_per_instance)
    if instance > 1 {
        let delta_offset = (instance - 1) * columns_per_instance;
        let scale_re = Regex::new(r"scale\(\s*scalarDelta\s*,\s*(\d+)\s*\)").unwrap();
        result = scale_re.replace_all(&result, |caps: &regex::Captures| {
            let original_power: usize = caps[1].parse().unwrap();
            let new_power = original_power + delta_offset;
            format!("scale(scalarDelta, {})", new_power)
        }).to_string();
    }
    
    result
}

pub fn emit_verifier_code(
    template_file: &Path, // aiken mustashe template
    aiken_file: &Path,    // generated aiken file, output
    profiler_file: Option<&Path>,
    circuit: &CircuitRepresentation,
    test_data: Option<(Vec<u8>, Vec<u8>, Vec<Scalar>)>,
) -> Result<String, RenderError> {
    let letters = 'a'..='z';
    let num_instances = circuit.instantiation_data.num_circuit_instances.max(1);
    
    // Calculate columns per instance for delta power adjustment in multi-instance permutations
    // This is the number of columns in the permutation circuit (sum of all permutation sets)
    let columns_per_instance = circuit.permutation_terms_right.len();
    
    // For multi-instance proofs, many steps are repeated per-instance
    // We need to expand them accordingly
    let proof_extraction: Vec<_> = circuit
        .proof_extraction_steps
        .iter()
        .chunk_by(|e| (*e).clone())
        .into_iter()
        .map(|(section_type, section)| {
            let section_vec: Vec<_> = section.collect();
            let section_count = section_vec.len();
            
            match section_type {
                ProofExtractionSteps::AdviceCommitments => {
                    // Per-instance: read num_instances × num_advice_columns commitments
                    (1..=num_instances)
                        .flat_map(|inst| {
                            (1..=section_count).map(move |col| {
                                if num_instances == 1 {
                                    format!("    let (a{}, transcript) = read_point(transcript)\n", col)
                                } else {
                                    format!("    let (a_{}_{}, transcript) = read_point(transcript)\n", inst, col)
                                }
                            })
                        })
                        .join("")
                }
                ProofExtractionSteps::Theta => "    let (theta, transcript) = squeeze_challenge(transcript)\n".to_string(),
                ProofExtractionSteps::Beta => "    let (beta, transcript) = squeeze_challenge(transcript)\n".to_string(),
                ProofExtractionSteps::Gamma => "    let (gamma, transcript) = squeeze_challenge(transcript)\n".to_string(),
                ProofExtractionSteps::PermutationsCommited => {
                    // Per-instance: read num_instances × num_permutation_chunks commitments
                    (1..=num_instances)
                        .flat_map(|inst| {
                            section_vec.iter().zip(letters.clone()).map(move |(_permutation, letter)| {
                                if num_instances == 1 {
                                    format!("    let (permutations_committed_{}, transcript) = read_point(transcript)\n", letter)
                                } else {
                                    format!("    let (permutations_committed_{}_{}, transcript) = read_point(transcript)\n", inst, letter)
                                }
                            })
                        })
                        .join("")
                }
                ProofExtractionSteps::VanishingRand => "    let (vanishing_rand, transcript) = read_point(transcript)\n".to_string(),
                ProofExtractionSteps::YCoordinate => "    let (y, transcript) = squeeze_challenge(transcript)\n".to_string(),
                ProofExtractionSteps::VanishingSplit => section_vec
                    .iter()
                    .enumerate()
                    .map(|(number, _vanishing_split)| {
                        format!(
                            "\tlet (vanishing_split_{idx}, transcript) =  read_point(transcript)\n\
                            \tlet vanishing_split_{idx} = decompress(vanishing_split_{idx})\n",
                            idx = number + 1)
                    })
                    .join(""),
                ProofExtractionSteps::XCoordinate => "    let (x, transcript) = squeeze_challenge(transcript)\n".to_string(),
                ProofExtractionSteps::AdviceEval => {
                    // Per-instance: read num_instances × num_advice_queries evaluations
                    (1..=num_instances)
                        .flat_map(|inst| {
                            (1..=section_count).map(move |idx| {
                                if num_instances == 1 {
                                    format!("    let (advice_eval_{}, transcript) = read_scalar(transcript)\n", idx)
                                } else {
                                    format!("    let (advice_eval_{}_{}, transcript) = read_scalar(transcript)\n", inst, idx)
                                }
                            })
                        })
                        .join("")
                }
                ProofExtractionSteps::FixedEval => section_vec
                    .iter()
                    .enumerate()
                    .map(|(number, _fixed_eval)| {
                        format!("    let (fixed_eval_{}, transcript) = read_scalar(transcript)\n", number + 1)
                    })
                    .join(""),
                ProofExtractionSteps::RandomEval => "    let (random_eval, transcript) = read_scalar(transcript)\n".to_string(),
                ProofExtractionSteps::PermutationCommon => section_vec
                    .iter()
                    .enumerate()
                    .map(|(number, _permutation_common)| {
                    format!("    let (permutation_common_{}, transcript) = read_scalar(transcript)\n", number + 1)
                })
                .join(""),
            ProofExtractionSteps::PermutationEval(letter) => {
                // Per-instance: read num_instances × num_evals_per_chunk evaluations
                (1..=num_instances)
                    .flat_map(|inst| {
                        (1..=section_count).map(move |n| {
                            if num_instances == 1 {
                                format!(
                                    "    let (permutations_evaluated_{}_{}, transcript) = read_scalar(transcript)\n",
                                    letter, n
                                )
                            } else {
                                format!(
                                    "    let (permutations_evaluated_{}_{}_{}, transcript) = read_scalar(transcript)\n",
                                    inst, letter, n
                                )
                            }
                        })
                    })
                    .join("")
            }
            ProofExtractionSteps::SqueezeChallenge => panic!("no Squeeze Challenge supported"),
            ProofExtractionSteps::LookupPermuted => {
                // Per-instance: read num_instances × num_lookups × 2 commitments
                (1..=num_instances)
                    .flat_map(|inst| {
                        (1..=section_count).map(move |number| {
                            if num_instances == 1 {
                                format!("    let (permuted_input_{}, transcript) =  read_point(transcript)\n", number)
                                    + &format!("    let (permuted_table_{}, transcript) =  read_point(transcript)\n", number)
                            } else {
                                format!("    let (permuted_input_{}_{}, transcript) =  read_point(transcript)\n", inst, number)
                                    + &format!("    let (permuted_table_{}_{}, transcript) =  read_point(transcript)\n", inst, number)
                            }
                        })
                    })
                    .join("")
            }
            ProofExtractionSteps::LookupCommitment => {
                // Per-instance: read num_instances × num_lookups commitments
                (1..=num_instances)
                    .flat_map(|inst| {
                        (1..=section_count).map(move |number| {
                            if num_instances == 1 {
                                format!("    let (lookup_commitment_{}, transcript) =  read_point(transcript)\n", number)
                            } else {
                                format!("    let (lookup_commitment_{}_{}, transcript) =  read_point(transcript)\n", inst, number)
                            }
                        })
                    })
                    .join("")
            }
            ProofExtractionSteps::LookupEval => {
                // Per-instance: read num_instances × num_lookups × 5 evaluations
                (1..=num_instances)
                    .flat_map(|inst| {
                        (1..=section_count).map(move |number| {
                            if num_instances == 1 {
                                format!("    let (product_eval_{}, transcript) = read_scalar(transcript)\n", number)
                                    + &format!("    let (product_next_eval_{}, transcript) = read_scalar(transcript)\n", number)
                                    + &format!("    let (permuted_input_eval_{}, transcript) = read_scalar(transcript)\n", number)
                                    + &format!("    let (permuted_input_inv_eval_{}, transcript) = read_scalar(transcript)\n", number)
                                    + &format!("    let (permuted_table_eval_{}, transcript) = read_scalar(transcript)\n", number)
                            } else {
                                format!("    let (product_eval_{}_{}, transcript) = read_scalar(transcript)\n", inst, number)
                                    + &format!("    let (product_next_eval_{}_{}, transcript) = read_scalar(transcript)\n", inst, number)
                                    + &format!("    let (permuted_input_eval_{}_{}, transcript) = read_scalar(transcript)\n", inst, number)
                                    + &format!("    let (permuted_input_inv_eval_{}_{}, transcript) = read_scalar(transcript)\n", inst, number)
                                    + &format!("    let (permuted_table_eval_{}_{}, transcript) = read_scalar(transcript)\n", inst, number)
                            }
                        })
                    })
                    .join("")
            },
            // section for halo2 multi open version of KZG
            ProofExtractionSteps::X1 => "    let (x1, transcript) = squeeze_challenge(transcript)\n".to_string(),
            ProofExtractionSteps::X2 => "    let (x2, transcript) = squeeze_challenge(transcript)\n".to_string(),
            ProofExtractionSteps::X3 => "    let (x3, transcript) = squeeze_challenge(transcript)\n".to_string(),
            ProofExtractionSteps::X4 => "    let (x4, transcript) = squeeze_challenge(transcript)\n".to_string(),
            ProofExtractionSteps::FCommitment => "    let (f_commitment, transcript) =  read_point(transcript)\n".to_string(),
            ProofExtractionSteps::PI => "    let (pi_term, _) =  read_point(transcript)\n".to_string(),
            ProofExtractionSteps::QEvals => section_vec
                .iter()
                .enumerate()
                .map(|(number, _permutation_common)| {
                    format!("    let (q_eval_on_x3_{}, transcript) = read_scalar(transcript)\n", number + 1)
                })
                .join(""),

            // section for GWC19 version of KZG
            ProofExtractionSteps::V => "    let (v, transcript) = squeeze_challenge(transcript)\n".to_string(),
            ProofExtractionSteps::U => "    let (u, _) = squeeze_challenge(transcript)\n".to_string(),
            ProofExtractionSteps::Witnesses => section_vec
                .iter()
                .enumerate()
                .map(|(number, _permutation_common)| format!("    let (w{}, transcript) =  read_point(transcript)\n", number + 1))
                .join(""),
        }})
        .collect();

    let mut data: HashMap<String, String> = HashMap::new(); // data to bind to mustache template

    data.insert(
        "PUBLIC_INPUTS_COUNT".to_string(),
        circuit.instantiation_data.public_inputs_count.to_string(),
    );

    let num_instances = circuit.instantiation_data.num_circuit_instances.max(1);
    let instance_counts = &circuit.instantiation_data.instance_counts;

    // For multi-instance: generate public input names as i_{circuit}_{column}_{value}
    // For single-instance backward compatibility: i_{value}
    //
    // IMPORTANT: halo2 prover writes public inputs as:
    //   for each circuit_instance:
    //     for each instance_column:
    //       write(column.len())
    //       for each value in column:
    //         write(value)
    //
    // So we need to replicate this structure in the verifier transcript.
    // Note: The template already writes `common_scalar(inputs_count, transcript)` once,
    // which is correct for single-instance with one column. For multi-instance,
    // we need to write the length before each column's values.
    let (public_inputs_names, public_inputs, instance_evals) = if num_instances == 1 {
        // Single instance: backward compatible naming
        // The template writes inputs_count once, then we write all values
        let count = circuit.instantiation_data.public_inputs_count;
        let names = (1..=count)
            .map(|n| format!("i_{}: State<Scalar>", n))
            .join(", ");
        // For single instance with one column, the existing format works:
        // template writes `common_scalar(inputs_count, transcript)` then we write values
        let inputs = (1..=count)
            .map(|n| format!("    let transcript = common_scalar(i_{}, transcript)\n", n))
            .join("");
        let lagrange = (1..=count)
            .map(|n| format!("i_{}", n))
            .join(", ");
        let evals = format!(
            "    let instance_eval_1_1 = inner_product(lagrange_polynomial_instances, [{}])\n",
            lagrange
        );
        (names, inputs, evals)
    } else {
        // Multi-instance: i_{circuit}_{column}_{value}
        // Each circuit instance writes: [column_len, values...] for each column
        // Since the template writes `common_scalar(inputs_count, transcript)` once,
        // we need to write the remaining length prefixes in PUBLIC_INPUTS.
        let mut names = Vec::new();
        let mut inputs = Vec::new();
        let mut evals = Vec::new();
        let mut first_column = true;

        for (circuit_idx, columns) in instance_counts.iter().enumerate() {
            let circuit_num = circuit_idx + 1;
            for (col_idx, &count) in columns.iter().enumerate() {
                let col_num = col_idx + 1;
                // Generate names for this column's public inputs
                for val_idx in 1..=count {
                    names.push(format!("i_{}_{}_{}: State<Scalar>", circuit_num, col_num, val_idx));
                }
                // Write length prefix for this column (except the first one which is written by template)
                // Actually, for multi-instance we need to write ALL lengths including the first
                // The template writes `common_scalar(inputs_count, transcript)` which is just one length.
                // For N instances × M columns, we need N×M length writes.
                // We'll handle this by having the template NOT write the length for multi-instance.
                if !first_column {
                    // Write length for non-first columns
                    inputs.push(format!(
                        "    let transcript = common_scalar(from_int({}), transcript)\n",
                        count
                    ));
                }
                first_column = false;
                // Write public input values for this column
                for val_idx in 1..=count {
                    inputs.push(format!(
                        "    let transcript = common_scalar(i_{}_{}_{}, transcript)\n",
                        circuit_num, col_num, val_idx
                    ));
                }
                // Generate instance evaluation for this circuit/column
                let lagrange: String = (1..=count)
                    .map(|v| format!("i_{}_{}_{}", circuit_num, col_num, v))
                    .join(", ");
                evals.push(format!(
                    "    let instance_eval_{}_{} = inner_product(lagrange_polynomial_instances, [{}])\n",
                    circuit_num, col_num, lagrange
                ));
            }
        }
        (names.join(", "), inputs.join(""), evals.join(""))
    };

    data.insert("PUBLIC_INPUTS_NAMES".to_string(), public_inputs_names);
    data.insert("PUBLIC_INPUTS".to_string(), public_inputs);
    data.insert("INSTANCE_EVALS".to_string(), instance_evals);
    data.insert("NUM_INSTANCES".to_string(), num_instances.to_string());

    let proof_extraction_stage = proof_extraction.join("");
    data.insert("PES".to_string(), proof_extraction_stage);

    data.insert(
        "X_EXPONENT".to_string(),
        circuit.instantiation_data.n_coefficient.to_string(),
    );

    // For multi-instance, we need to generate gate equations for EACH instance
    // The expressions reference advice_eval_N, which for multi-instance becomes advice_eval_I_N
    // Similarly for other per-instance evaluations
    let gates = if num_instances == 1 {
        circuit
            .compiled_gate_equations
            .iter()
            .enumerate()
            .map(|(id, gate)| {
                format!(
                    "    let gate_eq{:?} = {}\n",
                    id + 1,
                    gate.compile_expression()
                )
            })
            .join("")
    } else {
        // Multi-instance: generate gates for each instance with instance-prefixed variable names
        // Transform advice_eval_N -> advice_eval_I_N for each instance I
        // Also transform: permutations_evaluated_X_N -> permutations_evaluated_I_X_N
        //                 product_eval_N -> product_eval_I_N, etc.
        (1..=num_instances)
            .map(|inst| {
                circuit
                    .compiled_gate_equations
                    .iter()
                    .enumerate()
                    .map(|(id, gate)| {
                        // Get the base expression and transform it for this instance
                        let base_expr = gate.compile_expression();
                        // Transform per-instance evaluation names
                        let transformed = transform_expression_for_instance(&base_expr, inst, columns_per_instance);
                        format!("    let gate_eq{}_{:?} = {}\n", inst, id + 1, transformed)
                    })
                    .join("")
            })
            .join("")
    };
    data.insert("GATES".to_string(), gates);

    let lookup_tables = circuit
        .compiled_lookups_equations
        .1
        .iter()
        .enumerate()
        .map(|(id, gate)| {
            format!(
                "    let lookup_table_eq{:?} = {}\n",
                id + 1,
                combine_aiken_expressions(gate.clone())
            )
        })
        .join("");
    data.insert("LOOKUP_TABLES_EXPRESSIONS".to_string(), lookup_tables);

    // For multi-instance, lookup inputs need per-instance evaluation references
    let lookup_inputs = if num_instances == 1 {
        circuit
            .compiled_lookups_equations
            .0
            .iter()
            .enumerate()
            .map(|(id, gate)| {
                format!(
                    "    let lookup_input_eq{:?} = {}\n",
                    id + 1,
                    combine_aiken_expressions(gate.clone())
                )
            })
            .join("")
    } else {
        // Multi-instance: generate lookup inputs per-instance with transformed expressions
        (1..=num_instances)
            .flat_map(|inst| {
                circuit
                    .compiled_lookups_equations
                    .0
                    .iter()
                    .enumerate()
                    .map(move |(id, gate)| {
                        let base_expr = combine_aiken_expressions(gate.clone());
                        let transformed = transform_expression_for_instance(&base_expr, inst, columns_per_instance);
                        format!("    let lookup_input_eq{}_{:?} = {}\n", inst, id + 1, transformed)
                    })
            })
            .join("")
    };
    data.insert("LOOKUP_INPUTS_EXPRESSIONS".to_string(), lookup_inputs);

    // For multi-instance, generate lookup equations per-instance
    let lookup_equations = if num_instances == 1 {
        (1..=circuit.compiled_lookups_equations.0.len())
            .map(|id| {
                let l1 = format!("mul(evaluation_at_0, sub(scalarOne, product_eval_{}))", id);
                let l2 = format!("mul(last_evaluation, sub(mul(product_eval_{}, product_eval_{}), product_eval_{}))", id, id, id);
                let left = format!("mul(mul(product_next_eval_{}, add(permuted_input_eval_{}, beta)), add(permuted_table_eval_{}, gamma))", id, id, id);
                let right = format!("mul(mul(product_eval_{}, add(lookup_input_eq{}, beta)), add(lookup_table_eq{}, gamma))", id, id, id);
                let l3 = format!("mul(sub(lookup_left_{}, lookup_right_{}), active_rows)", id, id);
                let l4 = format!("mul(evaluation_at_0, sub(permuted_input_eval_{}, permuted_table_eval_{}))", id, id);
                let l5 = format!("mul(mul(sub(permuted_input_eval_{}, permuted_table_eval_{}), sub(permuted_input_eval_{}, permuted_input_inv_eval_{})), active_rows)", id, id, id, id);

                format!("    let lookup_expression_1_{} = {}\n", id, l1) +
                    format!("    let lookup_expression_2_{} = {}\n", id, l2).as_str() +
                    format!("    let lookup_left_{} = {}\n", id, left).as_str() +
                    format!("    let lookup_right_{} = {}\n", id, right).as_str() +
                    format!("    let lookup_expression_3_{} = {}\n", id, l3).as_str() +
                    format!("    let lookup_expression_4_{} = {}\n", id, l4).as_str() +
                    format!("    let lookup_expression_5_{} = {}\n\n\n", id, l5).as_str()
            })
            .join("")
    } else {
        // Multi-instance: generate lookup equations per-instance with instance-prefixed evals
        (1..=num_instances)
            .flat_map(|inst| {
                (1..=circuit.compiled_lookups_equations.0.len()).map(move |id| {
                    // For multi-instance, product_eval_1 -> product_eval_{inst}_1
                    let l1 = format!("mul(evaluation_at_0, sub(scalarOne, product_eval_{}_{}))", inst, id);
                    let l2 = format!("mul(last_evaluation, sub(mul(product_eval_{}_{}, product_eval_{}_{}), product_eval_{}_{}))", inst, id, inst, id, inst, id);
                    let left = format!("mul(mul(product_next_eval_{}_{}, add(permuted_input_eval_{}_{}, beta)), add(permuted_table_eval_{}_{}, gamma))", inst, id, inst, id, inst, id);
                    let right = format!("mul(mul(product_eval_{}_{}, add(lookup_input_eq{}_{}, beta)), add(lookup_table_eq{}, gamma))", inst, id, inst, id, id);
                    let l3 = format!("mul(sub(lookup_left_{}_{}, lookup_right_{}_{}), active_rows)", inst, id, inst, id);
                    let l4 = format!("mul(evaluation_at_0, sub(permuted_input_eval_{}_{}, permuted_table_eval_{}_{}))", inst, id, inst, id);
                    let l5 = format!("mul(mul(sub(permuted_input_eval_{}_{}, permuted_table_eval_{}_{}), sub(permuted_input_eval_{}_{}, permuted_input_inv_eval_{}_{})), active_rows)", inst, id, inst, id, inst, id, inst, id);

                    format!("    let lookup_expression_1_{}_{} = {}\n", inst, id, l1) +
                        format!("    let lookup_expression_2_{}_{} = {}\n", inst, id, l2).as_str() +
                        format!("    let lookup_left_{}_{} = {}\n", inst, id, left).as_str() +
                        format!("    let lookup_right_{}_{} = {}\n", inst, id, right).as_str() +
                        format!("    let lookup_expression_3_{}_{} = {}\n", inst, id, l3).as_str() +
                        format!("    let lookup_expression_4_{}_{} = {}\n", inst, id, l4).as_str() +
                        format!("    let lookup_expression_5_{}_{} = {}\n\n", inst, id, l5).as_str()
                })
            })
            .join("")
    };

    data.insert("LOOKUPS".to_string(), lookup_equations);

    // Permutation evaluations - for multi-instance, these need to reference instance-specific evals
    // However, the permutation check in halo2 has a different structure for multi-instance:
    // Each instance has its own permutation evaluation, and they're combined.
    // For multi-instance, generate permutation terms per-instance: term_{inst}_{n}
    let permutation_evals = if num_instances == 1 {
        circuit
            .permutations_evaluated_terms
            .iter()
            .enumerate()
            .map(|(id, expression)| {
                let term = expression.compile_expression();
                format!("    let term_{:?} = {}\n", id + 1, term)
            })
            .join("")
    } else {
        // For multi-instance, generate permutation terms for EACH instance
        (1..=num_instances)
            .flat_map(|inst| {
                circuit
                    .permutations_evaluated_terms
                    .iter()
                    .enumerate()
                    .map(move |(id, expression)| {
                        let base_term = expression.compile_expression();
                        let term = transform_expression_for_instance(&base_term, inst, columns_per_instance);
                        format!("    let term_{}_{:?} = {}\n", inst, id + 1, term)
                    })
            })
            .join("")
    };
    data.insert("PERMUTATIONS_EVALS".to_string(), permutation_evals);

    let mut sets_lhs: HashMap<char, String> = HashMap::new();
    let mut sets_rhs: HashMap<char, String> = HashMap::new();

    // For multi-instance, we need to generate permutation LHS/RHS/sets for each instance
    let (permutation_lhs, lhf_sets, permutation_rhs, rhf_sets, permutations_combined, sets_count) = if num_instances == 1 {
        // Original single-instance logic
        let permutation_lhs = circuit
            .permutation_terms_left
            .iter()
            .enumerate()
            .map(|(id, (set, expression))| {
                if sets_lhs.contains_key(set) {
                    let existing = sets_lhs
                        .get(set)
                        .unwrap_or_else(|| panic!("set {} not found", set));
                    sets_lhs.insert(*set, format!("mul({}, left{:?})", existing, id + 1));
                } else {
                    sets_lhs.insert(*set, format!("left{:?}", id + 1));
                };
                let term = expression.compile_expression();
                format!(
                    "    let left{:?} = {} //part of set {}\n",
                    id + 1,
                    term,
                    set
                )
            })
            .join("");

        let lhf_sets = sets_lhs
            .iter()
            .sorted_by_key(|(c, _)| **c)
            .enumerate()
            .map(|(set_number, (set_id, terms))| {
                format!(
                    "    let left_set{:?} = mul(permutations_evaluated_{}_2, {}) \n",
                    set_number + 1,
                    set_id,
                    terms
                )
            })
            .join("");

        let permutation_rhs = circuit
            .permutation_terms_right
            .iter()
            .enumerate()
            .map(|(id, (set, expression))| {
                if sets_rhs.contains_key(set) {
                    let existing = sets_rhs
                        .get(set)
                        .unwrap_or_else(|| panic!("set {} not found", set));
                    sets_rhs.insert(*set, format!("mul({}, right{:?})", existing, id + 1));
                } else {
                    sets_rhs.insert(*set, format!("right{:?}", id + 1));
                };
                let term = expression.compile_expression();
                format!(
                    "    let right{:?} = {} //part of set {}\n",
                    id + 1,
                    term,
                    set
                )
            })
            .join("");

        let rhf_sets = sets_rhs
            .iter()
            .sorted_by_key(|(c, _)| **c)
            .enumerate()
            .map(|(set_number, (set_id, terms))| {
                format!(
                    "    let right_set{:?} = mul(permutations_evaluated_{}_1, {}) \n",
                    set_number + 1,
                    set_id,
                    terms
                )
            })
            .join("");

        let sets_count = sets_lhs.len();
        let permutations_combined = if sets_lhs.len() == sets_rhs.len() {
            (1..=sets_count).map(|n| {
                format!("    let permutations{} = mul(sub(left_set{}, right_set{}), sub(scalarOne, add(last_evaluation, sum_of_evaluation_for_blinding_factors)))\n", n, n, n)
            }).join("")
        } else {
            panic!("permutations sets have to be equal length")
        };

        (permutation_lhs, lhf_sets, permutation_rhs, rhf_sets, permutations_combined, sets_count)
    } else {
        // Multi-instance: generate LHS/RHS for each instance with format left{inst}_{id}
        let mut all_lhs = String::new();
        let mut all_lhs_sets = String::new();
        let mut all_rhs = String::new();
        let mut all_rhs_sets = String::new();
        let mut all_permutations = String::new();
        let mut base_sets_count = 0;

        for inst in 1..=num_instances {
            let mut inst_sets_lhs: HashMap<char, String> = HashMap::new();
            let mut inst_sets_rhs: HashMap<char, String> = HashMap::new();

            // LHS for this instance
            for (id, (set, expression)) in circuit.permutation_terms_left.iter().enumerate() {
                if inst_sets_lhs.contains_key(set) {
                    let existing = inst_sets_lhs
                        .get(set)
                        .unwrap_or_else(|| panic!("set {} not found", set));
                    inst_sets_lhs.insert(*set, format!("mul({}, left{}_{:?})", existing, inst, id + 1));
                } else {
                    inst_sets_lhs.insert(*set, format!("left{}_{:?}", inst, id + 1));
                };
                let base_term = expression.compile_expression();
                let term = transform_expression_for_instance(&base_term, inst, columns_per_instance);
                all_lhs.push_str(&format!(
                    "    let left{}_{:?} = {} //part of set {} instance {}\n",
                    inst, id + 1, term, set, inst
                ));
            }

            // LHS sets for this instance
            for (set_number, (set_id, terms)) in inst_sets_lhs.iter().sorted_by_key(|(c, _)| **c).enumerate() {
                all_lhs_sets.push_str(&format!(
                    "    let left_set{}_{:?} = mul(permutations_evaluated_{}_{}_2, {}) \n",
                    inst, set_number + 1, inst, set_id, terms
                ));
            }

            // RHS for this instance
            for (id, (set, expression)) in circuit.permutation_terms_right.iter().enumerate() {
                if inst_sets_rhs.contains_key(set) {
                    let existing = inst_sets_rhs
                        .get(set)
                        .unwrap_or_else(|| panic!("set {} not found", set));
                    inst_sets_rhs.insert(*set, format!("mul({}, right{}_{:?})", existing, inst, id + 1));
                } else {
                    inst_sets_rhs.insert(*set, format!("right{}_{:?}", inst, id + 1));
                };
                let base_term = expression.compile_expression();
                let term = transform_expression_for_instance(&base_term, inst, columns_per_instance);
                all_rhs.push_str(&format!(
                    "    let right{}_{:?} = {} //part of set {} instance {}\n",
                    inst, id + 1, term, set, inst
                ));
            }

            // RHS sets for this instance
            for (set_number, (set_id, terms)) in inst_sets_rhs.iter().sorted_by_key(|(c, _)| **c).enumerate() {
                all_rhs_sets.push_str(&format!(
                    "    let right_set{}_{:?} = mul(permutations_evaluated_{}_{}_1, {}) \n",
                    inst, set_number + 1, inst, set_id, terms
                ));
            }

            // Combined permutations for this instance
            if inst_sets_lhs.len() != inst_sets_rhs.len() {
                panic!("permutations sets have to be equal length");
            }
            base_sets_count = inst_sets_lhs.len();
            for n in 1..=base_sets_count {
                all_permutations.push_str(&format!(
                    "    let permutations{}_{} = mul(sub(left_set{}_{}, right_set{}_{}), sub(scalarOne, add(last_evaluation, sum_of_evaluation_for_blinding_factors)))\n",
                    inst, n, inst, n, inst, n
                ));
            }
        }

        (all_lhs, all_lhs_sets, all_rhs, all_rhs_sets, all_permutations, base_sets_count)
    };

    data.insert("PERMUTATIONS_LHS".to_string(), permutation_lhs);
    data.insert("LHS_SETS".to_string(), lhf_sets);
    data.insert("PERMUTATIONS_RHS".to_string(), permutation_rhs);
    data.insert("RHS_SETS".to_string(), rhf_sets);
    data.insert("PERMUTATIONS_COMBINED".to_string(), permutations_combined);

    let gates_count = circuit.compiled_gate_equations.len();
    let permutations_eval_count = circuit.permutations_evaluated_terms.len();
    // sets_count is now returned from the permutation generation block
    let lookups_count = circuit.compiled_lookups_equations.0.len();

    // For multi-instance, we need to reference gate equations per-instance
    // gate_eq{inst}_{gate_num} for multi-instance, gate_eq{gate_num} for single
    let effective_gates_count = gates_count * num_instances;
    let effective_permutations_eval_count = permutations_eval_count * num_instances;
    let effective_sets_count = sets_count * num_instances;
    
    let mut vanishing_expressions = if num_instances == 1 {
        (1..=gates_count)
            .map(|n| format!("    let expression{} = gate_eq{}\n", n, n))
            .collect::<Vec<_>>()
    } else {
        (1..=num_instances)
            .flat_map(|inst| {
                (1..=gates_count).map(move |n| {
                    let expr_idx = (inst - 1) * gates_count + n;
                    format!("    let expression{} = gate_eq{}_{}\n", expr_idx, inst, n)
                })
            })
            .collect::<Vec<_>>()
    };

    // Permutation terms - for multi-instance use term_{inst}_{n} format
    let expressions = if num_instances == 1 {
        (1..=permutations_eval_count)
            .map(|n| format!("    let expression{} = term_{}\n", n + effective_gates_count, n))
            .collect::<Vec<_>>()
    } else {
        (1..=num_instances)
            .flat_map(|inst| {
                (1..=permutations_eval_count).map(move |n| {
                    let expr_idx = effective_gates_count + (inst - 1) * permutations_eval_count + n;
                    format!("    let expression{} = term_{}_{}\n", expr_idx, inst, n)
                })
            })
            .collect::<Vec<_>>()
    };
    vanishing_expressions.extend(expressions);

    // Permutation sets - for multi-instance use permutations{inst}_{n} format
    let expressions = if num_instances == 1 {
        (1..=sets_count)
            .map(|n| {
                format!(
                    "    let expression{} = permutations{}\n",
                    n + effective_gates_count + permutations_eval_count,
                    n
                )
            })
            .collect::<Vec<_>>()
    } else {
        (1..=num_instances)
            .flat_map(|inst| {
                (1..=sets_count).map(move |n| {
                    let expr_idx = effective_gates_count + effective_permutations_eval_count + (inst - 1) * sets_count + n;
                    format!("    let expression{} = permutations{}_{}\n", expr_idx, inst, n)
                })
            })
            .collect::<Vec<_>>()
    };
    vanishing_expressions.extend(expressions);

    // For multi-instance, lookup expressions are per-instance
    let effective_lookups_count = lookups_count * num_instances;
    let expressions = if num_instances == 1 {
        (1..=lookups_count)
            .flat_map(|n| {
                let base_offset = effective_gates_count + permutations_eval_count + sets_count;
                [
                    format!(
                        "    let expression{} = lookup_expression_1_{}\n",
                        ((n - 1) * 5) + 1 + base_offset,
                        n
                    ),
                    format!(
                        "    let expression{} = lookup_expression_2_{}\n",
                        ((n - 1) * 5) + 2 + base_offset,
                        n
                    ),
                    format!(
                        "    let expression{} = lookup_expression_3_{}\n",
                        ((n - 1) * 5) + 3 + base_offset,
                        n
                    ),
                    format!(
                        "    let expression{} = lookup_expression_4_{}\n",
                        ((n - 1) * 5) + 4 + base_offset,
                        n
                    ),
                    format!(
                        "    let expression{} = lookup_expression_5_{}\n",
                        ((n - 1) * 5) + 5 + base_offset,
                        n
                    ),
                ]
            })
            .collect::<Vec<_>>()
    } else {
        // Multi-instance: lookup expressions are named lookup_expression_{K}_{inst}_{lookup}
        // Use effective counts which are already multiplied by num_instances
        let base_offset = effective_gates_count + effective_permutations_eval_count + effective_sets_count;
        (1..=num_instances)
            .flat_map(|inst| {
                (1..=lookups_count).flat_map(move |n| {
                    let lookup_idx = (inst - 1) * lookups_count + n;
                    let offset = ((lookup_idx - 1) * 5) + base_offset;
                    [
                        format!("    let expression{} = lookup_expression_1_{}_{}\n", offset + 1, inst, n),
                        format!("    let expression{} = lookup_expression_2_{}_{}\n", offset + 2, inst, n),
                        format!("    let expression{} = lookup_expression_3_{}_{}\n", offset + 3, inst, n),
                        format!("    let expression{} = lookup_expression_4_{}_{}\n", offset + 4, inst, n),
                        format!("    let expression{} = lookup_expression_5_{}_{}\n", offset + 5, inst, n),
                    ]
                })
            })
            .collect::<Vec<_>>()
    };
    vanishing_expressions.extend(expressions);

    let _expressions_count = vanishing_expressions.len();

    data.insert(
        "VANISHING_EXPRESSIONS".to_string(),
        vanishing_expressions.join(""),
    );

    let total_expressions = effective_gates_count + effective_permutations_eval_count + effective_sets_count + effective_lookups_count * 5;
    let mut vanishing_evaluation = "add(mul(scalarZero, y), expression1)".to_string();
    for n in 2..=total_expressions {
        vanishing_evaluation = format!("add(mul({}, y), expression{})", vanishing_evaluation, n)
    }
    let vanishing_evaluation = format!("    let hEval = {}\n", vanishing_evaluation);
    data.insert("VANISHING_EVALUATION".to_string(), vanishing_evaluation);

    let h_commitments = circuit
        .h_commitments
        .iter()
        .map(|(variable_name, expression)| {
            let term = expression.compile_expression();
            format!("    let {} = {}\n", variable_name, term)
        })
        .join("");
    data.insert("H_COMMITMENTS".to_string(), h_commitments);

    let (unique_grouped_points, commitment_data) = precompute_intermediate_sets(circuit);

    // below there are computations for both cases HALO2 and GWC19, but not all of them are used
    // specific values are picked based on what is used in .hbs template
    // elements are separated by prefix HALO2_ elements are related to halo2 version of KZG
    // prefix GEC19_ is for elements related to gwc19 version of KZG

    // Helper function to check if a commitment is per-instance
    fn is_per_instance_commitment(c: &Commitments) -> bool {
        matches!(
            c,
            Commitments::Advice(_)
                | Commitments::Permutation(_)
                | Commitments::Lookup(_)
                | Commitments::PermutedInput(_)
                | Commitments::PermutedTable(_)
        )
    }

    let point_sets_indexes: Vec<usize> = (0..unique_grouped_points.len()).collect();
    // For multi-instance, per-instance commitments are expanded to all instances
    // We need to count the expanded number, not the original
    let max_commitments_per_points_set = point_sets_indexes
        .iter()
        .map(|&idx| {
            commitment_data
                .iter()
                .filter(|cd| cd.point_set_index == idx)
                .map(|cd| {
                    if num_instances > 1 && is_per_instance_commitment(&cd.commitment) {
                        num_instances // Each per-instance commitment expands to N entries
                    } else {
                        1
                    }
                })
                .sum::<usize>()
        })
        .max()
        .unwrap_or(0);
    data.insert(
        "HALO2_X1_POWERS_COUNT".to_string(),
        max_commitments_per_points_set.to_string(),
    );

    data.insert(
        "HALO2_X4_POWERS_COUNT".to_string(),
        (point_sets_indexes.len() + 1).to_string(),
    );

    let q_evaluations = (1..=circuit.instantiation_data.q_evaluations_count)
        .map(|n| format!("q_eval_on_x3_{}", n))
        .join(", ");
    data.insert("HALO2_Q_EVALS_FROM_PROOF".to_string(), q_evaluations);

    // Helper function to check if an evaluation is per-instance
    fn is_per_instance_evaluation(e: &Evaluations) -> bool {
        matches!(
            e,
            Evaluations::Advice(_)
                | Evaluations::Permutation(_, _)
                | Evaluations::Lookup(_)
                | Evaluations::LookupNext(_)
                | Evaluations::PermutedInput(_)
                | Evaluations::PermutedInputInverse(_)
                | Evaluations::PermutedTable(_)
        )
    }

    // Helper to generate instance-prefixed commitment name
    fn commitment_name_for_instance(c: &Commitments, instance: usize) -> String {
        match c {
            Commitments::Advice(idx) => format!("a_{}_{}", instance, idx),
            Commitments::Permutation(set) => format!("permutations_committed_{}_{}", instance, set),
            Commitments::Lookup(idx) => format!("lookup_commitment_{}_{}", instance, idx),
            Commitments::PermutedInput(idx) => format!("permuted_input_{}_{}", instance, idx),
            Commitments::PermutedTable(idx) => format!("permuted_table_{}_{}", instance, idx),
            _ => c.compile_expression(), // Fixed, PermutationsCommon, etc.
        }
    }

    // Helper to generate instance-prefixed evaluation name
    fn evaluation_name_for_instance(e: &Evaluations, instance: usize) -> String {
        match e {
            Evaluations::Advice(idx) => format!("advice_eval_{}_{}", instance, idx),
            Evaluations::Permutation(set, idx) => {
                format!("permutations_evaluated_{}_{}_{}", instance, set, idx)
            }
            Evaluations::Lookup(idx) => format!("product_eval_{}_{}", instance, idx),
            Evaluations::LookupNext(idx) => format!("product_next_eval_{}_{}", instance, idx),
            Evaluations::PermutedInput(idx) => format!("permuted_input_eval_{}_{}", instance, idx),
            Evaluations::PermutedInputInverse(idx) => {
                format!("permuted_input_inv_eval_{}_{}", instance, idx)
            }
            Evaluations::PermutedTable(idx) => format!("permuted_table_eval_{}_{}", instance, idx),
            _ => e.compile_expression(), // Fixed, PermutationsCommon, etc.
        }
    }

    // Pre-sort commitment data by point set index to save on this inside the contract
    // For multi-instance, expand per-instance commitments to all instances
    let halo2_commitment_data = point_sets_indexes
        .iter()
        .map(|idx| {
            let commitments_in_set: Vec<&CommitmentData> = commitment_data
                .iter()
                .filter(|&cd| cd.point_set_index == *idx)
                .collect();

            let commitments_in_set_str = if num_instances == 1 {
                // Single instance: use original names
                commitments_in_set
                    .iter()
                    .map(|commitment_data| {
                        format!(
                            "\t\t\t({}, [{}])",
                            commitment_data.commitment.compile_expression(),
                            commitment_data
                                .evaluations
                                .iter()
                                .map(AikenExpression::compile_expression)
                                .join(",")
                        )
                    })
                    .join(",\n")
            } else {
                // Multi-instance: expand per-instance commitments for all instances
                let mut entries: Vec<String> = Vec::new();
                for cd in &commitments_in_set {
                    if is_per_instance_commitment(&cd.commitment) {
                        // Generate entries for each instance
                        for inst in 1..=num_instances {
                            let commitment_name =
                                commitment_name_for_instance(&cd.commitment, inst);
                            let evals_str = cd
                                .evaluations
                                .iter()
                                .map(|e| {
                                    if is_per_instance_evaluation(e) {
                                        evaluation_name_for_instance(e, inst)
                                    } else {
                                        e.compile_expression()
                                    }
                                })
                                .join(",");
                            entries.push(format!("\t\t\t({}, [{}])", commitment_name, evals_str));
                        }
                    } else {
                        // Fixed/common commitments: use original names
                        entries.push(format!(
                            "\t\t\t({}, [{}])",
                            cd.commitment.compile_expression(),
                            cd.evaluations
                                .iter()
                                .map(AikenExpression::compile_expression)
                                .join(",")
                        ));
                    }
                }
                entries.join(",\n")
            };

            format!("\n\t\t[\n{}\n\t\t]", commitments_in_set_str)
        })
        .join(",");

    let kzg_halo2_commitment_map =
        format!("\tlet commitment_data = [{}]", halo2_commitment_data);
    data.insert("HALO2_COMMITMENT_MAP".to_string(), kzg_halo2_commitment_map);

    let kzg_halo2_point_sets = unique_grouped_points
        .iter()
        .map(|set| set.iter().map(decode_rotation).join(","))
        .join("],[");

    let kzg_halo2_point_sets = format!("     let point_sets = [[{}]]", kzg_halo2_point_sets);
    data.insert("HALO2_POINT_SETS".to_string(), kzg_halo2_point_sets);

    let kzg_gwc19_intermediate_sets = construct_intermediate_sets(circuit.all_queries_ordered());
    let (left, right) = construct_msm(kzg_gwc19_intermediate_sets);

    let optimized_left = flatten_msm(&left).optimize_msm();
    let optimized_right = flatten_msm(&right).optimize_msm();

    let kzg_gwc19_msm = format!(
        "    let el = eval({})\n    let er = eval({})",
        optimized_left.compile_expression(),
        optimized_right.compile_expression()
    );
    data.insert("GWC19_MSM".to_string(), kzg_gwc19_msm.clone());

    // Extract max powers of v and u by traversing scalar operations in optimized MSMs
    let max_v_power = optimized_left.find_max_power('v')
        .max(optimized_right.find_max_power('v'));
    let max_u_power = optimized_left.find_max_power('u')
        .max(optimized_right.find_max_power('u'));

    let generate_powers = |var_name: char, max_power: i32| -> String {
        (2..=max_power)
            .map(|i| format!("\tlet {}{} = mul({}{}, {})", var_name, i, var_name, i - 1, var_name))
            .join("\n")
    };

    data.insert("GWC19_V_POWERS".to_string(), generate_powers('v', max_v_power));
    data.insert("GWC19_U_POWERS".to_string(), generate_powers('u', max_u_power));

    let fixed_commitments_imports = (1..=circuit.instantiation_data.fixed_commitments.len())
        .map(|id| format!("f{}_commitment", id))
        .join(", ");
    let permutation_commitments_imports =
        (1..=circuit.instantiation_data.permutation_commitments.len())
            .map(|id| format!("p{}_commitment", id))
            .join(", ");

    data.insert("F_IMPORTS".to_string(), fixed_commitments_imports);
    data.insert("P_IMPORTS".to_string(), permutation_commitments_imports);

    match test_data {
        None => {
            data.insert(
                "TEST_VALID_PROOF_VALID_INPUTS".to_string(),
                "True".to_string(),
            );
            data.insert(
                "TEST_VALID_PROOF_INVALID_INPUTS".to_string(),
                "False".to_string(),
            );
            data.insert(
                "TEST_INVALID_PROOF_INVALID_INPUTS".to_string(),
                "False".to_string(),
            );
            data.insert(
                "TEST_VALID_PROOF_TRIVIAL_INPUTS".to_string(),
                "False".to_string(),
            );
            data.insert(
                "TEST_TRIVIAL_PROOF_TRIVIAL_INPUTS".to_string(),
                "False".to_string(),
            );
        }
        Some((proof, invalid_proof, public_inputs)) => {
            let test_valid_proof_valid_inputs = format!(
                "verifier(#\"{}\", {})",
                hex::encode(proof.clone()),
                public_inputs
                    .iter()
                    .map(|e| format!("from_int(0x{})", hex::encode(e.to_bytes_be())))
                    .join(", ")
            );

            data.insert(
                "TEST_VALID_PROOF_VALID_INPUTS".to_string(),
                test_valid_proof_valid_inputs,
            );

            if let Some(template) = profiler_file {
                let mut handlebars = Handlebars::new();
                handlebars.set_strict_mode(true);
                handlebars.register_template_file("profiler_template", template)?;
                let mut output_file = File::create("aiken-verifier/aiken_halo2/validators/profiler.ak")?;
                handlebars.render_to_write("profiler_template", &data, &mut output_file)?;
                handlebars.render("profiler_template", &data)?;
            }

            let test_valid_proof_invalid_inputs = format!(
                "verifier(#\"{}\", {})",
                hex::encode(proof.clone()),
                public_inputs
                    .iter()
                    .map(|e| {
                        let invalid_input = e.neg();
                        format!("from_int(0x{})", hex::encode(invalid_input.to_bytes_be()))
                    })
                    .join(", ")
            );

            data.insert(
                "TEST_VALID_PROOF_INVALID_INPUTS".to_string(),
                test_valid_proof_invalid_inputs,
            );

            let test_invalid_proof_invalid_inputs = format!(
                "verifier(#\"{}\", {})",
                hex::encode(invalid_proof),
                public_inputs
                    .iter()
                    .map(|e| {
                        let invalid_input = e.neg();
                        format!("from_int(0x{})", hex::encode(invalid_input.to_bytes_be()))
                    })
                    .join(", ")
            );

            data.insert(
                "TEST_INVALID_PROOF_INVALID_INPUTS".to_string(),
                test_invalid_proof_invalid_inputs,
            );

            let test_valid_proof_trivial_inputs = format!(
                "verifier(#\"{}\", {})",
                hex::encode(proof.clone()),
                public_inputs
                    .iter()
                    .map(|_e| format!("from_int(0x{})", hex::encode(Scalar::ONE.to_bytes_be())))
                    .join(", ")
            );
            data.insert(
                "TEST_VALID_PROOF_TRIVIAL_INPUTS".to_string(),
                test_valid_proof_trivial_inputs,
            );
        }
    }

    let mut handlebars = Handlebars::new();
    handlebars.set_strict_mode(true);
    handlebars.register_template_file("aiken_template", template_file)?;
    let mut output_file = File::create(aiken_file)?;
    handlebars.render_to_write("aiken_template", &data, &mut output_file)?;
    handlebars.render("aiken_template", &data)
}

pub fn emit_vk_code(
    template_file: &Path,
    aiken_file: &Path,
    circuit: &CircuitRepresentation,
) -> Result<String, RenderError> {
    let mut data: HashMap<String, String> = HashMap::new(); // data to bind to mustache template

    let points = circuit
        .instantiation_data
        .fixed_commitments
        .iter()
        .cloned()
        .map(|g| hex::encode(g.to_bytes()));

    let points = points
        .enumerate()
        .map(|(idx, g1_encoded)| {
            format!(
                "pub const f{}_commitment: ByteArray = #\"{}\"",
                idx + 1,
                g1_encoded
            )
        })
        .join("\n");

    data.insert("FIXED_COMMITMENTS".to_string(), points);

    let points = circuit
        .instantiation_data
        .permutation_commitments
        .iter()
        .cloned()
        .map(|g| hex::encode(g.to_bytes()));

    let points = points
        .enumerate()
        .map(|(idx, g1_encoded)| {
            format!(
                "pub const p{}_commitment: ByteArray = #\"{}\"",
                idx + 1,
                g1_encoded
            )
        })
        .join("\n");

    data.insert("PERMUTATION_COMMITMENTS".to_string(), points);

    let compressed_sg2 = hex::encode(circuit.instantiation_data.s_g2.to_bytes());

    debug!("compressed_sg2: {}", compressed_sg2);

    data.insert(
        "G2_DEFINITIONS".to_string(),
        format!("\"{}\"", compressed_sg2),
    );
    data.insert(
        "OMEGA".to_string(),
        hex::encode(circuit.instantiation_data.omega.to_bytes_be()),
    );
    data.insert(
        "OMEGA_INV".to_string(),
        hex::encode(circuit.instantiation_data.inverted_omega.to_bytes_be()),
    );
    data.insert(
        "BARYCENTRIC_WEIGHT".to_string(),
        hex::encode(circuit.instantiation_data.barycentric_weight.to_bytes_be()),
    );
    data.insert(
        "TRANSCRIPT_REP".to_string(),
        hex::encode(
            circuit
                .instantiation_data
                .transcript_representation
                .to_bytes_be(),
        ),
    );
    data.insert(
        "BLINDING_FACTORS".to_string(),
        circuit.instantiation_data.blinding_factors.to_string(),
    );

    let fixed_commitments = circuit.instantiation_data.fixed_commitments.len();

    let permutation_commitments = circuit.instantiation_data.permutation_commitments.len();

    let fixed = (1..=fixed_commitments).map(|idx| {
        format!(
            "\tlet f{idx}_commitment = decompress(f{idx}_commitment)\n\
            \texpect f{idx}_commitment == f{idx}_commitment"
        )
    });
    let permutations = (1..=permutation_commitments).map(|idx| {
        format!(
            "\tlet p{idx}_commitment = decompress(p{idx}_commitment)\n\
            \texpect p{idx}_commitment == p{idx}_commitment"
        )
    });

    let budget_check = fixed
        .chain(permutations)
        .chain(once("    expect g2_const == g2_const".to_string()))
        .join("\n");

    data.insert("BUDGET_CHECK".to_string(), budget_check);

    let mut handlebars = Handlebars::new();
    handlebars.set_strict_mode(true);
    handlebars.register_template_file("aiken_template", template_file)?;
    let mut output_file = File::create(aiken_file)?;
    handlebars.render_to_write("aiken_template", &data, &mut output_file)?;
    handlebars.render("aiken_template", &data)
}

fn construct_intermediate_sets(queries: [Vec<Query>; 6]) -> Vec<(Vec<Query>, RotationDescription)> {
    let mut point_query_map: Vec<(RotationDescription, Vec<Query>)> = Vec::new();
    for query in queries.iter().flatten() {
        if let Some(pos) = point_query_map
            .iter()
            .position(|(point, _)| *point == query.point)
        {
            let (_, queries) = &mut point_query_map[pos];
            queries.push(*query);
        } else {
            point_query_map.push((query.point, vec![*query]));
        }
    }

    point_query_map
        .into_iter()
        .map(|(point, queries)| (queries, point))
        .collect()
}

// symbolic representation of powers of specific scalar
fn powers(name: char) -> impl Iterator<Item = ScalarOperation> {
    (0..).map(move |idx| Power(name, idx))
}

//this is done in Plinth with template haskell since there is no macro language for aiken
// constructing final MSM was reimplemented with pure code generation
// to make it easier to debug this function is 1:1 analog to multi_prepare
// in src/poly/gwc_kzg/mod.rs
// in https://github.com/input-output-hk/halo2/blob/gwc19_kzg/src/poly/gwc_kzg/mod.rs#L142-L212
// but was translated to build MSM description instead of calculating one
fn construct_msm(
    commitment_data: Vec<(Vec<Query>, RotationDescription)>,
) -> (MsmOperations, MsmOperations) {
    let w_count = commitment_data.len();

    let mut commitment_multi = MsmOperations::Empty;
    let mut eval_multi = ScalarOperation::Zero;

    let mut witness = MsmOperations::Empty;
    let mut witness_with_aux = MsmOperations::Empty;

    for ((commitment_at_a_point, wi), power_of_u) in
        commitment_data.iter().zip(0..w_count).zip(powers('u'))
    {
        let (queries, point) = commitment_at_a_point;

        assert!(!queries.is_empty());
        let z = point;

        let (commitment_batch, eval_batch) = queries
            .iter()
            .zip(powers('v'))
            .map(|(query, power_of_v)| {
                assert_eq!(query.point, *z);

                let commitment = query.commitment;
                let mut msm = MsmOperations::Empty;
                msm = MsmOperations::Append(Box::new(msm), power_of_v.clone(), commitment);

                let eval = ScalarOperation::Mul(Box::new(power_of_v), query.evaluation);

                (msm, eval)
            })
            .reduce(|(commitment_acc, eval_acc), (commitment, eval)| {
                (
                    MsmOperations::Add(Box::new(commitment_acc.clone()), Box::new(commitment)),
                    ScalarOperation::Add(Box::new(eval_acc), Box::new(eval)),
                )
            })
            .unwrap();

        let commitment_batch =
            MsmOperations::Scale(Box::new(commitment_batch.clone()), power_of_u.clone());
        commitment_multi =
            MsmOperations::Add(Box::new(commitment_multi), Box::new(commitment_batch));
        eval_multi = ScalarOperation::Add(
            Box::new(eval_multi),
            Box::new(ScalarOperation::MulS(
                Box::new(power_of_u.clone()),
                Box::new(eval_batch),
            )),
        );

        witness_with_aux = MsmOperations::AppendW(
            Box::new(witness_with_aux),
            ScalarOperation::MulS(
                Box::new(power_of_u.clone()),
                Box::new(ScalarOperation::Rotation(*z)),
            ),
            wi,
        );
        witness = MsmOperations::AppendW(Box::new(witness), power_of_u, wi);
    }

    let left: MsmOperations = witness;
    let mut right: MsmOperations = MsmOperations::Empty;

    right = MsmOperations::Add(Box::new(right), Box::new(witness_with_aux));
    right = MsmOperations::Add(Box::new(right), Box::new(commitment_multi));
    right = MsmOperations::AppendNegatedG1(Box::new(right), eval_multi);

    (left, right)
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum ScalarOperation {
    Zero,
    Mul(Box<ScalarOperation>, Evaluations),
    MulS(Box<ScalarOperation>, Box<ScalarOperation>),
    Power(char, i32),
    Add(Box<ScalarOperation>, Box<ScalarOperation>),
    Rotation(RotationDescription),
}

#[derive(Clone, Eq, PartialEq)]
enum MsmOperations {
    Empty,
    Append(Box<MsmOperations>, ScalarOperation, Commitments),
    AppendW(Box<MsmOperations>, ScalarOperation, usize),
    AppendNegatedG1(Box<MsmOperations>, ScalarOperation),
    Add(Box<MsmOperations>, Box<MsmOperations>),
    Scale(Box<MsmOperations>, ScalarOperation),
}

#[derive(Debug)]
struct OptimizedMSM {
    elements: Vec<ElementMSM>,
}

#[derive(Debug)]
enum ElementMSM {
    Element(ScalarOperation, Commitments),
    ElementW(ScalarOperation, usize),
    ElementNegatedG1(ScalarOperation),
}

impl ElementMSM {
    fn get_scalar(&mut self) -> &mut ScalarOperation {
        match self {
            ElementMSM::Element(scalar, _) => scalar,
            ElementMSM::ElementW(scalar, _) => scalar,
            ElementMSM::ElementNegatedG1(scalar) => scalar,
        }
    }
}

/// Flattens the recursive MSM operations tree into a linear list of elements,
/// producing an optimized flat structure ready for Aiken code generation.
fn flatten_msm(msm: &MsmOperations) -> OptimizedMSM {
    match msm {
        MsmOperations::Empty => OptimizedMSM { elements: vec![] },
        MsmOperations::Append(msm, scalar, commitment) => {
            let mut flattened = flatten_msm(msm);
            flattened
                .elements
                .push(ElementMSM::Element(scalar.clone(), *commitment));
            flattened
        }
        MsmOperations::AppendW(msm, scalar, index) => {
            let mut flattened = flatten_msm(msm);
            flattened
                .elements
                .push(ElementMSM::ElementW(scalar.clone(), *index));
            flattened
        }
        MsmOperations::AppendNegatedG1(msm, scalar) => {
            let mut flattened = flatten_msm(msm);
            flattened
                .elements
                .push(ElementMSM::ElementNegatedG1(scalar.clone()));
            flattened
        }
        MsmOperations::Add(msm_a, msm_b) => {
            let mut flattened_a = flatten_msm(msm_a);
            let mut flattened_b = flatten_msm(msm_b);
            flattened_a.elements.append(&mut flattened_b.elements);
            flattened_a
        }
        MsmOperations::Scale(msm, scalar) => {
            let mut flattened = flatten_msm(msm);
            flattened.elements.iter_mut().for_each(|e| {
                let s = e.get_scalar();
                *s = ScalarOperation::MulS(Box::new(scalar.clone()), Box::new(s.clone()))
            });
            flattened
        }
    }
}

impl OptimizedMSM {

    /// Optimizes MSM by combining elements with the same G1 point.
    /// Elements sharing the same point have their scalars added together,
    /// reducing the number of point operations.
    fn optimize_msm(self) -> OptimizedMSM {
        // Key to identify unique G1 points
        #[derive(Clone, Eq, PartialEq, Hash)]
        enum G1PointKey {
            Commitment(Commitments),
            W(usize),
            NegatedG1,
        }

        let mut groups: HashMap<G1PointKey, Vec<ScalarOperation>> = HashMap::new();
        let mut insertion_order: Vec<G1PointKey> = Vec::new();

        // Group elements by their G1 point
        for element in self.elements {
            let (key, scalar) = match element {
                ElementMSM::Element(scalar, commitment) => (G1PointKey::Commitment(commitment), scalar),
                ElementMSM::ElementW(scalar, index) => (G1PointKey::W(index), scalar),
                ElementMSM::ElementNegatedG1(scalar) => (G1PointKey::NegatedG1, scalar),
            };

            // Track insertion order for deterministic output
            if !groups.contains_key(&key) {
                insertion_order.push(key.clone());
            }

            groups.entry(key).or_insert_with(Vec::new).push(scalar);
        }

        // Combine scalars for each G1 point
        let optimized_elements: Vec<ElementMSM> = insertion_order
            .into_iter()
            .map(|key| {
                let scalars = groups.remove(&key).unwrap();

                // Combine all scalars by adding them together
                let combined_scalar = scalars.into_iter().reduce(|acc, scalar| {
                    ScalarOperation::Add(Box::new(acc), Box::new(scalar))
                }).unwrap();

                // Reconstruct the element with combined scalar
                match key {
                    G1PointKey::Commitment(commitment) => {
                        ElementMSM::Element(combined_scalar, commitment)
                    }
                    G1PointKey::W(index) => {
                        ElementMSM::ElementW(combined_scalar, index)
                    }
                    G1PointKey::NegatedG1 => {
                        ElementMSM::ElementNegatedG1(combined_scalar)
                    }
                }
            })
            .collect();

        OptimizedMSM {
            elements: optimized_elements,
        }
    }

    /// Finds the maximum power exponent for a given variable in an MSM.
    /// Recursively traverses all scalar operations to find Power(var_name, exponent).
    fn find_max_power(&self, var_name: char) -> i32 {
        (*self).elements
            .iter()
            .map(|element| {
                let scalar = match element {
                    ElementMSM::Element(s, _) => s,
                    ElementMSM::ElementW(s, _) => s,
                    ElementMSM::ElementNegatedG1(s) => s,
                };
                Self::find_max_power_in_scalar(scalar, var_name)
            })
            .max()
            .unwrap_or(0)
    }

    /// Recursively finds max power exponent in a scalar operation tree
    fn find_max_power_in_scalar(scalar: &ScalarOperation, var_name: char) -> i32 {
        match scalar {
            ScalarOperation::Power(name, exponent) if *name == var_name => *exponent,
            ScalarOperation::Mul(s, _) => Self::find_max_power_in_scalar(s, var_name),
            ScalarOperation::MulS(s1, s2) => {
                Self::find_max_power_in_scalar(s1, var_name).max(Self::find_max_power_in_scalar(s2, var_name))
            }
            ScalarOperation::Add(s1, s2) => {
                Self::find_max_power_in_scalar(s1, var_name).max(Self::find_max_power_in_scalar(s2, var_name))
            }
            _ => 0,
        }
    }
}

impl AikenExpression for OptimizedMSM {
    fn compile_expression(&self) -> String {
        let elements = self
            .elements
            .iter()
            .map(|element| match element {
                ElementMSM::Element(scalar, commitment) => format!(
                    "\n\t\t\t\tMSMElement {{ scalar: {}, g1: {} }}",
                    scalar.compile_expression(),
                    commitment.compile_expression(),
                ),
                ElementMSM::ElementW(scalar, index) => format!(
                    "\n\t\t\t\tMSMElement {{ scalar: {}, g1: w{} }}",
                    scalar.compile_expression(),
                    index + 1,
                ),
                ElementMSM::ElementNegatedG1(scalar) => {
                    format!(
                        "\n\t\t\t\tMSMElement {{ scalar: {}, g1: neg_g1_generator }}",
                        scalar.compile_expression(),
                    )
                }
            })
            .join(", ");
        format!("MSM{{elements: [ {} ]}}", elements)
    }
}

impl AikenExpression for ScalarOperation {
    fn compile_expression(&self) -> String {
        match self {
            //if rules are for eliminating operations that outcome can be predicted
            Mul(scalar, evaluation) if matches!(**scalar, Power(_, 0)) => {
                evaluation.compile_expression()
            }
            ScalarOperation::MulS(scalar_a, scalar_b) if matches!(**scalar_a, Power(_, 0)) => {
                scalar_b.compile_expression()
            }
            ScalarOperation::MulS(scalar_a, scalar_b) if matches!(**scalar_b, Power(_, 0)) => {
                scalar_a.compile_expression()
            }
            Power(_name, exponent) if *exponent == 0 => "scalarOne".to_string(),
            ScalarOperation::Add(scalar_a, scalar_b) if **scalar_a == ScalarOperation::Zero => {
                scalar_b.compile_expression()
            }

            ScalarOperation::Zero => "scalarZero".to_string(),
            Mul(scalar, evaluation) => {
                format!(
                    "mul({}, {})",
                    scalar.compile_expression(),
                    evaluation.compile_expression()
                )
            }
            ScalarOperation::MulS(scalar_a, scalar_b) => {
                format!(
                    "mul({}, {})",
                    scalar_a.compile_expression(),
                    scalar_b.compile_expression()
                )
            }
            Power(name, exponent) => {
                // All powers of `v` and `u` are pre-computed to avoid duplication
                // so here instead of calling `scale(v, X)` we just refer to `vX` variable
                // format!("scale({}, {})", name, exponent)
                format!("{}{}", name, exponent)
            }
            ScalarOperation::Add(scalar_a, scalar_b) => {
                format!(
                    "add({}, {})",
                    scalar_a.compile_expression(),
                    scalar_b.compile_expression()
                )
            }
            ScalarOperation::Rotation(x) => decode_rotation(x),
        }
    }
}
