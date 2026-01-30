//! PlonkUp circuit implementation as described in the PlonkUp paper.
//!
//! This circuit demonstrates the key features of PlonkUp:
//! - Lookups for 3-element tuples (e.g., XOR lookup table: (a, b, a XOR b))
//! - Polynomial Plonk constraints
//! - No references to neighboring rows (only Rotation::cur())
//!
//! This circuit is used for benchmarking the on-chain verifier performance.
//!
//! # Note on table size
//!
//! The XOR lookup table size grows as O(2^(2*max_bits)), so:
//! - max_bits=2: 16 entries
//! - max_bits=4: 256 entries
//! - max_bits=8: 65,536 entries
//!
//! Keep max_bits small (≤ 4) for reasonable performance in testing.

use ff::PrimeField;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{
    Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector, TableColumn,
};
use halo2_proofs::poly::Rotation;
use std::marker::PhantomData;

/// Number of advice columns for lookups
pub const NB_LOOKUP_COLS: usize = 3;

/// Configuration for the PlonkUp circuit
#[derive(Clone, Debug)]
pub struct PlonkUpConfig {
    /// Instance column for public inputs (exposes sum of XOR results as public input)
    pub instance: Column<Instance>,
    /// Selector for the lookup argument
    q_lookup: Selector,
    /// Selector for the polynomial constraint
    q_poly: Selector,
    /// Selector for the accumulator constraint (used to compute sum of XOR results)
    q_acc: Selector,
    /// The advice columns for lookup inputs (a, b, c) where c = a XOR b
    advice_cols: [Column<Advice>; NB_LOOKUP_COLS],
    /// Advice column for accumulator (running sum of XOR results)
    acc_col: Column<Advice>,
    /// Table columns for 3-element tuple lookup (t_a, t_b, t_c)
    t_a: TableColumn,
    t_b: TableColumn,
    t_c: TableColumn,
}

/// PlonkUp circuit with 3-element tuple lookups and polynomial constraints.
/// Demonstrates XOR operations verified via lookup tables.
///
/// # Fields
///
/// - `xor_inputs`: Tuples (a, b, a XOR b) for lookup verification
/// - `poly_inputs`: Tuples (a, b, a * b) for polynomial constraint verification
/// - `max_bits`: Maximum bit length for lookup values (table size = 2^(2*max_bits))
/// - `xor_sum`: Sum of all XOR results (public input)
#[derive(Clone, Default)]
pub struct PlonkUpCircuit<F: PrimeField> {
    /// XOR lookup inputs: Vec of (a, b, a XOR b)
    pub xor_inputs: Vec<(u64, u64, u64)>,
    /// Polynomial constraint inputs: Vec of (a, b, a * b)
    pub poly_inputs: Vec<(u64, u64, u64)>,
    /// Maximum bit length for values (determines table size)
    pub max_bits: usize,
    /// Sum of all XOR results (exposed as public input)
    pub xor_sum: u64,
    /// Marker for the field type
    pub _marker: PhantomData<F>,
}

impl<F: PrimeField> PlonkUpCircuit<F> {
    /// Create a new PlonkUp circuit with the given XOR and polynomial inputs.
    ///
    /// # Arguments
    ///
    /// - `xor_inputs`: Pairs (a, b) for XOR lookup verification (c = a XOR b is computed)
    /// - `poly_inputs`: Pairs (a, b) for polynomial constraint verification (c = a * b is computed)
    /// - `max_bits`: Maximum bit length for lookup values (table size = 2^(2*max_bits))
    ///
    /// # Panics
    ///
    /// Panics if max_bits > 8 to prevent accidentally creating very large tables.
    pub fn new(xor_inputs: Vec<(u64, u64)>, poly_inputs: Vec<(u64, u64)>, max_bits: usize) -> Self {
        assert!(
            max_bits <= 8,
            "max_bits must be <= 8 to avoid excessive table sizes (2^(2*max_bits) entries)"
        );
        // Compute the XOR results and their sum
        let xor_inputs: Vec<_> = xor_inputs
            .into_iter()
            .map(|(a, b)| (a, b, a ^ b))
            .collect();
        let xor_sum: u64 = xor_inputs.iter().map(|(_, _, c)| c).sum();
        // Compute the multiplication results
        let poly_inputs = poly_inputs
            .into_iter()
            .map(|(a, b)| (a, b, a * b))
            .collect();
        Self {
            xor_inputs,
            poly_inputs,
            max_bits,
            xor_sum,
            _marker: PhantomData,
        }
    }
    
    /// Returns the public input (sum of XOR results) as a field element
    pub fn public_input(&self) -> F {
        F::from(self.xor_sum)
    }
}

impl<F: PrimeField> Circuit<F> for PlonkUpCircuit<F> {
    type Config = PlonkUpConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // Create advice columns for the 3-element tuple lookup
        let advice_cols: [Column<Advice>; NB_LOOKUP_COLS] = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        // Enable equality for advice columns
        for col in &advice_cols {
            meta.enable_equality(*col);
        }

        // Create accumulator column for computing sum of XOR results
        let acc_col = meta.advice_column();
        meta.enable_equality(acc_col);

        // Create instance column for public inputs (exposed sum of XOR results)
        let instance = meta.instance_column();
        meta.enable_equality(instance);

        // Create fixed column for constants (used for initial accumulator value via assign_advice_from_constant)
        let _constant = meta.fixed_column();
        meta.enable_constant(_constant);

        // Create selectors
        let q_lookup = meta.complex_selector();
        let q_poly = meta.selector();
        let q_acc = meta.selector();

        // Create table columns for 3-element tuple lookup
        let t_a = meta.lookup_table_column();
        let t_b = meta.lookup_table_column();
        let t_c = meta.lookup_table_column();

        // Configure the 3-element tuple lookup for XOR
        // This is the key PlonkUp feature: looking up 3-element tuples
        meta.lookup("xor_3tuple_lookup", |meta| {
            let sel = meta.query_selector(q_lookup);
            let a = meta.query_advice(advice_cols[0], Rotation::cur());
            let b = meta.query_advice(advice_cols[1], Rotation::cur());
            let c = meta.query_advice(advice_cols[2], Rotation::cur());

            // 3-element tuple lookup: (a, b, c) must be in table (t_a, t_b, t_c)
            vec![(sel.clone() * a, t_a), (sel.clone() * b, t_b), (sel * c, t_c)]
        });

        // Configure polynomial constraint (without neighboring row references)
        // This gate enforces: a * b - c = 0 (example polynomial constraint)
        // Note: This uses only Rotation::cur(), not Rotation::next() or Rotation::prev()
        meta.create_gate("poly_constraint", |meta| {
            let sel = meta.query_selector(q_poly);
            let a = meta.query_advice(advice_cols[0], Rotation::cur());
            let b = meta.query_advice(advice_cols[1], Rotation::cur());
            let c = meta.query_advice(advice_cols[2], Rotation::cur());

            // Polynomial constraint: a * b = c (only using current row)
            vec![sel * (a * b - c)]
        });

        // Configure accumulator constraint: acc = prev_acc + xor_result
        // This accumulates the sum of XOR results to expose as public input
        // Note: This uses only Rotation::cur() to stay PlonkUp-compatible
        meta.create_gate("accumulator", |meta| {
            let sel = meta.query_selector(q_acc);
            let xor_result = meta.query_advice(advice_cols[2], Rotation::cur());
            let prev_acc = meta.query_advice(advice_cols[0], Rotation::cur());
            let acc = meta.query_advice(acc_col, Rotation::cur());

            // Constraint: acc = prev_acc + xor_result
            vec![sel * (acc - prev_acc - xor_result)]
        });

        PlonkUpConfig {
            instance,
            q_lookup,
            q_poly,
            q_acc,
            advice_cols,
            acc_col,
            t_a,
            t_b,
            t_c,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // Assign the XOR lookup table (3-element tuples)
        layouter.assign_table(
            || "xor_3tuple_table",
            |mut table| {
                let mut offset = 0;
                let max_val = 1u64 << self.max_bits;

                // Populate the table with all possible XOR combinations
                for a in 0..max_val {
                    for b in 0..max_val {
                        let c = a ^ b;
                        table.assign_cell(
                            || "t_a",
                            config.t_a,
                            offset,
                            || Value::known(F::from(a)),
                        )?;
                        table.assign_cell(
                            || "t_b",
                            config.t_b,
                            offset,
                            || Value::known(F::from(b)),
                        )?;
                        table.assign_cell(
                            || "t_c",
                            config.t_c,
                            offset,
                            || Value::known(F::from(c)),
                        )?;
                        offset += 1;
                    }
                }
                Ok(())
            },
        )?;

        // Assign the lookup witnesses and enable lookup constraints
        layouter.assign_region(
            || "xor_lookups",
            |mut region| {
                for (offset, (a, b, c)) in self.xor_inputs.iter().enumerate() {
                    // Enable the lookup selector
                    config.q_lookup.enable(&mut region, offset)?;

                    // Assign the 3-element tuple for lookup
                    region.assign_advice(
                        || "a",
                        config.advice_cols[0],
                        offset,
                        || Value::known(F::from(*a)),
                    )?;
                    region.assign_advice(
                        || "b",
                        config.advice_cols[1],
                        offset,
                        || Value::known(F::from(*b)),
                    )?;
                    region.assign_advice(
                        || "c",
                        config.advice_cols[2],
                        offset,
                        || Value::known(F::from(*c)),
                    )?;
                }
                Ok(())
            },
        )?;

        // Compute and constrain the sum of XOR results using the accumulator
        // This uses the constant column for the initial zero value
        let final_acc = layouter.assign_region(
            || "accumulator",
            |mut region| {
                let mut running_sum: u64 = 0;
                let mut final_acc_cell = None;

                for (offset, (_, _, c)) in self.xor_inputs.iter().enumerate() {
                    // Enable the accumulator constraint
                    config.q_acc.enable(&mut region, offset)?;

                    // Assign prev_acc (running sum before adding current XOR result)
                    // Use assign_advice_from_constant for the first row to use the constant column
                    if offset == 0 {
                        region.assign_advice_from_constant(
                            || "prev_acc_zero",
                            config.advice_cols[0],
                            offset,
                            F::ZERO,
                        )?;
                    } else {
                        region.assign_advice(
                            || "prev_acc",
                            config.advice_cols[0],
                            offset,
                            || Value::known(F::from(running_sum)),
                        )?;
                    }

                    // Assign the XOR result
                    region.assign_advice(
                        || "xor_result",
                        config.advice_cols[2],
                        offset,
                        || Value::known(F::from(*c)),
                    )?;

                    // Update running sum
                    running_sum += c;

                    // Assign the new accumulator value
                    let acc_cell = region.assign_advice(
                        || "acc",
                        config.acc_col,
                        offset,
                        || Value::known(F::from(running_sum)),
                    )?;
                    
                    final_acc_cell = Some(acc_cell);
                }
                
                Ok(final_acc_cell)
            },
        )?;

        // Constrain the final accumulator value to equal the public input
        if let Some(acc_cell) = final_acc {
            layouter.constrain_instance(acc_cell.cell(), config.instance, 0)?;
        }

        // Assign polynomial constraint witnesses (a * b = c)
        // This demonstrates PlonkUp's polynomial constraints without neighboring row references
        layouter.assign_region(
            || "poly_constraints",
            |mut region| {
                for (offset, (a, b, c)) in self.poly_inputs.iter().enumerate() {
                    // Enable the polynomial constraint selector
                    config.q_poly.enable(&mut region, offset)?;

                    // Assign the values for the polynomial constraint a * b = c
                    region.assign_advice(
                        || "poly_a",
                        config.advice_cols[0],
                        offset,
                        || Value::known(F::from(*a)),
                    )?;
                    region.assign_advice(
                        || "poly_b",
                        config.advice_cols[1],
                        offset,
                        || Value::known(F::from(*b)),
                    )?;
                    region.assign_advice(
                        || "poly_c",
                        config.advice_cols[2],
                        offset,
                        || Value::known(F::from(*c)),
                    )?;
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blstrs::Scalar;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::plonk::k_from_circuit;

    #[test]
    fn test_plonkup_circuit() {
        // Create XOR inputs that should satisfy the lookup constraint
        let xor_inputs = vec![
            (0, 0), // 0 XOR 0 = 0
            (1, 0), // 1 XOR 0 = 1
            (0, 1), // 0 XOR 1 = 1
            (1, 1), // 1 XOR 1 = 0
            (2, 3), // 2 XOR 3 = 1
            (3, 3), // 3 XOR 3 = 0
        ];

        // Create polynomial inputs (a * b = c)
        let poly_inputs = vec![
            (2, 3), // 2 * 3 = 6
            (4, 5), // 4 * 5 = 20
            (1, 1), // 1 * 1 = 1
        ];

        let circuit = PlonkUpCircuit::<Scalar>::new(xor_inputs, poly_inputs, 2);

        // Public input is the sum of XOR results
        let pi = vec![vec![circuit.public_input()]];

        let k: u32 = k_from_circuit(&circuit);
        let prover =
            MockProver::run(k, &circuit, pi).expect("Failed to run PlonkUp mock prover");

        prover.assert_satisfied();
    }

    #[test]
    fn test_plonkup_circuit_larger() {
        // Create XOR inputs with larger values (4-bit)
        let xor_inputs = vec![
            (5, 10),  // 5 XOR 10 = 15
            (15, 15), // 15 XOR 15 = 0
            (8, 7),   // 8 XOR 7 = 15
            (12, 3),  // 12 XOR 3 = 15
        ];

        // Create polynomial inputs (a * b = c)
        let poly_inputs = vec![
            (3, 7),  // 3 * 7 = 21
            (10, 2), // 10 * 2 = 20
        ];

        let circuit = PlonkUpCircuit::<Scalar>::new(xor_inputs, poly_inputs, 4);

        // Public input is the sum of XOR results
        let pi = vec![vec![circuit.public_input()]];

        let k: u32 = k_from_circuit(&circuit);
        let prover =
            MockProver::run(k, &circuit, pi).expect("Failed to run PlonkUp mock prover");

        prover.assert_satisfied();
    }
}
