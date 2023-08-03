use halo2_proofs::{
    circuit::{Layouter, Value},
    halo2curves::{bn256::Fr as Fp, ff::PrimeField},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};

use crate::utils::{big_uint_to_8bit_chunks, running_sums_of_chunks};

/// This helper checks that the value witnessed in a given cell is within a given range defined by N_BYTES.
///
/// |     | value       | decomposed_value    | running_sum    | toggle_running_sum_check | toggle_lookup_check |
/// |-----|-------------|------               |------          | ------                   | ------              |
/// |  0  |  -          | -                   | 0x00           | 0                        | 0                   |
/// |  1  | 0x1f2f3f4f  | 0x1f                | 0x1f           | 1                        | 1                   |
/// |  2  |             | 0x2f                | 0x1f2f         | 1                        | 1                   |
/// |  3  |             | 0x3f                | 0x1f2f3f       | 1                        | 1                   |
/// |  4  |             | 0x4f                | 0x1f2f3f4f     | 1                        | 1                   |
///
/// The column decomposed_value contains the decomposed value of `value` in #N_BYTES byte chunks, big-endian.
/// The column running_sum contains the running sum of the values in decomposed_value. In particular the running_sum in a particular row is the result of concatenating the prev running_sum with the current decomposed_value.
/// The contraints that are enforced are:
/// - (running_sum(prev) << 8) + decomposed_value(cur) = running_sum(cur) (enable by toggle_running_sum_check)
/// - decomposed_value(cur) ∈ u8_lookup_table (enable by toggle_lookup_check)
/// - value(1) == running_sum(4) (copy constraint applied here)
#[derive(Debug, Clone)]
struct RangeCheckConfig<const N_BYTES: usize> {
    value: Column<Advice>,
    decomposed_value: Column<Advice>,
    running_sum: Column<Advice>,
    range: Column<Fixed>,
    toggle_running_sum_check: Selector,
    toggle_lookup_check: Selector,
}

impl<const N_BYTES: usize> RangeCheckConfig<N_BYTES> {
    pub fn configure(
        meta: &mut ConstraintSystem<Fp>,
        value: Column<Advice>,
        decomposed_value: Column<Advice>,
        running_sum: Column<Advice>,
        range: Column<Fixed>,
        toggle_running_sum_check: Selector,
        toggle_lookup_check: Selector,
    ) -> Self {
        meta.create_gate(
            "equality check between running_sum_cur and running_sum_prev << 8 + running_sum_cur",
            |meta| {
                let running_sum_prev = meta.query_advice(running_sum, Rotation::prev());
                let decomposed_value_cur = meta.query_advice(decomposed_value, Rotation::cur());
                let running_sum_cur = meta.query_advice(running_sum, Rotation::cur());
                let s = meta.query_selector(toggle_running_sum_check);
                vec![
                    s * (running_sum_prev * Expression::Constant(Fp::from(1 << 8))
                        + decomposed_value_cur
                        - running_sum_cur),
                ]
            },
        );

        meta.annotate_lookup_any_column(range, || "LOOKUP_MAXBITS_RANGE");

        meta.lookup_any("range u8 check for decomposed value", |meta| {
            let decomposed_value_cell = meta.query_advice(decomposed_value, Rotation::cur());
            let range = meta.query_fixed(range, Rotation::cur());

            let enable_lookup = meta.query_selector(toggle_lookup_check);
            vec![(enable_lookup * decomposed_value_cell, range)]
        });

        Self {
            value,
            decomposed_value,
            running_sum,
            range,
            toggle_running_sum_check,
            toggle_lookup_check,
        }
    }

    /// Performs the following assignements
    /// - Assign an empty cell to running_sum(0)
    /// - Assign value to be performed range check on to value(1)
    /// - Assign the decomposition in #N_BYTES assign decomposed_value to decomposed_value(1..N_BYTES)
    /// - Assign the runnings sums to running_sum(1..N_BYTES - 1)
    /// - Copy value(1) to running_sum(N_BYTES) enforcing a copy constraint
    pub fn assign(&self, mut layouter: impl Layouter<Fp>, value: Fp) -> Result<(), Error> {
        layouter.assign_region(
            || "assign values to range check",
            |mut region| {
                // enable the selectors in offset [1, N_BYTES]
                for i in 1..=N_BYTES {
                    self.toggle_running_sum_check.enable(&mut region, i)?;
                    self.toggle_lookup_check.enable(&mut region, i)?;
                }

                // assign an empty cell to running_sum column at offset 0
                region.assign_advice(
                    || "inital running sum starts at 0",
                    self.running_sum,
                    0,
                    || Value::known(Fp::zero()),
                )?;

                // assign value to value at offset 1
                let value_cell =
                    region.assign_advice(|| "value", self.value, 1, || Value::known(value))?;

                // decompose value into #N_BYTES 8-bit chunks
                let chunks = big_uint_to_8bit_chunks(value, N_BYTES);
                let running_sums = running_sums_of_chunks(chunks.clone());

                // assign decomposed_value to decomposed_value column at offset [1, N_BYTES]
                // assign running sum to running_sum column at offset [1, N_BYTES]
                for i in 1..=N_BYTES {
                    region.assign_advice(
                        || "assign decomposed value",
                        self.decomposed_value,
                        i,
                        || Value::known(Fp::from(chunks[i - 1] as u64)),
                    )?;

                    if i == N_BYTES {
                        value_cell.copy_advice(
                            || "value cell should match last running sum",
                            &mut region,
                            self.running_sum,
                            i,
                        )?;
                    } else {
                        region.assign_advice(
                            || "assign running sum",
                            self.running_sum,
                            i,
                            || {
                                Value::known(
                                    Fp::from_str_vartime(&running_sums[i - 1].to_str_radix(10)[..])
                                        .unwrap(),
                                )
                            },
                        )?;
                    }
                }
                Ok(())
            },
        )
    }

    /// Loads the lookup table with values from `0` to `2^8 - 1`
    pub fn load(&self, mut layouter: impl Layouter<Fp>) -> Result<(), Error> {
        let range = 1 << (8);

        layouter.assign_region(
            || format!("load range check table of {} bits", 8),
            |mut region| {
                for i in 0..range {
                    region.assign_fixed(
                        || "assign cell in fixed column",
                        self.range,
                        i,
                        || Value::known(Fp::from(i as u64)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::floor_planner::V1,
        dev::{FailureLocation, MockProver, VerifyFailure},
        halo2curves::bn256::Fr as Fp,
        plonk::{Any, Circuit},
    };

    const N_BYTES: usize = 4;

    use super::*;

    #[derive(Default)]
    struct RangeCheckCircuit<const N_BYTES: usize> {
        value: Fp,
    }

    impl<const N_BYTES: usize> Circuit<Fp> for RangeCheckCircuit<N_BYTES> {
        type Config = RangeCheckConfig<N_BYTES>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            let value = meta.advice_column();
            let decomposed_value = meta.advice_column();
            let running_sum = meta.advice_column();
            let range = meta.fixed_column();
            let toggle_running_sum_check = meta.selector();
            let toggle_lookup_check = meta.complex_selector();

            meta.enable_equality(value);
            meta.enable_equality(running_sum);

            RangeCheckConfig::configure(
                meta,
                value,
                decomposed_value,
                running_sum,
                range,
                toggle_running_sum_check,
                toggle_lookup_check,
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            config.load(layouter.namespace(|| "load range check table"))?;

            config.assign(
                layouter.namespace(|| "assign value to perform range check"),
                self.value,
            )?;

            Ok(())
        }
    }

    // range check for 32-bit value in 4 bytes should succeed
    #[test]
    fn test_range_check() {
        let k = 9;

        let circuit = RangeCheckCircuit::<N_BYTES> {
            value: Fp::from(0x1f2f3f4f),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    // range check for 32-bit value in 6 bytes should succeed
    /// |     | value               | decomposed_value    | running_sum              | toggle_running_sum_check | toggle_lookup_check |
    /// |-----|-------------        |------               |------                    | ------                   | ------              |
    /// |  0  |  -                  | -                   | 0x00                     | 0                        | 0                   |
    /// |  1  | 0x1f2f3f4f          | 0x00                | 0x00                     | 1                        | 1                   |
    /// |  2  |                     | 0x00                | 0x00                     | 1                        | 1                   |
    /// |  3  |                     | 0x1f                | 0x1f                     | 1                        | 1                   |
    /// |  4  |                     | 0x2f                | 01f2f                    | 1                        | 1                   |
    /// |  5  |                     | 0x3f                | 0x1f2f3f                 | 1                        | 1                   |
    /// |  6  |                     | 0x4f                | 0x1f2f3f4f               | 1                        | 1                   |
    #[test]
    fn test_range_check_2() {
        let k = 9;

        let circuit = RangeCheckCircuit::<6> {
            value: Fp::from(0x1f2f3f4f),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    // range check for 64-bit value in 4 bytes should fail.
    /// |     | value               | decomposed_value    | running_sum              | toggle_running_sum_check | toggle_lookup_check |
    /// |-----|-------------        |------               |------                    | ------                   | ------              |
    /// |  0  |  -                  | -                   | 0x00                     | 0                        | 0                   |
    /// |  1  | 0x1f2f3f4f5f6f7f8f  | 0x1f                | 0x1f                     | 1                        | 1                   |
    /// |  2  |                     | 0x2f                | 0x1f2f                   | 1                        | 1                   |
    /// |  3  |                     | 0x3f                | 0x1f2f3f                 | 1                        | 1                   |
    /// |  4  |                     | 0x4f                | 0x1f2f3f4f5f6f7f8f       | 1                        | 1                   |
    ///
    /// The constraint => (running_sum(prev) << 8) + decomposed_value(cur) = running_sum(cur) should fail at offset 4
    #[test]
    fn test_overflow() {
        let k = 9;

        let circuit = RangeCheckCircuit::<N_BYTES> {
            value: Fp::from(0x1f2f3f4f5f6f7f8f_u64),
        };

        let invalid_prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert_eq!(
            invalid_prover.verify(),
            Err(vec![VerifyFailure::ConstraintNotSatisfied {
                constraint: (
                    (0, "equality check between running_sum_cur and running_sum_prev << 8 + running_sum_cur").into(),
                    0,
                    ""
                )
                    .into(),
                location: FailureLocation::InRegion {
                    region: (1, "assign values to range check").into(),
                    offset: 4
                },
                cell_values: vec![
                    (((Any::advice(), 1).into(), 0).into(), "0x4f".to_string()),
                    (((Any::advice(), 2).into(), -1).into(), "0x1f2f3f".to_string()),
                    (((Any::advice(), 2).into(), 0).into(), "0x1f2f3f4f5f6f7f8f".to_string()),
                ]
            }])
        );
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn print_range_check() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("range-check-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Range Check Layout", ("sans-serif", 60))
            .unwrap();

        let circuit = RangeCheckCircuit::<N_BYTES> {
            value: Fp::from(0x1f2f3f4f),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(9, &circuit, &root)
            .unwrap();
    }
}
