use std::cell::RefCell;

use bus_mapping::state_db::EMPTY_CODE_HASH_LE;
use chiquito::{
    ast::{query::Queriable, Expr, ToExpr, ToField},
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Circuit,
        Compiler, FixedGenContext, WitnessGenContext,
    },
    dsl::{circuit, StepTypeContext},
};

use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::{bn256::Fr, FieldExt},
    plonk::{Column, ConstraintSystem, Error, Expression, Fixed},
};

use crate::{
    bytecode_circuit::bytecode_chiquito::bytecode_circuit,
    table::{BytecodeTable, KeccakTable},
    util::{get_push_size, Challenges, SubCircuit, SubCircuitConfig},
    witness,
};

use super::{
    bytecode_chiquito,
    bytecode_unroller::{unroll, BytecodeRow, UnrolledBytecode},
    push_data_chiquito::{self, push_data_table_circuit},
    wit_gen::BytecodeWitnessGen,
};

/// WitnessInput
pub type WitnessInput<F> = (Vec<UnrolledBytecode<F>>, Challenges<Value<F>>, usize);

/// BytecodeCircuitConfig
#[derive(Clone, Debug)]
pub struct BytecodeCircuitConfig<F: Field> {
    compiled: ChiquitoHalo2<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>>,
    push_data_table: ChiquitoHalo2<F, (), ()>,
    keccak_table: KeccakTable,

    minimum_rows: usize,
}

/// Circuit configuration arguments
pub struct BytecodeCircuitConfigArgs<F: Field> {
    /// BytecodeTable
    pub bytecode_table: BytecodeTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for BytecodeCircuitConfig<F> {
    type ConfigArgs = BytecodeCircuitConfigArgs<F>;

    /// Return a new BytecodeCircuitConfig
    fn new(meta: &mut ConstraintSystem<F>, config: Self::ConfigArgs) -> Self {
        let push_data_value = meta.fixed_column();
        let push_data_size = meta.fixed_column();

        let mut push_data_table =
            chiquito2Halo2(push_data_table_circuit(push_data_value, push_data_size));

        push_data_table.configure(meta);

        let mut circuit = chiquito2Halo2(bytecode_circuit(
            meta,
            &config,
            push_data_value,
            push_data_size,
        ));

        circuit.configure(meta);

        Self {
            compiled: circuit,
            push_data_table,
            keccak_table: config.keccak_table,
            minimum_rows: meta.minimum_rows(),
        }
    }
}

#[derive(Default, Debug, Clone)]
/// BytecodeCircuit
pub struct BytecodeCircuit<F: Field> {
    /// Unrolled bytecodes
    pub bytecodes: Vec<UnrolledBytecode<F>>,
    /// Circuit size
    pub size: usize,
}

impl<F: Field> BytecodeCircuit<F> {
    /// new BytecodeCircuitTester
    pub fn new(bytecodes: Vec<UnrolledBytecode<F>>, size: usize) -> Self {
        BytecodeCircuit { bytecodes, size }
    }

    /// Creates bytecode circuit from block and bytecode_size.
    pub fn new_from_block_sized(block: &witness::Block<F>, bytecode_size: usize) -> Self {
        let bytecodes: Vec<UnrolledBytecode<F>> = block
            .bytecodes
            .iter()
            .map(|(_, b)| unroll(b.bytes.clone()))
            .collect();
        Self::new(bytecodes, bytecode_size)
    }
}

impl<F: Field> SubCircuit<F> for BytecodeCircuit<F> {
    type Config = BytecodeCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        // TODO: Find a nicer way to add the extra `128`.  Is this to account for
        // unusable rows? Then it could be calculated like this:
        // fn unusable_rows<F: Field, C: Circuit<F>>() -> usize {
        //     let mut cs = ConstraintSystem::default();
        //     C::configure(&mut cs);
        //     cs.blinding_factors()
        // }
        let bytecode_size = block.circuits_params.max_bytecode + 128;
        Self::new_from_block_sized(block, bytecode_size)
    }

    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.push_data_table.synthesize(layouter, ());
        config.compiled.synthesize(
            layouter,
            (
                self.bytecodes.clone(),
                *challenges,
                self.size - (config.minimum_rows + 1),
            ),
        );

        Ok(())
    }

    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        (
            block
                .bytecodes
                .values()
                .map(|bytecode| bytecode.bytes.len() + 1)
                .sum(),
            block.circuits_params.max_bytecode,
        )
    }
}

#[cfg(any(feature = "test", test, feature = "test-circuits"))]
impl<F: Field> halo2_proofs::plonk::Circuit<F> for BytecodeCircuit<F> {
    type Config = (BytecodeCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let bytecode_table = BytecodeTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);

        let config = {
            let challenges = challenges.exprs(meta);
            BytecodeCircuitConfig::new(
                meta,
                BytecodeCircuitConfigArgs {
                    bytecode_table,
                    keccak_table,
                    challenges,
                },
            )
        };

        (config, challenges)
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&mut layouter);

        config.keccak_table.dev_load(
            &mut layouter,
            self.bytecodes.iter().map(|b| &b.bytes),
            &challenges,
        )?;
        self.synthesize_sub(&config, &challenges, &mut layouter)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        bytecode_circuit::{bytecode_unroller::BytecodeRow, dev::test_bytecode_circuit_unrolled},
        table::BytecodeFieldTag,
        util::{is_push, keccak},
    };
    use bus_mapping::evm::OpcodeId;
    use eth_types::{Bytecode, Word};
    use halo2_proofs::halo2curves::bn256::Fr;
    use log::trace;

    /// Verify unrolling code
    #[test]
    fn bytecode_unrolling() {
        let k = 10;
        let mut rows = vec![];
        let mut bytecode = Bytecode::default();
        // First add all non-push bytes, which should all be seen as code
        for byte in 0u8..=255u8 {
            if !is_push(byte) {
                bytecode.write(byte, true);
                rows.push(BytecodeRow {
                    code_hash: Word::zero(),
                    tag: Fr::from(BytecodeFieldTag::Byte as u64),
                    index: Fr::from(rows.len() as u64),
                    is_code: Fr::from(true as u64),
                    value: Fr::from(byte as u64),
                });
            }
        }
        // Now add the different push ops
        for n in 1..=32 {
            let data_byte = OpcodeId::PUSH32.as_u8();
            bytecode.push(
                n,
                Word::from_little_endian(&vec![data_byte; n as usize][..]),
            );
            rows.push(BytecodeRow {
                code_hash: Word::zero(),
                tag: Fr::from(BytecodeFieldTag::Byte as u64),
                index: Fr::from(rows.len() as u64),
                is_code: Fr::from(true as u64),
                value: Fr::from(OpcodeId::PUSH1.as_u64() + ((n - 1) as u64)),
            });
            for _ in 0..n {
                rows.push(BytecodeRow {
                    code_hash: Word::zero(),
                    tag: Fr::from(BytecodeFieldTag::Byte as u64),
                    index: Fr::from(rows.len() as u64),
                    is_code: Fr::from(false as u64),
                    value: Fr::from(data_byte as u64),
                });
            }
        }
        // Set the code_hash of the complete bytecode in the rows
        let code_hash = keccak(&bytecode.to_vec()[..]);
        for row in rows.iter_mut() {
            row.code_hash = code_hash;
        }
        rows.insert(
            0,
            BytecodeRow {
                code_hash,
                tag: Fr::from(BytecodeFieldTag::Header as u64),
                index: Fr::zero(),
                is_code: Fr::zero(),
                value: Fr::from(bytecode.to_vec().len() as u64),
            },
        );
        // Unroll the bytecode
        let unrolled = unroll(bytecode.to_vec());
        // Check if the bytecode was unrolled correctly
        assert_eq!(
            UnrolledBytecode {
                bytes: bytecode.to_vec(),
                rows,
            },
            unrolled,
        );
        // Verify the unrolling in the circuit
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unrolled], true);
    }

    /// Tests a fully empty circuit
    #[test]
    fn bytecode_empty() {
        let k = 9;
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unroll(vec![])], true);
    }

    #[test]
    fn bytecode_simple() {
        let k = 9;
        let bytecodes = vec![unroll(vec![7u8]), unroll(vec![6u8]), unroll(vec![5u8])];
        test_bytecode_circuit_unrolled::<Fr>(k, bytecodes, true);
    }

    /// Tests a fully full circuit
    #[test]
    fn bytecode_full() {
        let k = 9;
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unroll(vec![7u8; 2usize.pow(k) - 11])], true);
    }

    #[test]
    fn bytecode_last_row_with_byte() {
        let k = 9;
        // Last row must be a padding row, so we have one row less for actual bytecode
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unroll(vec![7u8; 2usize.pow(k) - 10])], false);
    }

    /// Tests a circuit with incomplete bytecode
    #[test]
    fn bytecode_incomplete() {
        let k = 9;
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unroll(vec![7u8; 2usize.pow(k) + 1])], false);
    }

    /// Tests multiple bytecodes in a single circuit
    #[test]
    fn bytecode_push() {
        let k = 9;
        test_bytecode_circuit_unrolled::<Fr>(
            k,
            vec![
                unroll(vec![]),                                                // 0
                unroll(vec![OpcodeId::PUSH32.as_u8()]),                        // 1
                unroll(vec![OpcodeId::PUSH32.as_u8(), OpcodeId::ADD.as_u8()]), // 3
                unroll(vec![OpcodeId::ADD.as_u8(), OpcodeId::PUSH32.as_u8()]), // 6
                unroll(vec![
                    // 9
                    OpcodeId::ADD.as_u8(),
                    OpcodeId::PUSH32.as_u8(),
                    OpcodeId::ADD.as_u8(),
                ]),
            ],
            true,
        );
    }

    /// Test invalid code_hash data
    #[test]
    fn bytecode_invalid_hash_data() {
        let k = 9;
        let bytecode = vec![8u8, 2, 3, 8, 9, 7, 128];
        let unrolled = unroll(bytecode);
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unrolled.clone()], true);
        // Change the code_hash on the first position (header row)
        {
            let mut invalid = unrolled;
            invalid.rows[0].code_hash += Word::one();
            trace!("bytecode_invalid_hash_data: Change the code_hash on the first position");
            test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
        }
        // TODO: other rows code_hash are ignored by the witness generation, to
        // test other rows invalid code_hash, we would need to inject an evil
        // witness.
    }

    /// Test invalid index
    #[test]
    #[ignore]
    fn bytecode_invalid_index() {
        let k = 9;
        let bytecode = vec![8u8, 2, 3, 8, 9, 7, 128];
        let unrolled = unroll(bytecode);
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unrolled.clone()], true);
        // Start the index at 1
        {
            let mut invalid = unrolled.clone();
            for row in invalid.rows.iter_mut() {
                row.index += Fr::one();
            }
            test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
        }
        // Don't increment an index once
        {
            let mut invalid = unrolled;
            invalid.rows.last_mut().unwrap().index -= Fr::one();
            test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
        }
    }

    /// Test invalid byte data
    #[test]
    fn bytecode_invalid_byte_data() {
        let k = 9;
        let bytecode = vec![8u8, 2, 3, 8, 9, 7, 128];
        let unrolled = unroll(bytecode);
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unrolled.clone()], true);
        // Change the first byte
        {
            let mut invalid = unrolled.clone();
            invalid.rows[1].value = Fr::from(9u64);
            test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
        }
        // Change a byte on another position
        {
            let mut invalid = unrolled.clone();
            invalid.rows[5].value = Fr::from(6u64);
            test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
        }
        // Set a byte value out of range
        {
            let mut invalid = unrolled;
            invalid.rows[3].value = Fr::from(256u64);
            test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
        }
    }

    /// Test invalid is_code data
    #[test]
    fn bytecode_invalid_is_code() {
        let k = 9;
        let bytecode = vec![
            OpcodeId::ADD.as_u8(),
            OpcodeId::PUSH1.as_u8(),
            OpcodeId::PUSH1.as_u8(),
            OpcodeId::SUB.as_u8(),
            OpcodeId::PUSH7.as_u8(),
            OpcodeId::ADD.as_u8(),
            OpcodeId::PUSH6.as_u8(),
        ];
        let unrolled = unroll(bytecode);
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unrolled.clone()], true);
        // Mark the 3rd byte as code (is push data from the first PUSH1)
        {
            let mut invalid = unrolled.clone();
            invalid.rows[3].is_code = Fr::one();
            test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
        }
        // Mark the 4rd byte as data (is code)
        {
            let mut invalid = unrolled.clone();
            invalid.rows[4].is_code = Fr::zero();
            test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
        }
        // Mark the 7th byte as code (is data for the PUSH7)
        {
            let mut invalid = unrolled;
            invalid.rows[7].is_code = Fr::one();
            test_bytecode_circuit_unrolled::<Fr>(k, vec![invalid], false);
        }
    }
}
