use std::cell::RefCell;

use bus_mapping::state_db::EMPTY_CODE_HASH_LE;
use chiquito::{
    ast::{query::Queriable, Expr, ToExpr, ToField},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Circuit,
        Compiler, WitnessGenContext, FixedGenContext, TraceContext,
    },
    dsl::{circuit, StepTypeContext}, backend::halo2::{ChiquitoHalo2, chiquito2Halo2},
};

use eth_types::{Field, Word, ToLittleEndian};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::{bn256::Fr, FieldExt},
    plonk::{ConstraintSystem, Error, Expression, Column, Fixed},
};

use crate::{
    table::{BytecodeTable, KeccakTable},
    util::{Challenges, SubCircuit, SubCircuitConfig, get_push_size},
    witness, evm_circuit::util::rlc as util_rlc,
};

use super::{bytecode_unroller::{unroll, BytecodeRow, UnrolledBytecode}, wit_gen::BytecodeWitnessGen};

struct IsZero<F> {
    value_inv: Queriable<F>,
    is_zero_expression: Expr<F>,
}

impl<F: FieldExt> IsZero<F> {
    pub fn setup<V: Into<Expr<F>>, StepArgs>(
        ctx: &mut StepTypeContext<F, StepArgs>,
        value: V,
        value_inv: Queriable<F>,
    ) -> IsZero<F> {
        let value: Expr<F> = value.into();
        let is_zero_expression = 1.expr() - (value.clone() * value_inv);

        ctx.constr("isZero", value * is_zero_expression.clone());

        IsZero {
            value_inv,
            is_zero_expression,
        }
    }

    pub fn is_zero(&self) -> Expr<F> {
        self.is_zero_expression.clone()
    }
}

impl<F: Field> IsZero<F> {
    pub fn wg(&self, ctx: &mut dyn WitnessGenContext<F>, value: F) {
        ctx.assign(self.value_inv, value.invert().unwrap_or(F::zero()));
    }
}

type WitnessInput<F> = (Vec<UnrolledBytecode<F>>, Challenges<Value<F>>, usize);

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

        let mut push_data_table = chiquito2Halo2(Self::circuit_push_data_table(push_data_value, push_data_size));

        push_data_table.configure(meta);

        let mut circuit = chiquito2Halo2(Self::circuit(meta, &config, push_data_value, push_data_size));

        circuit.configure(meta);

        Self {
            compiled: circuit,
            push_data_table,
            keccak_table: config.keccak_table,
            minimum_rows: meta.minimum_rows(),
        }
    }
}

impl<F: Field> BytecodeCircuitConfig<F> {
    fn circuit(
        meta: &mut ConstraintSystem<F>,
        BytecodeCircuitConfigArgs {
            bytecode_table,
            keccak_table,
            challenges,
        }: &BytecodeCircuitConfigArgs<F>,
        push_data_table_value: Column<Fixed>, push_data_table_size: Column<Fixed>,
    ) -> Circuit<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>> {
        let mut bytecode_circuit = circuit::<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>, _>(
            "bytecode circuit",
            |ctx| {
                use chiquito::dsl::cb::*;

                let length = ctx.forward("length");                
                let push_data_left = ctx.forward("push_data_left");
                let value_rlc = ctx.forward_with_phase("value_rlc", 1); // 1 -> SecondPhase

                let index = ctx.import_halo2_advice("index", bytecode_table.index);
                let hash = ctx.import_halo2_advice("hash", bytecode_table.code_hash);
                let is_code = ctx.import_halo2_advice("is_code", bytecode_table.is_code);
                let value = ctx.import_halo2_advice("value", bytecode_table.value); 
                let tag = ctx.import_halo2_advice("tag", bytecode_table.tag);

                let push_data_table_value = ctx.import_halo2_fixed("push_data_value", push_data_table_value);
                let push_data_table_size = ctx.import_halo2_fixed("push_data_size", push_data_table_size);

                let keccak_is_enabled =
                    ctx.import_halo2_advice("keccak_is_enabled", keccak_table.is_enabled);
                let keccak_value_rlc =
                    ctx.import_halo2_advice("keccak_value_rlc", keccak_table.input_rlc);
                let keccak_length =
                    ctx.import_halo2_advice("keccak_length", keccak_table.input_len);
                let keccak_hash = ctx.import_halo2_advice("keccak_hash", keccak_table.output_rlc);

                let header = ctx.step_type("header");
                let byte_step = ctx.step_type("byte");

                ctx.pragma_first_step(header);
                ctx.pragma_last_step(header);

                ctx.step_type_def(header, move |ctx| {
                    ctx.constr("index == 0", eq(index, 0));
                    ctx.constr("value == length", eq(value, length));

                    ctx.transition_to("cur.length == 0", header, eq(length, 0));

                    let empty_hash = rlc(
                        &EMPTY_CODE_HASH_LE.map(|v| (v as u64).expr()),
                        challenges.evm_word(),
                    );

                    ctx.transition_to("cur.hash == EMPTY_HASH", header, eq(hash, empty_hash));

                    ctx.transition_to(
                        "next.length == cur.length",
                        byte_step,
                        eq(length, length.next()),
                    );
                    ctx.transition_to("next.index == 0", byte_step, eq(index.next(), 0));
                    ctx.transition_to("next.is_code == 1", byte_step, eq(is_code.next(), 1));
                    ctx.transition_to("next.hash == cur.hash", byte_step, eq(hash, hash.next()));
                    ctx.transition_to(
                        "next.value_rlc == next.value",
                        byte_step,
                        eq(value_rlc.next(), value.next()),
                    );

                    ctx.wg(move |ctx, wit| {
                        let wit = wit.borrow();

                        ctx.assign(tag, 0.field());
                        ctx.assign(index, 0.field());
                        ctx.assign(length, wit.length.field());
                        ctx.assign(value, wit.length.field());
                        ctx.assign(is_code, 0.field());
                        ctx.assign(value_rlc, 0.field());

                        wit.code_hash.map(|v| ctx.assign(hash, v));
                    })
                });

                ctx.step_type_def(byte_step, move |ctx| {
                    
                    let push_data_size = ctx.signal("push_data_size");
                    let push_data_left_inv = ctx.signal("push_data_left_inv");

                    let push_data_left_is_zero =
                        IsZero::setup(ctx, push_data_left, push_data_left_inv);

                    ctx.constr(
                        "is_code == push_data_left_is_zero.is_zero",
                        eq(is_code, push_data_left_is_zero.is_zero()),
                    );

                    ctx.lookup(
                        "lookup((value, push_data_size_table.value)(push_data_size, push_data_size_table.push_data_size))",
                        vec![(value.expr(), push_data_table_value.expr()), (push_data_size.expr(), push_data_table_size.expr())]);

                    ctx.transition_to(
                        "next.length == cur.length",
                        byte_step,
                        eq(length, length.next()),
                    );
                    ctx.transition_to(
                        "next.index == cur.index + 1",
                        byte_step,
                        eq(index + 1, index.next()),
                    );
                    ctx.transition_to("next.hash == cur.hash", byte_step, eq(hash, hash.next()));
                    ctx.transition_to(
                        "next.value_rlc == cur.value_rlc * randomness + next.value",
                        byte_step,
                        eq(value_rlc.next(), (value_rlc * challenges.keccak_input()) + value.next()),
                    );

                    ctx.transition_to(
                        "next.push_data_left == cur.is_code ? cur.push_data_size : cur.push_data_left - 1",
                        byte_step,
                        eq(
                            push_data_left.next(),
                            select(is_code, push_data_size, push_data_left - 1),
                        ),
                    );

                    ctx.transition_to("cur.index + 1 == cur.length", header, eq(index + 1, length));

                    ctx.lookup(
                        "if header.next() then keccak256_table_lookup(cur.value_rlc, cur.length, cur.hash)",
                        vec![
                            (header.next().expr(), keccak_is_enabled.expr()),
                            (header.next() * value_rlc, keccak_value_rlc.expr()),
                            (header.next() * length, keccak_length.expr()),
                            (header.next() * hash, keccak_hash.expr()),
                        ],
                    );

                    ctx.wg(move |ctx, wit| {
                        let wit = wit.borrow();

                        ctx.assign(tag, 1.field());
                        ctx.assign(index, wit.index());
                        ctx.assign(length, wit.length.field());
                        ctx.assign(value, wit.value());
                        ctx.assign(is_code, wit.is_code());

                        wit.value_rlc.map(|v| ctx.assign(value_rlc, v));
                        wit.code_hash.map(|v| ctx.assign(hash, v));

                        ctx.assign(push_data_size, wit.push_data_size.field());
                        ctx.assign(push_data_left, wit.push_data_left.field());
                        push_data_left_is_zero.wg(ctx, wit.push_data_left.field());
                    });
                });

                ctx.trace(move |ctx, (bytecodes, challenges, last_row_offset)| {
                    let mut offset = 0;
                    for bytecode in bytecodes.iter() {
                        let wit = RefCell::new(BytecodeWitnessGen::new(bytecode, &challenges));

                        println!("start wit gen");

                        if offset == last_row_offset - 1 {
                            break;
                        }
                        ctx.add(&header, wit.clone());
                        offset += 1;

                        while wit.borrow_mut().has_more() {
                            if offset == last_row_offset - 1 {
                                break;
                            }

                            wit.borrow_mut().next_row();
                            ctx.add(&byte_step, wit.clone());
                            offset += 1;
                            
                        }
                    }

                    // padding
                    let wit = RefCell::new(BytecodeWitnessGen::new(&unroll(vec![]), &challenges));

                    while offset < last_row_offset {
                        ctx.add(&header, wit.clone());
                        offset += 1;
                    }
                })
            },
        );

        let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

        let compiled = compiler.compile(&mut bytecode_circuit);

        // println!("{:#?}", bytecode_circuit);

        // println!("{:#?}", compiled);

        compiled
    }

    fn circuit_push_data_table(push_data_value: Column<Fixed>, push_data_size: Column<Fixed>) -> Circuit<F, (), ()> {
        let mut push_data_table_circuit = circuit::<F, (), (), _>("push_table", |ctx| {
            let push_data_value = ctx.import_halo2_fixed("push_data_value", push_data_value);
            let push_data_size = ctx.import_halo2_fixed("push_data_size", push_data_size);

            ctx.fixed_gen(move |ctx: &mut dyn FixedGenContext<F>| {
                for byte in 0usize..256 {
                    let push_size = get_push_size(byte as u8);
                    ctx.assign(byte, push_data_value, byte.field());
                    ctx.assign(byte, push_data_size, push_size.field());
                }
            });
        });

        let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

        let compiled = compiler.compile(&mut push_data_table_circuit);

        // println!("{:#?}", push_data_table_circuit);

        // println!("{:#?}", compiled);

        compiled
    }
}

#[derive(Default, Debug)]
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
        // config.load_aux_tables(layouter)?;
        // config.assign_internal(layouter, self.size, &self.bytecodes, challenges, false)

        // println!("{:?}", self.bytecodes.clone());

        config.push_data_table.synthesize(layouter, ());
        config.compiled.synthesize(layouter, (self.bytecodes.clone(), *challenges, self.size - config.minimum_rows + 1));

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
        util::{is_push, keccak}, table::BytecodeFieldTag,
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
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unroll(vec![7u8; 2usize.pow(k) - 8])], true);
    }

    #[test]
    fn bytecode_last_row_with_byte() {
        let k = 9;
        // Last row must be a padding row, so we have one row less for actual bytecode
        test_bytecode_circuit_unrolled::<Fr>(k, vec![unroll(vec![7u8; 2usize.pow(k) - 7])], false);
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
                unroll(vec![]), // 0
                unroll(vec![OpcodeId::PUSH32.as_u8()]), // 1
                unroll(vec![OpcodeId::PUSH32.as_u8(), OpcodeId::ADD.as_u8()]), // 3
                unroll(vec![OpcodeId::ADD.as_u8(), OpcodeId::PUSH32.as_u8()]), // 6
                unroll(vec![ // 9
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
