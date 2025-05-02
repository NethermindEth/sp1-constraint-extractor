use core::panic;
use std::collections::HashMap;

use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;

use crate::{
    constraint_extraction::simplify::simplify_constraint, instruction::Instruction16,
    symbolic_var_ef::SymbolicVarEF, symbolic_var_f::SymbolicVarF,
};

use super::{
    constraint::Constraint,
    efexpr::{efexpr_add, efexpr_from_f, efexpr_mul, efexpr_neg_one, efexpr_sub, EFExpr},
    extracted_constraint::ExtractedConstraint,
    fexpr::{fexpr_add, fexpr_mul, fexpr_neg_one, fexpr_sub, FExpr},
    lookup::process_lookup_constraints,
    permutation::process_permutation_constraints,
};

///
/// Auxiliary functions
///

/// Symbolic f-variable from variant and data
fn fvar(variant: u8, data: u16) -> FExpr {
    FExpr::FVar(SymbolicVarF::from(variant, u32::from(data)))
}

/// Symbolic f-variable from first operand
fn fvar_from_b(instruction: &Instruction16) -> FExpr {
    fvar(instruction.b_variant, instruction.b)
}

/// Symbolic f-variable from second operand
fn fvar_from_c(instruction: &Instruction16) -> FExpr {
    fvar(instruction.c_variant, instruction.c)
}

/// Symbolic ef-variable from variant and data
fn efvar(variant: u8, data: u16) -> EFExpr {
    EFExpr::EFVar(SymbolicVarEF::from(variant, u32::from(data)))
}

/// Symbolic ef-variable from first operand
fn efvar_from_b(instruction: &Instruction16) -> EFExpr {
    efvar(instruction.b_variant, instruction.b)
}

/// Symbolic ef-variable from second operand
fn efvar_from_c(instruction: &Instruction16) -> EFExpr {
    efvar(instruction.c_variant, instruction.c)
}

/// The `eval_instruction` function takes as input:
/// - `f_constants`: a list of BabyBear constants;
/// - `ef_constants`: a list of constants from the degree-four extension of BabyBear;
/// - `f_store`: a map storing the contents of f-registers;
/// - `ef_store`: a map storing the contents of ef-registers; and
/// - `instruction`: the instruction to be evaluated;
///
/// evaluates `instruction`, updating the two register stores and returning an optional constraint.
/// This constraint is generated only when the instruction is an `FAssertZero` (opcode 59)
/// or an `EFAssertZero` (opcode 60) and is simplified before it is returned.
pub fn eval_instruction(
    f_constants: &[BabyBear],
    ef_constants: &[BinomialExtensionField<BabyBear, 4>],
    f_store: &mut HashMap<u16, FExpr>,
    ef_store: &mut HashMap<u16, EFExpr>,
    instruction: Instruction16,
) -> Option<Constraint> {
    let a = instruction.a;
    let b = instruction.b;
    let c = instruction.c;
    let f_const = |idx| FExpr::FConst(f_constants[usize::from(idx)]);
    let ef_const = |idx| EFExpr::EFConst(ef_constants[usize::from(idx)]);
    let f_reg = |idx| f_store[idx].clone();
    let ef_reg = |idx| ef_store[idx].clone();
    match instruction.opcode {
        // Empty
        0 => {}
        // FAssignC
        1 => {
            f_store.insert(a, f_const(b));
        }
        // FAssignV
        2 => {
            f_store.insert(a, fvar_from_b(&instruction));
        }
        // FAssignE
        3 => {
            f_store.insert(a, f_store[&b].clone());
        }
        // FAddVC
        4 => {
            f_store.insert(a, fexpr_add(fvar_from_b(&instruction), f_const(c)));
        }
        // FAddVV
        5 => {
            f_store.insert(a, fexpr_add(fvar_from_b(&instruction), fvar_from_c(&instruction)));
        }
        // FAddVE
        6 => {
            f_store.insert(a, fexpr_add(fvar_from_b(&instruction), f_reg(&c)));
        }
        // FAddEC
        7 => {
            f_store.insert(a, fexpr_add(f_reg(&b), f_const(c)));
        }
        // FAddEV
        8 => {
            f_store.insert(a, fexpr_add(f_reg(&b), fvar_from_c(&instruction)));
        }
        // FAddEE
        9 => {
            f_store.insert(a, fexpr_add(f_reg(&b), f_reg(&c)));
        }
        // FAddAssignE
        10 => {
            f_store.insert(a, fexpr_add(f_reg(&a), f_reg(&b)));
        }
        // FSubVC
        11 => {
            f_store.insert(a, fexpr_sub(fvar_from_b(&instruction), f_const(c)));
        }
        // FSubVV
        12 => {
            f_store.insert(a, fexpr_sub(fvar_from_b(&instruction), fvar_from_c(&instruction)));
        }
        // FSubVE
        13 => {
            f_store.insert(a, fexpr_sub(fvar_from_b(&instruction), f_reg(&c)));
        }
        // FSubEC
        14 => {
            f_store.insert(a, fexpr_sub(f_reg(&b), f_const(c)));
        }
        // FSubEV
        15 => {
            f_store.insert(a, fexpr_sub(f_reg(&b), fvar_from_c(&instruction)));
        }
        // FSubEE
        16 => {
            f_store.insert(a, fexpr_sub(f_reg(&b), f_reg(&c)));
        }
        // FSubAssignE
        17 => {
            f_store.insert(a, fexpr_sub(f_reg(&a), f_reg(&b)));
        }
        // FMulVC
        18 => {
            f_store.insert(a, fexpr_mul(fvar_from_b(&instruction), f_const(c)));
        }
        // FMulVV
        19 => {
            f_store.insert(a, fexpr_mul(fvar_from_b(&instruction), fvar_from_c(&instruction)));
        }
        // FMulVE
        20 => {
            f_store.insert(a, fexpr_mul(fvar_from_b(&instruction), f_reg(&c)));
        }
        // FMulEC
        21 => {
            f_store.insert(a, fexpr_mul(f_reg(&b), f_const(c)));
        }
        // FMulEV
        22 => {
            f_store.insert(a, fexpr_mul(f_reg(&b), fvar_from_c(&instruction)));
        }
        // FMulEE
        23 => {
            f_store.insert(a, fexpr_mul(f_reg(&b), f_reg(&c)));
        }
        // FMulAssignE
        24 => {
            f_store.insert(a, fexpr_mul(f_reg(&a), f_reg(&b)));
        }
        // FNegE
        25 => {
            f_store.insert(a, fexpr_mul(f_reg(&b), fexpr_neg_one()));
        }
        // EAssignC
        26 => {
            ef_store.insert(a, ef_const(b));
        }
        // EAssignV
        27 => {
            ef_store.insert(a, efvar_from_b(&instruction));
        }
        // EAssignE
        28 => {
            ef_store.insert(a, ef_store[&b].clone());
        }
        // EAddVC
        29 => {
            ef_store.insert(a, efexpr_add(efvar_from_b(&instruction), ef_const(c)));
        }
        // EAddVV
        30 => {
            ef_store.insert(a, efexpr_add(efvar_from_b(&instruction), efvar_from_c(&instruction)));
        }
        // EAddVE
        31 => {
            ef_store.insert(a, efexpr_add(efvar_from_b(&instruction), ef_reg(&c)));
        }
        // EAddEC
        32 => {
            ef_store.insert(a, efexpr_add(ef_reg(&b), ef_const(c)));
        }
        // EAddEV
        33 => {
            ef_store.insert(a, efexpr_add(ef_reg(&b), efvar_from_c(&instruction)));
        }
        // EAddEE
        34 => {
            ef_store.insert(a, efexpr_add(ef_reg(&b), ef_reg(&c)));
        }
        // EAddAssignE
        35 => {
            ef_store.insert(a, efexpr_add(ef_reg(&a), ef_reg(&b)));
        }
        // ESubVC
        36 => {
            ef_store.insert(a, efexpr_sub(efvar_from_b(&instruction), ef_const(c)));
        }
        // ESubVV
        37 => {
            ef_store.insert(a, efexpr_sub(efvar_from_b(&instruction), efvar_from_c(&instruction)));
        }
        // ESubVE
        38 => {
            ef_store.insert(a, efexpr_sub(efvar_from_b(&instruction), ef_reg(&c)));
        }
        // ESubEC
        39 => {
            ef_store.insert(a, efexpr_sub(ef_reg(&b), ef_const(c)));
        }
        // ESubEV
        40 => {
            ef_store.insert(a, efexpr_sub(ef_reg(&b), efvar_from_c(&instruction)));
        }
        // ESubEE
        41 => {
            ef_store.insert(a, efexpr_sub(ef_reg(&b), ef_reg(&c)));
        }
        // ESubAssignE
        42 => {
            ef_store.insert(a, efexpr_sub(ef_reg(&a), ef_reg(&b)));
        }
        // EMulVC
        43 => {
            ef_store.insert(a, efexpr_mul(efvar_from_b(&instruction), ef_const(c)));
        }
        // EMulVV
        44 => {
            ef_store.insert(a, efexpr_mul(efvar_from_b(&instruction), efvar_from_c(&instruction)));
        }
        // EMulVE
        45 => {
            ef_store.insert(a, efexpr_mul(efvar_from_b(&instruction), ef_reg(&c)));
        }
        // EMulEC
        46 => {
            ef_store.insert(a, efexpr_mul(ef_reg(&b), ef_const(c)));
        }
        // EMulEV
        47 => {
            ef_store.insert(a, efexpr_mul(ef_reg(&b), efvar_from_c(&instruction)));
        }
        // EMulEE
        48 => {
            ef_store.insert(a, efexpr_mul(ef_reg(&b), ef_reg(&c)));
        }
        // EMulAssignE
        49 => {
            ef_store.insert(a, efexpr_mul(ef_reg(&a), ef_reg(&b)));
        }
        // ENegE
        50 => {
            ef_store.insert(a, efexpr_mul(ef_reg(&b), efexpr_neg_one()));
        }
        // EFFromE
        51 => {
            ef_store.insert(a, efexpr_from_f(f_reg(&b)));
        }
        // EFAddEE
        52 => {
            ef_store.insert(a, efexpr_add(ef_reg(&b), efexpr_from_f(f_reg(&c))));
        }
        // EFAddAssignE
        53 => {
            ef_store.insert(a, efexpr_add(ef_reg(&a), efexpr_from_f(f_reg(&c))));
        }
        // EFSubEE
        54 => {
            ef_store.insert(a, efexpr_sub(ef_reg(&b), efexpr_from_f(f_reg(&c))));
        }
        // EFSubAssignE
        55 => {
            ef_store.insert(a, efexpr_sub(ef_reg(&a), efexpr_from_f(f_reg(&c))));
        }
        // EFMulEE
        56 => {
            ef_store.insert(a, efexpr_mul(ef_reg(&b), efexpr_from_f(f_reg(&c))));
        }
        // EFMulAssignE
        57 => {
            ef_store.insert(a, efexpr_mul(ef_reg(&a), efexpr_from_f(f_reg(&c))));
        }
        // Unimplemented: EFAsBaseSlice
        58 => {
            panic!("Unsupported instruction: EFAsBaseSlice")
        }
        // FAssertZero
        59 => {
            return simplify_constraint(Constraint::Basic(f_store[&a].clone()));
        }
        // EFAssertZero
        60 => {
            return simplify_constraint(Constraint::Argument(ef_store[&a].clone()));
        }
        opcode => panic!("Unsupported opcode: {}", opcode),
    };
    None
}

/// The `eval_code` function takes as input:
/// - `f_constants`: a list of BabyBear constants;
/// - `ef_constants`: a list of constants from the degree-four extension of BabyBear; and
/// - `instructions`: a sequence of instructions
///
/// evaluates `instructions` one-by-one starting from an empty f-store/ef-store,  given
/// `f_constants` and `ef_constants`, and returns a sequence of corresponding extracted constraints.
pub fn eval_code(
    f_constants: Vec<BabyBear>,
    ef_constants: Vec<BinomialExtensionField<BabyBear, 4>>,
    instructions: Vec<Instruction16>,
) -> Vec<ExtractedConstraint> {
    let mut f_store: HashMap<u16, FExpr> = HashMap::new();
    let mut ef_store: HashMap<u16, EFExpr> = HashMap::new();
    let mut constraints: Vec<Constraint> = Vec::new();
    let mut extracted_info: Vec<ExtractedConstraint> = Vec::new();

    // Evaluate instructions to obtain constraints
    for instruction in instructions.iter() {
        if let Some(constraint) =
            eval_instruction(&f_constants, &ef_constants, &mut f_store, &mut ef_store, *instruction)
        {
            constraints.push(constraint)
        }
    }

    // Process lookup and permutation constraints
    process_lookup_constraints(&mut constraints, &mut extracted_info);
    process_permutation_constraints(&mut constraints, &mut extracted_info);
    // The remaining constraints must be basic constraints
    for constraint in constraints {
        if let Constraint::Basic(constraint) = constraint {
            extracted_info.push(ExtractedConstraint::Basic(constraint));
        } else {
            panic!("Unprocessed argument-related constraint: {}", constraint)
        }
    }

    extracted_info
}
