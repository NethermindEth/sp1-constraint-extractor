use core::panic;
use std::fmt;

use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::AbstractField;

use crate::constraint_extraction::fexpr::FExpr;
use crate::symbolic_var_ef::SymbolicVarEF;

/// Lean-friendly printing of symbolic ef-variables
impl fmt::Display for SymbolicVarEF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SymbolicVarEF::PermutationLocal(idx) => write!(f, "PL{}", idx),
            SymbolicVarEF::PermutationNext(idx) => write!(f, "PN{}", idx),
            SymbolicVarEF::PermutationChallenge(idx) => write!(f, "PC{}", idx),
            SymbolicVarEF::CumulativeSum(idx) => write!(f, "CS{}", idx),
            _ => panic!("SymbolicVarF: Unsupported SymbolicVarEF variant: {}", self.variant()),
        }
    }
}

/// `FExpr` denotes the type of symbolic expressions over the degree-four extension of the
/// BabyBear field (symbolic ef-expressions), which can be either: a constant; a variable;
/// an addition; a subtraction; a multiplication; an exponentiation with a constant;
/// or a conversion from BabyBear.
#[derive(Clone, Eq, Hash, PartialEq)]
pub enum EFExpr {
    EFConst(BinomialExtensionField<BabyBear, 4>),
    EFVar(SymbolicVarEF),
    EFFromF(FExpr),
    EFAdd(Box<EFExpr>, Box<EFExpr>),
    EFSub(Box<EFExpr>, Box<EFExpr>),
    EFMul(Box<EFExpr>, Box<EFExpr>),
    EFExp(Box<EFExpr>, BinomialExtensionField<BabyBear, 4>),
}

/// Lean-friendly printing of symbolic ef-expressions
impl fmt::Display for EFExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EFExpr::EFConst(efc) => write!(f, "{}", efc),
            EFExpr::EFVar(efv) => write!(f, "{}", efv),
            EFExpr::EFFromF(efe) => write!(f, "fromF({})", *efe),
            EFExpr::EFAdd(efe1, efe2) => write!(f, "({} + {})", *efe1, *efe2),
            EFExpr::EFSub(efe1, efe2) => write!(f, "({} - {})", *efe1, *efe2),
            EFExpr::EFMul(efe1, efe2) => write!(f, "({} * {})", *efe1, *efe2),
            EFExpr::EFExp(efe1, efe2) => write!(f, "({} ^ {})", *efe1, efe2),
        }
    }
}

///
/// Wrappers
///

/// Addition
pub fn efexpr_add(efe1: EFExpr, efe2: EFExpr) -> EFExpr {
    EFExpr::EFAdd(Box::new(efe1), Box::new(efe2))
}

/// Subtraction
pub fn efexpr_sub(efe1: EFExpr, efe2: EFExpr) -> EFExpr {
    EFExpr::EFSub(Box::new(efe1), Box::new(efe2))
}

/// Multiplication
pub fn efexpr_mul(efe1: EFExpr, efe2: EFExpr) -> EFExpr {
    EFExpr::EFMul(Box::new(efe1), Box::new(efe2))
}

/// Conversion
pub fn efexpr_from_f(fe: FExpr) -> EFExpr {
    EFExpr::EFFromF(fe)
}

///
/// Constants
///

/// Zero
pub fn efexpr_zero() -> EFExpr {
    EFExpr::EFConst(BinomialExtensionField::zero())
}

/// One
pub fn efexpr_one() -> EFExpr {
    EFExpr::EFConst(BinomialExtensionField::one())
}

/// Negative one
pub fn efexpr_neg_one() -> EFExpr {
    EFExpr::EFConst(BinomialExtensionField::neg_one())
}
