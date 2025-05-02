use core::panic;
use std::fmt;

use p3_baby_bear::BabyBear;
use p3_field::AbstractField;

use crate::symbolic_var_f::SymbolicVarF;

/// Lean-friendly printing of symbolic f-variables
impl fmt::Display for SymbolicVarF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SymbolicVarF::PreprocessedLocal(idx) => write!(f, "PPL{}", idx),
            SymbolicVarF::MainLocal(idx) => write!(f, "ML{}", idx),
            SymbolicVarF::MainNext(idx) => write!(f, "MN{}", idx),
            SymbolicVarF::IsFirstRow => write!(f, "IsFirstRow"),
            SymbolicVarF::IsLastRow => write!(f, "IsLastRow"),
            SymbolicVarF::IsTransition => write!(f, "IsTransition"),
            SymbolicVarF::PublicValue(idx) => write!(f, "PV{}", idx),
            _ => panic!("SymbolicVarF: Unsupported SymbolicVarF variant: {}", self.variant()),
        }
    }
}

/// `FExpr` denotes the type of symbolic expressions over the BabyBear field
/// (symbolic f-expressions), which can be either: a constant; a variable; an addition;
/// a subtraction; or a multiplication.
#[derive(Clone, Eq, Hash, PartialEq)]
pub enum FExpr {
    FConst(BabyBear),
    FVar(SymbolicVarF),
    FAdd(Box<FExpr>, Box<FExpr>),
    FSub(Box<FExpr>, Box<FExpr>),
    FMul(Box<FExpr>, Box<FExpr>),
}

/// Lean-friendly Display printing of `FExpr`
impl fmt::Display for FExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FExpr::FConst(fc) => write!(f, "{}", fc),
            FExpr::FVar(fv) => write!(f, "{}", fv),
            FExpr::FAdd(fe1, fe2) => write!(f, "({} + {})", *fe1, *fe2),
            FExpr::FSub(fe1, fe2) => write!(f, "({} - {})", *fe1, *fe2),
            FExpr::FMul(fe1, fe2) => write!(f, "({} * {})", *fe1, *fe2),
        }
    }
}

/// Lean-friendly Debug printing of `FExpr`
impl fmt::Debug for FExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FExpr::FConst(fc) => write!(f, "{}", fc),
            FExpr::FVar(fv) => write!(f, "{}", fv),
            FExpr::FAdd(fe1, fe2) => write!(f, "({} + {})", *fe1, *fe2),
            FExpr::FSub(fe1, fe2) => write!(f, "({} - {})", *fe1, *fe2),
            FExpr::FMul(fe1, fe2) => write!(f, "({} * {})", *fe1, *fe2),
        }
    }
}

///
/// Wrappers
///

/// Addition
pub fn fexpr_add(fe1: FExpr, fe2: FExpr) -> FExpr {
    FExpr::FAdd(Box::new(fe1), Box::new(fe2))
}

/// Subtraction
pub fn fexpr_sub(fe1: FExpr, fe2: FExpr) -> FExpr {
    FExpr::FSub(Box::new(fe1), Box::new(fe2))
}

/// Multiplication
pub fn fexpr_mul(fe1: FExpr, fe2: FExpr) -> FExpr {
    FExpr::FMul(Box::new(fe1), Box::new(fe2))
}

///
/// Constants
///

/// Zero
pub fn fexpr_zero() -> FExpr {
    FExpr::FConst(BabyBear::zero())
}

/// One
pub fn fexpr_one() -> FExpr {
    FExpr::FConst(BabyBear::one())
}

/// Negative one
pub fn fexpr_neg_one() -> FExpr {
    FExpr::FConst(BabyBear::neg_one())
}
