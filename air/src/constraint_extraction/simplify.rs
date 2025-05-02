//! This module applies simple arithmetic simplifications to symbolic f-expressions,
//! symbolic ef-expressions, and constraints. These simplifications are applied in order
//! to streamline their processing by the lookup-argument decoder and Lean.

use p3_baby_bear::BabyBear;
use p3_field::{extension::BinomialExtensionField, AbstractField};

use crate::symbolic_var_ef::SymbolicVarEF;

use super::{
    constraint::Constraint,
    efexpr::{efexpr_zero, EFExpr},
    fexpr::{fexpr_zero, FExpr},
};

/// The `simplify_fexpr` function takes as input:
/// - `fe`: a symbolic ef-expression
///
/// simplifies it, and returns the result of this simplification.
pub fn simplify_fexpr(fe: FExpr) -> FExpr {
    match fe {
        // Addition
        FExpr::FAdd(fe1, fe2) => {
            let sfe1 = simplify_fexpr(*fe1);
            let sfe2 = simplify_fexpr(*fe2);
            match (sfe1.clone(), sfe2.clone()) {
                // Direct computation of addition for two constants
                (FExpr::FConst(fc1), FExpr::FConst(fc2)) => FExpr::FConst(fc1 + fc2),
                // 0 + x = x
                (FExpr::FConst(fc1), _) if (fc1 == BabyBear::zero()) => sfe2,
                // x + 0 = x
                (_, FExpr::FConst(fc2)) if (fc2 == BabyBear::zero()) => sfe1,
                // Default
                (_, _) => FExpr::FAdd(Box::new(sfe1), Box::new(sfe2)),
            }
        }
        // Subtraction
        FExpr::FSub(fe1, fe2) => {
            let sfe1 = simplify_fexpr(*fe1);
            let sfe2 = simplify_fexpr(*fe2);
            match (sfe1.clone(), sfe2.clone()) {
                // Direct computation of subtraction for two constants
                (FExpr::FConst(fc1), FExpr::FConst(fc2)) => FExpr::FConst(fc1 - fc2),
                // x - 0 = x
                (_, FExpr::FConst(fc2)) if (fc2 == BabyBear::zero()) => sfe1,
                // x - x = 0
                (sfe1, sfe2) if sfe1 == sfe2 => fexpr_zero(),
                // Default
                (_, _) => FExpr::FSub(Box::new(sfe1), Box::new(sfe2)),
            }
        }
        // Multiplication
        FExpr::FMul(fe1, fe2) => {
            let sfe1 = simplify_fexpr(*fe1);
            let sfe2 = simplify_fexpr(*fe2);
            match (sfe1.clone(), sfe2.clone()) {
                // Direct computation of multiplication for two constants
                (FExpr::FConst(fc1), FExpr::FConst(fc2)) => FExpr::FConst(fc1 * fc2),
                // 0 * x = 0
                (FExpr::FConst(fc1), _) if (fc1 == BabyBear::zero()) => sfe1,
                // x * 0 = 0
                (_, FExpr::FConst(fc2)) if (fc2 == BabyBear::zero()) => sfe2,
                // 1 * x = x
                (FExpr::FConst(fc1), fe) if (fc1 == BabyBear::one()) => fe,
                // x * 1 = x
                (fe, FExpr::FConst(fc2)) if (fc2 == BabyBear::one()) => fe,
                // Default
                (_, _) => FExpr::FMul(Box::new(sfe1), Box::new(sfe2)),
            }
        }
        _ => fe,
    }
}

/// The `simplify_efexpr` function takes as input:
/// - `efe`: a symbolic ef-expression
///
/// simplifies it, and returns the result of this simplification.
pub fn simplify_efexpr(efe: EFExpr) -> EFExpr {
    match efe {
        // Addition
        EFExpr::EFAdd(efe1, efe2) => {
            let sefe1 = simplify_efexpr(*efe1);
            let sefe2 = simplify_efexpr(*efe2);
            match (sefe1.clone(), sefe2.clone()) {
                // Direct computation of addition for two constants
                (EFExpr::EFConst(efc1), EFExpr::EFConst(efc2)) => EFExpr::EFConst(efc1 + efc2),
                // x + 0 = x
                (EFExpr::EFConst(efc1), _) if (efc1 == BinomialExtensionField::zero()) => sefe2,
                // 0 + x = x
                (_, EFExpr::EFConst(efc2)) if (efc2 == BinomialExtensionField::zero()) => sefe1,
                // Default
                (_, _) => EFExpr::EFAdd(Box::new(sefe1), Box::new(sefe2)),
            }
        }
        // Subtraction
        EFExpr::EFSub(efe1, efe2) => {
            let sefe1 = simplify_efexpr(*efe1);
            let sefe2 = simplify_efexpr(*efe2);
            match (sefe1.clone(), sefe2.clone()) {
                // Direct computation of subtraction for two constants
                (EFExpr::EFConst(fc1), EFExpr::EFConst(fc2)) => EFExpr::EFConst(fc1 - fc2),
                // x - 0 = x
                (_, EFExpr::EFConst(fc2)) if (fc2 == BinomialExtensionField::zero()) => sefe1,
                // Default
                (_, _) => EFExpr::EFSub(Box::new(sefe1), Box::new(sefe2)),
            }
        }
        // Multiplication
        EFExpr::EFMul(efe1, efe2) => {
            let sefe1 = simplify_efexpr(*efe1);
            let sefe2 = simplify_efexpr(*efe2);
            match (sefe1.clone(), sefe2.clone()) {
                // Direct computation of multiplication for two constants
                (EFExpr::EFConst(efc1), EFExpr::EFConst(efc2)) => EFExpr::EFConst(efc1 * efc2),
                // 0 * x = 0
                (EFExpr::EFConst(efc1), _) if (efc1 == BinomialExtensionField::zero()) => sefe1,
                // x * 0 = 0
                (_, EFExpr::EFConst(efc2)) if (efc2 == BinomialExtensionField::zero()) => sefe2,
                // 1 * x = x
                (EFExpr::EFConst(efc1), efe) if (efc1 == BinomialExtensionField::one()) => efe,
                // x * 1 = x
                (efe, EFExpr::EFConst(efc2)) if (efc2 == BinomialExtensionField::one()) => efe,
                // x * x = x ^ 2 for permutation-challenge variables
                (
                    EFExpr::EFVar(SymbolicVarEF::PermutationChallenge(x)),
                    EFExpr::EFVar(SymbolicVarEF::PermutationChallenge(y)),
                ) if x == y => EFExpr::EFExp(
                    Box::new(EFExpr::EFVar(SymbolicVarEF::PermutationChallenge(x))),
                    BinomialExtensionField::from(BabyBear::two()),
                ),
                // x ^ n * x = x ^ (n + 1)
                (EFExpr::EFExp(sefe1, exp), sefe2) if *sefe1 == sefe2 => {
                    EFExpr::EFExp(sefe1, exp + BinomialExtensionField::one())
                }
                // Default
                (_, _) => EFExpr::EFMul(Box::new(sefe1), Box::new(sefe2)),
            }
        }
        // Conversion
        EFExpr::EFFromF(fe) => {
            let sfe = simplify_fexpr(fe);
            match sfe.clone() {
                // Lifting of constants from BabyBear to degree-four extension of BabyBear
                FExpr::FConst(fc) => EFExpr::EFConst(BinomialExtensionField::from(fc)),
                // Default
                _ => EFExpr::EFFromF(sfe),
            }
        }
        _ => efe,
    }
}

/// The `simplify_constraint` function takes as input:
/// - `c`: a constraint
///
/// simplifies it, and returns the result of this simplification.
pub fn simplify_constraint(constraint: Constraint) -> Option<Constraint> {
    match constraint {
        // x = x <=> true
        Constraint::Basic(fe) => {
            let sfe = simplify_fexpr(fe);
            match sfe.clone() {
                _ if sfe == fexpr_zero() => None,
                _ => Some(Constraint::Basic(sfe)),
            }
        }
        // x = x <=> true
        Constraint::Argument(efe) => {
            let sefe = simplify_efexpr(efe);
            match sefe.clone() {
                _ if sefe == efexpr_zero() => None,
                _ => Some(Constraint::Argument(sefe)),
            }
        }
    }
}
