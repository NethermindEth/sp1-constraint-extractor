use std::fmt;

use crate::{
    constraint_extraction::fexpr::FExpr, symbolic_var_ef::SymbolicVarEF,
    symbolic_var_f::SymbolicVarF,
};

use super::{constraint::Constraint, efexpr::EFExpr, extracted_constraint::ExtractedConstraint};

/// `PermutationConstraint` denotes the type of permutation constraints, which can be either:
/// a constraint on the first, transition, or last row of the permutation argument
pub enum PermutationConstraint {
    FirstRow(u32),
    TransitionRow(u32),
    LastRow(u32),
}

/// Lean-friendly printing of permutation constraints
impl fmt::Display for PermutationConstraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermutationConstraint::FirstRow(n) => write!(f, "FirstRow({})", n),
            PermutationConstraint::TransitionRow(n) => write!(f, "TransitionRow({})", n),
            PermutationConstraint::LastRow(n) => write!(f, "LastRow({})", n),
        }
    }
}

/// The `is_sum` function takes as input:
/// - `efe`, a symbolic ef-expression
/// - `pl`, a boolean indicator of whether the sum is on PL- or PN-variables
/// - `n`, the bound of the sum
///
/// and returns `true`` iff `efe` is the sum of the first n-1 appropriate variables
pub fn is_sum(efe: &EFExpr, pl: bool, n: u32) -> bool {
    let perm_var = |n| {
        if pl {
            EFExpr::EFVar(SymbolicVarEF::PermutationLocal(n))
        } else {
            EFExpr::EFVar(SymbolicVarEF::PermutationNext(n))
        }
    };

    let mut efe: &EFExpr = efe;

    for i in (1..n).rev() {
        match efe {
            EFExpr::EFAdd(rest, last) => {
                if **last != perm_var(i) {
                    return false;
                }
                efe = rest.as_ref();
            }
            _ => {
                return false;
            }
        }
    }
    *efe == perm_var(0)
}

/// The `process_permutation_constraints` function takes as input:
/// - `constraints`, a sequence of constraints
/// - `extracted_constraints`, a sequence of already extracted constraints
///
/// identifies and removes the permutation-argument-related constraints from `constraints`,
/// and extends `extracted_info` with the appropriate decoded permutation constraints.
pub fn process_permutation_constraints(
    constraints: &mut Vec<Constraint>,
    extracted_constraints: &mut Vec<ExtractedConstraint>,
) {
    let mut is_permutation_constraint = |constraint: &Constraint| match constraint {
        Constraint::Argument(EFExpr::EFMul(perm_expr, perm_constraint_type)) => {
            match **perm_constraint_type {
                // (PLn - Sum_0^{n-1} PLi) * IsFirstRow = 0
                EFExpr::EFFromF(FExpr::FVar(SymbolicVarF::IsFirstRow)) => {
                    if let EFExpr::EFSub(pln, sum) = (**perm_expr).clone() {
                        if let EFExpr::EFVar(SymbolicVarEF::PermutationLocal(n)) = *pln {
                            if n > 0 && is_sum(&sum, true, n) {
                                extracted_constraints.push(ExtractedConstraint::Permutation(
                                    PermutationConstraint::FirstRow(n),
                                ));
                                true
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                }
                // ((PNn - PLn) - Sum_0^{n-1} PNi) * IsFirstRow = 0
                EFExpr::EFFromF(FExpr::FVar(SymbolicVarF::IsTransition)) => {
                    if let EFExpr::EFSub(pnn_pln, sum) = (**perm_expr).clone() {
                        if let EFExpr::EFSub(pnn, pln) = *pnn_pln {
                            match (*pnn, *pln) {
                                (
                                    EFExpr::EFVar(SymbolicVarEF::PermutationNext(n)),
                                    EFExpr::EFVar(SymbolicVarEF::PermutationLocal(m)),
                                ) if n == m => {
                                    if is_sum(&sum, false, n) {
                                        extracted_constraints.push(
                                            ExtractedConstraint::Permutation(
                                                PermutationConstraint::FirstRow(n),
                                            ),
                                        );
                                        true
                                    } else {
                                        false
                                    }
                                }
                                _ => false,
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                }
                // (PLn - CS0) * IsLastRow = 0
                EFExpr::EFFromF(FExpr::FVar(SymbolicVarF::IsLastRow)) => {
                    if let EFExpr::EFSub(pln, cs0) = (**perm_expr).clone() {
                        match (*pln, *cs0) {
                            (
                                EFExpr::EFVar(SymbolicVarEF::PermutationLocal(n)),
                                EFExpr::EFVar(SymbolicVarEF::CumulativeSum(0)),
                            ) => {
                                extracted_constraints.push(ExtractedConstraint::Permutation(
                                    PermutationConstraint::LastRow(n),
                                ));
                                true
                            }
                            _ => false,
                        }
                    } else {
                        false
                    }
                }
                _ => false,
            }
        }
        _ => false,
    };

    constraints.retain(|constraint| !is_permutation_constraint(constraint));
}
