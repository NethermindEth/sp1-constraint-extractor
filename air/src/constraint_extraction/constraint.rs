use std::fmt;

use crate::constraint_extraction::fexpr::FExpr;

use super::efexpr::EFExpr;

/// `Constraint` denotes the type of general constraints, which can be either:
/// a basic constraint, representing an equality of a symbolic f-expression with zero; or
/// an argument constraint, representing an equality of a symbolic ef-expression with zero.
#[derive(Clone, PartialEq)]
pub enum Constraint {
    Basic(FExpr),
    Argument(EFExpr),
}

/// Lean-friendly printing of constraints
impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Constraint::Basic(fe) => write!(f, "{} = 0", fe),
            Constraint::Argument(efe) => write!(f, "{} = 0", efe),
        }
    }
}
