use std::fmt;

use super::{fexpr::FExpr, lookup::LookupConstraint, permutation::PermutationConstraint};

/// `ExtractedConstraint` denotes the type of extracted constraints, which can be either:
/// basic constraints; lookup-argument constraints; or permutation-argument constraints.
pub enum ExtractedConstraint {
    Basic(FExpr),
    Lookup(LookupConstraint),
    Permutation(PermutationConstraint),
}

/// Lean-friendly printing of extracted constraints
impl fmt::Display for ExtractedConstraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExtractedConstraint::Basic(c) => write!(f, "Basic({} = 0)", c),
            ExtractedConstraint::Lookup(l) => write!(f, "Lookup({})", l),
            ExtractedConstraint::Permutation(p) => write!(f, "Permutation({})", p),
        }
    }
}
