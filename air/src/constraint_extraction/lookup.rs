use core::panic;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::{AbstractExtensionField, AbstractField, PrimeField32};

use super::extracted_constraint::ExtractedConstraint;
use super::fexpr::{fexpr_one, fexpr_zero};
use super::{constraint::Constraint, efexpr::EFExpr, fexpr::FExpr};
use crate::constraint_extraction::efexpr::efexpr_one;
use crate::symbolic_var_ef::SymbolicVarEF;

// `LookupConstraint` denotes the type of lookup constraints, which consist of: a multiplicity; and
// the coefficients of the associated permutation-challenge polynomial.
pub struct LookupConstraint {
    pub multiplicity: FExpr,
    pub coefficients: Vec<FExpr>,
}

/// Lean-friendly printing of lookup constraints
impl fmt::Display for LookupConstraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}, {:?}", self.multiplicity, self.coefficients)
    }
}

/// The `ef_add_terms` function takes as input:
/// - `efe`: a symbolic ef-term
/// - `max_terms`: the maximal number of returned terms
///
/// and separates `efe` into its additive terms, all if `max_terms` equals zero,
/// and `max_terms` top-level ones otherwise.
fn ef_add_terms(efe: EFExpr, max_terms: usize) -> Vec<EFExpr> {
    // `efe` is not an addition or there is only one more term allowed
    if !matches!(efe, EFExpr::EFAdd(_, _)) || max_terms == 1 {
        vec![efe]
    } else {
        match efe {
            EFExpr::EFAdd(efe1, efe2) => {
                let max_terms_left = (max_terms != 0) as usize;
                let max_terms_right = (max_terms != 0) as usize * max_terms.saturating_sub(1);
                let mut mfl = ef_add_terms(*efe1, max_terms_left);
                mfl.extend(ef_add_terms(*efe2, max_terms_right));
                mfl
            }
            _ => panic!("Impossible"),
        }
    }
}

/// Returns factors of a symbolic ef-expression multiplication.
fn ef_mul_factors(efe: EFExpr) -> Vec<EFExpr> {
    match efe {
        EFExpr::EFMul(efe1, efe2) => {
            let mut mfl = ef_mul_factors(*efe1);
            mfl.extend(ef_mul_factors(*efe2));
            mfl
        }
        _ => vec![efe],
    }
}

/// Converts an ef-constant into an f-constant
fn efc_to_fc(efc: BinomialExtensionField<BabyBear, 4>) -> Option<BabyBear> {
    let efc_components: &[BabyBear] = efc.as_base_slice();
    if efc_components[1] == BabyBear::zero()
        && efc_components[2] == BabyBear::zero()
        && efc_components[3] == BabyBear::zero()
    {
        Some(efc_components[0])
    } else {
        None
    }
}

/// The `process_lpoly` function takes as input:
/// - `lpoly`: a symbolic ef-expression
///
/// and returns the sequence of appropriate coefficients if `lpoly` represents a lookup polynomial,
/// and otherwise None.
///
/// A symbolic ef-expression represents a lookup polynomial if it is of the form
/// `[ PC(0) + C0 + PC(1) * C1 + PC(1) ^ 2 * C2 + PC(1) ^ n * Cn]``,
/// in which case the returned list is of the form `[ C0, C1, ..., Cn ]`.`
fn process_lpoly(lpoly: EFExpr) -> Option<Vec<FExpr>> {
    let mut coefficients: Vec<FExpr> = Vec::new();
    // Iterate over polynomial terms
    for (i, factor) in (ef_add_terms(lpoly, 0)).iter().enumerate() {
        match i {
            // First term must be the zero-th permutation-challenge variable
            0 => {
                if *factor != EFExpr::EFVar(SymbolicVarEF::PermutationChallenge(0)) {
                    return None;
                }
            }
            // Followed by a BabyBear constant representing the interaction kind
            1 => {
                if let EFExpr::EFConst(efc) = *factor {
                    let fc = efc_to_fc(efc)?;
                    coefficients.push(FExpr::FConst(fc));
                }
            }
            _ => {
                // Followed by degrees of the first permutation-challenge-variable
                match factor {
                    // PC(1) ^ 1 * 1
                    EFExpr::EFVar(SymbolicVarEF::PermutationChallenge(1)) => {
                        coefficients.push(fexpr_one())
                    }
                    // PC(1) ^ N * 1
                    EFExpr::EFExp(pc, deg) => {
                        if **pc != EFExpr::EFVar(SymbolicVarEF::PermutationChallenge(1)) {
                            return None;
                        }
                        // Degree must be in BabyBear
                        let deg = efc_to_fc(*deg)?;
                        // Account for potential gap in poly degrees
                        let gap = deg.as_canonical_u32() as usize - coefficients.len();
                        coefficients.extend(vec![FExpr::FConst(BabyBear::zero()); gap]);
                        // Add coefficient
                        coefficients.push(fexpr_one())
                    }
                    EFExpr::EFMul(pc_deg, efe) => {
                        // Compute the coefficient
                        let fe = match (**efe).clone() {
                            EFExpr::EFFromF(fe) => fe,
                            EFExpr::EFConst(efc) => FExpr::FConst(efc_to_fc(efc)?),
                            _ => return None,
                        };
                        // Understand degree of term
                        match (**pc_deg).clone() {
                            // Degree is 1, term is of the form `PC(1)`
                            EFExpr::EFVar(SymbolicVarEF::PermutationChallenge(1)) => {
                                // Add coefficient (which represents the opcode)
                                coefficients.push(fe)
                            }
                            // Degree is greater than 1, term is of the form `PC(1) ^ deg`
                            EFExpr::EFExp(pc, deg) => {
                                if *pc != EFExpr::EFVar(SymbolicVarEF::PermutationChallenge(1)) {
                                    return None;
                                }
                                // Degree must be in BabyBear
                                let deg = efc_to_fc(deg)?;
                                // Account for potential gap in poly degrees
                                let gap = deg.as_canonical_u32() as usize - coefficients.len();
                                coefficients.extend(vec![FExpr::FConst(BabyBear::zero()); gap]);
                                // Add coefficient
                                coefficients.push(fe)
                            }
                            _ => return None,
                        }
                    }
                    _ => return None,
                }
            }
        }
    }
    Some(coefficients)
}

/// The `process_lc_lhs` function takes as input:
/// `lhs` - a symbolic ef-expression
///
/// and returns the sequence of lookup-polynomial-coefficient sequences if `lhs` represents a
/// left-hand-side of a lookup constraint subtraction.
///
/// A symbolic ef-expression represents a left-hand-side of a lookup constraint subtraction if it
/// is of the form `E1 * ... * En * PL(_)`, where each `Ei` represents a lookup polynomial.
fn process_lc_lhs(lhs: EFExpr) -> Option<Vec<Vec<FExpr>>> {
    let candidates = ef_mul_factors(lhs);
    match candidates.last() {
        // Last factor must be a permutation-local variable
        Some(EFExpr::EFVar(SymbolicVarEF::PermutationLocal(_))) => {
            let mut lpolys: Vec<Vec<FExpr>> = Vec::new();
            for candidate in candidates.iter().take(candidates.len() - 1) {
                let lpoly = process_lpoly(candidate.clone())?;
                lpolys.push(lpoly);
            }
            Some(lpolys)
        }
        _ => None,
    }
}

/// Computes the difference of two vectors
pub fn vec_difference<T: Eq + Hash + Clone>(vec1: &[T], vec2: &[T]) -> Vec<T> {
    let mut vec2_counts: HashMap<T, usize> = HashMap::new();
    for item in vec2 {
        *vec2_counts.entry(item.clone()).or_insert(0) += 1;
    }

    let mut difference = Vec::new();
    for item in vec1 {
        match vec2_counts.get_mut(item) {
            Some(count) if *count > 0 => {
                *count -= 1;
            }
            _ => {
                difference.push(item.clone());
            }
        }
    }
    difference
}

///
/// Pads lookup constraints to correct length
///
fn pad_coefficients(coefficients: &mut Vec<FExpr>, interaction_kind: u32) {
    let param_count = match interaction_kind {
        1 => 8,
        2 => 16,
        3 => 24,
        5 => 6,
        8 => 6,
        9 => 11,
        _ => panic!("Unsupported interaction kind: {}", interaction_kind),
    };
    if coefficients.len() > param_count {
        panic!("Lookup argument with too many parameters for interaction kind {}: max {}, received {}.", interaction_kind, param_count, coefficients.len())
    }
    let extension: Vec<FExpr> = vec![fexpr_zero(); param_count - coefficients.len()];
    coefficients.extend(extension);
}

/// The `process_lc_rhs` function takes as input:
/// `lhs_lpolys` - a sequence of lookup-polynomial-coefficient sequences representing the
///                left-hand side of a lookup constraint substraction
/// `rhs` - a symbolic ef-expression
///
/// and returns the list of multiplicity-coefficient pairs representing a lookup constraint,
/// if `rhs` represents the corresponding right-hand-side of a lookup constraint subtraction.
///
/// Given a left-hand-side of a lookup constraint subtraction of `n` factors, `L1, ..., Ln`,
/// a symbolic ef-expression represents the corresponding right-hand-side of a lookup constraint
/// subtraction if it is a sum of `n` terms, and each term `Ti` is a product of a coefficient `Mi`
/// (multiplicity) and all factors except `Li`.
fn process_lc_rhs(lhs_lpolys: Vec<Vec<FExpr>>, rhs: EFExpr) -> Vec<ExtractedConstraint> {
    let default = vec![];
    let mut extracted_lookups: Vec<ExtractedConstraint> = vec![];

    // Separate `rhs` into `n` additive terms, returning `false` if that is not possible
    let all_but_ones: Vec<EFExpr> = ef_add_terms(rhs, lhs_lpolys.len());
    if all_but_ones.len() != lhs_lpolys.len() {
        return default;
    }

    let all_factors: Vec<Vec<FExpr>> = lhs_lpolys.iter().map(|coeff| (*coeff).clone()).collect();

    // Each lookup polynomial from the `lhs` must appear exactly `n - 1` times in the products
    for all_but_one in all_but_ones {
        // Understand multiplicity
        let (multiplicity, all_but_one) = match all_but_one.clone() {
            EFExpr::EFMul(efe1, efe2) => match *efe1 {
                EFExpr::EFConst(efc) => efc_to_fc(efc)
                    .map_or((fexpr_one(), all_but_one), |fc| (FExpr::FConst(fc), *efe2)),
                EFExpr::EFFromF(fc) => (fc, *efe2),
                _ => (fexpr_one(), all_but_one),
            },
            EFExpr::EFFromF(efe) => (efe, efexpr_one()),
            EFExpr::EFConst(efc) => match efc_to_fc(efc) {
                Some(fc) => (FExpr::FConst(fc), efexpr_one()),
                None => return default,
            },
            _ => (fexpr_one(), all_but_one),
        };
        // Single lookup
        if lhs_lpolys.len() == 1 && all_but_one == efexpr_one() {
            return vec![ExtractedConstraint::Lookup(LookupConstraint {
                multiplicity,
                coefficients: lhs_lpolys[0].clone(),
            })];
        }
        // Multiple batched lookups
        let all_but_one_coeffs: Option<Vec<Vec<FExpr>>> = ef_mul_factors(all_but_one)
            .iter()
            .map(|factor| process_lpoly((*factor).clone()))
            .collect::<Vec<Option<Vec<FExpr>>>>()
            .into_iter()
            .collect::<Option<Vec<Vec<FExpr>>>>();
        if let Some(all_but_one_coeffs) = all_but_one_coeffs {
            if all_but_one_coeffs.len() != lhs_lpolys.len() - 1 {
                return default;
            }
            let all_but_one_coeffs = all_but_one_coeffs
                .iter()
                .map(|coeff| (*coeff).clone())
                .collect::<Vec<Vec<FExpr>>>();
            if all_but_one_coeffs.len() != lhs_lpolys.len() - 1 {
                return default;
            }
            // Precisely one lpoly is missing
            let diff_expected_factor: Vec<Vec<FExpr>> =
                vec_difference(&all_factors, &all_but_one_coeffs);
            if diff_expected_factor.len() != 1 {
                return default;
            }
            // and all others are relevant
            let diff_factor_expected: Vec<Vec<FExpr>> =
                vec_difference(&all_but_one_coeffs, &all_factors);
            if !diff_factor_expected.is_empty() {
                return default;
            }
            // Extend extracted lookups with current
            if let Some(mut lookup_coefficients) = diff_expected_factor.first().cloned() {
                if let FExpr::FConst(interaction_kind) = lookup_coefficients[0] {
                    pad_coefficients(&mut lookup_coefficients, interaction_kind.as_canonical_u32());
                    extracted_lookups.push(ExtractedConstraint::Lookup(LookupConstraint {
                        multiplicity,
                        coefficients: lookup_coefficients,
                    }));
                } else {
                    panic!("Unsupported: symbolic interaction kind");
                }
            } else {
                panic!("Impossible");
            }
        } else {
            return default;
        }
    }
    extracted_lookups
}

/// The `process lookup constraints` function takes as input:
/// - `constraints`, a sequence of constraints
/// - `extracted_constraints`, a sequence of already extracted constraints
///
/// identifies and removes the lookup-argument-related constraints from `constraints`,
/// and extends `extracted_info` with the appropriate decoded lookup constraints.
///
/// A lookup constraint is of the form `lhs - rhs == 0`, where:
/// - `lhs` is a product of lookup polynomials and a permutation-local variable; and
/// - `rhs` is a sum of weighted all-but-one products of the lookup polynomials in `lhs`.
pub fn process_lookup_constraints(
    constraints: &mut Vec<Constraint>,
    extracted_info: &mut Vec<ExtractedConstraint>,
) {
    // Identify constraints originating from lookups
    *constraints = constraints
        .iter()
        .flat_map(|constraint| {
            let constraint = constraint.clone();
            let default = vec![constraint.clone()];

            // Early return for non-matching constraint patterns
            let (lc_lhs, lc_rhs) = match constraint {
                Constraint::Argument(EFExpr::EFSub(lhs, rhs)) => (*lhs, *rhs),
                _ => return default,
            };

            // Process left-hand side, returning default if it doesn't match
            let lpolys = match process_lc_lhs(lc_lhs) {
                Some(polys) => polys,
                None => {
                    return default;
                }
            };

            // Process right-hand side, returning default if it doesn't match
            let extracted_constraints = process_lc_rhs(lpolys.clone(), lc_rhs);
            if extracted_constraints.is_empty() {
                return default;
            }

            extracted_info.extend(extracted_constraints);

            vec![]
        })
        .collect::<Vec<Constraint>>();
}
