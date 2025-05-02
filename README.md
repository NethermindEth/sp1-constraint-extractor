# Constraint Extractor for SP1 zk chips

This repository extends the [sp1-symbolic](https://github.com/jtguibas/sp1-symbolic/commit/be96dc2426003dc7ba3e9244544c7e7cf6b61ebd) repository to provide a mechanism for extracting constraints from SP1 zk chips.
This mechanism is implemented in the [`air/src/constraint_extraction`](air/src/constraint_extraction) folder, where:
- [`fexpr.rs`](air/src/constraint_extraction/fexpr.rs) defines symbolic expressions over the BabyBear field;
- [`efexpr.rs`](air/src/constraint_extraction/efexpr.rs) defines symbolic expressions over the degree-four extension of the BabyBear field;
- [`constraint.rs`](air/src/constraint_extraction/constraint.rs) defines general constraints;
- [`simplify.rs`](air/src/constraint_extraction/simplify.rs) implements a simplifier for general constraints;
- [`lookup.rs`](air/src/constraint_extraction/lookup.rs) defines lookup constraints and implements a mechanism for their identification;
- [`permutation.rs`](air/src/constraint_extraction/permutation.rs) defines permutation constraints and implements a mechanism for their identification;
- [`extracted_constraint.rs`](air/src/constraint_extraction/extracted_constraint.rs) defines extracted constraints; and
- [`eval.rs`](air/src/constraint_extraction/permutation.rs) implements the main evaluation and extraction procedures.

### Running the extractor
Assuming an installation of Rust is present on the system, the extractor can be run using the following command:
```
RUST_MIN_STACK=104857600 cargo test -- --nocapture
```
which will extract constraints from all SP1 chips except `KeccakPermute` and `Global`.
The extracted constraints will be saved into the `air/chip_constraints` folder, with one `.constraints` file generated per chip.