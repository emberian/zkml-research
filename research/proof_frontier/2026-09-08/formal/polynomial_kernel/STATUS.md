# Polynomial matrix kernel — checked patch

[EXECUTED] The assigned degree-bounded rectangular polynomial-kernel theorem is proved in Lean 4.30. The distributable patch is `polynomial-kernel.patch`; it adds `Theory/PolynomialMatrixKernel.lean` and `LICENSES/ArkLib-Apache-2.0.txt` to minidregg. Standalone copies are saved beside it. No commits, pushes, or writes to companion source trees were made.

## Exact statement

[DERIVED, proved] For arbitrary universes, a field `F`, finite row type `ι`, natural `e`, and `K : Matrix ι (Fin (e + 1)) F[X]`, these hypotheses imply an actual nonzero polynomial kernel vector whose coordinate natural degrees are at most `e`:

- `[DERIVED]` `e + 1 ≤ Fintype.card ι`.
- `[DERIVED]` Every matrix entry has natural degree at most one.
- `[DERIVED]` For every row-selection function `r : Fin (e + 1) → ι`, `Matrix.det (K.submatrix r id) = 0`.

[DERIVED] The conclusion is `∃ a, a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ e) ∧ Matrix.mulVec K a = 0`. The hypotheses do not contain this conclusion, a kernel-existence carrier, or any Reed–Solomon/probability premise.

[EXECUTED] Named statement-first declarations in the delivered module are `PolynomialMatrixKernel.BoundedKernel` at line 35, `Premises` at line 40, and `Correctness` at line 47. The checked headline is `PolynomialMatrixKernel.correctness` at line 422. A direct source-compatible theorem is `PolynomialMatrixKernel.Source.RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one` at line 199, with the individual hypotheses above.

## Nonvacuity and teeth

[DERIVED, proved] `witnessMatrix` has both rows `[X, 1]`, and `witnessVector` is `[1, -X]`. `witnessMatrix_premises` proves the actual minor and degree premises; `witnessVector_valid` proves the explicit nonzero vector and annihilation; `premises_inhabited` additionally proves the matrix is nonzero; `satisfiable` joins the actual premises and conclusion. These witnesses work over every field, including characteristic two.

[DERIVED, proved] `determinant_hypothesis_teeth` at line 468 uses the identity matrix for every `e`: it satisfies the cardinality and linear-entry conditions but has no nonzero kernel. Dropping the vanishing-minor premise is therefore false.

[DERIVED, proved] `degree_bound_teeth` at line 481 proves that the singular witness matrix has no nonzero kernel vector all of whose coordinates have degree at most zero. The degree-one allowance is substantive, not a vacuous upper bound for a constant witness.

## Source and adaptation

[SOURCE] Read the construction proofs in `/Users/ember/src/ArkLib-2026-09/ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/BWMatrix.lean` at ArkLib commit `22dbd4e836c15a21f68889afa69b7130da04abbb`. The source theorem is at line 1175. Pure algebra dependencies are at lines 606, 618, 630, 742, 760, 789, 937, and 944. These are the adjugate-minor formulas, determinant invariance under row/column permutations, adjugate-column annihilation, determinant degree bound, and updated-row Laplace expansion.

[SOURCE] Upstream copyright/authors were preserved in the module. The complete upstream Apache 2.0 license is copied byte-for-byte as `LICENSES/ArkLib-Apache-2.0.txt`; the module points to this file. Changes are explicitly marked: standalone Mathlib imports, unnecessary source section assumptions removed, universe polymorphism, named correctness/witness/teeth declarations, and the Lean 4.30 port. This is an attributed adaptation, not a novelty claim.

[DERIVED] The source construction chooses a maximal nonzero minor, extends it by one row and column, takes a nonzero adjugate column, and extends that vector by zero to all matrix columns. Maximality makes every remaining row annihilate it; determinant degree bounds give coordinate degree at most the maximal-minor size, which is at most `e`.

[EXECUTED] Imports are six Mathlib modules. There are no ArkLib imports, Reed–Solomon definitions, or probability semantics in the delivered file. A local `rg` scan of the final module found no `sorry` or `axiom` declarations. There were zero web, Kagi, Scry SQL, or Scry schema queries in this lane; all sources were supplied local files.

## Validation and handoff

[EXECUTED] Isolated checkout: `/tmp/minidregg-polynomial-kernel-20260908`; minidregg baseline `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`; Mathlib `1c2b90b13009c65b090d95a83c98e248deafb6f1`; Lean 4.30.0. Full source/patch hashes and toolchain identity are in `provenance.json`.

[EXECUTED] `lake env lean Theory/PolynomialMatrixKernel.lean` exits zero with all eight `#guard_msgs`-pinned `#print axioms` checks; see `lean-final.log`. The direct theorem, named correctness, four witness/nonvacuity theorems, and both teeth depend only on `[propext, Classical.choice, Quot.sound]`. Observed unguarded reports are preserved in `axioms-observed.log`.

[EXECUTED] `bash scripts/check-import-boundary.sh` exits zero for Theory and Selvage; see `import-boundary.log`. `git apply --check --whitespace=error-all` and actual application into a fresh empty temporary directory pass, and both reconstructed files match the checked checkout byte-for-byte; see `patch-check.log`.

[EXECUTED] Failed attempts are retained: `lean-first.log` records a source-extraction truncation; `lean-second.log` records new witness noncomputability and self-rewriting simplifier errors; `lean-third.log` is the first fully green pre-pin check. `patch-first-check.log` records one extra final blank line, removed before the final patch.

[OPEN] Full minidregg umbrella build and integration into the full unique-decoding proximity caller belong to root and the `full_ud` lane. This patch alone proves the algebraic kernel step, not the final proximity theorem, a protocol soundness bound, or a shipped verifier. No other required mathematical seam remains inside this lane's assigned theorem.
