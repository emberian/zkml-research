# Arbitrary entry-degree polynomial matrix kernel

[EXECUTED] The complete successor [PolynomialMatrixKernel.lean](PolynomialMatrixKernel.lean) checks under Lean 4.30 with 26 theorem declarations and 26 exact standard-only guarded axiom pins. It generalizes the existing determinant/rank proof once and preserves every old degree-one theorem signature and guard block. The frozen original and all-pins predecessor packages are unchanged.

[EXECUTED] Source SHA-256: `f510b6cc0c648a3583e3eefa49e283b2186add24d2e4df71f3afeb9b06a3fa91`. Primary [polynomial-curve-kernel.patch](polynomial-curve-kernel.patch) SHA-256: `d93868e566910220380cfa96d33bcb665c6deb57090a34e62beaa0fe6fd56c8c`.

## Exact interface

[EXECUTED] Module `Theory.PolynomialMatrixKernel`, namespace `PolynomialMatrixKernel.Source`:

```lean
theorem RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le
    (M e : ℕ) (K : Matrix ι (Fin (e + 1)) F[X])
    (hcard : e + 1 ≤ Fintype.card ι)
    (hdeg : ∀ i j, (K i j).natDegree ≤ M)
    (hdet : ∀ r : Fin (e + 1) → ι,
      Matrix.det (K.submatrix r id) = 0) :
    ∃ a : Fin (e + 1) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ M * e) ∧
      Matrix.mulVec K a = 0
```

[EXECUTED] The interface is universe-polymorphic in `F : Type*` and `ι : Type*`, assuming `[Field F] [Fintype ι]`. It does not require a finite field, positive `M`, or positive `e`. The companion determinant helper is

```lean
RS_natDegree_det_le_of_entry_natDegree_le (M n : ℕ)
    (A : Matrix (Fin n) (Fin n) F[X])
    (hdeg : ∀ i j, (A i j).natDegree ≤ M) :
    (Matrix.det A).natDegree ≤ M * n
```

[EXECUTED] `DegreePremises`, `DegreeBoundedKernel` and `DegreeCorrectness` state the hypotheses and conclusion before the proof; `degree_correctness` proves that contract. The curve lane agreed to consume these exact theorem names and multiplication order. This package proves candidate-independent polynomial algebra only; curve interpolation, Reed–Solomon proximity and protocol security are separate consumers.

## Reuse and proof

[SOURCE] The predecessor adapted ArkLib's `BWMatrix.lean`, commit `22dbd4e836c15a21f68889afa69b7130da04abbb`, including its degree-one kernel theorem at line 1175 and the bounded helper closure. This successor retains the original authorship/header and [Apache 2.0 license](ArkLib-Apache-2.0.txt). Exact source pins are in [provenance.json](provenance.json).

[SOURCE/DERIVED] Inspection found the predecessor's determinant helper specialized to entry degree one; its rank argument was otherwise independent of that bound. The saved [Mathlib search](mathlib-degree-search.log), using `rg 'natDegree.*det|det.*natDegree'` over the pinned Mathlib tree, found the affine-specific `natDegree_det_X_add_C_le` rather than an arbitrary-entry-degree determinant interface. The existing polynomial product/sum degree inequalities supply the needed generalization.

[EXECUTED/DERIVED] The generalized determinant proof bounds each Leibniz product by the sum of its `n` entry degrees, hence by `M*n`. The existing maximal nonzero minor proof selects rank `r≤e`; an adjugate column of an `(r+1)`-square singular submatrix is nonzero because one cofactor is the chosen nonzero minor. Extending that column by zero annihilates every row, using the existing determinant/update-row identities. Its coefficient degrees are at most `M*r≤M*e`.

[EXECUTED] The original degree-one determinant and kernel heads are now `M=1` wrappers over those single generalized proofs. All other original theorem bodies remain in place. [api_preservation.json](api_preservation.json) checks all 16 old statement headers modulo whitespace and exact preservation of their 16 old guard blocks. [changes-from-all-pins.diff](changes-from-all-pins.diff) is a supplementary review diff, not the primary integration patch.

## Witnesses and teeth

[EXECUTED] For every `M`, the nonzero two-row matrix with repeated row `[X^M,1]` satisfies `DegreePremises M 1`. Its explicit nonzero annihilator `[1,-X^M]` has degrees at most `M` and multiplies to zero. `degree_premises_inhabited` and `degree_satisfiable` include `M=0`; positive values such as `M=2` exercise higher-degree entries.

[EXECUTED] `degree_strict_bound_teeth` proves this matrix admits no nonzero kernel vector whose coordinates all have degree strictly below `M`. Thus the `e=1` bound is sharp for every positive `M`. `degree_determinant_hypothesis_teeth` uses the identity matrix to refute removal of the vanishing-minor premise at every `M,e`. `entry_degree_hypothesis_teeth` retains a singular degree-one matrix whose kernel cannot satisfy the falsely substituted degree-zero conclusion. The old witness and falsifier theorems remain available.

## Checks and integration

[EXECUTED] Isolated checkout: `/tmp/minidregg-polynomial-curve-kernel-20260908`, cloned from main base `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`. The final command, source/output hashes, elapsed time, exit zero and empty stdout/stderr are retained in [lean_final.json](lean_final.json):

```sh
lake env lean -o /tmp/minidregg-polynomial-curve-kernel-20260908/.lake/build/lib/lean/Theory/PolynomialMatrixKernel.olean Theory/PolynomialMatrixKernel.lean
```

[EXECUTED] Three single-module iterations passed: generalized core, witness/axiom observation, then final exact guards. The root integration census verifies all 26 declarations/pins and rejects forbidden proof shortcuts. The companion import-boundary script passes, and all six direct imports are Mathlib modules. A clean `git apply --check`, application and byte-for-byte comparison passed for both target files; neither target exists in the main base. Exact records: [integration_census.json](integration_census.json), [patch_and_import_checks.json](patch_and_import_checks.json), [import-boundary.log](import-boundary.log).

[EXECUTED] The primary patch adds the complete successor `Theory/PolynomialMatrixKernel.lean` and `LICENSES/ArkLib-Apache-2.0.txt` against the main base. Select [integration_entry.json](integration_entry.json) **instead of** the predecessor polynomial-kernel lane. Do not apply both new-file patches. The source module/import path and every old public theorem signature are preserved; root owns dependency rebuilds and full integration. [support_file_entry.json](support_file_entry.json) records the unchanged license bytes.

[OPEN] No full umbrella build, curve consumer, complexity claim or cryptographic result is supplied here. Main/companion trees and frozen predecessors were not edited; no commit, push, external search or cryptographic execution occurred.
