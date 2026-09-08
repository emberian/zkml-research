# Per-row capacities for the actual nonlinear rescale compiler

[DERIVED] This replaces the uniform result width and carry width of the generated signed-matrix relation with compile-time widths for each matrix equation. It reuses the same scalar decomposition, signed rows, weighted-column gadgets, range gadgets, exact directed RNS formula, public columns, and witness arithmetic. The reusable compiler entry is `ProfiledMatrix.system`; `ProfiledMatrix.sourceSound` proves every accepted field assignment satisfies the original signed integer matrix under explicit `Capacity` premises. No runtime-authored AIR is introduced.

[EXECUTED] The actual 9→4 nonlinear instance now has **24,575 witness columns and 32,043 arithmetic constraints**, down from 63,845 and 76,269. The existing native prover accepted its generated witness for the **same 32 distinct actual positions**, covering **128 of 98,304 output residue equations**. Fresh-process verification accepted; changing public output column 64 was refused. This is a smaller relation for that batch, not a whole-ciphertext proof.

| Same 32-position workload | Frozen uniform layout | Per-row layout |
|---|---:|---:|
| Witness columns | 63,845 | 24,575 |
| Scalar digits and bits | 8,970 | 8,970 |
| Result digits and bits | 10,350 | 6,220 |
| Carry values and bits | 44,436 | 9,296 |
| Public wire reservation | 89 | 89 |
| Arithmetic constraints, excluding lookup | 76,269 | 32,043 |
| Trace bytes | 8,172,160 | 3,145,600 |
| Proof bytes | 14,454,987 | 5,664,793 |
| Prove seconds | 2.590259 | 0.381009 |
| Fresh verification seconds | 0.506974 | 0.196285 |
| Peak process RSS bytes | 412,254,208 | 175,882,240 |

[EXECUTED] Layout counts come from `results/profile.json`, `results/cost_breakdown.json`, and `artifacts/emission.json`. Proof measurements come from the saved original run and the single successor observation in `../rescale_cost_runtime/`; the original was not rerun. Both use the same frozen executable/backend, public inputs, and four Rayon threads. These observations are not repeated timing statistics or full-operation estimates.

## Compiler and theorem scope

[DERIVED] `ProfiledMatrix.RowLayout` supplies a result width and a carry-bit count per equation. The shared scalar prefix is allocated once. Each equation still emits the existing left and right weighted-column gadgets with a shared result. `sourceSound` derives exact integer equality from their range constraints and local BabyBear bounds; it does not assume output equations.

[DERIVED] `ProfiledBounds.unsignedMassBound` bounds each side for every bounded scalar assignment. `widthSufficient` and `auto_width_sufficient` prove the result width selected from that full unsigned mass is sufficient. `NonlinearRnsProfiled.profileDerived` proves the concrete vectors equal `autoLayout` applied to the original matrix, independent of runtime witnesses. `coefficients_fit`, `constants_fit`, and `capacity` discharge the actual source-soundness premises by kernel-checked arithmetic.

[DERIVED] `NonlinearRnsProfiled.rowSound` and `simplifiedSource_sound` reuse the predecessor's canonical-input, native word-accumulator, public alias, and modulo-Q projection theorems. Every accepting assignment forces all four target residues to equal `nativeProjectedOutput` on its nine public input residues. The actual modulus counts, constants, Garner shift125 and directed correction are unchanged; this is not ideal rational rounding.

[DERIVED] `ProfiledAgreement.layoutAgreement` proves that accepting old and new layouts on the same public input have the same complete four-residue output tuple. This is output agreement. No total auxiliary-witness bijection or generic field-witness completeness theorem is claimed.

[DERIVED] `ProfiledExhibits.inhabitedCompiler` gives a nonzero accepted assignment and an inhabited `Capacity`. `missingCapacityFalsifier` proves the capacity premise matters: a one-bit truncated constant2 relation accepts zero although its integer equation is false, and its required capacity fails. The predecessor's q31 half-rounding witness and universally refused wrong output remain available unchanged.

[OPEN] The automatic carry profile uses one plus the sum of coefficient digit masses. `carry_step_bound` proves the conventional recurrence bound given a static column budget. This package does not prove the complete digit-window argument connecting that automatic budget to every possible producer carry, nor a total witness-construction theorem. This does not weaken accepted-assignment soundness: the explicit field/constant/coefficient capacities are proved, and any too-small carry allocation can only reject a witness. All 32 supplied witnesses actually passed every generated term and the real prover.

## Executed path

[EXECUTED] `EmitProfiledRns.lean` folds the same simplified source terms into the existing strict IR2 tagged syntax. `ProfiledWitness` changes allocation; scalar values, sparse coefficient caches, radix installation and carry evaluation call the frozen generic producer. It authors no separate rescale arithmetic. The emitter generated and checked all 32 rows, rejected a changed public output and a radix512 digit equal to512, and exited0. `results/emission_002.log` retains the full output; elapsed emission was331.504s. This Lean interpreter run is not an efficient whole-operation witness path.

[EXECUTED] The public tuple is unchanged: `rowID`, nine input residues with seven radix512 digits each, then four output residues with six digits each. Arity88, output start64, ExactPublicRows table11. The source rows and exact selection mapping remain `../proved_rescale_generic/results/case001/`; there are no padding positions.

[EXECUTED] Frozen artifacts:

- `artifacts/template_ir2.json`: SHA256 `37a02768080e1ca8284fab4bc186b2e5981ad0b97a4af7965472953cdfe4df5a`.
- `artifacts/trace.leu32`: SHA256 `92ceb5ab11ffa4ff2b3032d1658ad0f13a4e70c28bc6d409bedbbcff86c9e591`.
- Unchanged public rows: SHA256 `0b817b8b538062557a5a6add1d08ba159b1874afda6e3d36ce882993b83f87f7`.
- Actual successor proof: SHA256 `2c4806c9526b7aa2a975cfa8bdf2e722d2ca35b9a3aff02d2181970d4d407045`.

[EXECUTED] Six new Compiler modules contain15 theorem declarations with15 exact axiom pins. Final isolated per-module commands, source hashes and logs are in `results/checked_modules.json`. They reuse the checked predecessor oleans through an owned overlay; there was no full build or companion edit. `proposal.patch` adds the six modules and standalone emitter after the frozen generic package. The existing import-boundary script is recorded in `results/import_boundary.log`; no Theory or Selvage source is changed. Parent integration remains separate.

[EXECUTED] Failed attempts are retained. The first profile proof was stopped after155.227s; later finite-capacity proof attempts failed before the final proof succeeded. The first emission was stopped after214.543s while repeatedly recomputing prefix allocations. Let-binding the identical row start/width/carry start in `rowWires` fixed that execution cost. None of these stopped runs is evidence of kernel infeasibility. The final large actual trace was executed, not reduced as a closed kernel witness.

## Boundaries and next construction

[OPEN] This retains the predecessor's exact-gamma family (`theta_gamma=0`) and executable trust boundary: captured native constructor constants, Rust source/ciphertext extraction, serializer/IR2/ExactPublicRows adapter, proof protocol/PCS implementation, native scaler language semantics, NTT/convolution and BFV correctness are not newly proved. Generic Nat-wire bounds and witness completeness are not newly proved. The native parser checked the emitted finite indices; the actual proof checked the emitted witness.

[OPEN] The next authorized construction is a compiler-emitted BigInt witness plan for this exact relation, one byte-exact comparison on the original32 rows, then six4096-row chunks covering all24,576 actual positions. This package itself proves only the32-position batch. Earlier sources, outputs and runtime evidence remain frozen. No new web searches were used.
