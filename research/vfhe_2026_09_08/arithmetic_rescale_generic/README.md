# Parameterized exact directed RNS rescale

[DERIVED] This adds a reusable signed-affine matrix compiler and an exact directed RNS scaler frontend. The frontend takes the source/target modulus counts, moduli, fixed-point constants, quotient offsets, radix, and carry/result capacities. It emits the existing weighted-column and range gadgets. There is no replacement Rust AIR or scalar-equation list authored in the runtime.

[EXECUTED] The actual nonlinear 9→4 instance produced one descriptor and a Lean-generated trace for **32 distinct positions**, selected in advance from the real N=8192, three-component multiplication output. These cover **128 output residue equations out of 98,304**, or 32 of 24,576 component/coefficient positions. The selected boundary positions and their source binding are in `../proved_rescale_generic/results/case001/selection.json`. This package does not claim the whole ciphertext.

[EXECUTED] The existing prover accepted the emitted relation and witness; fresh-process verification passed and changing public output column 64 was refused. Runtime evidence belongs to `../proved_rescale_generic/`. Reported proof size is 14,454,987 bytes, SHA256 `eb887940a2734828b56500a4d5f42316e29c1fb12c20a795ee341c6c24f62a31`; measured prove 2.590s, self-verify 0.641s, fresh verify 0.507s. These are this small batch's observed costs, not whole-ciphertext estimates.

## Exact arithmetic being forced

[DERIVED] For canonical input residues `r`, the generic source forces

```
v = floor((2·Σ r_i θG_i + dG)/(2·dG))
w = floor((2·Σ r_i θF_i + dF)/(2·dF))
Y = (Σ r_i Ω_i − Γ·v + w) mod Q
out_j = Y mod q_j
```

[DERIVED] Two signed Euclidean quotient/remainder equations force `v` and `w`; complement variables force both remainder ranges. Input and output complements force canonical residues. All target projections share the same `Y` and exact output-quotient equation. `Q>0`, both rounding denominators positive, target moduli positive, and each target modulus dividing `Q` are explicit validated parameter premises. The compiler derives integer equalities from range constraints and local sums strictly below BabyBear, rather than asking the caller to assume integer gate equations.

[SOURCE] This scaler family assumes **exact gamma**, hence native `theta_gamma=0`. That condition holds for this multiplication downscale because the target product divides the extended product, and it is recorded by the actual native constructor capture. General nonzero `theta_gamma` correction is outside this frontend. It does not replace the source's directed fixed-point theta with ideal rational rounding.

[DERIVED] The actual instance uses native Garner shift125, correction denominator2^127, and native signed theta words. Canonical inputs imply the Garner and signed-correction accumulator bounds required by the reused U256-word mathematical model. `wordV 125_correct` extends the existing shift126/127 bridge. Canonical modulo-Q lifts of native omega/gamma reduce coefficient widths; `projectionAgreement` and `canonical_lift_preserves_native` prove that all four target modular outputs are preserved.

[SOURCE] Native construction and directed correction are read from `fhe-math-0.1.1/src/rns/scaler.rs:84`, `:175`, and `:247`; Garner construction is `rns/mod.rs:80`. Exact absolute source paths and hashes are in `source_pins.json`. The public native constructor capture is `nonlinear_successor_2026_09_08/public_trace/native_scaler_constants.json`, SHA256 `928be 24496d 3b 6668a 98d 64aa 65dccabd 1e 7028380cf 85b 6e 8d 37d 1447ea 5574`. No web searches were used.

## Checked theorem chain

[DERIVED] The35 theorem declarations have exact `#guard_msgs`/`#print axioms` pins. `results/checked_modules.json` records the final isolated per-module commands and source hashes. There is no `sorry`, added axiom, or `native_decide`.

- `SignedMatrix.splitSound`: signed affine evaluation equals equality of positive/negative natural masses.
- `SignedMatrix.sourceSound`: existing range and weighted-column constraints imply every signed matrix equation, for any layout satisfying `Capacity`.
- `DirectedRnsScaler.certificateSound`, `matrixSound`, `compiledSound` (`Compiler/DirectedRnsEmit.lean:19`): universal exact source/projection composition across basis counts and layout parameters.
- `NonlinearRnsInstance.capacity`, `sourceSound`: actual9→4 constants and layout instantiate that arithmetic chain.
- `NonlinearRnsInstance.nativeWordRefinement`, `projectionAgreement`, `canonical_lift_preserves_native`: the actual shift125 word model and captured native target projections agree with the source formula.
- `NonlinearRnsPublic.publicRowSound`, `nativeProjectedRow_sound`, `simplifiedSource_sound` (`Compiler/NonlinearRnsPublicSound.lean:87`, `:92`): every accepting assignment to the actual public-column relation forces all four public outputs, with both canonical inputs and word-accumulator range premises supplied by the relation.
- `DirectedRnsScaler.nonvacuous`: a cheap nonzero q31 matrix witness with input3, output8, and a true half-rounding boundary. `wrongRoundingRefused` excludes output7 for every auxiliary certificate. `honest_accepts` supplies a semantic certificate for every canonical input; full field-witness completeness for every canonical input is not claimed.

## Executable artifact

[EXECUTED] `EmitNonlinearRns.lean` serializes a `Signature.fold` of the existing simplified source terms using the backend's strict tagged-key order. The constant-only `generate_instance.py` reconstructs the native public projections and directed theta values; it authors no matrix equations or witness carries. The generic Lean witness producer reads the same matrix, caches sparse constant columns, installs radix bits, and computes both carry chains. Every selected row was checked against every generated term before export.

| Item | Value |
|---|---:|
| Public prefix | rowID, 9×7 radix512 input digits, 4×6 radix512 output digits |
| Public arity / output start | 88 / 64 |
| Matrix scalar groups / digits | 39 / 23 |
| Matrix rows / result columns / carry bits | 23 / 45 / 20 |
| Trace columns | 63,845 |
| Arithmetic assertions | 76,269 |
| ExactPublicRows lookups | one per row, table11 |
| Selected rows | 32, all distinct actual positions; no padding |
| Trace bytes | 8,172,160 |

[EXECUTED] Frozen artifact hashes:

- `artifacts/template_ir 2.json`: `66a 7e 92c 42525450458f 4a 4bd 0062ddd 43fb 4da 095b 476e 9ced 54940ad 56e 517`
- `artifacts/trace.leu 32`: `29d 91935adc 01233ed 674a 5f 8a 74bddb 12ef 79f 332457fe 655bd 186914611c 51`
- Source public rows: `0b 817b 8b 538062557a 5a 6add 1d 08ba 159b 1874afda 6e 3d 36ce 882993b 83f 87f 7`

[EXECUTED] `results/emission_002_command.json` and `emission_002.log` preserve the132.829s Lean emission/trace run. It checked all32 rows and rejected a changed output and a noncanonical radix digit. Earlier syntax/proof attempts are retained. A broad closed constant proof was stopped after98.162s; structural per-form capacity proofs succeeded. Two public-column expansion attempts were stopped after145.053s and83.587s; structural wire and zero-padding sum lemmas succeeded in about4s. Those stops do not establish kernel infeasibility.

## Reproduction and remaining trust boundary

[EXECUTED] `proposal.patch` adds only the eleven Compiler modules and the standalone emitter. Apply after the frozen predecessor formal compiler dependencies in an isolated minidregg checkout. The local `build/Compiler` overlay reuses previously checked dependency oleans; no companion source or shared target directory was changed. `results/checked_modules.json` is the precise module build order. `results/import_boundary.log` records the existing companion boundary script; new files are in Compiler, never imported by Theory or Selvage.

[OPEN] Kernel checking establishes the Lean source/gadget/word-model theorems. It does not prove Rust language execution, the native constructor implementation, serde parsing, canonical ciphertext-to-row extraction, NTT/basis conversion, extension or convolution, BFV encryption/noise correctness, or the proof protocol/PCS/backend implementation. The native constructor values and actual public row source binding are pinned executed inputs, not a Rust refinement theorem. The JSON fold serializer and existing Rust IR2/ExactPublicRows adapter remain in that executable trust boundary. The generic Nat-wire layout has no new proved index-bound theorem; the existing parser validated the finite emitted indices against nVars. No secret material was needed in this lane.

[OPEN] The immediate larger arithmetic step is proving or efficiently emitting all 24,576 positions, and joining this rescale to the actual extended-basis product/convolution and native output transform. The existing assertion-sharing compiler pass can reduce duplicated range assertions in a separate successor without changing these frozen artifacts.
