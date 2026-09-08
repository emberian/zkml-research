# One generated relation for complete BFV integer rescale

[EXECUTED] The actual prover/verifier consumed this Lean-generated relation and witness for every coefficient of a small BFV ciphertext multiplication's rescale stage. The instance has N8, three output components, 24 actual coefficient positions and 72 output RNS residues. Eight explicitly repeated positions with fresh row IDs pad the proof to 32 rows. The proof passes fresh-process verification; changing a public output is refused. See `../proved_rescale/results/{prove,verify,verify-changed-output}.stdout` and their saved commands.

[DERIVED] The new compiler step composes the existing exact six-input rounding certificate with all three target residue projections **inside one source constraint system**. Its integer output Y is shared before emission, and public input/output digits are aliases of the relevant internal variables. This replaces the prior separate-checker equality boundary for this executable path. It does not prove the preceding convolution or a complete ct×ct instruction.

## Exact source arithmetic, including directed rounding

[SOURCE] The actual operation is `Multiplicator::new(one,one,extended_basis,t/Q,par).multiply(a,b)`, without relinearization or modulus switching. The library performs extension, NTT products, conversion to PowerBasis and downscaling at `/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv/ops/mul.rs:159`. The RNS scaler's fixed-point Garner selection and correction are in `/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/fhe-math-0.1.1/src/rns/scaler.rs:239`.

[SOURCE] The inherited `FheRnsScaleDecomposition.lean` proves the exact directed fixed-point calculation for these constants and exhibits an actual nearest+1 result. The inherited `FheSourceCertificate` forces both integer quotient/remainder roundings and the output modulo Q; `FheTargetProjection` forces all three canonical target residues. The emitted relation therefore retains the actual algorithm's rounding decisions. It does not substitute ideal nearest-integer rounding or allow either neighboring answer.

[DERIVED] New theorem `BfvRescaleRow.rowSound` quantifies over **every** assignment to the combined source variables. Acceptance alone forces each public output residue to equal `FheRnsScale.deployedOutput(publicResidues) % targetPrime`. Canonicality and quotient/remainder bounds come from the generated source constraints. `source_public`, `shared_output`, and `target_public` prove the public and shared-variable bindings; `simplifiedSource_sound` covers the exact simplified system serialized to IR2. Existing `renameS` and its evaluation theorem are reused; no new evaluator is defined.

[EXECUTED] Three new Compiler modules compile separately with Lean 4.30.0. The ten exact `#guard_msgs` axiom reports are all `[propext, Classical.choice, Quot.sound]`. No new axiom, `sorry`, `native_decide`, old Checks runner, whole-tree build or large closed-witness kernel reduction is used. `joinedMatricesInhabited` reuses the cheap nonzero inherited matrix witnesses; `wrongNearestExcluded` universally rejects the incorrect 172480 output for the captured input whose actual output is 172481. Full source-assignment inhabitation is exercised by the executable producer and actual prover, separately from the kernel matrix witness. Commands, hashes and outputs are in `results/checked_modules.json`.

## Executable artifact

[EXECUTED] Base moduli are `[68719403009,68719230977,137438822401]`, t is 1032193, and the extended basis appends `[4611686018427322369,4611686018427289601,4611686018427215873]`. The small runtime uses this exact basis with the public constructor. This is an arithmetic instance, without a security claim for N8.

[EXECUTED] `EmitBfvRescale.lean` emits `artifacts/template_ir2.json` by an ordered `Signature.fold` of `simplifySystem system`, then writes `artifacts/trace.leu32`. `Compiler/BfvRescaleWitness.lean` provides one parameterized matrix witness producer for both inherited source layouts. It computes radix digits and carry chains from their existing matrices; it contains neither the downscaler formula nor replacement constraints. Aliased public values and shared Y are checked before installation, so the producer cannot overwrite the supplied actual output.

[EXECUTED] The public tuple has 88 columns: rowID, six extended-product PowerBasis residues in 11 little-endian radix 64 digits each, then three actual output PowerBasis residues in 7 digits each. Trace width is 37665; the fixed zero is column 88. The original source storage starts at 89 and target storage at 30383; unused original slots remain zero-filled holes. The source and target use existing compiler renaming to bind the public variables and shared Y.

[EXECUTED] The template has 45209 arithmetic constraints plus one ExactPublicRows lookup. The complete trace is 4,821,120 bytes (32×37665×4), row-major canonical BabyBear words encoded as little-endian u32. The producer checked every row and accepted the captured nearest+1 control; wrong-nearest and radix 64 controls were refused. `artifacts/emission.json`, `results/export_001.log` and `artifact_pins.json` record the exact handoff. Input is `../proved_rescale/results/case001/public_rows.json`.

[EXECUTED: runtime lane] The actual proof is 8,592,353 bytes, SHA256 `939cc8f8c3c2d24e2f5809b1fb4e50057aab72835744fb5aff529cccf67a63b2`. Saved runtime output reports 1.377 seconds proving and 0.408 seconds self-verification for this small 32-row instance. Fresh native verification and changed-public-output rejection are saved separately. These numbers do not estimate a full N4096 or N8192 proof.

## Apply and scope

[EXECUTED] `proposal.patch` contains only `Compiler/BfvRescaleRow.lean`, `Compiler/BfvRescaleWitness.lean`, `Compiler/BfvRescaleSound.lean` and `EmitBfvRescale.lean`. It applies to isolated scratch and produces byte-identical files (`results/patch_application.json`). Relevant inherited source and exact reused olean hashes are in `source_pins.json`. The existing read-only companion import-boundary script passes; this proposal changes no Theory/Selvage source. Root owns integration and commits. The finished weighted/expiry package is unchanged.

[SOURCE] Apply the existing `bfv_lift_refinement/engine_refinement`, `source_certificate` and `target_projection` compiler proposals and their dependencies first. The new pure proof entrypoint is `Compiler.BfvRescaleSound`; the producer is `Compiler.BfvRescaleWitness`. No old `*Checks.lean` module is imported.

```
lake env lean --run EmitBfvRescale.lean OUT_DIR PUBLIC_ROWS_JSON
```

[OPEN] The theorem concerns the exact Lean source arithmetic model and existing compiler refinements. Rust language semantics, scaler constructor/implementation correspondence, coefficient extraction, basis conversion, extension, convolution, encryption/noise correctness, JSON parsing, ExactPublicRows implementation, proof-protocol security and serialized-ciphertext binding remain outside this Lean theorem. The runtime lane records the actual public intermediate/outputs and prover execution. The full nonlinear learner's different 9→4 scaler parameters are not covered by this six-to-three instance. The separate cost-successor lane may optimize these fixed artifacts; no optimization result is assumed here.
