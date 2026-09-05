# Stage-0 Lane B — the lawful "reader" as generated glue: work 9103, `WORK_2_ROWS`, and the Rust evaluator

**2026-09-05. Lane B of `descriptor-reader-scout.md` §4, executed** on `/Users/ember/dev/minidregg`
branch `main` (HEAD `d43be5a`; Lane A's `b4f5f77` present). Nothing committed, no stash, no
`add -A`. Every `file:line` anchor in the brief was opened before use; all held
(`SemanticArtifactBundle.lean:254/:262`, `NativeGlueGen.lean:66/:72/:85/:120/:196/:371`,
`ArithmeticNativeDeployment.lean:326–331`, `NativeKernelPlan.lean:52/:86/:100/:258/:351`,
`BignumKernelABI.lean:98`, `EvmAddAir.lean:290/:304/:589/:597`). The process died once mid-work
(machine hard-fault ~03:15); the two Lean edits on disk were re-read and continued from.

**One STOP.** `prover/src/lib.rs` needs the generated module mounted (§6). Not made. In-tree
`cargo check -p minidregg-prover --tests --offline` is therefore RED at exactly one error
(`E0432 unresolved import crate::evm_stage0_add_aux`, `native_dispatch.rs:14`) until those lines
land — **this blocks the co-tenant's cargo builds in this tree too.** The same crate copied to the
scratchpad with the two lines added is green: `cargo check --tests` clean, the one test
**4/4, all five vectors byte-identical** (§5).

## 1. The decision-doc line, quoted, and the shape it forced

`docs/decisions/2026-08-09-rust-native-authority.md`, "Hard invariants": **"Rust does not parse
the authoritative semantic request, construct a receipt/history entry, draw protocol challenges,
or choose a proof relation."** And "Deleted authority islands": **"... descriptor satisfaction,
and WGPU FRI. They must not be reintroduced as handwritten parallel protocol profiles."**
Permitted: "(1) mechanically generated artifact constants, DTOs, identifiers, and bytes/error
dispatch; and (2) handwritten opaque arithmetic ... candidate computation selected by a
Lean-owned plan."

So: no reader, no `descriptor_holds`. The descriptor's 3,298 gates are EMITTED by `NativeGlueGen`
as a Rust constant (`WORK_2_ROWS`, tuples `(op, aKind, a, bKind, b, out)`), the way
`babyBearAdd1ZeroCandidateBytes` already emits a tag-selected constant; the kernel tag selects
`EvmAddAir.evmAddDescriptor` at generation time (`NativeGlueGen` now imports `Compiler.EvmAddAir`;
no cycle — nothing in `EvmAddAir`'s closure imports the generator). Rust evaluates the rows in
order over the 833 request words and returns 4,131 words; the reply is judged only by
`descriptorHoldsCheck` inside `checkInstruction`, on the Lean side of the plan.

## 2. The Lean statements added (copied)

`Compiler/SemanticArtifactBundle.lean` — `KernelTag.evmStage0AddAux`;
`ByteCodecShape.evmStage0AddVarsU32LE` (833 words, 3,332 B) and `.evmStage0AddWiresU32LE`
(4,131 words, 16,524 B); JSON names `evm_stage0_add_aux`, `evm_stage0_add_vars_u32_le`,
`evm_stage0_add_wires_u32_le`.

`Compiler/NativeGlueGen.lean` — arms in `responseWidth`, `requestShapeConstants`,
`kernelFunction` (→ `"crate::native_dispatch::evm_stage0_add_aux_bytes"`), `kernelConstructor`,
`benchmarkConstants`, `fixedCandidateConstants`; `workConstants` now appends
`descriptorRowConstants`, which for the Stage-0 tag emits `WORK_n_FIELD_MODULUS`,
`_DESCRIPTOR_N_PUBLIC/_N_VARS/_N_WIRES`, `_ROWS`, `_ZEROS`. The row encoding is a Lean object
with its own theorem:

```lean
def evmStage0RequestWords : Nat := 833
def evmStage0ResponseWords : Nat := 4131

structure GateRow where
  op : Nat; aKind : Nat; a : Nat; bKind : Nat; b : Nat; out : Nat

def rowOfGate (g : DGate BabyBear) : GateRow       -- op 0 = add / 1 = mul; operand (0, val) | (1, index)
def gateOfRow (row : GateRow) : Option (DGate BabyBear)

/-- The row table is a faithful image of the gate list: decoding any gate's tuple returns it. -/
theorem gateOfRow_rowOfGate (gate : DGate BabyBear) : gateOfRow (rowOfGate gate) = some gate
```

`Compiler/EvmStage0NativeDeployment.lean` — NEW (≈ 700 lines), imports
`Compiler.ArithmeticNativeDeployment`, `Compiler.DescriptorEval`. Registration:

```lean
def requestCodec  : ByteCodecProfile   -- nativeAbi 9007 / valueType 9008 / v1 / evmStage0AddVarsU32LE
def responseCodec : ByteCodecProfile   -- nativeAbi 9009 / valueType 9010 / v1 / evmStage0AddWiresU32LE
def workProfile : WorkProfile          -- workId 9103, carrier 206, kernel .evmStage0AddAux
theorem work_profile_pins_exact : workProfile.workId = 9103 ∧ workProfile.carrierProfileId = 206 ∧
    workProfile.requestCodec.codecId = 9007 ∧ workProfile.responseCodec.codecId = 9009 ∧
    workProfile.kernel = .evmStage0AddAux

theorem descriptor_nPublic : evmAddDescriptor.nPublic = 48 := rfl
theorem descriptor_nVars  : evmAddDescriptor.nVars = evmStage0RequestWords := rfl
theorem descriptor_nWires : evmAddDescriptor.nWires = evmStage0ResponseWords := evmAddDescriptor_shape.2.1

def segments : List WireSegment        -- x,y,z public radixLimbs 16 at 0/16/32; x_bits,y_bits,z_bits witness at 48/304/560 (256); carry witness at 816 (17)
def call : KernelCall := { abiVersion := 1, entry := .constraintDescriptorV1, segments, calls := [], descriptor := evmAddDescriptor }
theorem call_fullyWellFormed : call.FullyWellFormed

def publicInputs (X Y Z : ℕ) : List BabyBear := (List.finRange 48).map (encodeBoundary X Y Z)
def clause : DialectClauseDecl         -- clauseId 407, relation 417, carrier 206, dialect codecs 16/17, suite 427
def instruction (X Y Z : ℕ) : Instruction := Instruction.arithmetic clause.clauseId call (publicInputs X Y Z)

def manifest : Manifest := { MinidreggV1ArithmeticWork.manifest with dialectClauses := … ++ [clause] }
theorem clause_registered : manifest.lookupClause clause.clauseId = some clause
theorem manifest_wellFormed : manifest.WellFormed

def artifact : ArtifactBundle := pack.extendArtifact ArithmeticNativeDeployment.artifact   -- catalog [9101, 9102, 9103]
theorem artifact_contains_exact_native_surface :
    requestCodec ∈ artifact.nativeAbiCodecs ∧ responseCodec ∈ artifact.nativeAbiCodecs ∧
    workProfile ∈ artifact.nativeWorkCatalog
theorem work_9103_pinned : ∀ work ∈ artifact.nativeWorkCatalog, work.workId = 9103 → work = workProfile
theorem work_9104_absent : ∀ work ∈ artifact.nativeWorkCatalog, work.workId ≠ 9104
theorem artifact_nativeCatalogWellFormed :
    NativeCatalogWellFormed artifact.manifest artifact.nativeAbiCodecs artifact.nativeWorkCatalog
theorem registry_wellFormed : registry.WellFormed artifact.manifest
def deployment : DeploymentJoin        -- artifact, registry, the three closures
theorem resolved_controller_exact : resolved.controllerEntry.declaration = clause
```

The plan-level witness and falsifiers (the honest response is Lane A's `evmAddCandidate`; `Z`
enters only through the instruction's type):

```lean
def honestResponse (X Y Z : ℕ) : KernelResponse (instruction X Y Z)
theorem honestResponse_accepts (X Y Z) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) :
    (instruction X Y Z).call.Accepts (honestResponse X Y Z).totalWires
theorem honestResponse_prefix (X Y) :
    PublicPrefixExact (instruction X Y ((X + Y) % 2 ^ 256)) (honestResponse X Y ((X + Y) % 2 ^ 256))

/-- Witness. -/
theorem honest_certified (X Y) (hX) (hY) : ∃ certificate,
    checkInstruction manifest (instruction X Y ((X + Y) % 2 ^ 256)) (honestResponse X Y _) = .inr certificate
/-- Falsifier at the public prefix: a claimed Z that is not the wrapped sum, on the HONEST reply. -/
theorem forged_claim_refused (X Y Z) (hX) (hY) (hZ : Z < 2 ^ 256) (forged : Z ≠ (X + Y) % 2 ^ 256) :
    checkInstruction manifest (instruction X Y Z) (honestResponse X Y Z) = .inl (.publicPrefixMismatch clause.clauseId)
/-- Falsifier at the clause: an unregistered clause id is refused before any descriptor check. -/
theorem unregistered_clause_refused (X Y Z) (response) :
    checkInstruction manifest (Instruction.arithmetic (MinidreggV1Artifact.id 408) call (publicInputs X Y Z)) response
      = .inl (.unregisteredClause (MinidreggV1Artifact.id 408))
theorem malformed_bytes_cannot_certify (claim) (wrongWidth : bytes.length ≠ 4 * evmStage0ResponseWords) :
    ¬ ∃ response certificate, byteController.check claim bytes = .certified bytes response certificate
theorem native_error_blocks … : DialectClauseDispatch.run resolved input oracle = .blocked failure
```

`byteController : DialectController clause` — `Input := Claim (X Y Z)`, `issue := requestBytes X Y`
(the 833 words of `evmAddAsg`, `requestBytes_length : = 4 * 833`), `check := decodeResponse` (exactly
16,524 bytes → 4,131 canonical words, else `none`) then `checkInstruction`. Why a new clause 407
rather than 406: `MinidreggV1ArithmeticWork.controllerDeclaration` pins clause 406 to
`arithmeticCall` (`addKernelCall 1 1`); a second call under it would contradict `declaration_exact`.

Axiom pins (all `#guard_msgs`, matched): `honest_certified`, `forged_claim_refused`,
`unregistered_clause_refused`, `call_fullyWellFormed`, `artifact_nativeCatalogWellFormed`,
`registry_wellFormed`, `work_9103_pinned`, `work_9104_absent`, `malformed_bytes_cannot_certify`,
`resolved_controller_exact` → `[propext, Classical.choice, Quot.sound]`; `manifest_wellFormed` →
`[propext, Quot.sound]`; `gateOfRow_rowOfGate` (NativeGlueGen) needs no pin change to that file's
existing guards. No `sorry`, no axiom.

Compiled exhibits with teeth (the Lane A idiom, an `#eval` that throws): Lane A's five anvil vectors
through `byteController` on Lean's own honest bytes → **certified** ×5 (each also checks the issued
request is the reply's 3,332-byte prefix); `⟨2²⁵⁶−1, 5, claimed 5⟩` → **rejected
(publicPrefixMismatch)**; V1 reply with wire 833 `+1` (mutation asserted) → **rejected
(descriptorRejected)**; V1 reply minus one word → **malformedResponse**.

A lesson paid for in three build rounds: any tactic that lets the elaborator *evaluate*
`evmAddDescriptor.nWires` or `evmAddCandidate` as a closed term (`simpa`, `split`'s discharger,
`rw`'s closing `rfl` on `≤`) runs the 3,298-gate flattening at elaboration and times out. The
response lemmas are therefore stated over a VARIABLE instruction and array
(`responseOfArray_totalWires`, `responseOfArray_prefix`) and instantiated by term-mode chains through
the kernel-decided `evmAddDescriptor_shape` (`instruction_nWires`).

## 3. What was regenerated

- `prover/generated/evm_stage0_add_aux.rs` — NEW, 239 lines, **124,680 B**, written by
  `#eval rustBuildTarget.run` (`EvmStage0NativeDeployment.rustBuildTarget`, path
  `prover/generated/evm_stage0_add_aux.rs`). Catalog `[9101, 9102, 9103]` → `WORK_0/1/2`; `Work2`
  tag, constructor `evm_stage0_add_aux`, dispatch arm →
  `crate::native_dispatch::evm_stage0_add_aux_bytes`, `WORK_2_RESPONSE_WIDTH = 16524`,
  `_REQUEST_WIRE_COUNT = 833`, `_FIELD_MODULUS = 2013265921`, `_DESCRIPTOR_N_PUBLIC/N_VARS/N_WIRES =
  48/833/4131`, `WORK_2_ROWS`: **3,298 tuples = 1,665 add + 1,633 mul** (first
  `(0, 1, 48, 0, 2013265920, 833)`, last `(0, 1, 4126, 1, 4129, 4130)`), `WORK_2_ZEROS`: **850**,
  all wire operands. The artifact's embedded canonical JSON now carries the three works and five
  native codecs.
- `prover/src/semantic_artifact_arithmetic.rs` — re-emitted by the rebuilt
  `ArithmeticNativeDeployment`, **byte-identical** (git clean; its catalog is unchanged and the new
  constants are empty for its tags). `prover/generated/semantic_artifact_v1.rs` was not in my
  targets; the umbrella will re-emit it identically for the same reason.
- ⚑ Deviation from the brief: `WORK_n_ZEROS` is `&[(u8, u32)]` (kind, value), not `&[u32]` — a
  `DWire.cnst` zero-check has no `u32` index; the pair keeps the emitter total. All 850 here are
  `(1, wire)`. Rust does not evaluate zeros (that is the checker's job); the test counts them.

## 4. The Rust

`prover/src/native_dispatch.rs` (+158 lines): eight new `NativeDispatchError` variants
(`FieldModulus`, `HeaderShape`, `WordAboveModulus`, `ReadBeforeWrite`, `Rewrite`, `WireOutOfRange`,
`RowEncoding`, `UnwrittenWire` — local errors, no verdict), and

```rust
pub type DescriptorRow = (u8, u8, u32, u8, u32, u32);
pub fn evaluate_descriptor_rows(rows: &[DescriptorRow], n_vars: usize, n_wires: usize,
    modulus: u64, request: &[u8]) -> Result<Vec<u8>, NativeDispatchError>
pub fn evm_stage0_add_aux_bytes(request: &[u8]) -> Result<Vec<u8>, NativeDispatchError>
```

The generic evaluator decodes `4·n_vars` LE bytes (word ≥ p → error), visits rows in order
(constant or already-written wire operands; `badd`/`bmul` from `babybear`; write to a fresh wire,
`Rewrite`/`ReadBeforeWrite`/`WireOutOfRange` otherwise), refuses a table over another modulus, and
refuses to fabricate a default for a wire no row wrote. The brief-named wrapper binds
`WORK_2_ROWS`/`_N_VARS`/`_N_WIRES`/`_FIELD_MODULUS`. No zero-check is evaluated; no descriptor is
parsed.

## 5. The test

`prover/tests/evm_stage0_dispatch.rs` — a `deny_unknown_fields` serde mirror of Lane A's eleven-key
witness schema (serde/serde_json were already dev-dependencies; nothing added). Run in the scratch
copy with the lib.rs mount, `cargo test --test evm_stage0_dispatch --offline`:

| test | result |
|---|---|
| `generated_constants_pin_the_stage0_shape` (**control: counts unchanged** — 3,298 rows = 1,665 add + 1,633 mul, 850 zeros, 833/48/4131, SSA order, pins 9103/206/9007/9009, modulus = `P`) | ok |
| `dispatch_reproduces_the_lean_written_wires_on_all_five_vectors` — V1..V5 through `from_ids` + `dispatch_native`: reply **byte-identical** to the Lean-written 4,131 words (16,524 B each); variable prefix echoed | ok, **5/5** |
| `unregistered_work_id_and_wrong_pins_are_refused_by_the_generated_constructor` (9104 → `UnsupportedWork`; carrier 205 → `MalformedRequest`) | ok |
| `local_error_shapes_are_errors_not_verdicts` (short request, word = p, and at the generic evaluator: read-before-write, rewrite, unwritten wire, foreign modulus; the honest 1-row table `7 + 1 = 8`) | ok |

`4 passed; 0 failed`, `cargo check --tests --offline` clean (no warnings). Vector agreement, never
verification: there is no semantics of Rust here.

## 6. The edit I stopped at (exact)

`prover/src/lib.rs` — after the `include!("../generated/uwueave_preo_projection_v2.rs");` block
(or beside the `semantic_artifact_v1` mount):

```rust
// Generated by Lean from `Compiler.EvmStage0NativeDeployment`: the Stage-0 (EVM u256
// add) work 9103, its gate-row table, DTOs, and opaque dispatch. Data and transport only.
#[path = "../generated/evm_stage0_add_aux.rs"]
pub mod evm_stage0_add_aux;
```

Also for the coordinator (not mine to touch): `Compiler.lean` needs
`import Compiler.EvmStage0NativeDeployment` — suggested after `import Compiler.DescriptorEval`
(it imports `ArithmeticNativeDeployment` and `DescriptorEval`, both already rooted). Its elaboration
ran **301 s** on this laptop at load ≈ 18 (the eight exhibits fill five 4,131-wire candidates and
the build target renders 3,298 rows) — laptop wall-clock, evidence of nothing.

## 7. Exact file list, and status

Modified: `Compiler/SemanticArtifactBundle.lean` (+13), `Compiler/NativeGlueGen.lean` (+127),
`prover/src/native_dispatch.rs` (+158). New: `Compiler/EvmStage0NativeDeployment.lean`,
`prover/generated/evm_stage0_add_aux.rs` (generated), `prover/tests/evm_stage0_dispatch.rs`,
`/Users/ember/dev/zkml-research/notes/stage0-lane-b.md`. Not touched: `prover/src/lib.rs`,
`prover/Cargo.toml`, `Compiler.lean`, `Compiler/UwueavePreoProjectionV2.lean`,
`prover/generated/uwueave_preo_projection_v2.rs`, `LICENSE*`, `NOTICE`, `docs/**`,
`Compiler/ArithmeticNativeDeployment.lean`, `Compiler/MinidreggV1Artifact.lean` (the re-pin did not
need them: the new deployment stacks on `ArithmeticNativeDeployment.artifact`).

Elaboration: `lake build Compiler.SemanticArtifactBundle Compiler.NativeGlueGen
Compiler.EvmStage0NativeDeployment` green, zero warnings in the touched modules (the
`ArithmeticNativeDeployment.lean:92` `simpa` lint is pre-existing); `scripts/check-import-boundary.sh`
green. ⚑ Confession: my second targeted build overlapped a coordinator `lake build Minidregg`
(pid 21478) for part of its run — I ran `pgrep` in the same command instead of waiting; both
completed, no conflict observed, but it was the wrong order. Cargo: in-tree red at the one
unmounted import (§0); scratch copy with §6 applied green, 4/4.

## 8. Residuals

- `honest_certified` is at the response level; the byte-level round trip
  `decodeResponse (honestBytes X Y) = some (honestResponse …)` for all `X Y` is not a theorem (it
  needs a `decodeWords ∘ flatMap encodeWord` lemma over `Bignum.digitsLE`); it is exhibited on the
  five vectors and on the tamper/short cases.
- The 785 witness words still come only from Lean (`evmAddAsg`); the Rust side never generates
  them — as the scout required.
- `EmitSerialize.lean:190` still cites the deleted `prover/tests/conformance.rs` (scout §5); not
  fixed here.
