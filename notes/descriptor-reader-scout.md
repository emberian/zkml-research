# Descriptor-reader scout — Stage 0 (EVM u256 add) through minidregg's native seam

**2026-09-04. Scout only; nothing built.** Charge: SLVG_THOUGHT §IV-e ("one Rust descriptor
reader closes routability, the units question, and Stage-0 time-to-proof together"), under the
law *the derived path is the ONLY path: Rust is generated glue or opaque fallible computation,
never a semantics*. Read: minidregg `CLAUDE.md`, `ATLAS.md` §0–7, `PROJECT.md` §Native, the two
commits in full, `Compiler/{Emit,EmitSerialize,EmitShare,EvmAddAir,NativeKernelPlan,
NativeGlueGen,BignumKernelABI,ArithmeticNativeDeployment,GateMleExt6,Ext6GateProofController}`,
`prover/src/*`, `prover/generated/*`, `docs/decisions/2026-08-09-rust-native-authority.md`,
breadstuffs `circuit/src/{lean_descriptor_air,descriptor_ir2,descriptor_proof_backend}.rs`.
`cargo check --tests --offline` in `prover/` is green (4.8 s). **Verdict in one line: the reader
alone buys routability and units; time-to-proof is blocked on a Lean-emitted PCS
(`GateMleExt6.CommittedTerminal`) that no lane closes tonight — §3(c), §4.**

## §1. What was deleted, and why (quoted)

Both commit messages are one line each; the reasons live in the deleted files' own headers,
the replacement's header, and the decision record written two hours later.

**`d55ef32` 2026-08-09 07:53 "prover: delete handwritten descriptor and trace semantics"**
(-94 `descriptor.rs`, -67 `trace.rs`; `gate_kernels.rs` rewritten). What died:
- `descriptor.rs`: a serde reader whose types were *twins* — "Mirror of
  `Minidregg.Compiler.GateOp`", "Mirror of `DWire`", "Mirror of `ConstraintDescriptor`,
  plus the field modulus the Lean writer stamps" — and `Descriptor::from_json_str/from_file`.
- `trace.rs`: `generate_trace(d, vars) -> Vec<Fp>` evaluating gates in emission order, and (per
  the 16fe1b0 landing message) "`descriptor_holds = gates_hold && zeros_hold`, a literal
  index-by-index mirror of the Lean `descriptorHolds`".
- The replacement drew the line: `gate_kernels.rs` header became "Explicit low-level compute
  work. The native boundary receives already materialized rows and buffers; **it performs no
  file or byte-format decoding**." `lib.rs`: "Inputs are explicit low-level work data; outputs
  are buffers or local execution errors."
- `GOAL.md:1159`: "**RETRACTED native descriptor interpreter**… The former Rust descriptor
  reader, trace generator, and `descriptor_holds` mirror were diagnostic conformance code with
  no semantics and were deleted."
- `docs/decisions/2026-08-09-rust-native-authority.md`: "Rust does not parse the authoritative
  semantic request… Deleted authority islands: … **descriptor satisfaction**, and WGPU FRI.
  They must not be reintroduced as handwritten parallel protocol profiles." Permitted: "(1)
  mechanically generated artifact constants, DTOs, identifiers, and bytes/error dispatch; and
  (2) handwritten opaque arithmetic… candidate computation selected by a Lean-owned plan."
- ⚑ The replacement itself was deleted within five hours: `8a2ab17` 08:10 "delete handwritten
  local plan ABI" (`LowLevelComputePlan`, -369), `dd81749` 08:16 "delete handwritten factored
  gate profile" (-157, the 7-operand-table kernels of `GateFactoredExt6`), `345a0ca` 08:28
  "delete orphan sumcheck mirror" (file gone). A Rust struct describing a plan is a twin of the
  Lean plan; the surviving shape is *generated* constants + one opaque `fn(&[u8]) -> bytes`.

**`b297c7d` 08:19 "prover: retire the unowned Ext4 FRI GPU island"** (-2,551: `fri.rs`,
`field4.rs`, `gpu.rs`, `shaders/fri_fold.wgsl`, `bin/fri_fold_bench.rs`, `fri_conformance.{rs,
json}`, `gpu_fold_conformance.rs`; wgpu/pollster/bytemuck/serde deps). `fri.rs` header: "This is
UNVERIFIED COMPUTE. **Rust selects the field representation, domain order, pair order, twiddle
convention, and beta-squaring schedule** used here. No compiled generated adapter currently
pins those choices or connects this module to Lean-owned control… There is no refinement
theorem or semantic relation for this Rust." `Cargo.toml`: "deliberately outside the generated
protocol core; future acceleration is chosen for the protocol actually deployed rather than
inherited from this experiment." `Emit.lean` residuals today: "The historical Rust descriptor
reader and BabyBear⁴/FRI/WGPU path were deleted; no current native module consumes this
descriptor."

**The line, exactly.** Deleted = (i) Rust type-mirrors + parsers of Lean types, (ii) a Rust
satisfaction predicate, (iii) protocol conventions chosen in Rust. Kept/permitted = generated
constants and dispatch; opaque candidate compute over *Lean-materialized* rows whose reply Lean
re-checks. A "descriptor reader" in `src/` that parses the JSON is (i) verbatim.

## §2. The emit→consume map today

| Lean def | artifact | consumer |
|---|---|---|
| `Compiler/Emit.lean:79–105` `DWire`/`DGate`/`ConstraintDescriptor`; `:127` `descriptorHolds` (`Decidable` `:133`); `emit`, `emit_faithful`, `emit_accepts_iff_fin`, `emit_wellFormed` | — (Prop + first-order data) | every theorem below |
| `Compiler/EmitShare.lean:317` `ConstraintDescriptor.SSA`; `:552` `emit_ssa` | — | the aux-filler's hypothesis (§4) |
| `Compiler/EmitSerialize.lean:108` `descriptorToJson`; `:147` `descriptorFromJson?`; `:159` `writeDescriptorJson`; `:237` writes `demo_descriptor.json` | `prover/testdata/demo_descriptor.json` (23 wires) | ⚠ none — `:190` still cites `prover/tests/conformance.rs`, deleted in d55ef32 |
| `Compiler/EvmAddAir.lean:290` `evmAddWires` (X 0–15, Y 16–31, Z 32–47 public; bits 48–815; carries 816–832); `:300` `evmAddSystem := addModGadget`; `:304` `evmAddDescriptor := emit Fin.val 48 833 evmAddSystem`; `:334` `evmAddAsg : Fin 833 → BabyBear` (computable witness-gen); `:513` `evmAddDescriptor_means_semantics`; `:589` `_wellFormed`; `:597` shape 3298/4131/850 (`decide +kernel`); `:650/:658/:673` V1, V3-wrap satisfiable, forgery refused — all via the meaning theorem, **never by evaluation**; `:697` `#eval writeDescriptorJson` | `prover/testdata/evm_stage0_add_descriptor.json` — 231,487 B, landed `8c5a732` 2026-08-17 | **none.** `grep -rn 'evm_stage0\|EvmAdd' prover/` → nothing; serde_json is a *dev*-dep ("Test-only: reading the Lean-authored conformance vectors"); no test reads it; no Lean consumer of `evmAddDescriptor` outside its file. `notes/evm-stage0.md` residual 7 says so. |
| `Compiler/NativeKernelPlan.lean:52` `Instruction {kind, clauseId, call : KernelCall, publicInputs}`; `:86` `KernelResponse.wires : Fin nWires → BabyBear`; `:100` `PlanRunner := (i : Instruction) → Except Error (KernelResponse i)`; `:258` **`descriptorHoldsCheck : ConstraintDescriptor BabyBear → (ℕ → BabyBear) → Bool`**, `:265` `_eq_true_iff`; `:351` `checkInstruction` | — | the ONLY executable descriptor checker; the derived path's judge |
| `Compiler/BignumKernelABI.lean:98` `KernelCall {abiVersion, entry := .constraintDescriptorV1, segments, calls : List WitnessCall, descriptor}`; `:108` `Accepts := descriptorHolds`; `:298` `addKernelCall w b` = `emit … (AirBignum.addGadget …)` (top carry PINNED — not `addModGadget`) | — | work 9102 |
| `Compiler/NativeGlueGen.lean:196` `rustSourceFromEncoding`; `:85` `kernelFunction : KernelTag → "crate::native_dispatch::…_bytes"`; `:66` `responseWidth`; `:111` `babyBearAdd1ZeroCandidateBytes` (Lean-emitted 144 B); `:371` `BuildTarget` | `prover/generated/semantic_artifact_v1.rs` (via `MinidreggV1NativeGlue.buildTarget`, `#eval` at build); `prover/src/semantic_artifact_arithmetic.rs` (via `ArithmeticNativeDeployment.rustBuildTarget :326–331`) | `prover/src/native_dispatch.rs:62` `tower256_dot_product_bytes`, `:103` `baby_bear_add1_zero_witness_bytes`; `lib.rs:12` `#[path]` include |

Census of the Stage-0 JSON (this scout, Python over the file): **3,298 gates = 1,665 add +
1,633 mul; 850 zero-checks; 4,131 wires; 833 vars, 48 public**; 1,681 constant operands over 19
distinct constants (`−1 = 2013265920` ×849; 1,2,4,…,32768 ×48 each); 4,915 wire operands;
outputs strictly increasing 833→4130 and no gate reads a wire ≥ its own output (exactly
`emit_ssa`); 849 zero-checks read aux wires, one reads var 816 (the carry₀ pin).

**Shape of the derived path for descriptors — it already exists, at n=1.** Work `9102`: Lean
`Instruction` with `addKernelCall 1 1` (36 wires) → generated dispatch → Rust returns a FIXED
Lean-emitted 144-byte candidate → Lean decodes 36 words → `descriptorHoldsCheck` →
`CertifiedResponse`/`Verified` (`ArithmeticNativeDeployment.lean`, decision §"Current controller
examples"). The Stage-0 descriptor is not registered on it: `WitnessCall` has only
`add`/`scalarMulConst` and `addKernelCall` builds `addGadget`, not `addModGadget`.

## §3. The three options, with the law applied

**(a) A reader in minidregg's prover for its own JSON.** Verbatim d55ef32's `descriptor.rs`;
forbidden in `src/` by the decision ("does not parse the authoritative semantic request";
"descriptor satisfaction… must not be reintroduced"). Two lawful forms:
- (a1) *test-only* serde reader under `prover/tests/` — the sanctioned pattern
  (`tests/sumcheck_conformance.rs:22–35` mirrors a Lean-written file with `deny_unknown_fields`).
  Gets Rust vector-agreement on the five vectors; adds no capability toward proof.
- (a2) **the reader as generated glue**: extend `NativeGlueGen` so the descriptor's rows are
  emitted as Rust *constants* beside a new `KernelTag`; Rust never parses, it evaluates rows
  over Lean-supplied var words and returns candidate words that `descriptorHoldsCheck` judges.
  This is the "reader" the law permits, and it closes routability through the real boundary.
- ⚑ Neither form can generate the *witness*: 785 of the 833 variables (768 range bits + 17
  carries) are witness vars, not gate outputs; only `evmAddAsg` knows them. A Rust bit/carry
  generator is a twin of `evmAddAsg` — `trace.rs` again. Witness-gen stays in Lean.
- (a) does **not** buy time-to-proof: there is nothing in `prover/src` to hand a trace to.

**(b) Bridge to breadstuffs' interpreter.** breadstuffs v1: `LeanDescriptor {name, trace_width,
constraints: [{lhs, rhs}]}` with `LeanExpr = Var|Const(i64)|Add|Mul`, `parse_descriptor(json)`
(`lean_descriptor_air.rs:672`), `build_trace(desc, &[i64])` (`:916`, one row at
`MIN_TRACE_HEIGHT`), `prove_descriptor`/`verify_descriptor` (`:971/:982`, `p3-uni-stark`,
`create_config` = `PROD_FRI_LOG_BLOWUP 3`, `NUM_QUERIES 38`, `QUERY_POW_BITS 16`,
`plonky3_prover.rs:108–118`). Header marks it RETIRED/IR-v1 but it is compiled and evaluated
(air-interpreter.md §4). Translation is mechanical: gate → `{lhs: op(a,b), rhs: var(out)}`,
zero → `{lhs: var(w), rhs: const 0}`, `trace_width 4131`. ⚠ v1 has **no public inputs**
(`:977` "No public inputs for the PART-I per-row gate class"): the proof binds "∃ wire
vector", not `encode(X,Y,Z)`. IR-v2 (`descriptor_ir2.rs`: `pi_binding`, `public_input_count`,
`prove_vm_descriptor2`) binds PIs but needs its own grammar. Law (STEERS §4): a throwaway
differential oracle, never the trust path → lives in zkml-research scratch or a breadstuffs
test, never in minidregg; yields a **labeled** proof-bytes + latency number and an
accept/reject differential against Lean's `descriptorHoldsCheck` on the same vectors.

**(c) A proof backend minidregg does not have.** Lean has, for BabyBear descriptors:
`GateMleExt6` (γ-batched residual MLE), `GateFactoredExt6` (7 operand tables),
`GateTraceRelationExt6`, `Ext6GateProofController` (cSHAKE Fiat–Shamir, `Accepts`, `run` over
`OpaqueProofRunner := List UInt8 → Except Error (List UInt8)`, `:345/:361`), `…Deployment`,
`…PositiveRun` — ~2,400 lines, all `noncomputable section` because `Ext6Q := AdjoinRoot
ext6Polynomial` (`Ext6Conformance.lean:252`). Its PCS is an explicit hole:
`GateMleExt6.lean:246 structure CommittedTerminal … factoredSelectorOpening : value = mle
(gammaResidualTable d wv enc gamma) r` — "The forthcoming Mobius/FRI assembly constructs this
record." The Tower256 additive-FRI controller (718+546+567 lines) is over GF(2²⁵⁶), lists
"executable checker" among its residuals, and has no BabyBear carrier bridge. Rust: no FRI
(b297c7d), no 7-table kernels (dd81749); `sumcheck.rs` is degree-1/3 with caller-supplied
challenges and no commitment; `hash_kernels.rs` is raw cSHAKE. **Missing Lean object:** (1) a
computable `Ext6` carrier for the controller (the lane multiplication in `Ext6Conformance` is
already proved equal to `AdjoinRoot` multiplication — a representation swap, not new math);
(2) a realizer of `CommittedTerminal` — a BabyBear/Ext6 PCS (FRI or Basefold + Merkle over the
existing cSHAKE) with its Lean controller. By analogy to the Tower256 stack: ~1.8K lines of
Lean, ~0.5K lines of opaque Rust (fold/Merkle kernels), plus the reductions `PROJECT.md`
lists as residual (PCS, subfield, proximity, binding, ROM, sampling-bias, final LDT). Not a
tonight lane; it is `PROJECT.md` "Ordered frontier" item 3.

## §4. The build brief — what a Fable lane can close tonight, and the blocker

**Honest framing:** Stage-0 time-to-proof on minidregg's own path is blocked on §3(c). Lanes A
and B close routability + units in the lawful shape; Lane C gets a labeled oracle number.

### Lane A — Lean: the routability closure (no Rust; do this first)
New `Compiler/DescriptorEval.lean` (imports `Compiler.EvmAddAir`, `Compiler.NativeKernelPlan`).
1. `def fillAux (d : ConstraintDescriptor BabyBear) (vars : Array BabyBear) : Array BabyBear`
   — `arr := vars ++ mkArray (d.nWires − d.nVars) 0`; walk `d.gates` in list order,
   `arr := arr.set! g.out (g.op.denote (read g.a) (read g.b))`, reads via `arr.getD _ 0`.
   Theorem (worth having, not required for the exhibits since the checker judges):
   `fillAux_gates_hold (hssa : d.SSA) (hwf : d.WellFormed) (h : vars.size = d.nVars) :
   ∀ g ∈ d.gates, g.holds (fun i => (fillAux d vars).getD i 0)`; hypotheses discharged by
   `emit_ssa` (`EmitShare.lean:552`) and `evmAddDescriptor_wellFormed` (`EvmAddAir.lean:589`).
2. `def evmAddCandidate (X Y : ℕ) : Array BabyBear := fillAux evmAddDescriptor (Array.ofFn
   (evmAddAsg X Y))`; `def evmAddClaimed (X Y Z : ℕ)` = same but wires 32–47 overwritten by
   `encodeBoundary X Y Z` (the forgery shape of `evmAdd_forged_refused`).
3. Exhibits as `#eval` (compiled; **never `decide`** — law 9: graded non-vacuity witnesses
   beside the existing theorems, not new theorems): `descriptorHoldsCheck evmAddDescriptor
   (fun i => c.getD i 0) = true` for the five anvil vectors of `Theory/EvmFragment.lean:161–195`
   — V1 (1, 2 → 3); V2 (0x243f6a88…ec4e6c89, 0x452821e6…b5470917 → 0x69678c6e…a19575a0);
   V3 (2²⁵⁶−1, 5 → 4); V4 (0xfedcba98…76543210, **Y = 0x1122334455667788 · 2¹⁹²** — the
   descriptor sees the zero-padded CALLDATALOAD word; the padding is the machine's fact,
   covered by `fragment_faithful`, not by the descriptor → 0x0ffeeddc…76543210); V5 (0, 0 → 0);
   and `= false` for `evmAddClaimed (2²⁵⁶−1) 5 5` and for one single-wire `+1` tamper of V1.
   Any `false` on an honest vector or `true` on a forgery throws → elaboration fails (teeth).
4. Write the five candidate vectors (4,131 canonical words each) with a sibling of
   `writeDescriptorJson` to `prover/testdata/evm_stage0_add_witness_v{1..5}.json` — the
   Lean-authored conformance vectors Lane B reads (the `EmitSerialize` precedent).
5. **Units, exact tier (the whole answer for Stage 0 in this dialect):** one u256 add =
   3,298 degree-≤2 gates (1,665 add / 1,633 mul mod p), 4,131 wires, 850 boundary pins, 768 of
   833 witness vars are range bits. A check = 3,298 gate evals + 850 reads. `notes/evm-stage0.md`
   already warns Nebula's R1CS units are incomparable; do not re-derive §8 pricing from this.
   `#eval` wall-clock, if mentioned at all, is labeled "laptop script wall-clock, evidence of
   nothing" (forcodex/03-MEASUREMENTS §0).
Gate: `lake env lean Compiler/DescriptorEval.lean`; if the `Compiler.lean` umbrella is touched,
full `lake build Minidregg` on hbox via `swarm-build`; `scripts/check-import-boundary.sh`.

### Lane B — Rust: the lawful "reader" as generated glue (after A; ~80 lines Rust, larger Lean edit)
1. Lean: add `KernelTag.evmStage0AddAux` (`SemanticArtifactBundle.lean:254`) and request/
   response shapes to `ByteCodecShape` (`:262`): request = 833 words u32 LE (3,332 B),
   response = 4,131 words (16,524 B). One arm each in `NativeGlueGen.responseWidth` (`:66`),
   `requestShapeConstants` (`:72`), `kernelFunction` (`:85` →
   `"crate::native_dispatch::evm_stage0_add_aux_bytes"`). Extend `workConstants` (`:120`) to
   emit `pub const WORK_n_ROWS: &[(u8, u8, u32, u8, u32, u32)]` (op, aKind, a, bKind, b, out;
   3,298 tuples) and `WORK_n_ZEROS: &[u32]` from the profile's descriptor. Work id `9103`,
   carrier `206` (the BabyBear residue-ring carrier of `MinidreggV1ArithmeticWork`). A
   `KernelCall {abiVersion := 1, entry := .constraintDescriptorV1, segments := 7 segments
   (x,y,z public; xBits,yBits,zBits,carry witness), calls := [], descriptor := evmAddDescriptor}`
   and an `Instruction.arithmetic` with `publicInputs := encodeBoundary X Y Z` as a 48-list.
   Regenerate through a new `BuildTarget` (pattern `ArithmeticNativeDeployment.lean:326–331`).
   ⚠ This re-pins the authenticated catalog: `MinidreggV1Artifact.bundle_native_catalog_wellFormed`
   and `ArithmeticNativeDeployment`'s membership theorems re-elaborate → whole-tree build.
2. Rust `prover/src/native_dispatch.rs`:
   `pub fn evm_stage0_add_aux_bytes(request: &[u8]) -> Result<Vec<u8>, NativeDispatchError>`
   — decode 833 LE words (≥ p → local error), evaluate `WORK_n_ROWS` in order with
   read-before-write / rewrite as local errors (what `generate_candidate_trace` did), return
   4,131 LE words. **No `descriptor_holds` in Rust** — that predicate stays deleted;
   `descriptorHoldsCheck` judges the reply on the Lean side of the plan.
3. Test `prover/tests/evm_stage0_dispatch.rs`: dev-dep serde reads Lane A's witness JSON,
   feeds the 833-var prefix through the generated `dispatch_native`, asserts the reply is
   byte-identical to the Lean-written 4,131 words for V1..V5. Control: counts unchanged
   (3,298 row evals). Vector agreement, never verification.
Value: the Stage-0 descriptor becomes a registered `Instruction` with a real `PlanRunner`
behind it — the routability SLVG asked for, in the only shape the decision permits.

### Lane C — the throwaway oracle number (STEERS §4; never in minidregg's tree)
zkml-research scratch: a ~40-line Python translator `evm_stage0_add_descriptor.json` →
breadstuffs v1 `LeanDescriptor` JSON; a breadstuffs `#[ignore]` test: `parse_descriptor` →
`build_trace(desc, &lane_A_witness_as_i64)` → `prove_descriptor` → `verify_descriptor`, and the
forgery vector must fail `verify` (debug builds panic in `prove` — run release). Differential =
p3's accept/reject vs Lean's `descriptorHoldsCheck` on the same 5 + 2 vectors. Report proof
bytes (exact tier) first; latency on **hbox only** (`taskset -c 0-15`, `RAYON_NUM_THREADS=1`,
min-of-21, interleaved A/B, load < 1, `-C target-cpu=native`, `DREGG_REQUIRE_LEAN=0` as in
air-interpreter.md §6). Label every number: "p3-uni-stark, log_blowup 3, q 38, pow 16, v1 AIR,
**no public-input binding**, 4,131 columns × `MIN_TRACE_HEIGHT` rows, breadstuffs' FRI floor —
not minidregg." Never on this laptop (STEERS §5).

### The blocker, named
`Compiler/GateMleExt6.lean:246 CommittedTerminal` has no realizer, and the controller that
would consume one is `noncomputable`. Until a Lean-owned BabyBear/Ext6 PCS controller exists
(§3(c): ~1.8K Lean + ~0.5K opaque Rust + the listed reductions), "Stage-0 time-to-proof" on
the derived path is not a measurement anyone can take; Lane C's number is breadstuffs', and
says so on the label.

## §5. What I could not determine
- Whether breadstuffs `dregg-circuit` builds on hbox tonight (HEAD carried 102 pre-existing
  reds under `DREGG_REQUIRE_LEAN=0` on 2026-08-18; not re-checked — read-only scout, no builds).
- Whether `p3-uni-stark` at `MIN_TRACE_HEIGHT` accepts a 4,131-column trace (v1 tests used
  ≤ 20 columns; the Poseidon2 chip is 386). Probably; unmeasured.
- Whether `ByteCodecShape` can gain a parametrized/width-carrying constructor without breaking
  `Encodable` and the artifact content-address pins; the re-pin cost is Lane B's real cost and
  I did not enumerate every dependent theorem.
- Whether `checkInstruction` accepts `KernelCall.calls := []` (vacuous `CallsWellShaped` reads
  as fine; not elaborated).
- `#eval` cost of `descriptorHoldsCheck` over a `Nat → BabyBear` closure on `Array.getD`
  (expected milliseconds; not run).
- Whether `LeanDescriptorAir` v1 is still compiled at breadstuffs HEAD today (it was on 08-18).
- `EmitSerialize.lean:190` cites `prover/tests/conformance.rs` (deleted in d55ef32) — stale
  pointer, not fixed here.
