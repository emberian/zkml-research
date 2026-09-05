# Stage-0 Lane A — `Compiler/DescriptorEval.lean`: the aux-filler, its theorems, and the compiled witnesses

**2026-09-04. Lane A of `descriptor-reader-scout.md` §4, executed.** Branch `main` of
`/Users/ember/dev/minidregg`; nothing committed; `Compiler.lean` untouched (the file is unrooted
until the coordinator roots it). Gate: `lake env lean Compiler/DescriptorEval.lean` exits 0 with
no errors and no warnings; `scripts/check-import-boundary.sh` green (Theory/Selvage unchanged).
Every file:line anchor in the brief's §2/§4 was opened and checked before use; all held
(`Emit.lean:79–105/:127/:427`, `EmitShare.lean:317/:552`, `EmitSerialize.lean:108/:147/:159/:237`,
`EvmAddAir.lean:290/:300/:304/:334/:513/:589/:597/:650/:658/:673/:697`,
`NativeKernelPlan.lean:258/:265`, `EvmFragment.lean:161–195`).

## 1. The ATLAS law applied, quoted (§6, law 9)

> **`#guard` is silent `native_decide`.** Case-tests in Lean are still case-tests (848 of them
> = zero theorems about the subject). Prove the general fact; use guards as non-vacuity
> *witnesses*, graded and confessed (`#assert_compiled`).

Applied as written: the general facts are theorems (§2 below, kernel-checked, axioms pinned by
`#guard_msgs`); the five honest vectors and two forgeries are compiled `#eval` witnesses, each
confessed in its docstring as a computed check of the COMPILED `descriptorHoldsCheck` on concrete
data — never a theorem, never `decide` over the 3,298 gates. ATLAS names `#assert_compiled`; the
minidregg tree has no such command (grep: none). The tree's own idiom for a graded witness is an
`#eval` that THROWS so elaboration fails (`EmitSerialize.roundTripDemo`,
`Sp800185Cshake256Conformance`), and that is the idiom used. The scout's reading ("compiled
`#eval` witnesses that throw on failure beside theorems; never `decide` on 3,298 gates") matches
ATLAS and the tree; no divergence to report.

The other laws that bit: **law 2** (both poles — five accepts AND two refusals at the same
checker, mutation asserted before the refusal is read); **derived path only** (no Rust written;
the evaluator is a Lean function over the Lean-emitted descriptor; the deleted Rust
`descriptor_holds` stays deleted).

## 2. Definitions and theorem statements (copied from the file)

Imports: `Compiler.EvmAddAir`, `Compiler.EmitShare`, `Compiler.NativeKernelPlan`. ⚑ The brief
named only the first and third; `ConstraintDescriptor.SSA`/`emit_ssa` live in `EmitShare`
(the brief's own `EmitShare.lean:552` anchor), so the second is required. Namespace
`Minidregg.Compiler.DescriptorEval`; `variable {F : Type u} [Field F]` — `fillAux` is generic in
the field (the brief wrote it at `BabyBear`; `fillAux evmAddDescriptor …` is that instance).

```lean
def readArr (arr : Array F) : DWire F → F
  | .cnst c => c
  | .wire n => arr.getD n 0

def fillStep (arr : Array F) (g : DGate F) : Array F :=
  arr.set! g.out (g.op.denote (readArr arr g.a) (readArr arr g.b))

def fillAux (d : ConstraintDescriptor F) (vars : Array F) : Array F :=
  d.gates.foldl fillStep (vars ++ Array.replicate (d.nWires - d.nVars) 0)

theorem fillAux_gates_hold (d : ConstraintDescriptor F) (vars : Array F)
    (hssa : d.SSA) (hwf : d.WellFormed) (h : vars.size = d.nVars) :
    ∀ g ∈ d.gates, g.holds (fun i => (fillAux d vars).getD i 0)

theorem fillAux_size (d : ConstraintDescriptor F) (vars : Array F)
    (hwf : d.WellFormed) (h : vars.size = d.nVars) :
    (fillAux d vars).size = d.nWires

theorem fillAux_getD_of_lt (d : ConstraintDescriptor F) (vars : Array F)
    (hwf : d.WellFormed) (h : vars.size = d.nVars) {i : ℕ} (hi : i < d.nVars) :
    (fillAux d vars).getD i 0 = vars.getD i 0

theorem fillAux_descriptorHolds_iff (d : ConstraintDescriptor F) (vars : Array F)
    (hssa : d.SSA) (hwf : d.WellFormed) (h : vars.size = d.nVars) :
    descriptorHolds d (fun i => (fillAux d vars).getD i 0) ↔
      ∀ z ∈ d.zeros, z.read (fun i => (fillAux d vars).getD i 0) = 0

theorem emit_gates_hold_iff (ix : Idx → ℕ) (nPublic nVars : ℕ) (s : ConstraintSystem F Idx)
    (wv : ℕ → F) :
    (∀ g ∈ (emit ix nPublic nVars s).gates, g.holds wv) ↔
      gatesHold (readVars ix wv) (readAux nVars wv) (flattenSystem s 0).gates

theorem flattenSystem_roots_forced (asg : Idx → F) (auxv : ℕ → F)
    (s : ConstraintSystem F Idx) (n₀ : ℕ)
    (hg : gatesHold asg auxv (flattenSystem s n₀).gates) (hacc : systemAccepts asg s) :
    ∀ r ∈ (flattenSystem s n₀).roots, r.read asg auxv = 0

theorem fillAux_emit_holds {K : Type} [Field K] (m nPublic : ℕ) (hpub : nPublic ≤ m)
    (asg : Fin m → K) (s : ConstraintSystem K (Fin m)) (hacc : systemAccepts asg s) :
    descriptorHolds (emit Fin.val nPublic m s)
      (fun i => (fillAux (emit Fin.val nPublic m s) (Array.ofFn asg)).getD i 0)

def evmAddCandidate (X Y : ℕ) : Array BabyBear :=
  fillAux evmAddDescriptor (Array.ofFn (evmAddAsg X Y))

def evmAddClaimed (X Y Z : ℕ) : Array BabyBear :=
  (List.finRange 48).foldl
    (fun arr i => if 32 ≤ i.1 then arr.set! i.1 (encodeBoundary X Y Z i) else arr)
    (evmAddCandidate X Y)

theorem evmAddCandidate_holds (X Y : ℕ) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) :
    descriptorHolds evmAddDescriptor (fun i => (evmAddCandidate X Y).getD i 0)

theorem evmAddCandidate_pins (X Y : ℕ) (i : Fin 48) :
    (evmAddCandidate X Y).getD i.1 0 = encodeBoundary X Y ((X + Y) % 2 ^ 256) i

def checkCandidate (c : Array BabyBear) : Bool :=
  descriptorHoldsCheck evmAddDescriptor (fun i => c.getD i 0)
```

The brief asked for `fillAux_gates_hold` and said the exhibits do not depend on it. It closed
(no `sorry`, no named obligation left), via one list-level induction
(`foldl_fillStep_holds`, head case `foldl_fillStep_holds_head`) over `Array.setIfInBounds`
lemmas — `Array.set!_eq_setIfInBounds` is `rfl` in the v4.30.0 toolchain, so `set!` is used as
the brief wrote it. Beyond the brief: `fillAux_emit_holds` (completeness at the evaluator —
`emit_faithful` + `flatten_forces`, reused; one new list lemma `flattenSystem_roots_forced`,
the converse of `flattenSystem_forces`), and its Stage-0 instances `evmAddCandidate_holds`
(all in-range `(X, Y)`, via `evmAddAsg_accepts`) and `evmAddCandidate_pins`. Net effect: the
`∃ wv` of `evmAdd_satisfiable_v1` / `evmAdd_satisfiable_wrap` is now a computable vector one can
print, and the five exhibits are the non-vacuity witnesses of `evmAddCandidate_holds` at the
compiled checker — exactly law 9's shape.

Axiom pins (`#guard_msgs` on `#print axioms`, all matched):
`fillAux_gates_hold` → `[propext, Quot.sound]`; `fillAux_emit_holds`, `evmAddCandidate_holds`,
`evmAddCandidate_pins` → `[propext, Classical.choice, Quot.sound]` (`Classical.choice` enters
through `emit_accepts_iff`'s neighbourhood / `evmAddAsg_accepts`, as in `EvmAddAir` §7).

## 3. Exhibits that ran, and their results (compiled `#eval`, throw-on-failure)

Vectors re-typed from `Theory/EvmFragment.lean:161–195` as `(X, Y, Z, calldata)`; each honest
exhibit checks, in order, and throws on the first failure:
(a) `c.size = evmAddDescriptor.nWires`; (b) the machine re-run (compiled `evmRun fragmentFuel
fragmentCode calldata`) returns `beBytes Z` — pinning the re-typed constants to
`conformance_v1…v5` (V4 on its real 40-byte calldata, V5 on `[]`); (c) the candidate's 48-wire
public prefix equals `encodeBoundary X Y Z`; (d) `descriptorHoldsCheck evmAddDescriptor
(fun i => c.getD i 0) = true`; then writes the witness JSON.

| exhibit | vector | result |
|---|---|---|
| V1 | `(1, 2 → 3)` | accepted |
| V2 | `(0x243f6a88…ec4e6c89, 0x452821e6…b5470917 → 0x69678c6e…a19575a0)` | accepted |
| V3 wrap | `(2²⁵⁶−1, 5 → 4)` | accepted |
| V4 short calldata | `(0xfedcba98…76543210, Y = 0x1122334455667788·2¹⁹² → 0x0ffeeddc…76543210)`, calldata `beBytes X ++ [11 22 33 44 55 66 77 88]` | accepted |
| V5 empty | `(0, 0 → 0)`, calldata `[]` | accepted |
| forged claim | `evmAddClaimed (2²⁵⁶−1) 5 5` (wires 32–47 ← limbs of the claimed `5`) | mutation asserted (`forged ≠ honest`), **refused** |
| single-wire tamper | V1 candidate, wire `833` (= `nVars`, the first aux wire, gate 0's output) `+1` | mutation asserted, **refused** |

Any `false` on an honest vector, `true` on a forgery, prefix mismatch, size mismatch, or
machine-run mismatch throws → elaboration fails. Wall-clock: the whole file (Mathlib import
load + 7 checks + 5 JSON writes + census) elaborated in 6–20 s on this laptop at load ≈ 90 —
laptop script wall-clock, evidence of nothing.

## 4. Units, recounted from the descriptor in Lean (the `census` `#eval`; expected figures asserted with teeth)

```
Stage-0 units (recounted): 3298 gates = 1665 add + 1633 mul; 4131 wires = 833 vars
(48 public + 785 witness) + 3298 aux; 850 boundary pins (849 on aux roots, 1 on variables);
operands: 4915 wire, 1681 constant over 19 distinct constants; witness vars: 768 range bits
+ 17 carries (booleanity gates on 785 distinct variables); a check = 3298 gate evals + 850 reads
```

All figures agree with the brief's §2 census and §4 item 5. One precision on the brief's
phrasing "768 of 833 witness vars are range bits": 833 is `nVars` (all variables); the witness
variables are `833 − 48 = 785`, of which 768 are range bits and 17 carries (the layout's
`xBit/yBit/zBit` and `carry` images, checked in the census to partition `[0, 833)` together with
the 48 limbs; the descriptor independently shows booleanity gates `add (wire w) (cnst −1)` on
exactly 785 distinct variable wires). The single zero-check on a variable wire is the carry₀
pin (`vr (w.carry 0)`, wire 816 — the scout's reading; the census confirms the count is one).
`fillAux_descriptorHolds_iff` makes the cost line honest: on the filled vector the 3,298 gate
evaluations are true by construction; only the 850 reads carry information. No pricing
derived from these (the brief's warning about Nebula's R1CS units stands).

## 5. Files written

- `/Users/ember/dev/minidregg/Compiler/DescriptorEval.lean` — new, 535 lines, unrooted
  (coordinator roots it in `Compiler.lean`; suggested placement: after the
  `import Compiler.EvmAddAir` line, since it imports `EvmAddAir`, `EmitShare`,
  `NativeKernelPlan`, all already in the umbrella).
- `/Users/ember/dev/minidregg/prover/testdata/evm_stage0_add_witness_v1.json` … `_v5.json` —
  new, Lean-authored (written at every elaboration of the file, the `writeDescriptorJson`
  precedent), 27.6–29.1 KB each. Schema:
  `{ "p": 2013265921, "descriptor": "evm_stage0_add_descriptor.json", "vector": "v3",
  "x": "0x…", "y": "0x…", "z": "0x…", "nPublic": 48, "nVars": 833, "nWires": 4131,
  "accepted": true, "wires": [ 4131 canonical values, 0 ≤ v < p ] }` — `x/y/z` are hex
  STRINGS (256-bit values do not fit a JSON reader's integer), `wires` canonical `ZMod.val`s
  (the descriptor's constant contract), `accepted` the embedded verdict of the compiled checker
  on that very vector. Independently re-read with Python: 4,131 words each, all `< p`.
- `/Users/ember/dev/zkml-research/notes/stage0-lane-a.md` — this note.

Not touched: `Compiler.lean` (pre-existing uncommitted edit belongs to someone else; `git diff`
of it contains no `DescriptorEval`), `Compiler/UwueavePreoProjectionV2.lean`, `LICENSE*`,
`NOTICE`, `docs/*`, `prover/src/*`. No Rust written. No commit, no stash, no `add -A`.

## 6. What Lane B needs next — the brief's list, quoted, with what Lane A changed marked

> ### Lane B — Rust: the lawful "reader" as generated glue (after A; ~80 lines Rust, larger Lean edit)
> 1. Lean: add `KernelTag.evmStage0AddAux` (`SemanticArtifactBundle.lean:254`) and request/
>    response shapes to `ByteCodecShape` (`:262`): request = 833 words u32 LE (3,332 B),
>    response = 4,131 words (16,524 B). One arm each in `NativeGlueGen.responseWidth` (`:66`),
>    `requestShapeConstants` (`:72`), `kernelFunction` (`:85` →
>    `"crate::native_dispatch::evm_stage0_add_aux_bytes"`). Extend `workConstants` (`:120`) to
>    emit `pub const WORK_n_ROWS: &[(u8, u8, u32, u8, u32, u32)]` (op, aKind, a, bKind, b, out;
>    3,298 tuples) and `WORK_n_ZEROS: &[u32]` from the profile's descriptor. Work id `9103`,
>    carrier `206` (the BabyBear residue-ring carrier of `MinidreggV1ArithmeticWork`). A
>    `KernelCall {abiVersion := 1, entry := .constraintDescriptorV1, segments := 7 segments
>    (x,y,z public; xBits,yBits,zBits,carry witness), calls := [], descriptor := evmAddDescriptor}`
>    and an `Instruction.arithmetic` with `publicInputs := encodeBoundary X Y Z` as a 48-list.
>    Regenerate through a new `BuildTarget` (pattern `ArithmeticNativeDeployment.lean:326–331`).
>    ⚠ This re-pins the authenticated catalog: `MinidreggV1Artifact.bundle_native_catalog_wellFormed`
>    and `ArithmeticNativeDeployment`'s membership theorems re-elaborate → whole-tree build.
> 2. Rust `prover/src/native_dispatch.rs`:
>    `pub fn evm_stage0_add_aux_bytes(request: &[u8]) -> Result<Vec<u8>, NativeDispatchError>`
>    — decode 833 LE words (≥ p → local error), evaluate `WORK_n_ROWS` in order with
>    read-before-write / rewrite as local errors (what `generate_candidate_trace` did), return
>    4,131 LE words. **No `descriptor_holds` in Rust** — that predicate stays deleted;
>    `descriptorHoldsCheck` judges the reply on the Lean side of the plan.
> 3. Test `prover/tests/evm_stage0_dispatch.rs`: dev-dep serde reads Lane A's witness JSON,
>    feeds the 833-var prefix through the generated `dispatch_native`, asserts the reply is
>    byte-identical to the Lean-written 4,131 words for V1..V5. Control: counts unchanged
>    (3,298 row evals). Vector agreement, never verification.
> Value: the Stage-0 descriptor becomes a registered `Instruction` with a real `PlanRunner`
> behind it — the routability SLVG asked for, in the only shape the decision permits.

Marks from Lane A:
- **Item 3, the JSON shape (changed/now concrete):** the serde mirror must match §5's schema —
  `wires` is the 4,131-word array (the first 833 are the request; all 4,131 are the expected
  reply); `x/y/z` are strings; `accepted` is a bool. Use `deny_unknown_fields` against exactly
  those eleven keys. `descriptor` is a relative filename, not a path.
- **Item 2, the Rust evaluator's semantics (clarified):** Lean's `fillAux` reads unwritten wires
  as `0` (`getD _ 0`) and never errors; on the Lean-emitted rows read-before-write cannot occur
  (`emit_ssa`, a theorem for every emitted descriptor), so the brief's stricter Rust behaviour
  (local error on read-before-write / rewrite) cannot disagree with Lean on these rows. The
  `≥ p` rejection is Rust's alone — Lean's request is already `Array BabyBear` (canonical).
  Gate evaluation order = list order of `evmAddDescriptor.gates` = `WORK_n_ROWS` order; outputs
  strictly increase 833→4130 (SSA), so an in-order Rust loop is exactly `fillAux`.
- **Item 1, the reply's Lean-side reference (strengthened, not changed):** the Lean candidate
  the Rust reply is compared against is `evmAddCandidate X Y`, now a THEOREM-satisfying vector
  (`evmAddCandidate_holds`) whose prefix is the pin (`evmAddCandidate_pins`); acceptance of
  the reply is still `descriptorHoldsCheck` (`kernelCallAcceptsCheck`), and the differential is
  vector agreement. The public-input list the `Instruction` carries is
  `(List.finRange 48).map (encodeBoundary X Y Z)`.
- **Unchanged but worth knowing:** the extra import `Compiler.EmitShare` is already in the
  umbrella; rooting `DescriptorEval` adds no new dependency edge. The tamper exhibit (one aux
  word wrong → refused) is the shape of Lane B's negative control; Lane B may reuse
  `exhibitForgery` for a Rust-reply-with-one-flipped-word test on the Lean side.
- **Scout's open item resolved:** "`#eval` cost of `descriptorHoldsCheck` over a
  `Nat → BabyBear` closure on `Array.getD` (expected milliseconds; not run)" — ran, seven checks
  plus witness generation inside a 6–20 s whole-file elaboration; evidence of nothing more.
