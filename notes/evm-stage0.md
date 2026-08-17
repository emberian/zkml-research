# EVM decompilation Stage 0 — five opcodes, end to end (BUILD lane, live log)

2026-08-17. Executes `notes/evm-decompilation.md` §9 Stage 0: the fragment
`CALLDATALOAD · CALLDATALOAD · ADD · MSTORE · RETURN`, semantics → residual →
Lean-authored constraints → emitted descriptor → meaning theorem. Substrate said
out loud, per house law: **every constraint is Lean-authored, through
`minidregg/Compiler/Air`'s DSL and the proved `emit`; the decompiler writes no
constraint.**

Labels as in the design note: [measured] / [derived] / [recalled] / [ASSUMED].

## Decisions, stated up front

### D1 — semantics anchor: DIRECT statement in Lean, differential vectors from a real EVM

The five-opcode fragment interpreter is stated directly in
`minidregg/Theory/EvmFragment.lean` (byte-level: real bytecode, byte-granular
PC, a real stack with the 1024 depth check, byte-addressed memory, CALLDATALOAD
zero-padding past the calldata end). NOT an import of EVMYulLean. Why:

* EVMYulLean is 22K+ tests of Cancun surface; the Stage-0 footprint is five
  opcode kinds. Importing it means importing its toolchain pin, its state
  representation, and its execution monad into minidregg's `Theory/` (whose
  import boundary is mechanically Mathlib-only) for a fragment where the whole
  interpreter is ~100 lines. The design note (§6) already scoped this register:
  the fidelity anchor for the fragment interpreter is **differential, not
  machine-checked** — Pickles-Phase-A register, stated as such.
* The upgrade path is unchanged and real: EquiVM/EVMYulLean become the front
  end at the stage where solc-emitted dispatch enters (Stage 3–4). Nothing in
  Stage 0's statement shape has to change — `evmRun` is already the §6 shape.

**The conformance vectors are from a real EVM** [measured]: anvil v1.7.1
(revm), via `anvil_setCode` + `eth_call` of the actual 15-byte runtime
`0x6000356020350160005260206000f3` (built programmatically, not hand-hexed).
Five vectors, committed into the Lean file as kernel-decided theorems:

| vector | what it exercises | calldata | returndata |
|---|---|---|---|
| V1 | small values | X=1, Y=2 | 3 |
| V2 | arbitrary 256-bit | two π-digit words | `0x69678c6e…75a0` |
| V3 | **wraparound** | X=2²⁵⁶−1, Y=5 | 4 |
| V4 | **CALLDATALOAD past end** (40-byte calldata) + carry ripple into top byte | X=`0xfedc…3210`, 8 bytes `0x1122334455667788` | `0x0ffeeddccbbaa998fedc…3210` |
| V5 | empty calldata | (empty) | 0 |

Raw JSON: scratchpad `evm-stage0/vectors.json`; the committed form is the Lean
theorems.

### D2 — the five opcodes are really five KINDS, and PUSH1 is one of them

The design note's "five-opcode bytecode" is not executable as literally five
bytes: CALLDATALOAD, MSTORE and RETURN all pop operands that must be pushed.
The real fragment is 15 bytes, opcode kinds {PUSH1, CALLDATALOAD, ADD, MSTORE,
RETURN}. PUSH1 is exactly the machine content the decompilation kills (§5 of
the design note: "PUSH/POP/DUP/SWAP — the stack becomes de Bruijn wiring"), so
it must EXIST in the semantics to visibly die in the residual.

### D3 — ⚑ the 256-bit question: LIMB-DECOMPOSE, 16 limbs × 16 bits, wraparound constrained

**The known-cost route, not the scope-to-<p dodge.** The emitted circuit
carries the full 2²⁵⁶ ring: each 256-bit word is 16 little-endian limbs of 16
bits over BabyBear (16·16 = 256 exactly; 2·2¹⁶ ≤ p gives per-equation
no-field-wrap headroom), each limb bit-range-checked (the existing
`rangeGadget`), boolean carries, schoolbook equations, **low carry pinned to 0,
top carry boolean but FREE** — discarding the top carry IS the mod-2²⁵⁶
semantics. The conformance suite contains a genuine wraparound vector (V3) that
a <p-scoped circuit could not even state.

Why not 8×32 (the design brief's shorthand): a 32-bit limb does not fit
BabyBear (p = 2³¹−2²⁷+1 < 2³²) — the recorded pigeonhole
(`Theory/Bignum.lean`'s `eight_radix_2013265921_limbs_lt_248_bits`) is about
exactly this geometry. 16×16 covers 256 bits injectively with headroom;
injectivity of the boundary encoding is a named theorem, not an assumption.

Reuse, not invention [measured, minidregg]: `Compiler/AirBignum.lean` already
proves the no-overflow limb adder (`addGadget_sound`, ranges + carries +
telescope) through the existing `emit`. Stage 0 adds the **modular** variant
(`addModGadget`: same blocks, top-carry pin dropped) with soundness AND
completeness — completeness via an executable witness builder (Lean-side
witness-gen: bits, carries computed, not chosen).

### D4 — what the emitted object binds (boundary)

Public wires = 48 limbs: X (calldata word 0), Y (calldata word 32), Z (the
claimed returndata word). Witness = 768 bit wires + 17 carries. The meaning
theorem quantifies over X, Y, Z < 2²⁵⁶ and says: a satisfying total wire vector
pinning the public limbs to encode(X,Y,Z) exists **iff**
`evmRun fragment (calldata X Y) = .ok (returnBytes Z)`. `encode_injective` is
its own theorem at this geometry.

## The chain (files)

* `minidregg/Theory/EvmFragment.lean` — bytes/words codec (shared little-endian
  algebra from `Theory.Bignum`), the byte-level interpreter, conformance
  theorems V1–V5.
* `minidregg/Theory/EvmResidual.lean` — the Stage-0 residual vocabulary
  (calldata-word context roles + `add`; NOTHING unused declared), its total
  denotation, the UNTRUSTED refusing `decompile` (symbolic stack machine over
  bytes), `decompile fragment = .ok D` exhibited, and the per-output TV theorem
  `∀ cd, evmRun fragment cd = .ok (denote D cd)`.
* `minidregg/Compiler/EvmAddAir.lean` — `addModGadget` (generic width/limbBits)
  + soundness/completeness, the concrete 16×16 BabyBear layout + descriptor,
  `evmAddDescriptor_means_semantics` (the §6 statement, Stage-0 instance),
  teeth (constructive forgery refused at descriptor AND denotation; conformance
  vector accepted), emitted JSON artifact.

## Trusted base (enumerated, §6 register)

1. Lean kernel + [propext, Classical.choice, Quot.sound] (guarded per theorem).
2. EVM-fidelity of `evmRun` on the fragment: differential vs anvil/revm on
   V1–V5 [measured], NOT machine-checked. Gas-free: the statement speaks about
   executions the deployed EVM completes within gas (§7.5 premise, visible).
3. `[EMIT-sound]` unchanged: prover acceptance inherits the FRI/STARK floor.
4. Not the decompiler (untrusted, per-output TV). Not Rust (reads JSON only —
   note: the eltwise precedent's JSON also has no Rust consumer test yet;
   Stage 0 mirrors the precedent exactly and inherits that open seam).

## Results — the chain, closed (all [measured] on the built tree)

`Compiler/EvmAddAir.lean` GREEN; **full minidregg default target (9,000 modules)
GREEN** with both umbrellas importing the three new files;
`scripts/check-import-boundary.sh` OK.

* **`addModGadget`** (generic width/limbBits/prime): `AirBignum`'s limb ranges +
  boolean carries + schoolbook equations with the top-carry pin DROPPED —
  `addModGadget_sound` forces `denote z = (denote x + denote y) mod B^width`
  (the free top carry is boolean, so the telescope determines the reduction
  exactly). Completeness is an executable witness builder: `evmAddAsg` computes
  limbs, bits and carries from `(X, Y)` (`carryChain`), and
  `evmAddAsg_accepts` proves it accepted for EVERY in-range pair — witness-gen
  in Lean, the crux being `schoolbook_digit_eq` (computed carry chain lands on
  the wrapped sum's digits; proved by the reused telescope + canonical
  uniqueness, not re-proved arithmetic).
* **The meaning theorem** `evmAddDescriptor_means_semantics (X Y Z < 2²⁵⁶)`:
  `(∃ wv pinning the 48 public limbs to encode(X,Y,Z), descriptorHolds) ↔
  evmRun fragmentCode (calldata X Y) = .ok (beBytes Z)`. Axioms:
  `[propext, Classical.choice, Quot.sound]`, guarded.
* **`encodeBoundary_injective`** — the "does ONLY that program" half at the
  16×16 geometry, a named theorem.
* **Shape [measured]**: 3,298 gates · 4,131 wires (833 vars + 3,298 aux) · 850
  zero-checks; `evmAddDescriptor_shape` kernel-decided (`decide +kernel`,
  maxRecDepth 16384), `evmAddDescriptor_wellFormed` proved. JSON artifact
  (231 KB) Lean-written to `prover/testdata/evm_stage0_add_descriptor.json`.
  ⚠ §8-pricing note: ONE u256 add with full bit-range checks is already ~3.3K
  gates in THIS gate dialect — the design note's "decompiled transfer ≈ 3–4K"
  was priced in Nebula's R1CS unit with 2-element words; the units are NOT
  comparable and the §8 table should be re-derived against our own emitted
  counts at Stage 3 (as its §9 already plans). The dominant term here is the
  768 bit wires; a lookup-based range check (the deployed logup machinery)
  collapses that, and is the obvious Stage-1-adjacent optimization.
* **Teeth** (mutation asserted first): `forged_wrap_differs` (`5 ≠ 4` decided)
  → `evmAdd_forged_refused` (no satisfying vector at the forged claim) +
  `evmAdd_forged_denotation_fails` (the residual refutes it too);
  `evmAdd_satisfiable_v1` and `evmAdd_satisfiable_wrap` (the WRAPAROUND anvil
  vector satisfiable at the descriptor). At the residual layer:
  `forged_residual_differs`/`forged_residual_fails_tv` (wrong operand wiring
  refuted by TV on V1); decompiler refusals computed (STOP, data-dependent
  CALLDATALOAD offset, foreign opcode).

## What Stage 0 dodged — the Stage-1+ gap list (deliverable 5)

1. **MSTORE-as-memory.** Here the single static-offset MSTORE dies into a wire
   (the residual has no memory at all); a program whose stores survive
   specialization needs the `TwistContinuity` bus
   (`SparseAuthenticatedStateLogupBridge.lean`) — the design note routes
   storage there (§7.3) and a sibling lane is on the seam. The decompiler
   already refuses every other memory shape, so nothing silently pretends.
2. **256-bit beyond ADD.** The vocabulary has exactly {calldata roles, add}.
   Stage 1's bill ({cmp, iszero, select, guard, shiftConst, bit}, design §9)
   each needs its limb gadget + the revert-path split (§7.6). The general
   `Residual → ConstraintSystem` compiler does not exist yet — Stage 0's
   emission handles the one-op shape; growing the vocabulary means growing the
   compiled fragment WITH its meaning theorem, `ZkmlTensorOps`-style.
   Also: range checks are bit-decomposition here (768 aux wires); the
   logup/lookup range argument is the cost lever before keccak enters.
3. **Keccak** — untouched, and it dominates every real contract (§8.1: the
   hash choice must be named by whoever quotes a price).
4. **The decompiler's reach**: straight-line only, one MSTORE, RETURN(o, 32),
   no jumps (solc dispatch needs static jump folding — Stage 3), no dedup of
   repeated calldata reads (costs a wire, never soundness), constants cannot
   reach the returned word (Stage 1's `literal` role). All refusals, none
   repairs.
5. **The boundary to the switchboard/IVC**: this descriptor is one
   self-contained statement — batching many fragment executions per proof
   (the §8.2 "many transfers per proof" shape), folding loop bodies
   (`SelfEmbedding`), and call composition (`VerifierEmbedding` rungs) all sit
   ABOVE the per-program descriptor and are untouched. The residual
   interpreter (a switchboard at un-specializable sites, §1.3) is likewise
   future — Stage 0 refuses instead.
6. **Fidelity register**: `evmRun` is differential-only (five anvil vectors),
   gas-free, and the fragment ISA is 5 opcode kinds + STOP. EquiVM/EVMYulLean
   remain the industrial front half for Stage 3+.
7. **Rust prover consumption**: the JSON artifact has no Rust-side reader test
   yet — exactly the eltwise precedent's open seam, inherited knowingly, and
   the vector-agreement-only label applies at that boundary.

## Log

* 2026-08-17: bytecode built programmatically; 5 vectors from anvil v1.7.1, all
  cross-checked against an independent Python computation of the intended
  semantics [measured]. Lean files next.
* `Theory/EvmFragment.lean` GREEN (13s): byte-level interpreter; V1–V5
  conformance as kernel-decided named theorems (V3 wraparound needs only
  `[propext]`); codec lemmas (`beBytes_inj`, `cdWord_calldataOf_{zero,32}`).
* `Theory/EvmResidual.lean` GREEN (17s): the decompiler runs and
  `decompile fragmentCode = .ok fragmentResidual` is `rfl`; **the per-output TV
  theorem `fragment_faithful : ∀ cd, evmRun … cd = .ok (beBytes
  (fragmentResidual.denote cd))` is LITERALLY `rfl`** — with the program
  concrete and calldata symbolic, the stack/PC/decode/MSTORE/RETURN machinery
  reduces away definitionally; the machine was pure structure, and the kernel
  checking that reduction IS the decompilation theorem. Teeth: three refusals
  computed; a forged residual (wrong operand wiring) refuted by the TV
  obligation on V1, mutation asserted first.
