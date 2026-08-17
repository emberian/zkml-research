# Decompilation into logic: the EVM program-specific circuit, stated precisely

2026-08-17, DESIGN lane. Ember's direction, verbatim: *"we'll be using a
'decompilation into logic' approach for recompiling an EVM program into something
that does ONLY that program, but verifiably."* This note states that approach
precisely, places it against Nebula's switchboard, charts what the stack already
provides, and prices the prize. Substrate said out loud, per house law: **every
constraint in this design is Lean-authored; the decompiler's OUTPUT is the thing
proved about.** Rust stages and serializes; Rust authors nothing.

Labels: [measured] = read at source or counted; [derived] = computed here from
sourced inputs, arithmetic shown; [recalled] = from memory/training, unverified;
[ASSUMED] = a premise this note takes without evidence.

---

## §1. The approach, stated precisely — and the framing tested

**The claim under test**: a switchboard is *runtime* specialization; decompilation
is *compile-time* specialization — **the first Futamura projection applied to
circuits**. Specializing the EVM-interpreter circuit at a fixed program yields a
program-specific circuit with no machine left.

The classical statement: for an interpreter `int` and program `p`,
`mix(int, p) = target_p` with `⟦target_p⟧(x) = ⟦int⟧(p, x)`. The circuit version
replaces the equation of *functions* with an equation of *accepted relations*:

> `spec(C_int, p) = C_p` such that
> `Accept(C_p) = { (x, y, w) : EVMsem(p, x) = y }` — up to an injective boundary
> encoding and an existential over advice `w`.

Where the framing is exact, and where it breaks — tested, not adopted:

1. **Exact at "what is specialized."** The universal step circuit *is* an
   interpreter (fetch, decode, dispatch, stack discipline are all constraints);
   fixing the program constant-folds all of it. The specialization wins are the
   classical ones: dead-branch elimination (the dispatch), constant propagation
   (PC, jump targets, static shift amounts), arity specialization (a
   dynamic-length SHA3 opcode becomes a fixed-64-byte hash). §8 prices each.
2. **Broken at residualization.** Classical `mix` handles dynamic control by
   *residualizing* — emitting a loop into the target. **Circuits have no loops.**
   Where the program's control depends on data, a circuit specializer has exactly
   three moves: unroll under a bound (Buffet, 2014 — and in the EVM *gas is a
   static bound on everything*), push the loop to the recursion seam
   (IVC/folding), or **refuse**. The Futamura projection for circuits is
   *partial*, and its partiality is precisely the map of §7.
3. **The residual interpreter IS the switchboard.** When `mix` cannot specialize
   a site, it leaves interpreter code in the target. The circuit analogue of
   "leftover interpreter" is a switchboard for the un-specializable sites (e.g. a
   call to a data-dependent address). So the two techniques are not rivals; they
   are the static and dynamic halves of one mixed computation, and the
   materialize-vs-virtualize threshold (`docs/COST-MODEL.md`, `docs/SELVAGE.md`
   §2's "not zero, there's a sweet spot") prices exactly the per-program-point
   choice a decompiler makes.
4. **The second projection exists and we are deliberately not taking it.**
   `mix(mix, int)` = a verified *compiler* — proving the decompiler correct once,
   for all programs. The cheaper stance (and the one the stack already practices
   in `EmitByName`'s snapshot→emit→diff) is per-output **translation validation
   done right**: the decompiler is untrusted, partial, free to be heuristic;
   each output carries its own machine-checked refinement to the semantics. TV
   is a lie only when the source has no semantics (the house-law point about
   Rust); here BOTH sides live in Lean, so per-program TV is genuine.

---

## §2. Nebula at source — what the switchboard is and what it measures

Read at source: `~/paperbin/nebula-folding-machine-executions.pdf` (Arun–Setty,
*Nebula: Efficient read-write memory and switchboard circuits for folding
schemes*). A sibling lane covers Nebula/Vega at depth — this section extracts
only what the pricing needs. ⚠ Correction to the brief's shorthand: **Vega
(eprint 2025/2094, Kaviani–Setty, S&P 2026) is credententials/identity, not EVM**
[measured, eprint listing]; the 2026 MSR-page "Nebula: Proving Machine…" entry is
for the sibling to resolve.

Mechanism [measured, their §5]: given instruction circuits `C_1..C_ℓ` (R1CS),
stitch block-diagonally into `C⋆` with per-instruction **switch variables**:
`Σ z[s_i] = 1`, `z[s_i](1−z[s_i]) = 0`, and input-consistency rows
`z[j] = z[s_i]·z[input j]`. Inactive subcircuits take all-zero witnesses
(their Lemma 3), so with a commitment scheme where zeros are free (MSM), the
prover pays only for the active instruction. Rows: `m⋆ = Σ m_i + 1 + ℓ(1+|x|)`;
nonzero witness ≤ `1 + |x| + |ω_active|`.

The numbers, disaggregated — the brief's "~30×/~260×" conflates two levers
[measured, their Table 1 + §6]:

| configuration | constraints/step | ERC20 prove | ratio |
|---|---:|---:|---:|
| Spice memory + multiplexer | 3,640 K | OOM | — |
| Spice memory + switchboard | 3,640 K | 2,400 s | 480× |
| Nebula memory, no switchboard | 115 K | 1,300 s | 260× |
| Nebula memory + switchboard | 116 K | **5 s** | 1× |

- **30× is the MEMORY technique** (3,640K → 116K structure), not the switchboard.
- **260× is the SWITCHBOARD** (1,300s → 5s wall-clock at fixed 116K structure).
- Their proto-EVM: 100 of 141 opcodes, ~120K R1CS total; largest subcircuit is a
  **custom hash replacing SHA3 at ≈20% of total (≈24K)**; POP < 100; most common
  opcodes < 250 ("500× smaller than the full circuit"); a third are 250–1,000;
  left shift ≈ 4.8K ("25× smaller"). Memory write: Merkle 3,750–8,000, Spice
  ~1,100, Nebula **4 + range-check + amortized scans** (2 scans ≤ 4|M| per body).
- **The ERC20 transfer's semantic profile** [measured, their App C]: 635 EVM
  steps; the costly content is **3 SHA3 calls, 2 shifts, 19 RAM accesses, 8
  storage accesses**. Everything else is machine.

**What the machine costs even with switches** — the measure the brief asked for:
under the switchboard the prover still carries (a) the 116K-row *structure* (VK,
folding object), (b) `1 + ℓ(1+|x|)` switch/consistency rows per step, (c)
fetch/decode (a code-memory read every step: 635 reads), (d) **all stack traffic
as memory operations** (~2/step ≈ 1,270 ops — pure machine, zero semantic
content), (e) the folding-verifier overhead amortized over β = 20 steps/fold.
Decompilation's target is exactly this list: every item goes to zero.

Formal content, placed honestly: Nebula's lemmas are about the *transform*
(circuits → circuit, satisfiability preserved) — as is powdr's verified optimizer
(§3). **Neither anchors at an ISA or EVM semantics.** What the instruction
circuits *mean* is, in both systems, an unverified Rust artifact. That is the
opening §6 walks through.

One recorded caution carried forward: Nebula's *memory* trick does not port to
our setting — in a monolithic STARK with post-commitment challenges,
fingerprint/logup memory is already the cheap thing
(`notes/lookup-ram-verdicts.md`, "the folding substrate does not port").

---

## §3. Prior art: Futamura-for-circuits mostly exists, in pieces, and nobody has the semantic anchor

Corpus and instrument, per doctrine — each absence claim names both.

1. **The compile-vs-interpret fork is as old as SNARK engineering (2013–15).**
   BCTV's TinyRAM is the interpreter stance; **Buffet** (eprint 2014/674, NDSS'15)
   is the specializer stance, at source: *"In Buffet, the C compiler produces
   constraints tailored to the computation… Buffet's circuits are not universal"*
   — loop unrolling, program-specific memory wiring, exactly moves (1) of §1.2.
   [measured, paper + NDSS text via web]. The zkVM era re-ran the interpreter
   side for tooling reasons; Nebula's switchboard and powdr are the pendulum
   returning.
2. **powdr autoprecompiles (2025–26) are automatic partial evaluation of zkVM
   circuits at basic-block granularity** — merge a block's instruction circuits
   into one, then constant-propagate and delete redundant memory traffic; >3.5×
   measured speedup [measured, powdr blog]. **And their optimizer is verified in
   Lean 4**: soundness ("each satisfying assignment of the output system has one
   of the input system with the same side effects") + completeness, against a
   ~500-line human-reviewed `Spec.lean`, with ~10K lines of AI-generated,
   CI-checked proofs [measured, powdr "Formally Verified Autoprecompiles"].
   **This is the closest existing thing to Futamura-for-circuits.** The two
   deltas that leave the prize on the table: (i) their refinement anchor is the
   *original instruction circuits* — themselves unverified Rust AIRs — not a
   machine semantics; (ii) basic-block granularity keeps the machine alive
   between blocks (PC, dispatcher, RAM bus all survive). Program-granularity
   with a semantic anchor is unclaimed.
3. **Hardware synthesis did interpreter-specialization first.** Singh–McKay,
   *Partial Evaluation of Hardware* (PEPM/LNCS 1999) and *Dynamic Specialisation
   of XC6200 FPGAs by Partial Evaluation* (FPL'98): specialize a general circuit
   at a slowly-changing input (their example: a decryption circuit at a fixed
   key) by rippling constants through gates [measured, titles+abstracts via web;
   bodies unread]. The idea transfers wholesale; the correctness story there is
   informal.
4. **"Decompilation into logic" is literally the EVM analysis lineage.**
   Gigahorse (ICSE'19) lifts EVM bytecode to three-address IR **in Datalog**;
   Elipmoc (OOPSLA'22) resolves operands/jumps for **99.5%** of sampled
   contracts (Gigahorse 62.8% fully-resolved; decompiles >99.98% of deployed
   contracts at least partially) [measured, papers' claims via web]. Unverified,
   analysis-oriented — but the front-end feasibility number we need: **dynamic
   jump resolution succeeds on essentially all deployed code** (§7.1).
5. **The Lean EVM semantics exists — twice.** (a) Nethermind's **EVMYulLean**:
   executable EVM+Yul model in Lean 4, **22,330/22,332 Cancun conformance tests**
   [measured, their blog/repo]. (b) Argot Collective's **EquiVM**: per-contract
   *refinement proofs in Lean* — bytecode refines a Sol⁻ spec, both revert
   identically or both succeed with identical storage/returns — against their
   EVMLean model, with real contracts done (WETH9, Dss, OpenZeppelin), built for
   LLM-generated proofs [measured, repo via web]. **EquiVM is the front half of
   our pipeline, already alive**: bytecode → checked high-level meaning in Lean.
   Nobody has the back half — high-level meaning → *emitted, proved circuit* —
   because nobody else has a proved emission pipeline. We do (§4).
6. **Distiller (eprint 2022/1557, S&P'23)** — compiles "an abstracted
   specification of the computation," provably safely, via a refinement chain
   over transition systems; zero follow-ups in the eprint corpus
   (`docs/SELVAGE.md` §5.3) [measured previously]. A decompiled EVM program *is*
   an abstracted specification; Distiller is the design's closest academic
   sibling, minus mechanization and minus the EVM front-end.
7. **The name "Futamura" in the ZK literature: not found.** Corpus: `~/paperbin`
   (1,218 full texts) — `grep -i futamura` → **0**; targeted web searches
   (Futamura × zkVM/SNARK/circuit ×2) → generic PL results only. Instrument
   limits: the IACR mirror is PDFs-only and was NOT swept full-text; ⚠ the
   shared scratchpad ft cache (`…/ca67a4c1…/scratchpad/ft/`) is currently
   **EMPTY (0 files)** despite PREFLIGHT recording it as populated to 2026/777 —
   flagged, someone's cache got cleaned. So: *the phrase* is plausibly novel;
   *the idea* demonstrably is not (items 1–3). Claim accordingly.

---

## §4. What our stack already provides, cited exactly

1. **The stance.** The kernel proves *semantic turns*, not VM steps — "a typed
   semantic transition's boundary is the state delta; its interior is an
   execution trace. The kernel's statements are boundary statements by
   construction — which is why they are cheap, and it is the same fact as 'we
   don't emulate a VM'" (`docs/SELVAGE.md` §2). Decompilation extends this
   refusal-of-the-machine to programs we did not write: an EVM contract's turn
   is its state delta, and the machine that computed it is interior.
2. **The emission pipeline — we already compile specific statements to specific
   circuits.** Per-descriptor Lean-authored AIRs with the drift gate closed:
   `breadstuffs/metatheory/EmitByName.lean` regenerates the entire deployed
   `circuit/descriptors/by-name/` surface *from the verified Lean emission*
   ("Law #1: the constraints are AUTHORED in the `Dregg2/Circuit/Emit/*`
   modules… Rust interprets; Rust authors nothing"), and its header records why
   the hand-transcription hop it deleted was a demonstrated forgery. The missing
   front end is exactly one thing: **EVM bytecode → Lean semantics**.
3. **The virtualization threshold.** `docs/COST-MODEL.md`'s exchange rate (one
   committed felt ≈ 3,120–12,331 field mults vs ~40 to virtualize; hash-bound
   iff Y > X with X ≤ 178, Y ≈ 890) prices the per-program-point
   materialize-vs-virtualize fork the decompiler faces at every wire.
4. **The zkML trace precedent — the EVM version of this is the design.**
   - `minidregg/Theory/ZkmlTensorOps.lean`: 13 constructors, total denotation
     (`TOp.denote`), one program with many readings (`run = fold denAlg`),
     transport theorems (`run_transport`, `arith_transport`) with the
     **gadget bill derived** (`TOp.arithmetic`: what a `RingHom` fails to carry),
     the `[N3-converse]` discipline (no data payloads in ops; constants enter as
     initial-context entries with roles), and computed teeth.
   - `minidregg/Compiler/ZkmlTraceCheck.lean`: the checked reader whose output
     type IS the intrinsically-typed trace — "the reader returned `.ok` is not a
     claim to be audited"; refusal, never repair.
   - `minidregg/Compiler/ZkmlEltwiseAir.lean`: ONE op end-to-end —
     `TOp.bin .add` → `eltAddSystem` → `emit` → descriptor, with
     `addDemoDescriptor_means_denotation`: *a total wire vector satisfying the
     emitted descriptor exists iff the denotation of the trace equals the
     claimed output*. And its honest boundary: `[EMIT-sound]` unchanged — prover
     acceptance still inherits the FRI/STARK floor.
5. **The seams the hard parts route to** (§7): `TwistContinuity`
   (`minidregg/Compiler/SparseAuthenticatedStateLogupBridge.lean:90` — the
   row-chained store-continuity relation) for storage; `VerifierEmbedding`
   (`minidregg/Selvage/HeteroComposition.lean:74` — B's witness type is A's
   proof type; `rung_sound` gives one rung per one-way embedding;
   `ivc_tower_sound` shows unbounded depth needs a self-embedding cycle) for
   calls; the accumulation/Depth stack for loops-as-folding.

---

## §5. The residual op-vocabulary, with ERC20 as the worked example

Stated the way `ZkmlTensorOps` states its constructors: an indexed signature
with a **total denotation**, deliberately the *residual* after specialization —
not the 141 opcodes. Scope, per the brief: the residual of the **solc-emitted
ERC20-class** (straight-line after jump folding, static memory offsets, static
keccak arities). Working name `Theory/EvmResidualOps.lean`.

**Types.** One value dtype: `u256` (address = `u256` with a 160-bit range fact;
`pred` = 0/1 in-carrier, exactly `ZkmlTensorOps.Dtype.pred`'s trick so `select`
stays degree-2). Context `Γ : List RTy`; ops append one wire; `Var` is de Bruijn.

**What enters as initial context, not as ops** (the `[N3-converse]` discipline,
mirrored from `ZkmlTraceCheck.WireRole`): calldata words at static offsets
(`role := input`), environment reads CALLER/ADDRESS/CALLVALUE (`role := env`),
program constants — the function selector, storage slot bases, the 160-bit mask
(`role := literal`). A residual trace that cannot name which calldata word
entered a wire cannot be checked against the transaction, same argument as
weights vs the weight commitment.

**The constructors** (each with the denotation question answered, not deferred):

| # | constructor | denotation (reference reading at `ZMod 2^256`) | why it survives specialization |
|---|---|---|---|
| 1 | `arith (k : add∣sub∣mul) (a b)` | mod-2^256 ring ops (wraparound IS the semantics) | the program's arithmetic |
| 2 | `cmp (k : lt∣eq∣sle…) (a b) → pred` | `if cmpB then 1 else 0`, as in `TOp.cmp` | require-guards, balance check |
| 3 | `bit (k : and∣or∣xor∣not) (a b)` | bitwise on the 256-bit representation | address masking |
| 4 | `shiftConst (n : ℕ) (a)` | `a·2^n` / `a/2^n` — **the shift amount is a payload ℕ, not a wire** | dynamic SHL/SHR died in constant-folding; what survives is linear |
| 5 | `iszero (a) → pred` | `if a = 0 then 1 else 0` | guard negation |
| 6 | `select (p : pred) (a b)` | `p·a + (1−p)·b`, degree-2, booleanity owed by `cmp` — verbatim the `ZkmlTensorOps` choice | folded short branches |
| 7 | `keccak (n : ℕ) (as : Fin n → Var Γ u256)` | an opaque family `K_n : (Fin n → u256) → u256` — a `FnId`-style *syntactic* id, semantics supplied by the instantiating layer | storage-slot derivation; **arity `n` is static** — the whole dynamic-length SHA3 machinery died |
| 8 | `sload (slot)` / `sstore (slot, v)` | against an explicit `Store` threaded by the trace state — the denotation is a state monad fold, the constraint side is a `TwistContinuity` bus | the 8 semantic storage accesses |
| 9 | `guard (p : pred)` | conjoin into the trace's success predicate | the require/revert residual (§7 note on revert) |
| 10 | `log (topics data : List (Var Γ u256))` | append to the effect list — boundary output, constrains nothing interior | the Transfer event |

**What is absent, and absent is the point**: PC, JUMP/JUMPI/JUMPDEST (resolved
at decompile time or refused), PUSH/POP/DUP/SWAP (the stack becomes de Bruijn
wiring — this is *literally* what the intrinsically-typed context does), MLOAD/
MSTORE at static offsets (scratch memory becomes wires; all 19 of the ERC20
transfer's RAM accesses are solc scratch for keccak input and ABI encoding —
they residualize to **zero ops**), CODECOPY/EXTCODE\*, GAS (refused, §7.5),
CALL-family (a stage boundary, §7.4), dynamic-length keccak (refused in v1).

**The gadget bill, derived as in `TOp.arithmetic`**: the fragment a `RingHom`
carries is {arith, shiftConst, select}; the bill is {cmp, bit, iszero, keccak,
sload/sstore} — comparisons and bitwise need limb/range decomposition (our
256-bit-over-BabyBear geometry: 8 lanes cannot injectively carry 32 bytes —
247.26 vs 256 bits, the recorded pigeonhole — so the ninth lane / injective
encoding is a *constructor-level* obligation here, not an afterthought), keccak
is a lookup/permutation gadget, storage is the authenticated bus.

**ERC20 transfer, worked** [derived from the OpenZeppelin transfer path Nebula
benchmarks — their App C profile: 3 SHA3, 2 shifts, 19 RAM, 8 storage, 635
steps]: context = {selector, to, amount (calldata); CALLER (env); slot-base
literals}. Trace ≈ mask `to`; 2× `keccak 2` (balance slots of CALLER and `to`;
the third SHA3 in their count is the allowance/dispatch path); `sload` ×2;
`cmp` (balance ≥ amount) → `guard`; `arith .sub`, `arith .add`; `sstore` ×2;
`log` (Transfer). **Roughly 15–20 residual ops from 635 machine steps** — a
~35× step-level compression before a single constraint is counted, and every
surviving op is semantic.

---

## §6. ⚑ The correctness statement — the whole point

"Does ONLY that program" = the emitted circuit's accepted relation EQUALS the
EVM semantics of that program on its stated state class. In Lean-statement form
(the shape, with every quantifier and the trusted base named — not yet a
theorem):

```lean
/- reference side: an executable EVM fragment interpreter, small-step, total
   via fuel; validated differentially against EVMYulLean/hevm on the fragment -/
def evmRun (P : Bytecode) (env : CallEnv) (σ : Store) : ExecResult
  -- ExecResult = .ok (ret : CallResult) (σ' : Store) (effects : List Event)
  --            | .revert … | .refuse …   (gas: see §7.5 premise)

/- the decompiler: UNTRUSTED, partial, refusing — its output is intrinsically
   typed (a term of `ResidualTrace P` cannot mention an out-of-scope wire),
   mirroring ZkmlTraceCheck's checked reader -/
def decompile (P : Bytecode) : Except String (ResidualTrace P)

/- per-program translation validation: the decompilation theorem.
   discharged per output, by decide/rfl/simp over the two folds -/
theorem decompile_faithful (P) (D) (h : decompile P = .ok D) :
    ∀ env σ, evmRun P env σ = denoteResidual D env σ

/- the emission theorem: the ZkmlEltwiseAir chain, instantiated at D -/
theorem descriptor_means_semantics (P) (D) (h : decompile P = .ok D) :
    ∀ (env : CallEnv) (σ σ' : Store) (r : CallResult) (fx : List Event),
      (∃ w, descriptorHolds (emit (constraints D)) (encode env σ σ' r fx w))
        ↔ evmRun P env σ = .ok r σ' fx

/- and the "ONLY" half is not free — it needs the boundary encoding injective,
   as a THEOREM with a name, never an assumption: -/
theorem encode_injective : Function.Injective (encode · · · · ·)
```

- **Quantified**: over *all* call environments and *all* stores in the stated
  class. v1 states it at the class of all well-formed stores; if a program's
  proof needs a reachability invariant (e.g. `Σ balances = totalSupply`), the
  class is **named in the statement**, never silently assumed.
- **The two directions have different jobs.** `→` (acceptance ⇒ semantics) plus
  `encode_injective` is **"does ONLY that program"** — nothing outside the
  program's graph is accepted, and no two boundary values collide into one
  accepted vector (the recorded 2^92.7 sibling-lane failure was exactly a
  missing injectivity theorem). `←` (semantics ⇒ a witness exists) is
  completeness — the honest prover is never refused.
- **The reference side**: our own *fragment* interpreter, not an import of
  EVMYulLean wholesale — the fragment is small (v1: the §5 vocabulary's
  footprint) and the fidelity anchor is **differential**: run the fragment
  interpreter against EVMYulLean/hevm on shared vectors. That register is
  Pickles-Phase-A ("differential fidelity, NOT machine-checked") and is stated
  as such. EquiVM's Sol⁻ route is the upgrade path: start from their checked
  bytecode-refines-Sol⁻ theorems and decompile Sol⁻ instead of raw bytecode.

**The trusted base, enumerated** (what a reader must grant, in order of pain):

1. Lean kernel + `[propext, Classical.choice, Quot.sound]` — same footprint the
   `ZkmlTensorOps` guards pin.
2. **EVM-fidelity**: `evmRun` = the deployed EVM on the fragment. Test-anchored
   (conformance + differential vs EVMYulLean's 22,330/22,332), not proved.
   This is a *modeling* assumption every EVM formalization on earth shares.
3. **`[EMIT-sound]`**: "the prover accepted, therefore `descriptorHolds`"
   inherits the undischarged FRI/STARK floor — unchanged from `ZkmlEltwiseAir`,
   and the honest pair is the recorded conjectured-130 / proven-51–73.
4. **Nothing else.** Not the decompiler (untrusted, per-output TV). Not the
   serializer (`EmitByName`'s gate). Not Rust (interprets only).

**Where this surpasses Nebula and powdr in kind, said precisely**: their
theorems (Nebula Lemma 3/4; powdr's Lean soundness+completeness) relate
*circuits to circuits* — satisfying assignments preserved across a transform
whose endpoints are unverified artifacts. Ours relates the **emitted circuit to
the machine semantics**, per program, machine-checked end to end above the
PCS floor. The switchboard is engineering with a satisfiability lemma; the
decompiler output carries a refinement theorem whose left-hand side is the EVM.

---

## §7. The hard parts, named honestly, each with its route

1. **Dynamic jumps.** solc-emitted code is push-jump dominated; Elipmoc-class
   analysis fully resolves operands for 99.5% of sampled contracts and Gigahorse
   decompiles >99.98% of deployed ones [measured, §3.4]. Route: the decompiler
   resolves what constant-folding reaches and **REFUSES the rest** —
   `ZkmlTraceCheck`'s posture, refusal never repair. Per-program TV makes
   incompleteness free: an unresolvable contract costs us a customer, never
   soundness. No completeness theorem over all bytecode is claimed, ever.
2. **Loops.** Two honest observations, then the seam. (i) *EVM has no unbounded
   loops* — gas bounds every execution; a 30M-gas block caps the cheapest loop
   at ~10^6 iterations [derived, folklore gas table — recalled]. So unrolling is
   always *possible* and usually *insane*; the COST-MODEL threshold decides
   per loop. (ii) Where unrolling loses, the loop body is itself a decompiled
   straight-line fragment and the loop is the recursion seam: fold the body's
   circuit — `SelfEmbedding` (`HeteroComposition`: unbounded depth needs the
   cycle; bounded depth is one rung each, "where heterogeneity is free"). This
   is where the sibling folding lane's story attaches: the folded object is the
   *residual body*, not a machine step — folding a 300-constraint body instead
   of a 116K-row switchboard is the same prize one level up. ERC20 transfer
   needs none of this (loop-free after folding).
3. **Storage.** The residual is 8 `sload/sstore` rows against the pre/post
   store commitment — exactly a `TwistContinuity` bus
   (`SparseAuthenticatedStateLogupBridge.lean`), with `[LOGUP-ADDRESS-LINK]` as
   the named open seam. Carried caution: do NOT import Nebula's memory
   machinery — post-commitment challenges already give the ~4-constraint/op
   regime in a monolithic STARK (`notes/lookup-ram-verdicts.md`). The real
   design fork is **what the statement binds**: a global storage root (Merkle
   paths ≈ 3,750/op re-enter and dominate the residual [derived, Nebula Table
   2]) vs the kernel-native committed store delta (our stance; the chain's
   consensus object binds the commitment). The kernel stance wins by ~2 orders
   on this program and is the one consistent with SELVAGE §2.
4. **Calls and reentrancy.** A static-target call composes two decompiled
   circuits: callee's proof = caller's witness — one `VerifierEmbedding` rung
   (`rung_sound`), state threaded through the storage bus. EVM call depth
   ≤ 1024 and gas make every call tree bounded-depth, i.e. the free regime.
   Reentrancy is not special: each re-entry is another rung with the store
   threaded between rungs — but say the open part out loud:
   `[COMPOSE-error]`/`[COMPOSE-fixedpoint]` are **left as obligation Props** in
   `HeteroComposition`, so the cross-circuit error accounting is stated, not
   proved. A **data-dependent callee** (address from storage) is the genuine
   wall: refuse, or leave a switchboard at that one site (§1.3 — the residual
   interpreter, priced at that site only).
5. **Gas.** Refused in v1, and the refusal shapes the statement: `evmRun` runs
   gas-free, so the theorem carries a visible premise — *it speaks about
   executions the deployed EVM completes within gas*. An OOG execution is one
   our circuit neither accepts nor claims. Path-specialized gas is *almost* a
   constant (per fixed control path) — the residue is EIP-2929 warm/cold access
   sets and memory expansion [recalled] — so the later upgrade is gas as an
   affine function of access-set boundary data, provable, not heroic. Do not
   let the coarse v1 premise be silent in any downstream citation.
6. **Revert semantics.** `guard` failure must yield the *revert* state (all
   writes discarded), not an unconstrained state. v1: the statement's `.ok`
   branch covers the success path, and the revert path is its own (trivial)
   circuit — two descriptors, one program, dispatch by the success bit in the
   boundary. Cheap, honest, and avoids in-circuit rollback machinery.

---

## §8. The prize, priced against Nebula's own numbers

Discipline from `docs/COST-MODEL.md`: every row names its unit; structure
constraints and committed-witness work are different columns and are never
composed; wall-clock appears only where THEY measured it. All in **their unit**
(R1CS constraints over their field, two field elements per 256-bit word) for
comparability.

**The switchboarded transfer** — what runtime specialization still pays
[derived from their Fig 2 sizes + App C op counts; consistency anchor: their
measured 1,300s → 5s]:

| item | count × unit cost | subtotal |
|---|---|---:|
| 3 SHA3-substitute calls | 3 × ≈24K | ≈72K |
| 2 dynamic shifts | 2 × ≈4.8K | ≈9.6K |
| 630 remaining steps, active opcode | × ~250–500 | ≈157–315K |
| stack+code memory traffic | ~1,900 ops × (4+rc) + scans | ≈10–30K |
| switch + input-consistency rows | 635 × (1 + ℓ(1+&#124;x&#124;)), ℓ=100 | structure-heavy, witness-sparse |
| **active witness per transfer** | | **≈0.25–0.43M** |

plus the 116K-row structure carried by the folding object, and the folding
verifier amortized over β=20.

**The decompiled transfer** [derived, bottom-up from §5's worked trace]:

| item | count × unit cost | subtotal |
|---|---|---:|
| u256 add/sub ×2, cmp ×3 | 5 × ≈300 | ≈1.5K |
| shifts (now by constants) | linear maps — **0** | 0 |
| keccak ×3 at fixed 64-B arity | 3 × ≈250 (their hash substitution) | ≈0.75K |
| 19 RAM accesses (static offsets) | became wires — **0** | 0 |
| 8 storage ops, logup bus | 8 × ~tens + binding surface | ≈0.5–1K |
| boundary encoding, injective | ~40 committed felts | ≈0.3K |
| guards, select, log | | ≈0.2K |
| stack / PC / decode / switches | **the machine — 0** | 0 |
| **total** | | **≈3–4K** |

**Read-off**: ≈**60–140× beyond the switchboard** on committed work, ≈30× on
structure (116K → 3–4K), and vs the unswitched universal step trace
(635 × 116K ≈ 73.7M constraint-instances) ≈ **20,000×** — each ratio labeled
[derived], none composable with the others, none a wall-clock claim.

Three honesty clauses that survive contact:

1. **Keccak is the elephant on every side.** Real keccak-f in R1CS is
   ~25–150K/permutation [recalled range from public implementations — not
   measured here]; Nebula substituted a cheap hash (their fn. 5) and so does
   this table. With real keccak the decompiled circuit is ≈80–450K and *still*
   wins by the same factors, because the bill is common — but the absolute
   numbers move by 100×. Whoever quotes this section quotes the hash choice.
2. **The win saturates at the proof-system floor.** At 3–4K constraints the
   prover is floor-dominated, not circuit-dominated — our own deployed point is
   P(b) = 3381·2^b + 766 permutations with grind alone at 47,917
   (`docs/COST-MODEL.md`, [measured]). A lone transfer is the B=1 regime
   (overhead `1/B + 1/n`, SELVAGE §2's own caveat). The deployment shape is
   therefore **many transfers per proof** — which the tiny residual makes
   natural (thousands of decompiled transfers fit where 635 switchboard steps
   sat).
3. **Storage binding can eat the prize** if the statement binds a global Merkle
   root (§7.3): 8 × 3,750 ≈ 30K re-enters. The kernel-native delta-commitment
   stance keeps the table above; the choice is architectural and is named, not
   defaulted.

---

## §9. The staged plan — one fragment end-to-end beats twenty opcodes with no path

The `ZkmlEltwiseAir` precedent applied: each stage lands a *complete* chain
(semantics → decompiled constraints → emitted descriptor → meaning theorem)
for a strictly larger fragment, and no stage hand-writes a constraint anywhere
but the Lean emit path.

- **Stage 0 — the eltAdd of EVM** (the cheapest end-to-end fragment): the
  five-opcode bytecode `CALLDATALOAD · CALLDATALOAD · ADD · MSTORE · RETURN`
  (u256 add of two calldata words). Needs: a ~10-opcode fragment interpreter
  `evmRun` in `Theory/`; `ResidualTrace` with constructors {arith, context
  roles}; `decompile` for straight-line code; the u256-limb `arith` constraint
  relation through the existing `emit`; and the Stage-0 instance of
  `descriptor_means_semantics` — the analogue of
  `addDemoDescriptor_means_denotation`, kernel-decided. Also the differential
  harness: `evmRun` vs EVMYulLean (or hevm) on the same bytecode+calldata
  vectors. **This stage is where the design is falsified or not**; everything
  in it reuses an existing pattern.
- **Stage 1 — guards and the gadget bill**: add {cmp, iszero, select, guard,
  shiftConst, bit}; the revert-path split (§7.6); `encode_injective` proved at
  the 256-bit/BabyBear geometry (the ninth-lane obligation). Fragment: the
  balance-check-and-update dataflow of ERC20 minus storage and keccak.
- **Stage 2 — storage**: `sload/sstore` on the `TwistContinuity` bus; the
  state-binding decision of §7.3 made and recorded; fragment = a two-slot
  read-modify-write program.
- **Stage 3 — keccak + the whole ERC20 transfer**: fixed-arity keccak gadget
  (hash choice named per §8.1); `decompile` handles the solc dispatch prologue
  (static jump folding); land `descriptor_means_semantics` for the real
  OpenZeppelin transfer bytecode, and the §8 table gets re-derived as
  [measured] against our own emitted descriptor's counts.
- **Stage 4 — the composition frontier** (each named, none blocking 0–3):
  calls via `VerifierEmbedding` rungs; loops via unroll-or-fold with the
  COST-MODEL threshold; gas as affine boundary data; the EquiVM/Sol⁻ front-end
  as the industrial-strength jump resolver.

**Refusal doctrine throughout**: at every stage `decompile` refuses what it
cannot prove — refusal is a lane's success condition, not a failure. The
switchboard is the fallback *inside* the design (§1.3), never a reason to
defer the specializer.

---

## §10. Loose ends flagged upward

1. ⚠ The shared eprint full-text cache
   (`/private/tmp/claude-501/-Users-ember-dev-breadstuffs/ca67a4c1…/scratchpad/ft/`)
   is **empty** — PREFLIGHT records it populated to 2026/777. Absence claims in
   §3 were made against paperbin + web only, and say so.
2. The brief's "Nebula's ~30×" attributes the constraint reduction to the
   switchboard; at source it belongs to the memory technique (§2 table). The
   framing survives — stronger, in fact: the switchboard never shrank the
   structure at all, which is exactly the "machine still standing" the
   decompiler removes.
3. Vega (2025/2094) is credentials, not EVM — the MSR-page 2026 "Nebula:
   Proving Machine…" entry is left to the sibling lane covering Nebula/Vega at
   source.
4. powdr's verified-optimizer result (§3.2) is worth its own read by whoever
   picks up Stage 0 — their spec/proof split (500-line human spec, AI-generated
   proofs under CI) is the same shape our per-program TV would industrialize.
