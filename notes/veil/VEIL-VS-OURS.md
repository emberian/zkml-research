# Veil 2.0 against our temporal, program and protocol logics (initiative 19)

2026-11-06. Veil read at `verse-lab/veil` `4eaf93e9` (2026-11-07 UTC), cloned to `/Users/ember/src/veil`,
built on the Mac (1,287 jobs, about 10 min, 1.7 GB `.lake`, no Mathlib). Pilot package:
`/Users/ember/dev/veil-pilot` (own git repo). Tags: [READ] read in source, [MEASURED] run here,
[INFERRED] reasoned, not checked.

## 1. What Veil 2.0 is [READ]

- Apache-2.0. Lean `v4.35.0`, Batteries/Aesop `v4.35.0`, **no Mathlib**. Dependencies are all
  verse-lab: `lean-smt` (`v4.35.0-veil-no-mathlib`, cvc5 native plugin), `Loom` (monadic program
  logic: the action language and its WP), `Lasso` (LTL model checking, 54.7k LOC), `Lentil` (TLA-style
  LTL proof mode, ported from coq-tla), `VerifiedHAMT`.
- DSL: `type`, `relation`/`function`/`individual` state, `immutable`/`param`/`instantiate` theory,
  imperative `action`s with `require`/`assume`/`:|` choice, two-state `transition`s, `ghost` relations,
  `safety`/`invariant`/`assumption`, `temporal` LTL with `𝒲ℱ`/`𝒮ℱ`, `Enabled`, `⟨a⟩`, `↝`.
  Distributed DSL (`network (synchrony, loss, channels, order, faults)` + per-node `program`)
  compiles to an ordinary module. This is the "PlusCal-style" part.
- Commands: `#check_invariants` (SMT inductiveness, CTI widget, stubs for manual proofs),
  `#updr` (invariant synthesis), `#model_check` (explicit-state BFS, parallel, compiled),
  `#simulate`, `sat/unsat trace` (symbolic BMC), `#temporal_check` (LTL with fairness),
  `prove_temporal_by` (Lentil proof mode, all instantiations).
- `tla-to-veil` skill (`.agents/skills/tla-to-veil/`, symlinked as `.claude/skills`): an agent recipe
  with a validation protocol against TLC (invariants agree, known violations reproduce, distinct-state
  counts match, temporal properties agree). It is a prompt, not a verified translator.

### What "verified model checker" means here [READ]

- Safety (`Veil/Core/Tools/ModelChecker/Concrete/`): the BFS (sequential and map-reduce parallel) is
  written in Lean with proofs that every reported violation comes with a trace valid in the system
  (`searchResult_sound`, `recoverViolationTrace_sound`) and that a completed search saw every
  reachable state (`bfs_completeness`). Trace soundness needs nothing about the hash. Completeness
  takes `Function.InjectiveOn fp.view sys.reachable` as a hypothesis
  (`SequentialLemmas.lean:126`): the default fingerprint is a 63-bit hash, so a "no violation" verdict
  is sound only if the hash has no collision among reachable states. That is assumed, not proved. TLC has
  the same exposure and prints a collision probability; Veil does not print one.
- The executable system comes from the DSL by `MultiExtractor.NonDetT.extractList` with an
  equivalence obligation discharged by `veil_extract_list_tactic` at elaboration, so the checked system
  is tied to the specification's semantics, not to a hand-written twin.
- Liveness (`Veil/Core/Tools/LivenessMC/`, Lasso): LTL → TGBA translation, product, SCC emptiness and
  fairness routes, each proved; `checkFair_empty_unsat` says an `.empty` result means every labelled
  run satisfies φ, given `FiniteReach` and `LawfulHashable`. `LawfulHashable` is equality-aware
  hashing (hash sets compare states by `==`), not collision freedom, so the liveness side has no
  fingerprint assumption. `FiniteReach` is a hypothesis of the theorem; the runtime `fair` route's
  certificate is `True` (`LivenessMC.lean:326`), so finiteness is the user's to know (easy for
  bounded models like ours).
- Not every Veil path is message-only: `#updr` certification produces kernel-checked invariant or
  counterexample theorems and reports any `sorryAx` fallback (`docs/Synthesizer-Guide.md:163`).
- **The model-checking run is not a kernel certificate.** `#model_check` and `#temporal_check` execute the proved
  algorithm in the interpreter or as a compiled binary and print the verdict. No theorem about the
  module is added to the environment, and nothing like `#assert_compiled` pins the trust. The trust base of
  a verdict is the Lean compiler/interpreter, the runtime, the hash assumption, and that
  `FiniteReach` holds (on the default `fair` route it is a hypothesis of the soundness theorem, not
  something checked). Veil's own doc says a passing run "is a test, not a proof": it covers one
  instance and one theory.
- `prove_temporal_by` gives a real kernel theorem for all instances, but it assumes the invariants
  (`hInv`) rather than proving them, and proofs consider only runs where every step is an action:
  deadlock semantics differ between `#temporal_check` (stutter forever) and proofs. Composition of
  `#check_invariants` and the temporal theorem is the user's job. With `veil.smt.trust false`, SMT
  steps are reconstructed by lean-smt; the default trusts cvc5.
- "2–20x faster than TLC": not re-measured here. `scripts/tlc-vs-veil-mc-evaluation.py` is their harness.

## 2. Ours, by construct

Census by a read-only helper lane; every L-rung is from the files and their check scripts, nothing
was rebuilt for the census.

| Construct | Ours (path) | Rung | Veil's counterpart |
|---|---|---|---|
| LTL □/◇/◯ | `breadstuffs/metatheory/Dregg2/Proof/Temporal.lean` (400): over one schedule; `always_iff_reachable` (`:280`) takes step-invariance and initial truth as premises, so it is not an independent schedule/reachability equivalence; the existing ◇ lemmas are trivial (the logic can state more than the library proves) | L2 | Lentil: LTL proof mode, `↝`, WF1, `always_induction`, tactics (`tintro`, `tsuffices`...). **Theirs ahead** in proof support. |
| CTL, μ-calculus | `Proof/CTL.lean` (625, all eight operators as lfp/gfp), `MuCalculus.lean` (409, `encode_EF` etc.) | L2 | none (Veil is linear-time only). **Ours ahead** on branching time. |
| Fairness | `Proof/Fairness.lean` (709): van Glabbeek B-justness; `CTLLiveness.lean` `af_plain_fails_on_stutter` | L2 | WF/SF as LTL atoms, checker routes for fairness [LSFZ16, PAT]. Different notions, not compared property by property here; theirs is checked end to end, ours is proof-only. |
| Hoare / wp | `Proof/WP.lean` (404, `vcg_run_sound`, partial correctness over `σ → α → Option σ`) | L2 | Loom (monadic WP over nondeterminism + exceptions), automatically generated VCs to SMT. **Theirs ahead** in automation. |
| Refinement / simulation | `Proof/LTS.lean`, `Refine.lean`, `CoinductiveAdversary.lean` + vendored paco | L2 | No refinement-between-modules command in what I read (absence of a command, not a proof that Lean-level refinement is impossible in Veil). Ours has the coinductive machinery; neither side automates it. |
| ω-automata, runtime verdicts | `Dregg2/Stream/` (DOmega, Büchi/co-Büchi, LTL3 verdicts, `verdict_viol_sound`, `windows_compose`, `stream-check` exe over live logs) | L2→L3 | Lasso: verified LTL→TGBA + emptiness, offline over a finite system. Different problem: ours monitors a prefix of ONE run, with window certificates; theirs decides all runs of a finite model. Lasso's translation could generate our monitor automata (see §4). |
| Protocol models | `Distributed/` (21.4k LOC: EpochReconfig, CellMigration, CrashRecovery, Blocklace...), `Consensus/Safety.lean`, BFT/GST, minidregg hand-rolled `Reachable` + `reachable_inv` | L2 | Veil's whole point: TransitionSystem class, SMT inductive invariants, UPDR, explicit checking. We hand-roll `Reachable` per model and have no checker on the Lean side. **Theirs far ahead** in automation; ours proved for all sizes where proved. |
| Model checking | TLA+ `breadstuffs/spec/CellModel.tla` (1094, TLC, no liveness), loom twins, 27 herd7 litmus files; no Kani/GenMC (plans only, `DreggNet/docs/engine/21-FORMAL-MODEL.md`) | L2 | `#model_check`/`#temporal_check` inside Lean on the same spec that is proved. **Theirs ahead.** Our loom/litmus target real Rust memory models, which Veil does not touch. |
| Compiled-check discipline | `#guard`, `native_decide` pinned by `#assert_compiled` (which names and re-runs compiler trust; it does not remove it, `Dregg2/Tactics.lean:185`), extracted checker exes (`stream-check`, `calltree-check`, `tree-check`) re-run by strangers | L3 | `#model_check`/`#temporal_check` verdicts are messages with no pinned claim; `#updr` emits kernel theorems. Per path: ours pins compiled claims, theirs does not for model checking. |
| Toolchain | breadstuffs/metatheory v4.30.0 + Mathlib `1c2b90b1`; minidregg v4.35.0 + Mathlib `56a00585`; obend v4.35.0; DreggNet/drorb/dregg-serve-spec v4.30.0; chokepoint bare v4.33.1 | | v4.35.0, no Mathlib. Same toolchain as minidregg; a Batteries/Aesop pin clash with minidregg's Mathlib is likely, so a separate package with a bridge, not a dependency [INFERRED]. |

## 3. Pilot 1: the chokepoint device with an asynchronous host [MEASURED]

Model: `/Users/ember/dev/veil-pilot/VeilPilot/ChokepointAsync.lean` (about 260 lines with runs).
Source: `degg-research/experiments/chokepoint-step/CommitStep.lean`, whose `commit_before_forward`
is proved for a synchronous step (persist and forward in one transition); the asynchronous refinement
is the named residual (Astra S06 in `degg-research/research/governance-astra-response.md`). The model
splits the step into `arrive` (the device takes `occ := hw`), `hostPersist` (durable leaf + durable
counter), `hostForward` (only after the persist, the host obligation as a guard), and adds `crash`
(volatile state lost), `restore` (CommitStep's counter rule), `saveSnapshot`/`rollback` (an adversary
replays one older authentic durable store). Instance: 2 frames, capacity 2, `hw ≤ 4`. 21 checks,
interpreted, about 4 minutes on the Mac. Log: `runs/chokepoint-run4.txt` in the pilot repo.

| Configuration | commit_before_forward (safety) | persisted frame eventually forwarded (SF forward, crashes, no rollback) | honest crash recovered | admitted frame forwarded, no crash |
|---|---|---|---|---|
| A. counter at admission (CommitStep), host may persist out of order | **FAILS**: arrive 0, arrive 1, persist 1, save, persist 0, forward 0, crash, rollback, restore. The saved store already has `dCtr = hw` (the highest occurrence committed first), so the counter check passes and the device resumes without frame 0's leaf, which has left | fails (bricks) | **fails** | holds (415) |
| B. counter at admission, persists in order | holds (212 states) | fails (bricks) | **fails**: arrive, arrive, persist one, crash, restore: `dCtr < hw`, halted forever | holds (239) |
| C. counter at the durable commit, atomic with the write | holds (306) | holds (723) | holds (383) | holds (277) |
| D. counter at commit, bump then write (two steps) | holds (490) | fails | **fails**: bump, crash, restore halts | holds (371) |
| E. D plus the naive repair "accept a store one behind" | **FAILS**: arrive, bump, save, persist, forward, crash, rollback, restore | — | fails (a second torn commit) | — |

Every configuration also fails `admitted_forwarded` with crashes: a frame admitted but not yet durable
dies with RAM, neither forwarded nor refused. That is inherent to any design that admits before
committing; the sender must retry.

What this found that we did not have:
1. With the counter advanced at admission, the restore check `c = hw` alone does not certify a complete
   durable prefix once persists can complete out of order (A). CommitStep's second conjunct
   `n = log.length` compares against the in-RAM log, which a real crash destroys, so after an actual
   crash the counter is the only hardware-anchored fact. Codex's review is right that A is a
   counterexample for this pilot's refinement, not for CommitStep as written: CommitStep never models a
   crash. The pilot names what the asynchronous host must add: in-order durable commit, or a counter
   that counts durable leaves.
2. Even in order, the CommitStep placement turns every honest crash between admission and persist into
   a permanent halt (B). `rollback_halts` cannot tell a torn commit from a rollback. Astra S06 asked
   for no-crash premises; this is the concrete reason.
3. Advancing the counter at the durable commit fixes both (C) **only if** the counter bump and the
   durable write are one atomic step. Split into two steps (D), the brick returns; the obvious repair
   (E) reopens the rollback. This is the state-continuity problem that Memoir (Parno et al., S&P 2011)
   and Ariadne (Strackx and Piessens, USENIX Security 2016) address [INFERRED from memory of those
   papers, not re-read here]; the device needs one of their constructions, or a TPM-style counter
   whose increment is bound to the write. No novelty is claimed for the observation.
4. Weak fairness on `hostForward` is not enough once crashes are allowed: crashing after every restore
   starves forwarding. The checker found that lasso; the property needs strong fairness or eventual
   quiescence of crashes.

Effort: about 1.5 hours including learning the DSL, three model revisions after Codex's review. No
proof was attempted: these are finite-instance checks (Veil's own words: "a test, not a proof").

## 4. Pilot 2: custody handover for the dark-learning fork [MEASURED]

Model: `/Users/ember/dev/veil-pilot/VeilPilot/CustodyHandover.lean`. We have no handover
(`notes/dark-learning-handover-2721.md` §1: "none: a static committee"), so this is a design model of
plain resharing for n-of-n additive custody: old custodian `i` sends `sub i j` to new custodian `j`,
`j` combines, `i` erases. The adversary is mobile, holds up to n − 1 custodians per period, and a held
custodian leaks what it holds after every step. Deductions are a three-round peeling closure over the
row and column sums, written as ghost relations (sound, not shown complete for general linear
algebra). Instance: 3 custodians. Runs: `runs/handover-run7.txt` (about 2 minutes, compiled; commit `564fab5`).

| Configuration | Result |
|---|---|
| window counted in both periods, senders erase subshares | secrets hidden, 12,901 states |
| window counted only in the new period | **old secret leaks**: corrupt 2 before, start, corrupt 1 and 0 in the new period while they still hold old shares |
| both periods, senders keep subshares until the end | hidden, the same 12,901 states (the kept subshares never add knowledge under the both-periods rule) |
| liveness, no adversary, one crash allowed | **fails**: one crashed custodian blocks `combine` for everyone, forever |
| liveness, no crash | completes under weak fairness (1,195 product states) |
| non-vacuity | `ph ≠ after` added as an invariant fails (the handover finishes); the adversary is live (row 2) |

What it says: the both-periods budget rule (the proactive secret sharing rule, not ours) is what makes
plain resharing safe here, and n-of-n additive custody cannot hand over past a single crashed
custodian. That second point is the operational price of the dishonest-majority choice in note
2721 §2a, alongside the proving-wire price: any handover that tolerates a crash needs a threshold
sharing (t-of-n resharing, or the paper's DPVSS). Neither result is new in the literature; what is new
for us is a checked model of the handover we lack, with the corruption budget stated as code.

Codex's review caught a budget bug in an earlier version: parties held when the window opened were
not charged to the new period, so the adversary could hold four of three. Fixed in `startHandover`.

Effort: about 1 hour of modelling. One tooling lesson: an 18-statement `procedure` inlined into ten
actions made elaboration run past 40 minutes at 12 GB (two runs abandoned); moving the deductions into
ghost relations brought the whole file to about 2 minutes.

## 5. Recommendation, per construct

| Construct | Verdict | Why, and how |
|---|---|---|
| Veil as a design-space checker for new protocols (async devices, handovers, gossip, rotation) | **Adopt, as a separate package** (`/Users/ember/dev/veil-pilot` pattern) | Both pilots produced counterexamples in minutes that our hand-rolled `Reachable` + induction style would only meet as a failed proof, if at all. Same Lean v4.35.0 as minidregg and obend; no Mathlib, so no Mathlib store issue. Not a dependency of minidregg (Batteries/Aesop pins vs Mathlib's [INFERRED]) or breadstuffs (v4.30.0). A bridge, when one is needed, carries the transition system and the property statement into our tree, not Veil's tactics. |
| Model-checking verdicts as evidence | **Adopt with our trust rules on top** | A `#model_check` verdict is a message from a proved algorithm run by the compiler, conditional on hash injectivity. Count it as [MEASURED] on one instance, never as a theorem. Where a verdict must carry weight, reify it: identity fingerprint (no injectivity premise) + the soundness theorems + `native_decide` pinned by `#assert_compiled`. |
| `#check_invariants` (SMT inductiveness, CTIs), `#updr` | **Borrow the workflow; adopt per protocol** | We have nothing like CTI-guided invariant discovery. For all-sizes proofs of a pilot model, run `#check_invariants` with `veil.smt.trust false` (lean-smt reconstruction) and `#updr` certification (kernel theorems). Not done in this pilot. |
| Lentil LTL proof mode, `prove_temporal_by` | **Borrow** for liveness proofs; our `Proof/Temporal.lean` cannot state WF/SF and has only trivial ◇ lemmas | Note the gap: proofs assume `hInv` and exclude deadlock-stutter; compose with the invariant proof ourselves. |
| Lasso (verified LTL → TGBA, emptiness, LTL satisfiability) | **Borrow for Stream/** | Our streaming monitor (`Dregg2/Stream/`) takes hand-built deterministic automata. Lasso can check that a policy formula is satisfiable and not valid (vacuity guard), and its translation is a candidate generator for the safety/co-safety fragment we monitor. A monitor still needs determinisation or a fragment restriction; Lasso's TGBA is nondeterministic. |
| Distributed DSL (`network`, `program`) | **Borrow the vocabulary** | Its network options (sync/async, lossy, set/multiset, fifo, faults) are a checklist our protocol notes should state explicitly. |
| `tla-to-veil` skill | **Ignore for now** | We have one TLA+ spec in scope (`breadstuffs/spec/CellModel.tla`, no liveness). Port it only if CellModel comes back into play; the skill's TLC-agreement protocol (state counts, known violations) is the right acceptance test. |
| CTL / μ-calculus, justness, coinductive bisimulation | **Keep ours; candidate contribution** | Veil is linear-time only and has no branching-time or refinement command. Our `CTL.lean`/`MuCalculus.lean` are proof-only and tied to one system; they would need generalising before they are useful upstream. |
| What Veil would want from us | **Contribute** (offer, do not push) | (1) An identity-fingerprint mode and a verdict-as-theorem command (closes the injectivity premise and the message-only gap; `#assert_compiled` is the pattern). (2) The two pilots as examples of crash/rollback and mobile-adversary modelling, if they survive review. (3) The weak-fairness-under-crash lasso as a doc note in the Temporal Checker Guide. |


## 6. Cross-model review

`codex exec -m gpt-6-astra` attacked the draft comparison and the pilot claims; output committed as
`codex-astra-review-1.md` beside this note. Accepted and applied: C1 restated as a counterexample to
this pilot's refinement, not to CommitStep (which never models a crash); the liveness property needed
fairness on `bumpCounter`; restore now re-queues persisted frames; the handover budget bug (above);
trace soundness vs completeness of the checker separated; `LawfulHashable` is not collision freedom;
`#updr` does emit kernel theorems; "ours ahead on trust" narrowed to per-path; our
`always_iff_reachable` premise noted. Not yet acted on: running the pilots at larger instances.

## 7. Follow-on: Ariadne state continuity for the chokepoint device (ember's choice)

Ariadne read from `/Users/ember/paperbin/strackx2016-ariadne-state-continuity.txt` (USENIX Security
2016, open access; §4.1 Listing 2, §4.2 Gray codes, §5 a 4,823-line proof of the base
algorithm). [READ]

- **Veil model** `/Users/ember/dev/veil-pilot/VeilPilot/ChokepointAriadne.lean` (commit `1f83fe8`):
  `#check_invariants` with `veil.smt.trust false` passes every obligation (333 reconstructed, none
  trusted) except the variants' own non-omission clause, which is the attacks; for Ariadne's
  parameters that clause is vacuous, so the induction closes (Codex's review forced this split: an
  unproved clause left in the antecedent would have made the rest conditional). Model checks
  (`frame := Fin 2`, `runs/ariadne-run15.txt`): safe under rollback (1,874 states) and rollback plus
  counter tampering (2,684); honest disk: safe and never halts (14,318), `recovers` (6,678 product
  states) and `committed_forwarded` (23,558) hold; seven controls fail as they must; accept-one-behind
  omits (even with the honest disk, which still holds the stale package) and one-increment retrieve
  omits (Ariadne's Appendix A.3, 17 steps, three crashes). [MEASURED]
- **A vacuity the controls caught**: without an idle step, every infinite run of the bounded instance
  must crash forever, so "once crashes stop, it recovers" held with 0 product states explored. Adding
  `idle` and an impossible-consequent control (`ctrl_same_antecedent`) fixed it. Worth a Veil doc note.
- **Counter word** `/Users/ember/dev/veil-pilot/VeilPilot/CounterWord.lean`: a binary word torn by a
  crash mid-increment reads below the old value (1 → 2 interrupted reads 0); the Gray word never does.
- **Device, kernel-proved for every hash and every run**:
  `/Users/ember/dev/degg-research/experiments/chokepoint-step/AriadneStep.lean` and `GrayCounter.lean`
  (commit `248f1cf`, bare Lean 4.33.1 and 4.35.0, axioms `propext`, `Classical.choice`, `Quot.sound`):
  `non_omission`, `restore_accepts_only_current`, `occ_binds`, `honest_never_halts`,
  `honest_recovers`, `gray_one_flip`, `grayEnc_injective`; falsifiers `tolerateOne_omits`,
  `singleInc_omits` by `decide`.
- **Codex astra review 2** (`codex-astra-review-2.md`): duplicate forwards are real (recovery
  re-queues), so `occ_binds` was added; a wrong control comment fixed; model boundary named (MAC,
  synchronous atomic writes, NV single-bit atomicity and counter width, membership not order,
  purge only initial, single instance).
- **Not done yet**: the refinement theorem from `AriadneStep.step` to Veil's
  `ChokepointAriadne.relationalTransitionSystem`. Feasibility shown: Veil's generated transition for
  `commitInc` reduces definitionally (`exact ⟨hpc, hh, rfl⟩` after unfolding `Next`, `NextAct`,
  `commitInc.ext.derived_eq`, `commitInc.ext.tr`); the rest is list-index bookkeeping for package ids.
