# GKR substrate: closer than we thought, and our Ext6 theorem can't see the wall

2026-08-13. Design memo at `notes/gkr-substrate-design.md` (829 lines), five
cards in WORKSTREAMS. These are the findings that change decisions.

## ⚑ Our own soundness model has a missing leg

`Assurance/MixedFieldBudget.lean` carries named theorems
`baseGateExt4Fri_secure_16` / `ext6GateExt4Fri_secure_75` /
`unifiedExt6_secure_137`. **But its proximity leg is
`mixedProximityTerm = codeLen / proximityCard` — a FIELD-SIZE-bound term.
There is no query-count leg in `mixedFieldSoundness` at all.**

The grey-lit sweep established that the FRI/WHIR **query phase is
query-count-bound and extension degree does nothing for it** (OpenVM2
itemizes `whir_query 100` while its sumcheck legs sit at 122/127). So
**`unifiedExt6_secure_137` is a theorem of a model that cannot see the wall
it would have to clear.** Not false — it is true of its model — but the model
is missing the binding constraint.

**Recommendation: add the query leg to the model BEFORE deciding the field.**
And note the pin we adopted needs re-derivation: grey-lit said "Ext5, not
Ext6," derived against zkVMs running Ext4/Ext5 — **it did not know we already
hold Ext6**, built, with fieldness proved via a Kummer tower and no
`native_decide` (`prover/src/field6.rs` + `Compiler/Ext6Conformance.lean`).
⚠ And Ext4/Ext5 exist as types **nowhere in our tree**.

## ⚑ The p3 pitfall, mechanism verified at source — worse than "no final check"

At our pin the sumcheck round message is `[h(0), h(∞)]` and **`h(1)` is
DERIVED by the verifier as `claimed_sum − h(0)`**. So `h(0) + h(1) =
claimed_sum` holds **by construction**: the round check is not skipped, **it
has been made a tautology**, and 100% of soundness relocates to one terminal
check in the caller. The compression was chosen for prover speed (the file
cites eprint 2026/587 Lemma 2) and **deleted the check as a side effect.**

Two laws for our substrate, both of which Selvage's engine already obeys:
1. **No partial verifier.** A `PendingClaim` that only `settle(terminal)` can
   discharge; on the Lean side, **no lemma of the form "if every round check
   passes then…"**.
2. **Never compress `h(1)` out of the wire.** Cost: one field element per
   round — ~480 bytes at m=20/Ext6, against 327 KiB proofs. The `{0,1,∞}`
   basis stays a prover-internal trick.

## The substrate is much closer than the convergence note implied

- **Selvage's sumcheck protocol layer is already degree-generic**: `{d : ℕ}`
  runs through `sumcheckRound_prob`, `adaptive_sumcheck_soundness` (→
  `v·d/|F|`), `AdaptiveUnionBound`; and the round-chain skeleton
  (`roundSum_fold/_zero/_succ/_last`, `glue`) is proved for an **arbitrary**
  `g` with no multilinearity hypothesis. Degree 1 is pinned only at the
  realizer layer.
- **`Assurance/AirSumcheckQuadratic.lean` already did the degree-2 port end
  to end** (916 lines, CLOSED), with the terminal check **factored** as
  `Â(r)·B̂(r) − Ĉ(r)` and soundness derived by one `simpa` from the generic
  theorem. **Degree 3 is a line-for-line port of a template that exists.**
- Degree ≤5 decided, 3 as the landed rung: GKR fraction-tree layers are
  `eq·(p_L·q_R + p_R·q_L)` = degree 3; zkML matmul is `eq·(Â·B̂−Ĉ)` = degree
  3. **Same rung serves both**, and soundness cost is negligible
  (60/2^186 at m=20, d=3, Ext6) — **degree is not the soundness problem.**
- Dominant NEW proof term: **multilinear Schwartz–Zippel** (`≤ m/|F|`,
  ~80–120 lines) — Selvage's SZ today is univariate only.

## ⚑ The Binius64 pitfall, reproduced inside our own repo

`prover/src/tower256_kernels.rs` already holds `equality_weight` (a two-vector
`eq`, char-2 only) and `fraction_add_layer` (**the inversion-free fraction-tree
layer — the LogUp/GKR step**) — **with no protocol driver above it.** So the
GKR fraction tree's kernel exists in our Rust, **in the binary line**, while
the sumcheck engine lives in the **prime line**. Our Lean is already
`variable {F} [Field F]` and the general `eq` specializes to the char-2 kernel
by `ring`, so two instantiations of one interface is cheap — ⚠ but the
`{0,1,2,3}` node set needs `ringChar F > 3`, so char-2 needs different nodes
or coefficient-form messages. **OPEN fork, deliberately not closed.**

## The commitment seam, stated and NOT solved

`Selvage/Commitment.lean`'s `OpeningScheme` is **positional**
(`openAt : … → ι → Op`) — a vector commitment, **the wrong shape for a
multilinear claim.** Needs a sibling `MultilinearOpeningScheme` with
`openAt : … → (Fin m → F) → Op`, copying that file's discipline **including
its equivocator with a refutation theorem**. What we hold is univariate
RS/FRI proximity throughout; `Selvage/MultiplicativeMleTerminal.lean` is the
one seed for a BaseFold bridge. **That bridge is a campaign, not a memo
section.**

## Corrections to my brief, and to the lane's own claims

- **"umem" does not exist** — zero grep hits. The memory model is
  `Kernel/SparseAuthenticatedState.lean` + `Kernel/State.lean`, and the proof
  side is `TwistContinuity` — *the statement a Twist argument must prove*,
  named but **unproved**, with mutable-RAM consistency an explicit residual.
- **GKR / layered circuits / zerocheck / two-vector `eq` in Lean: all absent**
  (verified by grep over our trees).
- `GOAL.md:1135` claims `gate_defect_table`/`prove_gates`/`verify_gates`
  landed; **those identifiers are not in `prover/src/sumcheck.rs`.**
- Upstream Plonky3 HEAD has since added a `generic_degree` module — not at our
  pin, so "degree-2-pair only" held as briefed, but the shipped systems
  clearly needed generic degree.
- The lane corrected two of its own claims in place, and both were the same
  mistake: **carrying a neighbouring repo's convention across a boundary** —
  minidregg has exactly one `@[export]` (not zero), and uses
  `#guard_msgs in #print axioms` (308 files) where breadstuffs uses
  `#assert_axioms`, which `Kernel/Camera.lean:30` says does not exist there.
