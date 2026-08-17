# The leaf/recursion architecture, in exact counts

2026-08-14. Answering ember's question — *should the leaf and recursion systems
differ?* — with a new instrument and a Lean interface.
Full note: `notes/leaf-vs-recursion.md`.

## ⚑ THE ANSWER: nobody changes proof system between layers, and our problem is that THE LEAF IS TOO SMALL

**SP1 and OpenVM, read at source: neither changes proof system between leaf and
recursion.** Both change **parameters** per layer, plus one **hash-field** swap
at the last STARK layer. ⚠ And **OpenVM's blowup RISES** 1→2→3→4 while **ours
FALLS** 6→3.

**The deciding quantity is `K = wrap/leaf`: ours is 26.9 — the leaf is 3.7% of
the object. Theirs is < 1.**

> ***Our problem is not the proof system. It is that the leaf is too small.***

A heterogeneous stack is a real option, but it is not the lever here; **making
the leaf carry more work is.**

## ⚑ The hashing hypothesis FAILS — and this is the second refutation today

I predicted the in-circuit verifier would be hashing-dominated, which would
make binary fields the escape. **Measured: it is ARITHMETIC-bound — 36.45%
hashing vs 60.75% arithmetic. A free hash is worth only ×1.57.**

⚑ **Hash-dominance is a symptom of FIELD MISMATCH, not of a proof system** —
the *same* FRI verifier in BN254 is 78.3% hashing native, **99.46% emulated.**

> **So the binary-field case must be argued on cryptanalytic surface, not on
> verifier cost.** (The hash-landscape lane reached the same conclusion from
> the other direction: proving converges, verification does not.)

## ⚑ The IOP is ~0.2% of the bill; the PCS is ~99.8%

Spartan's entire two-sumcheck IOP at `n = 2^20` is **~70 permutations** against
FRI's **38,168**. So ***"cheapest system to verify in circuit" ≈ "cheapest
PCS"*** — the proof system barely enters. (Only FRI has a reachable in-circuit
verifier today; the rest are Lean/paper-only and labelled derived.)

## ⚑ The lever is WIDTH, not height — refuting our own prose

`Δperms/Δm = 209 = 19×11` **exactly constant** across `m ∈ [9,16]`;
`ΔHornerAcc/Δm = 0` **exactly**; `HornerAcc = 20,564·q` linear with **zero
intercept**, max residual 0.00.

Decomposition of the deployed 38,168: **transcript absorption of OOD values
29.2% · per-query leaf sponge 64.9% · Merkle paths 5.9%.** So **94.1% of
hashing and 88.5% of arithmetic are width-driven** — which **refutes
`recursion-tower-profile.md`'s own prose** that most in-circuit permutations
are 2-to-1 compressions along query paths. Corrected at source.

## The knobs, priced

- **Deployed `lb=6` is the MINIMUM** of an iso-security grid **nobody had
  computed**, by 1.5–3× — and the minimum sits on a power-of-two rung, so it
  is fragile.
- **Folding arity is a null knob** (−2.0% hashing, +0.3% arithmetic).
- **Extendability costs ×27.9 per turn, paid whether or not a chain is ever
  extended.** Bounded-depth aggregation is where heterogeneity is free;
  **unbounded IVC needs a cycle.**
- ⚑⚑ **THE ×2.13 LEVER IS NOT REACHABLE OVER TWO-ADIC FRI — and the reason
  nobody took it was never written down.** A sumcheck over `Σ_k α^k v_k`
  terminates in a claim about **the MLE of the opened values at a random
  point**, which the verifier can discharge only by recomputing it (Θ(N), no
  saving) or by opening it from a commitment to `V` — and **`V`'s only
  commitment is a Merkle leaf, which supports no evaluation opening.** The
  verifier already holds every value in the clear. ***Lever 3(b) is a PCS
  REPLACEMENT, not a backend rewrite*** — the Jagged→BaseFold / Stacked→WHIR
  move SP1 6.4 and OpenVM 2.0 both made. **The ×2.13 is the sumcheck endpoint.**
  ⚠ And three docs carried three different verdicts on the same phrase
  **about different circuits**, which nobody had noticed: pure upside · an
  *ownership* obstruction ("it's in the fork") · and "now MARGINAL", true **of
  gnark only.**
- ✅ **What IS reachable, and landed** (`emberian/plonky3-recursion@0ed1182`):
  the **algebraic half**. A matrix opened at `P` points was paying `P` Horner
  chains per query **over the same opened row** — restructured `q·P·n →
  q·n + P·n`. **Measured as a WORK claim with no latency column offered,
  because none was measured**, controls identical:
  **`HornerAcc` ×1.806 · `Alu` ×1.651 · ALU table 2¹⁸ → 2¹⁷ · wrap cells
  58,249,216 → 40,554,496 = ×1.436** — and ⚑ **the Poseidon2 share moves
  36.45% → 52.36%, so a free hash goes from ×1.57 to ×2.10.** Win grows with
  `q` (×1.928 at q=57).
  ⚑ **The falsifier fired exactly where predicted**: the old law
  `HornerAcc = 20,564·q` had intercept **exactly 0**; the new one is
  `10,306·q + 20,516`, still `max|resid| = 0.00`, and
  **2·(20,564 − 10,306) = 20,516 exactly** — so **99.77% of the reduced
  opening was the two-point case that nothing was sharing.**
  **Verdict: VK rotation, not a wire change** — the child proof is untouched
  bit for bit and the accepted predicate is identical (one expression
  re-associated), but every in-circuit FRI verify emits a different op list.
  ⚠ **The `Cargo.toml` pin was deliberately NOT moved**: the re-emit chain
  ends at a **deployed on-chain verifier**, which is short-pause-list item 3.
- ⚑ **A latent contract found en route, worth more than the 1.44×**:
  `HornerAcc`'s accumulator is **not a constrained operand**, and
  `compute_schedule` infers chains from **ADJACENCY** — so two independent
  chains back to back produce an invalid trace whose *only* symptom is
  `OodEvaluationMismatch { index: 2 }`, **naming neither op nor cause.** It
  held only because the one emitter that produces `HornerAcc` happened to
  satisfy it. Now a build-time refusal, **made refutable by four tests because
  it had only ever been seen to ACCEPT.**
- ⚠ **Substrate, said out loud**: the in-circuit FRI verifier is pre-existing
  **Rust-authored** circuit logic — *debt by the house law.* This change
  authored no constraint, and **nothing here is Lean-authored or verified.**
- **Next lever, newly visible**: `recompose` now sets the wrap's global max
  height — 2¹⁸ rows for 160,263 ops at `npo_lanes = 1`, 3.9% of its cells,
  **and the lane count has never been priced.** And it is the
  **precondition** that makes the hashing argument true at all (a free hash
  goes ×1.57 → ×4.5). **Already named in `WRAP-NATIVE-HASH-DECISION.md` and
  never taken.**

## The Lean interface — it did not exist, and now does

`Selvage/HeteroComposition.lean`. The existing `Reduction` forces one shared
`W`/`Idx`/`Chal`, so **all seven instances are intra-system** — heterogeneity
was unstateable. **`VerifierEmbedding A B` makes B's *witness* type A's *proof*
type**, with `rung_sound`, `ivc_tower_sound` (**unbounded depth needs a
SELF-embedding**), and the tooth that matters:
**`widened_relation_refuses_embedding` proves the type is `IsEmpty` when a
verifier gadget accepts strictly more than the verifier it stands for.**

## ⚠ Corrections, including to my own brief

- **My "net ≈65× worse per turn" was WRONG.** 65× is the ratio of *loss to
  saving*; **the per-turn total is ×3.21** (independent grid: ×2.96). It had
  already propagated into a note's summary. Corrected at source.
- ⚠ **A live vacuity with a docstring claiming the opposite**:
  `Dregg2/Circuit/RecursiveAggregation.lean`'s `real_engine_sound` discharges
  *"EngineSound is INHABITED — the headline is not vacuous"* **at an instance
  where `RealProof := Unit`, `acceptAll ≡ true`, and every hash is
  constant-zero.** A `P → P` witness with extra steps, **not disclosed in the
  file.** Flagged, not fixed.
- ⚠ `OB2_depth_composition_nonneg` composes protocol **rounds**, not stack
  **layers** — reading `(t+k)·ε` as a per-layer bound is a category error.
- ⚠ **The additive basis-binding gap should land before anything recurses over
  additive FRI.**
