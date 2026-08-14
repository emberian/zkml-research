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
- ⚑ **The biggest untaken lever is neither field nor system: sumcheck-batch
  the reduced opening — ×2.13 on the wrap, ×2.05 per turn.** And it is the
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
