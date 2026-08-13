# Field choice: KoalaBear everywhere — the memo's verdict and its corrections

2026-08-13. Final lane of the campaign. Full memo published as an artifact by
the lane (v4, with its v1 error retracted in-place — the discipline held).

## The verdict

**KoalaBear everywhere. Binary towers as the committed second field. Not
Goldilocks, not M31, not the BFV limbs.** The case is *constraint degree,
not hashing speed*: measured at our pin, KoalaBear's Poseidon2 is only ~2%
faster natively — but BabyBear's `3 | p−1` forces a degree-7 S-box that
floors the production blowup (`plonky3_prover.rs:126`) and forces 8 quotient
chunks in Ext4 where degree 3 needs 2. Crossing to sumcheck the two-adicity
advantage (27 vs 24) evaporates — FRI consumes it, sumcheck doesn't — and
constraint degree becomes round degree with no rate knob to trade against.

**Seam rule**: two 31-bit primes in one system is strictly worse than one —
KoalaBear everywhere or BabyBear everywhere, never per-subsystem. The one
seam worth paying is prime↔binary-tower, and minidregg already holds ~9,750
lines / ~311 theorems / 0 sorry of it, unwired to breadstuffs.

## The live risk, honestly

The peer's 2.07× Goldilocks-over-BabyBear recursion measurement is the
strongest anti-31-bit evidence — but ~75% of a Plonky2 recursive circuit is
in-circuit Merkle hashing, i.e. exactly the deg-7 S-box and deg-4 extension
KoalaBear removes and halves. It reads as "the default is wrong," not
"64-bit is right." **KoalaBear-vs-Goldilocks recursion exists in no harness;
adding it to the already-field-generic goldibear repo is days.** If
KoalaBear doesn't close most of the 2×, 64-bit wins and the memo re-opens.

## Hard prerequisite, with a soundness catch inside it

The in-AIR Kimchi/Wrap verifier pads to exactly 2^21 rows; at KoalaBear's
two-adicity 24 with log_blowup 6 the ceiling is 2^18 — **it does not fit**
without the per-descriptor blowup knob (`descriptor_ir2.rs:7196` names it).
And that knob's stated prerequisite is a real finding regardless of field:
**the recursion path reads `num_queries` from the inner proof and never pins
it against a configured count — masked today only because every child runs
19 queries.** Fix that first, field or no field.

## Corrections the memo lands on OUR notes

1. **BFV-limbs-as-packed-sumcheck-fields: REFUTED.** The Laminate/719 lane's
   "strongest transfer result" dropped the (2k−1)d numerator from the p^k
   comparison — zero saving at λ=100 — and the limbs' two-adicity is
   consumed by the FHE NTT. `vfhe-shortest-path.md` corrected in place.
2. **"Stwo's constraint blowup is additive with FRI blowup": REFUTED at
   source** (whitepaper Eq. 34 states the identical bound; Eq. 35 is worse).
   The nonlinear lane's M31/Stwo substrate recommendation loses its main
   plank.
3. Ext soundness: the Fenzi–Sanso loss and the Crites–Stewart Elias-radius
   correction are the SAME 1/log p term — do not double-count; ~1.5 bits at
   our knobs. **Ext4→Ext6 buys zero bits (their Lemma 3.5); Ext6 overshoots
   128 by 57 bits while paying every sumcheck round; Ext5 is the right
   degree.** MixedFieldBudget's question has a sharper answer than either
   of its own branches.
4. SP1's KoalaBear rationale **does not exist publicly** (empty commit body;
   the reasoning lives in Plonky3 PR #329). **Ceno left Goldilocks FOR
   BabyBear** (2025-08-26); nobody moved to Goldilocks in 2025–26.
5. "DEGF" is unsourceable; DeepProve is BaseFold-over-Goldilocks (watch for
   FRI-M61 conflations — that figure is OpenLLM's own system).

## Field-independent and first

`MixedFieldBudget.lean` proves the deployed challenge split at **16 bits**
(base-field gate batching + sumcheck) — identical under every candidate
field, and worth more than any migration. Fix order: the 16-bit hole and
the num_queries pin BEFORE any field work; then the KB-vs-GL recursion
benchmark (days); then decide.
