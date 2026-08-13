# Spain and Celer: verdicts

2026-08-13. Both read at source; eprint-vs-OSDI diffed; figures rendered to
read what the text omits.

## Spain — REJECT as design, ADOPT as evidence (three citations for §5)

The one-constraint div/sqrt is real but the saving is not
verify-don't-compute — it is **deleting the range checks**, bought three
ways, every one unavailable to us: squares-are-nonnegative (a theorem of
ORDERED fields, false in F_p, where every F_{p²} element is a square); the
magnitude bound lives in the DARK integer PCS (hash PCS have none — range
checks come straight back); and rounding is never proved (one global
denominator, ε absorbs the residue — a Kulisch accumulator for the whole
program, with ε buying the right to skip renormalization). Plus: interactive,
designated-verifier (**the verifier holds the RSA factorization**, Appx. C),
2^-40 soundness, ~11× per-constraint backend penalty (their own Otti A/B).

**The §5 upgrade:** Spain PROVES a composition lemma (E.1 Lemma 6) whose
conclusion — `out ∈ (G∘F)^δ(in)` — is verbatim Zamir's δ-consistent set,
which Theorem 1 shows is the entire output ball for adversarial F′. Correct
lemma, vacuous conclusion, gap delegated to "numerical analysis" in their
own §5. At their published ML parameters the ReLU guarantee is δ = √ε =
2^-20, and Zamir's trigger weight at GPT-2 effective depth (≥24) is **≤ 10 —
ordinary weights**. New sentence available: *the best ε-carrying system in
the literature is exploitable at its own published parameters with ordinary
weights at GPT-2 depth.* (Spain does not cite Zamir; DeStefano is on both
Spain and approximate-sumcheck.)

**Ozaki-lane ratios STAND** (3.48× / 10.28×, re-verified against ZKLP Table 1
at source). Spain doesn't make addition cheaper; it deletes the rounding
proof, which a bit-exact design cannot do.

**Publishable freebie:** Spain skipped tables on its §2.2 premise (tables
only win at ~2^8) — and its own GELU costs **15 constraints/element vs one
2^16 lookup**. Their strongest arithmetization is ~15× more committed work
per activation than the design they declined to evaluate.

**The real find is a citation: eprint 2026/347 (relaxed Mod-PCS from ANY
PCS, Papadopoulos–Papamanthou group)** — Spain's range-check-free economics,
but for EXACT integers, hash-based, transparent, PQ. The Ozaki gap attacked
from the commitment side. Unimplemented asymptotics aimed at ≥2^10-bit
integers — read-and-price BEFORE more limb-based constraint counting.

## Celer — ADAPT, gated on one measurement

Transferable content is exactly one constant: **grand product 10m field ops
vs logUp-GKR's 43m** (their own §4.4 attribution). The curve-specific
framing (sublinear group ops) is worth nothing on a hash stack. Gotchas
found by reading what the paper doesn't say:

- **The crossover is in their own Figure 4a and never in the text**: at
  n=2^16, logUp-GKR WINS below m≈2^21 (0.6× at 2^20). The advantage is
  asymptotic in m/n; m/n is invariant under table fusion; at our 3–20
  tables (m/n ≈ 675) we are comfortably past it; at 80 tables we are not.
  **Table count is now a first-class prover-design variable.**
- Soundness is O(mn/|F|) — one extension degree more than logUp-GKR at our
  shapes, eating a third of the 2.4×. The n-factor looks removable with one
  O(n) check (Σe′ = m against committed p_j) — do that first if building.
- Set membership only (multiplicities unconstrained) — replaces the
  activation-table lookup, NOT a bus/memory argument. No preprocessing
  (U_j is data-dependent per proof). No ZK or extractability statement.
- Baselines are self-implemented, single-threaded; logUp-GKR was added
  post-review (acknowledgments) — the 2.4× is plausibly against a
  partially-tuned baseline.
- **Same group as zkGPT and OpenLLM (Xuanming Liu again)** — three papers,
  one contact.

**Spike:** bare grand product over BabyBear-deg4 at m=2^28 vs our own tuned
logUp-GKR, in isolation. ≥2× or nothing else recovers it. Net expectation
if it holds: ~1.4–1.8× on the lookup argument, less end-to-end (the Ω(m)
query-column floor is untouched).
