# The multilinear seam is one RBR instance, not a new abstraction

2026-08-13. `notes/multilinear-pcs-landscape.md` (1692 lines).

## ⚑ My brief's premise was wrong, and it shrinks the job

I briefed that `Selvage/Commitment.lean`'s `OpeningScheme` is *positional* and
therefore "the wrong shape," needing a sibling with
`openAt : … → (Fin m → F) → Op`.

**That is the KZG/homomorphic shape. NO hash-based multilinear PCS has it.**
In BaseFold, WHIR, Ligerito and every Ligero/Brakedown descendant the
commitment **IS a Merkle vector commitment to a codeword** — exactly our
existing `OpeningScheme`, **reusable unchanged** (verified verbatim at ZCF23
p.20, Haböck p.8, WHIR Construction 5.1). The opening is an **interactive
reduction**, and `Rbr` → `Depth.lean:1982` → `FiatShamir` → `AccRbrBcs`
**already compile it.**

**So the deliverable is ONE `RbrKnowledgeSoundness` instance, not a new
commitment abstraction.** ⚠ And changing `openAt`'s index type would have
built **a mirror no candidate can instantiate** — the exact failure the house
memory warns about, and I briefed it.

## The recommendation, with the path spelled out

**BaseFold at Reed–Solomon, in Selvage's own unconditional `(1−ρ)/3` band,
packaged round-by-round.** Then WHIR-UD (Thm 5.2).

Two facts make it the shortest path, both about theorems we already hold:
- **`Proximity.lean:321` and `MultiplicativeMleTerminal.lean:210` are the SAME
  OPERATOR**, and `foldMleVariables_booleanMobiusPolynomial` **is already
  BaseFold's central identity** — completeness is a composition of held
  theorems.
- The fold-chain-consistency step (which the lane first called "the whole
  risk," as an MCA application) is **elementary and costs ZERO error** —
  `codeword_eq_of_close_of_close` is deterministic. It is **ZCF23's own Lemma
  8**, and `RateRegimeSelector`'s `oneThirdUD` band is exactly the radius it
  needs — **arrived at independently.**

**Genuinely new work: five items** — Möbius round-trip, tower-fold induction,
a degree-2 honest sumcheck family, `relDist_fold_le`, and the RBR instance.
**No conjecture. No new proximity result.** So "all of them need a proximity
result we don't have" is *not* the outcome.

## Three findings that change other plans

1. ⚑ **Jagged alone is a green theorem that commits to nothing.** It has **no
   cryptographic content** (zero grep hits for extract / binding /
   knowledge-sound / round-by-round) — which is *why* it is tractable. I had
   it ranked as a large win; it is a large **convenience**, and it must sit on
   top of a PCS that does the security work. C7 re-scoped accordingly.
2. ⚑ **The highest-leverage item was in no lane's top pick**: **MCA at the
   1.5-Johnson bound is proven for arbitrary linear codes by ELEMENTARY
   COUNTING** (GKL 2024/1810, Khatam 2024/1843 — grep-verified: zero
   function-field or Hensel machinery). **It upgrades the radius of everything
   without touching BCIKS §5.**
3. **Capacity is refuted over prime fields with smooth domains — our exact
   setting** — and the proven alternative is cheap: **WHIR-UD costs 4× proof
   size, 3.4× verifier, and 0× PROVER** vs WHIR-CB.

## Our MCA theorem is better than the printed Lemma 4.10

WHIR's Lemma 4.10 as published has `min{1−δ_C/2, B}` where it must be **max**
(its own Cor. 4.11 confirms), and Def 4.9's `1−B` must be `1−B*`. Ours is
stated for an **arbitrary generator**, and `herr_mono` repairs a step the
paper's proof uses silently. **Nothing needs undoing.**

## Cheapest open action

**TensorSwitch 2025/2065** is on disk, unassessed, **takes our
`CorrelatedAgreement` predicate as its hypothesis**, and has the RBR section
nobody else has. Read §3.19 against Crites–Stewart.

Also recorded: **11 errata in source papers** and **7 corpus
misidentifications** (`tensorcommitments.pdf` is an arXiv ML paper; a
"successor to Zinc" filename is actually a competitor; 2026/1367 has six
identical copies and one truncated `.txt`).
