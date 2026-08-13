# SIS/lattice sparsity: the retraction, the discovery, and the Lean objects

2026-08-13. The lane retracted its own central law mid-delivery and the
correction ends in a discovery that is ours.

## The retraction, and what replaced it

Claimed: "lattice-PCS-friendly primes and FRI-friendly primes are disjoint."
**True only for negacyclic (X^d+1) cyclotomics** — there, splitting is
governed by v₂(q−1), the quantity FRI maximizes. Non-power-of-two conductors
DECOUPLE. Neo/SuperNeo exploit exactly this and say so — their "Almost
Goldilocks" is Goldilocks−32, subtracted precisely to destroy two-adicity:
the law, executed by its victims as a design decision.

**The computation that decides it: Φ_{3^k} is IRREDUCIBLE mod KoalaBear** —
R_q is a FIELD, maximal inertia, strictly best of our five candidate fields
(Goldilocks splits in 2, M31/M61 in 6). Meanwhile KoalaBear fully splits
X^d+1 for every d ≤ 1024, so the shelf PCS (Hachi/Greyhound/LaBRADOR — all
negacyclic) are genuinely dead there. **A SIS commitment over unmodified
KoalaBear is arithmetically possible, and KoalaBear is the best field for
one. Nothing has walked through that door yet.**

## Verdict: BUILD-TOWARD (formalization) / WATCH (deployment). Not adopt.

The compatible ring family contains no PCS; the escape carries an unpriced
bill (Ducas et al. 2025/1904: non-power-of-two cyclotomics give module-BKZ a
subexponential speedup — THE sharpest open item, unquantified anywhere);
non-full-splitting forfeits the NTT (both Neo and Greyhound say so); ZK is
structurally absent (Akita has a literal compile_error! on zk; Hachi's body
greps 0 for "hiding") against Selvage's large ZK corpus; and the security
labels are soft — LatticeFold/Neo's "128 bits" traces to a 2018
enumeration-era estimator run and re-derives to **~98 bits core-SVP** (our
flattering-number class, in the wild, inside the assumption we'd adopt),
with the floor eroding another 4–6 bits (2026/607). Also: Hachi's 55 KB is
ESTIMATED not measured; RoKoko (13 ms verify) is the real Greyhound
challenger; Hachi's parameters are rank-1 Ring-SIS chosen by a bare
heuristic.

## The Lean objects (impl-ready)

1. **The conductor theorem — novel, checkable, OURS**: Φ_{3^k} irreducible
   mod KoalaBear (ord₈₁(KB) = 54 = φ(81)), currently a Python computation.
   The statement any future lattice decision rests on. Machinery exists:
   `metatheory/Dregg2/Crypto/InvertibilityNorm.lean` runs the same CRT/
   min-norm apparatus at toy parameters. → DISPATCHED.
2. **Close ArkLib's `Guarded.lean:116/:155`** — two sorries tainting Hachi's
   entire openingChain certificate; proof plans in their own docstrings;
   the compilation half we own. Days-scale, high leverage, upstream gift.
3. **The convention-in-the-type SIS budget** — core-SVP vs gate-model vs
   enumeration-era δ as a type-level tag, instantiated below 1: the
   two-regime calculator's third family.
4. Two-way trade: import ArkLib's LyubashevskySeiler (0-sorry, proves our
   named gap) against our CRT construction + teeth (which their file lacks).

Method line worth keeping verbatim: *"A law that holds in every case you
looked at is a law about where you looked."*
