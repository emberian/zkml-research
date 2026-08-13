# Implementation readiness: what is verified, what must be transported

2026-08-13. Two lanes closed the gap between "recorded in notes" and
"dispatchable into Selvage." Both corrected me; both improve the plan.

## Mechanical verification of the audit-theorem legs (not docblock reading)

A lane re-elaborated the three light-client files from source and ran
`#print axioms` against fresh oleans. All nine theorems depend on exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`ofReduceBool`, no custom axioms, no `#guard`. Locations confirmed:
`Selvage/LightClientSound.lean:520`, `LightClientFS.lean:303`,
`LightClientGrinding.lean:455`, with the necessity witness at
`LightClientGrinding.lean:812` proving `1/|F₅| < 9/25` strictly.

**Two precision corrections to our own record:**

1. **"The bound is attained" is true of the EXACT-WORD sibling, not the
   deployable δ-headline.** `lightClientSound_exact` attains 1/|F| with
   equality (`phantom_forging_prob` = 1/5). The δ form has honest
   union-bound slack — `phantom_delta_prob_eq` computes true probability
   1/5 against a bound of 2/5, and the file says so itself. Anywhere we
   have written "sharp, attained" about the deployable statement, narrow it.
2. **ε_beacon: we hold the MECHANISM, not the statement.** Selvage has no
   `Sel`, no audit rate, no fire event (grep confirms). The grinding theorem
   gives a *multiplicative* (t+n) try-count factor on the challenge oracle —
   which lives on the **ε_chk side** of the FS/ROM model — where the audit
   note's ε_beacon is an *additive* degradation of the selection probability.
   What is machine-checked is the phenomenon (selection made after seeing
   oracle answers costs the option-count factor, and no fixed-shape bound
   survives). Implementation must **transport** it to the Sel object: new
   statement work, consistent with our own claim-2 correction ("cited
   lemmas, not the theorem").

**Two transport obligations for the ε_chk leg**, now precisely known: the
corruption predicate is *δ-far-falseness*, not "τ_t fails R" (a word δ-close
to a satisfying codeword sits outside the hypothesis), and the event is
anchored at the honest fold/satisfiability interface — the gap to the
prover's own recommitments is exactly ε_bind, so the decomposition is
consistent *because* the audit statement prices ε_bind separately.

Nuance worth having: `[ACC-extract]` remains open in the light-client
vocabulary, but `Selvage/ZkExtraction.lean:781`
(`extractChain_committed_seam`) closes a composed binding seam on the ZK
flank at unique decoding — reusable machinery closer to hand than we thought.

## The SIS lane's self-correction, and the fact that came out of it

Its earlier law — "lattice-PCS-friendly primes and FRI-friendly primes are
disjoint" — was **right for the family it read and wrong as stated**. The
coupling (splitting governed by `v₂(q−1)`) holds only for **power-of-two
negacyclic** rings `X^d+1`. For conductor η not a power of two, splitting is
governed by `ord_η(q)`, which is *independent* of two-adicity. Neo/SuperNeo
exist to exploit exactly this and say so — and their power-of-two parameter
set uses "Almost Goldilocks" = Goldilocks − 32, which drops `v₂(p−1)` from
32 to 5: the law executed as a design decision in the one set that could not
escape it.

**The computation that matters, verified three ways: `Φ_{3^k}` is
irreducible mod KoalaBear at every `3^k` tested** (ord₈₁(KB) = 54 = φ(81);
KB mod 81 generates all 54 units). So `R_q = F_q[X]/Φ₈₁` is **a field** —
maximal inertia, strictly better than Goldilocks (2 factors) and M31 (6).
Meanwhile KoalaBear fully splits `X^d+1` for every `d ≤ 1024`, which is why
the negacyclic PCS family is genuinely dead there. **A lattice commitment
over unmodified KoalaBear is arithmetically possible, and KoalaBear is the
best of our five candidates for one.**

**Verdict unchanged, reasons replaced: BUILD-TOWARD (formalization) / WATCH
(deployment).** Because: (1) the KoalaBear-compatible ring family contains
**no PCS** — Neo/SuperNeo are folding schemes; every lattice PCS on the
shelf is negacyclic. The escape exists; nobody has walked through it.
(2) The escape carries an **unpriced bill**: non-power-of-two cyclotomics
give module-BKZ a subexponential speedup (Ducas–Engelberts–de Perthuis),
unquantified for these parameters anywhere. (3) Non-full-splitting costs the
NTT (both Neo and Greyhound say so). (4) **ZK is structurally absent** —
Hachi has zero occurrences of "hiding"; Akita hard-`compile_error!`s on
`zk + akita` — and Selvage carries a large hiding corpus. (5) The "128 bits"
in this family traces to a 2018 enumeration-era estimator ⇒ **~98 bits
core-SVP**, our own quote-the-flattering-number class appearing inside an
assumption we would be adopting. (6) The floor is moving: 2026/607 costs
Dilithium 3.65–6.09 bits.

Also corrected: Hachi's 55 KB is **estimated**, its 227 ms is a composite
with a third-party tail, and its prover is 6–12× slower than Greyhound's;
RoKoko (13.04 ms verify) is the current challenger, not Hachi.

## The lane's own lesson, worth keeping verbatim

*"A law that holds in every case you looked at is a law about where you
looked."* It excluded the folding family for being estimate-only, and the
folding family held the structural answer. The tell it chased rather than
smoothed: a table listing Neo's fields as Goldilocks and M61, which should
have been impossible under its own law.
