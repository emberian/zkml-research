# The inspiration sweep: four contradictions, one port, and four vocabularies we never searched

2026-08-13. Three lanes (eprint full text, arXiv cs.CC + ECCC, arXiv cs.PL/LO).
Notes at `inspiration-sweep{,-cc,-pl}.md`, ~95 files to `~/paperbin`.

## ⚑ 1. The highest-value find: a certificate CATALOGUE meets our FS leg

**Dumas–Kaltofen–Villard (ISSAC 2011→) define "essentially optimal" =
verification linear in input size — our boundary criterion, named, in 2014** —
and they hold a *catalogue* of protocols: rank (2 matrix-vector products +
n^{1+o(1)}), determinant, characteristic and minimal polynomial, Frobenius
form, positive-semidefiniteness, rank profiles.

**And their protocols are two-round Σ-protocols compiled with Fiat–Shamir AS A
HEURISTIC, with no round-by-round soundness — precisely the leg Selvage holds
and nobody else does.** Absence checked: `interactive certificate` → 5 hits in
25,765 eprint texts, none this line; zero in `~/paperbin`.

**The two halves have never met, and joining them is a port, not a campaign.**
It lands on the ML workload directly. **This is the near-term item.**

## ⚑ 2. CONTRADICTION — the boundary compiler exists (SELVAGE §5.3 is wrong)

**Distiller (eprint 2022/1557, IEEE S&P 2023)**: *"A user translates to
constraints **not the original computation but an abstracted specification of
it** … the first in this area to perform such transformations in a way that is
provably safe … 1.3–50×, and in some cases better asymptotics."* Mechanism: a
composable refinement chain `T_I ≤ T_E ≤ T_S` over transition systems, with
obligations discharged to SMT — and **they state the mechanization is a free
choice.**

Our *"nobody has turned boundary choice into a discipline"* is **false**. What
survives is narrower and still ours: **the cost theory** (which abstraction is
cheapest, and why) and **the Lean instantiation**. It has **no follow-ups** in
25,765 eprint texts.

## ⚑ 3. Semirings PRESCRIBE the emitted AIR's shape (answers open question 3)

Green–Karvounarakis–Tannen (PODS'07) Prop 3.5: **transport commutes with a
value-ring change iff the map is a homomorphism**; Thm 4.3: semantics in *any*
K **factors through the free object.**

**So the emitted AIR should be a syntactic expression over ℤ-coefficients with
each concrete ring a valuation — NOT a `BabyBear → BabyBear` function.** That
is a design prescription, not an analogy. Independently: **Kovach–Kjolstad,
PLDI'23 — a compiler proved in Lean 4, parametric in the semiring, ~540
lines**; and eprint 2022/587 argues for *"agile proof systems where the ring
can be switched through the software life cycle."*

`semiring provenance` → **0 hits in eprint, 0 in our notes.**

## ⚑ 4. Two more contradictions

- **"Value-ring polymorphism must be designed in from day one" is NOT
  supported.** Hierarchy Builder exists precisely to evolve algebraic
  hierarchies *"without breaking user code"*, and MathComp completed that
  retrofit. **The true narrower statement: cheap iff constraints consume the
  ring through an interface, ruinous iff `Felt` leaks everywhere — a check,
  not a deadline.**
- **"There is no semantics of Rust" is false as written** — CatCrypt (eprint
  2026/604) ports *"the hax pipeline in Lean (AST, denotational semantics,
  compilation phases)"* with `ImpExpr` modelling safe Rust, across 172
  protocols. **The house doctrine's conclusion survives; its stated reason
  does not.** Restate it.

## 5. The cost of a boundary is a conserved PRODUCT

Four non-communicating literatures say the same thing in different variables:
`b + c ≥ d` (Dell–van Melkebeek), `queries × communication ≈ n` (RVW IPPs),
`space × help = Ω(n²)` (streaming), `proof-length × queries ≈ n` (MAPs).

⚠ **Scope correction (the lane's, and correct)**: Dell–van Melkebeek is about
*generic* NP relations; **it does not touch structured relations — Freivalds is
unconditional.** What it does say: **a boundary compiler must exploit
per-family structure, and must be redeemed INTERACTIVELY, never precomputed.**

⚑ And **RVW Thm 1.3 (AffineMem completeness) is our organizing sentence,
proved**: every low-depth computation's boundary is a sparse affine system.

## 6. A deployed commit-then-audit protocol with a broken published bound

**Randomized Partial Checking (2012/063)** — deployed in Civitas and
Scantegrity — whose published bound was **"(3/4)^t and not 2^{-t} as
claimed"**, because the audit selection is **pairwise-dependent for PRIVACY**
and the adversary spreads cheats across pairs.

It does **not** refute `AuditSampling.lean` (our sequential theorem assumes
independent per-round draws, so an RPC-shaped deployment falls *outside* it
rather than getting a wrong number) — **but it is the named instantiation
hazard for `expOver`, with a documented cost in the base of the exponential.**
Add to the audit prior-art file; it is not among its six families.

## 7. Also new, and each touches an open question

- **Paneth–Pass 2026/662** — a mergeable SNARG that is **depth-linear and
  size-independent**, killing exponential-in-merges degradation. **Resets the
  bar our accumulation-depth work is positioned against.**
- **ZODA 2025/034** — sampled rows/columns **are proofs of their own
  correctness**: the limit case of a boundary carrying its own certificate.
- **Campanelli–Hall-Andersen 2024/1548** — author over ℤ, reduce mod arbitrary
  p. A **third, different** answer to the value-ring question.
- **Kothapalli–Parno, Algebraic Reductions of Knowledge** — a composition
  calculus **whose objects are relations.**
- **Klauck**: a proved **√n floor** on the one-message-plus-sampling boundary
  of a bilinear form.

## ⚑ 8. Vocabularies we have never searched in

**computer-algebra certificates · semiring provenance · descriptive complexity
· refinement calculi · interactive proofs of proximity.**

And the sharpest one: **rational proofs are already in `~/paperbin` and cited
ZERO times in our notes — the economics half of our audit theorem has a
literature we own and have never opened.**

## Method caveat

eprint **hard-429'd every PDF fetch (11/11 at 12s spacing) and returns the
refusal page under the requested filename** — those were deleted and the items
filed from mirror full text instead. **Anyone fetching from eprint must check
that what landed is a PDF.**
