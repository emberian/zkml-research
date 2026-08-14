# Spartan over what we hold — the piece-by-piece inventory, and the top of the stack as a Lean object

Date: 2026-08-14. Lane: **DESIGN + LEAN, Spartan**. Siblings: Ligerito, ring-switching.
Companion: `notes/binaryspartan-position.md` (same day) — read its **§0.5** before quoting anything
about the BinarySpartan paper. This note **does not depend on BinarySpartan existing**; it is about
Spartan, which is published (Setty, CRYPTO 2020) and whose structure is not in dispute.

Provenance legend: **[READ]** primary source at cited file/line · **[CLAIM]** asserted elsewhere,
not verified here · **[MEASURED]** I ran the command · **[BUILT]** I wrote it and `lake build` is
green.

**Substrate, said out loud (house law):** everything below is **Lean-authored**. The new artifact is
`/Users/ember/dev/minidregg/Assurance/SpartanR1CS.lean`. No Rust AIR is written, extended, or
implied. The Rust prover, where one exists, is bound by conformance vectors, never by a refinement
claim.

---

## 0. The headline — the suspicion was right, and sharper than briefed

The brief asked: *"which of Spartan's three pieces do we already have, and in what form?"*

**Answer: two of the three reductions are ours today; the third is a commitment-scheme obligation,
not a reduction.** Concretely:

| Spartan piece | verdict | where |
|---|---|---|
| **Zerocheck randomization** (`Q(τ) = Σ_x eq(τ,x)·F(x)`, sat ⟺ `Q(τ)=0` w.h.p.) | **HAVE, proved** | `Selvage/EqPolynomial.lean` `eqMle_fold` + `Selvage/MultilinearZeroTest.lean` `mle_zero_uniform_bound` |
| **Outer sumcheck** (degree-3, `eq(τ,x)·(Âz·B̂z − Ĉz)(x)`) | **HAVE the engine; the R1CS instance was missing and is now BUILT** | `Assurance/AirSumcheckCubic.lean` `cubic_sumcheck_soundness`; new: `spartan_outer_sound` |
| **Inner sumcheck** (degree-2, `Σ_y (r_A Ã + r_B B̃ + r_C C̃)(r_x,y)·z̃(y)`) | **HAVE the engine; the R1CS instance was missing and is now BUILT** | `Selvage/QuadraticSumcheck.lean` `quad_sumcheck_soundness` + `Selvage/ConstrainedCode.lean` `batch_survives_prob_le`; new: `spartan_inner_sound`, `spartan_inner_batch_sound` |
| **Witness PCS opening** (`z̃(r_y)`) | **claim object HAVE, protocol ABSENT** | `Selvage/MultilinearCommitment.lean` `MleEvalClaim` (+ binding); the opening reduction is the **Ligerito lane's** |
| **Sparse structure-matrix evaluation** (`Ã(r_x,r_y)` in sublinear V time) | **ABSENT** | no SPARK, no offline memory checking, no timestamp/multiset check anywhere |

⚑ **The reframing that matters.** "Spartan's inner sumcheck" is routinely described as the missing
hard part. It is not. The inner sumcheck is a degree-2 sumcheck on `Σ_y wt(y)·z̃(y)` — the exact
shape `QuadraticSumcheck.lean` was built for — and its three claims are literally three
`Selvage.LinearConstraint` values on the **witness word**, so the landed γ-batching lemma retires
them at `2/|F|` with nothing new proved. What is actually absent is **SPARK / offline memory
checking**: the machinery that lets the verifier learn `Ã(r_x,r_y)` without reading `A`. That is a
*commitment scheme for sparse multilinears*, not a sumcheck, and it is the single largest named
missing piece in a machine-checked Spartan.

⚑ **Correction to a sibling note.** `binaryspartan-position.md` §5 quotes
`AirSumcheckQuadratic.lean`'s docblock residual (ii) — *"the multilinear zero-test … not yet
vocabulary"* — as a live gap. **It is closed.** `Selvage/MultilinearZeroTest.lean` (276 lines, in
`Selvage.lean`, axiom-pinned, teeth for satisfiability/tightness/refutability) proves
`mle_zero_uniform_bound : f ≠ 0 → Pr_{z←F^m}[f̂(z)=0] ≤ m/|F|` and `eqMle_zero_test`. [READ, MEASURED]
The docblock it quotes is **stale relative to its own sibling file**. Spartan's zerocheck step is
therefore not an obligation — it is a citation.

---

## 1. Piece-by-piece inventory, at source

### 1.1 The protocol layer — degree-generic, field-generic, char-free [READ]

`Selvage/SumcheckReduction.lean:281` `AdaptiveAcceptsFalse`, and
`adaptive_sumcheck_soundness {v d : ℕ}` → `≤ v·d/|F|`. Binders throughout:
`variable {F : Type} [Field F] [Fintype F] [DecidableEq F]`. **No characteristic, no prime, no
smooth subgroup.** The degree parameter `d` is carried symbolically, so a new rung costs one
realizer and zero probability theory. `SumcheckAccepts` (`:145`) is
*(every round's boolean check) ∧ (terminal folded claim = honest truth chain at `v`)* — the terminal
check is a **comparison against the honest side's final value**, which is what makes the factored
terminal theorems below load-bearing rather than cosmetic.

### 1.2 Degree-2 rung — Spartan's inner shape. **HAVE.** [READ]

`Selvage/QuadraticSumcheck.lean` (247 lines). `prodDiff A B C x = Â(x)·B̂(x) − Ĉ(x)`;
`prodDiff_line` (the quadratic line restriction, from `mle_multilinear` + `ring`);
`quadRoundPoly` / `_eval` / `_degree`; `quadHonest` with all four honest-side hypotheses discharged;
`scChain_quadHonest_final : … = mle A r * mle B r - mle C r` — **the FACTORED terminal**; and
`quad_sumcheck_soundness ≤ m·2/|F|`.

This is the R1CS satisfaction shape as the brief said. But note *which* R1CS shape: it is the shape
of the **inner** sumcheck (`Σ_y wt(y)·z̃(y)`, factored terminal `wt̃(r)·z̃(r)`), and equally the shape
of a *dense* Hadamard check. It is **not** the outer sumcheck, which needs the `eq` head and
therefore degree 3.

### 1.3 Degree-3 rung — Spartan's outer shape, **built char-2-deliberately.** [READ]

`Assurance/AirSumcheckCubic.lean` (629 lines).
`cubicForm E A B C D x = Ê(x)·(Â(x)·B̂(x) + Ĉ(x)·D̂(x))`.

The char-2 claim in the brief checks out at source, and the reason is stated in the file:

> "The line restriction is COEFFICIENT-FORM, not interpolation-form: for multi-affine `f`,
> `f̂(x[i↦t]) = f₀ + t·Δf` … This form needs **no division and no characteristic hypothesis** — it
> works over any commutative ring, which matters because the char-2 (binary-tower) instantiation
> cannot use `{0,1,2,3}` interpolation nodes at all."

[READ, `AirSumcheckCubic.lean:43-47`.] Verified independently: the binders are `[Field F] [Fintype F]
[DecidableEq F]`, there is no `CharP` anywhere in the file, and the round polynomial is built by
`Polynomial.C _ * X^k` sums, never by Lagrange interpolation through nodes.

`scChain_cubicHonest_final` gives the terminal as `Ê(r)·(Â(r)·B̂(r) + Ĉ(r)·D̂(r))` — **five openings
the verifier combines itself**, which is exactly Spartan's outer terminal.
`cubicForm_fraction_layer` supplies the `eq` head via `eqMle_eq_mle`; `cubicForm_hadamard` supplies
`Ê·(Â·B̂ − Ĉ)`. **Composing those two IS Spartan's outer summand**, and that composition is what
`spartan_outer_sound` now performs.

### 1.4 The zerocheck bridge and its test. **HAVE, both halves.** [READ]

- `Selvage/EqPolynomial.lean:69` `eqMle_fold : Σ_b eq(z,b)·f(b) = mle f z` — the zerocheck→sumcheck
  bridge, an identity, no probability.
- `Selvage/MultilinearZeroTest.lean:127` `mle_zero_uniform_bound` — multilinear Schwartz–Zippel.
  Proof: induction peeling the LSB coordinate through `mle_lsb_recurrence`. Teeth pin the event
  **nonempty**, the bound **tight at m=1**, and the hypothesis **necessary** (so the floor is
  refutable, not a tautology).
- `:212` `eqMle_zero_test` composes them.

⚠ Both files' binders are `[Field F] [Fintype F]`, no characteristic. `MultilinearZeroTest` imports
`MultiplicativeMleTerminal`, which imports `Selvage.Proximity` — **but `mle_lsb_recurrence` takes no
`FoldingData` argument** (`variable {F : Type*} [Field F]`, [MEASURED]), so nothing on this line is
downstream of the `two_ne` trap. See §5.

### 1.5 The contraction face. **HAVE, and it is the inner sumcheck at ν = 0.** [READ]

`Assurance/ZkmlMatmulSumcheck.lean:163` `mle₂_contraction : Ĉ(x,y) = Σ_p Â(x,p)·B̂(p,y)` at **every**
`(x,y)`. Set `ν = 0` (the right factor is a column vector) and this is
`mle (Az) (x) = Σ_y Ã(x,y)·z̃(y)` — **Spartan's inner-sumcheck identity, already proved**, modulo the
trivial second index. The new file exhibits that specialization as a theorem
(`matVec_is_contraction_at_nu_zero`) rather than restating the identity, so there is one object and
not a twin.

`matmul_sumcheck_soundness` is also a template for the composition style I follow: *two different
events with two different causes, added, and the flattering half never quoted alone.*

### 1.6 The PCS claim seam. **Claim object HAVE; protocol is the sibling lane's.** [READ]

`Selvage/MultilinearCommitment.lean`: `MleEvalClaim (root, point, value)`, `MleEvalClaim.Holds`,
`basefoldWord_injective` (vector-root binding ⟹ multilinear-value binding, inside the degree
window), `value_unique`, and a refusal tooth. Its own docblock is explicit: *"This is not the opening
protocol. The remaining object is exactly the braided BaseFold `Reduction`/`RbrKnowledgeSoundness`
instance."* That remaining object is what the **Ligerito lane** is aimed at, and BinarySpartan swaps
BaseFold for Ligerito in exactly that slot.

### 1.7 The sparse structure-matrix commitment. **ABSENT.** [MEASURED]

Zero hits across `Selvage/`, `Assurance/`, `Theory/`, `Compiler/` for `SPARK`, `offline memory`,
`memory check`, `timestamp`, `multiset check`, `Lasso`, `Surge`, `Twist`, `Shout`. No sparse
multilinear representation of any kind. Confirms the sibling note's row, and this note sharpens
*why* it matters: it is the **only** piece of Spartan that is not a sumcheck or a PCS opening, and it
is the piece Irreducible's Binius64 blueprint §1.2 ("Why Not Binary Spartan?") argues is the
construction's weak point over binary fields.

---

*(§2 onward: the Lean object, the optimization classification, and the scope statement — below.)*

---

## 2. Spartan as a Lean object — `Assurance/SpartanR1CS.lean` [BUILT]

`/Users/ember/dev/minidregg/Assurance/SpartanR1CS.lean` — **883 lines, 56 declarations, 20 axiom
pins, no `sorry`**, registered in `Assurance.lean`. `lake build Assurance` builds the whole library
(8834 jobs) green with it in; `scripts/check-proof-hygiene.sh` PASS (472 tracked Lean files).
Commits `8fba211` · `b3fbde8` · `ef12ccf` · `323a7b3`.

⚠ Verification note: I built the working tree, not a detached clone. That is sound *here* because
`git status` over `Assurance/ Selvage/ Theory/ Compiler/` is **empty** — my entire dependency
closure is committed — and HEAD's copy of the new file is byte-identical to disk (md5 checked).
Concurrent lanes' uncommitted work is confined to `Compiler.lean` and `prover/`, neither in the
closure.

Binders throughout: `{F : Type} [Field F] [Fintype F] [DecidableEq F]`, `{s t : ℕ}` — `s` indexes
the constraint cube, `t` the variable cube. **No characteristic hypothesis anywhere.**

### 2.1 The statement of R1CS, and its reshaping

`matVec` (`(Az)(a) = Σ_y A a y · z y`) is **not defined here** — it is
`Assurance/ZkmlLowRankUpdate.lean`'s, imported. See §2.7; my first draft defined a second one and
the umbrella build caught it.

```lean
def R1CSSat  (A B C) (z) : Prop := ∀ a, matVec A z a * matVec B z a = matVec C z a
def r1csDefect (A B C) (z) : (Fin s → Bool) → F :=
  fun a => matVec A z a * matVec B z a - matVec C z a

theorem r1csSat_iff_defect_zero : R1CSSat A B C z ↔ r1csDefect A B C z = 0
```

and the identity that makes phase 2 exist at all:

```lean
theorem mle_matVec (A) (z) (x : Fin s → F) :
    mle (matVec A z) x = ∑ y, rowPartial A x y * z y
```

`mle_matVec` is **`mle₂_contraction` at `ν = 0`**, not a second reordering proof;
`matVec_is_contraction_at_nu_zero` exhibits the instance by `rfl`, so the contraction file and this
one denote one object. (Anti-twin discipline: a fresh 4-line reorder would have been easier and
would have been a twin.)

### 2.2 The outer reduction — proved

```lean
theorem spartan_outer_sound {A B C : R1CSMatrix F s t} {z : (Fin t → Bool) → F}
    (hunsat : ¬ R1CSSat A B C z)
    {prover : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < s →
      (prover χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb ((Fin s → F) × (Fin s → F)) (SpartanOuterAccepts A B C z prover)
      ≤ (s : ℝ) / Fintype.card F + (s : ℝ) * (3 / Fintype.card F)
```

Two events, two causes, added: the zerocheck point failed to separate (`s/|F|`, from
`mle_zero_uniform_bound`) or the degree-3 sumcheck was laundered (`s·3/|F|`, from
`cubic_sumcheck_soundness`). The honest side is **built**, not hypothesized. The prover's claimed
total is the literal constant `0` — that is the zerocheck's assertion — so the false-claim clause
`H ≠ S` reduces to `defect^(τ) ≠ 0`, which is exactly what Schwartz–Zippel bounds.

The outer summand is exhibited as the composition of the degree-3 rung's two named consumers:

```lean
theorem spartanOuterForm (A B C) (z) (τ) :
    cubicForm (eqHead τ) (matVec A z) (matVec B z) (fun a => -(matVec C z a)) (fun _ => 1)
      = fun x => eqMle τ x
          * (mle (matVec A z) x * mle (matVec B z) x - mle (matVec C z) x)
```

⚠ This theorem is **not consumed** by `spartan_outer_sound` — the soundness proof runs on the
engine's own syntactic shape. It is there because it is the claim a reader should distrust first
("is the thing you instantiated actually Spartan's summand?"), and it is cheaper to answer with a
theorem than with a paragraph.

### 2.3 The hand-off — the object the other two lanes can aim at

⚠ **First, the modelling honesty this turns on.** Selvage's `SumcheckAccepts` idealizes the
verifier's terminal oracle check as *"the prover's folded claim equals the HONEST side's final
value"*. A deployed Spartan verifier does not have the honest side; it computes
`eq(τ,r_x)·(v_A·v_B − v_C)` from three claimed openings. If that gap were left unstated, everything
above would be a theorem about an idealized verifier. It is not left unstated — it is discharged:

```lean
def spartanTerminal (τ rx : Fin s → F) (vA vB vC : F) : F := eqMle τ rx * (vA * vB - vC)

theorem spartanTerminal_eq_honest (A B C) (z) (τ rx) {vA vB vC}
    (hA : vA = mle (matVec A z) rx) (hB : vB = mle (matVec B z) rx)
    (hC : vC = mle (matVec C z) rx) :
    spartanTerminal τ rx vA vB vC
      = scChain (mle (r1csDefect A B C z) τ)
          (spartanOuterHonest A B C z τ (chalOf rx)) (chalOf rx) s
```

**This is the deliverable.** It says: the verifier's own expression coincides with the honest chain
exactly when the three supplied values are the three true row openings. So phase 2's obligation is
**exactly three values, no more and no fewer** — and, notably, the `eq(τ,r_x)` factor is *not* one
of them (the verifier computes it). `spartan_reduces_to_two_openings` is the same equation read in
the other direction.

### 2.4 The inner reduction — also proved, and cheaper than expected

```lean
def innerClaim (A : R1CSMatrix F s t) (rx : Fin s → F) (v : F) :
    LinearConstraint (Fin t → Bool) F := ⟨rowPartial A rx, v⟩

theorem innerClaim_satisfied_iff (A) (z) (rx) (v) :
    Satisfies z (innerClaim A rx v) ↔ v = mle (matVec A z) rx
```

⚑ Once a phase-2 claim is a `LinearConstraint` on the witness word, everything follows from landed
machinery:

```lean
theorem spartan_inner_batch_sound (…) (hbad : vA ≠ … ∨ vB ≠ … ∨ vC ≠ …) :
    uniformProb F (fun γ => Satisfies z (batchConstraint γ (innerBatch A B C rx vA vB vC)))
      ≤ (2 : ℝ) / Fintype.card F                                    -- batch_survives_prob_le

theorem spartan_inner_sound {cγ} {z} {prover} (hpm) (hdeg : degree < 2+1) :
    uniformProb (Fin t → F)
      (AdaptiveAcceptsFalse prover (spartanInnerHonest cγ z) cγ.target (dotWt cγ.wt z))
      ≤ (t : ℝ) * (2 / Fintype.card F)                              -- quad_sumcheck_soundness

theorem spartan_inner_terminal (cγ) (z) (ry) :
    scChain (dotWt cγ.wt z) (spartanInnerHonest cγ z (chalOf ry)) (chalOf ry) t
      = mle cγ.wt ry * mle z ry                                     -- FACTORED, two openings
```

with `mle_rowPartial_eq_mle₂ : mle (rowPartial A rx) ry = mle₂ A rx ry` identifying the first
factor as Spartan's `Ã(r_x,r_y)` rather than some other object.

The batched summand `wtγ(y)·z(y)` is a `prodDiff` with the third table identically zero, so the
**degree-2 engine with its factored terminal drives it unchanged** — the reason the inner rung is
degree 2 and not degree 1 is exactly that the terminal must split into two openings.

### 2.5 The two obligations, named and refutable

```lean
def SpartanOpeningProtocol {Root ι Op} (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (Accepts : MleEvalClaim Root F t → Prop) : Prop :=
  ∀ c, Accepts c → c.Holds S dom

def SpartanSparseEvalOracle (A : R1CSMatrix F s t)
    (Accepts : (Fin s → F) → (Fin t → F) → F → Prop) : Prop :=
  ∀ x y v, Accepts x y v → v = mle₂ A x y
```

`spartanOpeningsBound` proves the binding half of the first (it is `basefoldWord_injective`
consumed); the *protocol* half is the Ligerito/BaseFold lane's. `sparseEvalOracle_refutable`
proves the second is not free: the all-accepting oracle falsifies it. That check exists because a
`Prop` that quietly reads as `True` is the standard way an obligation stops being one.

⚑ **And `[SPARTAN-sparse]` is a COST obligation, not a soundness one.** Everything in the file is
sound against a *dense* commitment to `A, B, C` (`spartanOpeningsBound` closes that against
`flatten₂ A` and a binding root). What SPARK buys is that the verifier need not be linear in the
matrix. That is a real and large gap, but naming it as a soundness hole would be wrong, and getting
that classification right changes what the next lane builds.

### 2.6 Teeth

`ZMod 7`, `s = t = 1`, the **squaring gate `w·w = v`** — deliberately not a `C = 0` instance, which
the zero witness would satisfy for free and which would have made `spartan_outer_sound`'s
hypothesis describe an empty discrimination. `goodZ_sat` (`w,v = 3,2`; `3² = 2` in F₇) and
`badZ_unsat` (`3,1`) are two live witnesses on one instance. The bad defect word is `(1,0)`, whose
extension is `1 − τ`: `badZ_survives_at_one` exhibits the `s/|F|` event as **nonempty**, and
`badZ_caught_at_three` separates elsewhere, so the zerocheck is not a formality. The inner claim
predicate fires both ways (`innerClaim_fires` through the iff, `innerClaim_refuses` by
computation). `terminal_fires` computes the hand-off to `1·(4·4 − 6) = 3`, so
`spartanTerminal_eq_honest` is not an equation between two constants.

### 2.7 What I changed in existing files, and one thing I broke into

- `Assurance/ZkmlMatmulSumcheck.lean`: `uniformProb_fst_le` was `private`. Made public and cited,
  rather than re-proved beside it.
- `Assurance/AirSumcheckQuadratic.lean`: **docblock correction, no code.** Residual (ii) still read
  *"not yet vocabulary"* and was stale from the day `MultilinearZeroTest.lean` landed; residual (i)
  ("Spartan's second phase") now points at the R1CS instance of exactly that move, which is built.
  This is a *documented wound that had already healed* — the mirror image of the usual failure, and
  it cost a sibling lane a wrong citation on the same day.
- `Assurance.lean`'s import line for the new file was swept into a concurrent lane's commit
  `0dd9a48` before I could commit the file itself, so HEAD briefly imported a file that did not
  exist in it. Reported, not rewritten; fixed forward by `8fba211`.

⚑ **And one finding worth more than the fix.** My first draft defined `matVec` — and
`Assurance/ZkmlLowRankUpdate.lean` had defined the identical object, character for character, in
the same namespace, since the low-rank pass. `lake build Assurance.SpartanR1CS` was **green**: the
new file does not import `ZkmlLowRankUpdate`, so the two definitions never met. Only
`lake build Assurance` — the umbrella, which imports both — said *"environment already contains
`Minidregg.Assurance.matVec`"*. **A per-file green cannot see a twin, by construction**, because a
twin is precisely two definitions that never meet. Fixed in `b3fbde8` by deleting mine and
importing theirs; `Assurance` now builds whole (8834 jobs). This is the cheapest instance of the
repo's own twin-deletion law I have seen — the linker did the audit — and it only fired because I
built the umbrella rather than the file.


### 2.8 And then the composition — `spartan_sound` [BUILT, `ef12ccf`]

§2.3 said the hand-off is the deliverable. Having built it, the composition became cheap, so it is
built too, and it closes a modelling gap that would otherwise have made everything above weaker
than it reads.

⚠ **The gap.** `SumcheckAccepts` renders the terminal oracle check as *"the prover's folded claim
equals the HONEST side's final value"*. A deployed verifier has no honest side. Left unstated,
`spartan_outer_sound` would be a theorem about an idealized verifier — and *that is precisely the
shape of a vacuity that survives a green build and passes its axiom pins.*

```lean
def SpartanOuterRealAccepts (τ rx : Fin s → F) (outer : ℕ → Polynomial F) (vA vB vC : F) : Prop :=
  (∀ i, i < s → (outer i).eval 0 + (outer i).eval 1 = scChain (0 : F) outer (chalOf rx) i)
    ∧ scChain (0 : F) outer (chalOf rx) s = spartanTerminal τ rx vA vB vC
```

No honest side occurs in that predicate. `outerReal_iff_sumcheckAccepts` proves it coincides with
Selvage's idealized one exactly when the three claims are true, and then:

```lean
theorem spartan_sound {A B C} {z} (hunsat : ¬ R1CSSat A B C z)
    {vA vB vC : SpartanClaim F s}
    {outer : (Fin s → F) → (ℕ → F) → ℕ → Polynomial F}
    {inner : (Fin s → F) → (Fin s → F) → F → (ℕ → F) → ℕ → Polynomial F}
    (houterPm) (houterDeg) (hinnerPm) (hinnerDeg) :
    uniformProb (((Fin s → F) × (Fin s → F)) × (F × (Fin t → F)))
        (SpartanAccepts A B C z vA vB vC outer inner)
      ≤ ((s : ℝ) / |F| + (s : ℝ) * (3 / |F|)) + (2 : ℝ) / |F| + (t : ℝ) * (2 / |F|)
```

One joint draw `((τ, r_x), (γ, r_y))`; **both** phases must accept. The provers are adaptive —
`outer` sees `τ`, `inner` sees `(τ, r_x, γ)`, the claimed values are functions of `(τ, r_x)` — which
is what a real Spartan prover is, and required generalizing `spartan_outer_sound` to a τ-indexed
prover family.

**The case split is the whole content**: either the prover told the truth about the three row
openings, in which case phase 1 must carry the lie and cannot (`s/|F| + 3s/|F|`); or it lied, in
which case phase 2 must carry it and cannot (`2/|F|` for the batch, `t·2/|F|` for the sumcheck).

⚠ **And what this did NOT do, stated in the file next to the theorem rather than in a footnote: it
moved the idealization from phase 1 to phase 2.** The inner phase's two terminal openings are still
compared against an honest chain rather than against opened commitments. That is `[SPARTAN-pcs]`,
one level down, and it is the Ligerito / BaseFold lane's object.

**A tooth that is also the ring-switching argument.** `composed_bound_is_vacuous_at_f7` proves
`1 < 1/7 + 3/7 + 2/7 + 2/7 = 8/7`. At the toy parameters the composed bound is a *true statement
that constrains nothing*. Every term in the whole file is `k/|F|`: the proofs are
characteristic-free, the **usefulness is not**. A Spartan over a binary field must run its
sumchecks in a large extension — which is exactly what ring-switching buys, and why it is
load-bearing rather than an optimization. Stating that as a theorem rather than a caveat is the
difference between a scope note and a fact.

**Two elaboration findings, paid for in build failures.** (i) The two product splits the composition
needs must be done **once, at opaque types** — inlining them at the concrete event types is a `whnf`
**heartbeat timeout**, not a slowdown, because `spartanBatch` unfolds through `batchConstraint` into
three `rowPartial`s and thence into `mle`'s `Finset.sum`. `uniformProb_mid_le` / `uniformProb_last_le`
are those splits, following the recorded reasoning in `uniformProb_fst_le`'s own docstring.
(ii) Naming the events (`spartanBatchAt`, `SpartanInnerAccepts`, `SpartanInnerFalse`) rather than
inlining them is what made the proof elaborate at all.

---

## 3. The optimizations BinarySpartan names — soundness-relevant or prover-side?

**The criterion, stated before the answers,** because it is what makes the classification usable:
our formal layer proves things about **the statement the verifier checks** and **the relation being
proved**. So an optimization is *free to us* exactly when it emits the identical transcript against
the identical check. Three questions, not one: does the **verifier's check** change (different
messages, different degrees, different equation)? does the **relation** change? does the
**soundness bound** change?

⚑ **Correction to a sibling note.** `binaryspartan-position.md` §9 records *"Gruen / Dao–Thaler /
Bagad–Domb–Thaler sumcheck opts — ABSENT, correctly out of scope. All are prover-cost optimizations
that do not change the `v·d/|F|` soundness statement."* **Three of those are protocol changes with
new soundness arguments**, and one of them needs a *tower-basis* lemma. The line is not uniform and
must not be triaged as a block. Sources read below.

| optimization | verifier's check | relation | soundness bound | verdict for us |
|---|---|---|---|---|
| **Gruen §3** — factor `eq` out of the round message, drop `v(1)` | **CHANGED** | same | **CHANGED — improves**, `n(d+2)/\|G\| → n(d+1)/\|G\|` | protocol change, re-prove |
| **Gruen §4** — Gröbner decomposition `C = Σ x_i(x_i−1)Q_i` | same | same | same | **FREE** (paper says so) |
| **Gruen §5 / univariate skip** | **CHANGED** (higher-degree interpolation) | same | **CHANGED**, `(d(2^k−1) + (n−k)(d+1))/\|G\|` | protocol change, re-prove |
| **Phalanx SIMD R1CS** (eprint 2021/1263) | **CHANGED** | **CHANGED — a different NP language** | **CHANGED** (new Lemma 1) | **re-prove from the relation up** |
| **SuperSpartan `ñext`** (CCS §5.1) | **SAME in the IOP** | same | **same**, and it *removes* an assumption | ⚑ **the cheap one — see below** |
| CCS Remark 11 (periodic constraints) | **CHANGED** (+η elements) | same | same | small protocol change |
| **Speedup §3–§6** (delayed reduction, multiproduct, streaming, eq-decomposition) | same | same | same | **FREE** (paper says so) |
| Bagad–Domb–Thaler Alg. 4 (`2^i` rescale) | **CHANGED** (invertible rescale) | same | same | trivial re-prove |
| **Dao–Thaler constraint packing** (2024/1038) | **CHANGED** (7 coordinates derandomized; rounds removed) | same | **CHANGED**, `n/\|F\| → (n−7)/\|F\|` | **re-prove, and it needs tower bases** |
| **Binius64 byte lookup tables** (§4.3.3) | same | same | same | **FREE** |

### 3.1 The three that are genuinely free, and why that matters

**Gruen §4** and **Speedup §3–§6** say it in their own words. From Gruen §4: *"Note that these
improvements make no change to the protocol. It is simply a method which allows P to compute the
required information with less effort."* From Dao–DeStefano–Bagad–Domb–Thaler §1.1: *"This work
presents a variety of prover-side optimizations for sum-check that, except for one (univariate skip
(Section 7)), leave the protocol, verifier, and soundness unchanged."* [READ]

**Binius64's "byte lookup tables" is the one most likely to be mis-triaged, and the sibling note
already caught it: it is not a lookup argument at all.** The section is titled *"Prover Algorithm"*;
the soundness argument lives entirely in the preceding subsection and ends at `O(ℓ_and)/|K|` without
mentioning the tables; and `Extrap : F₂^64 → F_{2^8}^64` is a **deterministic `F₂`-linear map**,
tabulated as 8 chunks × 256 entries + 7 byte-wise XORs, 128 KiB. It is a memoized evaluation of a
public linear function — the same category as a multiplication table. `grep -ci logup` on the
Binius64 spec: **0**. All four `lookup` hits are "lookup *table*", none a lookup *argument*. [READ,
MEASURED]

**Consequence: three of the ten rows cost our formal layer nothing at all** — they belong in
`prover/src/`, bound by a conformance vector, never by a refinement claim.

### 3.2 ⚑ SuperSpartan's `ñext` is the cheap one, and for a structural reason

CCS §5.1 Theorem 2 gives `ñext = h + g` in closed form, evaluable in `O(log D)` after a ratio
recurrence and one batch inversion. `next(i,j) = 1` iff `to-int(j) = to-int(i) + 1` — *"adding 1 in
binary"* — which is exactly the shift an AIR transition relation needs.

**Who evaluates it: the VERIFIER**, on its own. And here is the structural point: CCS's IOP already
has the verifier *querying an oracle* for `M̃_i(r_x,r_y)` (Figure 2 step 4: *"check if ∀i,
`M̃_i(r_x,r_y) = v_i`, with one query to `M̃_i`"*). §5 changes only **how the verifier answers a
query it was already making**. Equation (15), both sum-checks, all degrees and all challenge
distributions are byte-identical. [READ]

So `ñext` is soundness-neutral in the IOP *and strictly weakens the trust model*: CCS footnote 10
says of the non-uniform (preprocessing) path that the structure commitments *"must be computed
honestly for the resulting pre-processing SNARK to be sound"*. The `ñext` route eliminates that
indexer-honesty assumption by deriving `M̃` from a closed form.

⚑ **For us that is the single most attractive row in the table, and it is attractive for a reason
that is not about `ñext` at all.** §1.7 named the sparse structure-matrix commitment as the largest
missing piece. `ñext` is the route that *does not need one*: for uniform / AIR-shaped constraint
systems the verifier evaluates `M̃` itself, so `[SPARTAN-sparse]` never arises. **The cheapest path
to a machine-checked succinct Spartan in this tree does not go through SPARK.**

⚠ Two honest caveats. `Compiler/Air.lean` has **no trace, no rows and no transition relation** — a
`Term (AirSig F Idx)` over one flat assignment — so "uniform constraint structure" does not exist as
a concept here yet; that is a real prerequisite, not a detail. And CCS §5.3's SIMD-CCS is a sketch:
it claims `O(log(βℓ))` IO-consistency work, *"an exponential improvement over Phalanx's cost"*, and
then closes with *"We leave a full description of these details to the near-term future work."*
Nothing there is provable as written.

### 3.3 Phalanx is the expensive one, and the paper is not the one anyone thinks

⚠ **Two corpus traps, both now resolved at source.** (i) The `Phalanx` PDF in `~/paperbin` is the
**wrong paper** — an FHE-friendly SNARK whose "SIMD" is BFV ciphertext-slot packing. (ii) eprint
**2021/1263** is the right one but is **not** titled *"Transparent Error Correcting…"*: it is
Tzialla–Kothapalli–Parno–Setty, **"Transparency Dictionaries with Succinct Proofs of Correct
Operation"**. The system is **Verdict**; *Phalanx is the SNARK inside it* (§IV). [READ]

SIMD R1CS there is one shared `A, B, C ∈ F^{m×m}` over `β` witness columns, plus IO consistency:

> "SIMD R1CS considers the same circuit (represented with matrices `A,B,C`) over `β` witness vectors
> `{w_1,…,w_β}` … we additionally require IO consistency, i.e., that the input of each data-parallel
> unit is the output of the previous unit."

with (Eq. 1) `x_i[ℓ/2:] = x_{i+1}[:ℓ/2]`, and the first/last halves tied to the public `x`.

**This is a different NP language**, with a new polynomial `F(k,i)` over `log β + log m` variables,
a new zero-polynomial, an extra challenge block `(τ_1,τ_2)`, a sub-protocol for IO consistency, and
a Nova-style folding scheme for the relaxed version. All three of our questions answer "changed".
⚠ And its folding soundness is stated **informally** — *"as with most batching techniques, soundness
holds due to the randomness of the linear combination"*, with no explicit bound. For a
machine-checked treatment that is not a citation, it is an open lemma.

**Verdict: Phalanx is the one row that requires re-proving from the relation up, and its own paper
leaves a hole where the bound should be.** Given §3.2, it is also the row most likely to be
obsoleted rather than ported.

### 3.4 Dao–Thaler constraint packing — the one the block-triage got wrong

The verifier **stops sampling** the first 7 coordinates and fixes them to specific tower elements:

> "This is exactly the standard 'zero-check PIOP' except that the first 7 entries of `(z_0,…,z_6,r)`
> are deterministically fixed to the special field elements `z_0,…,z_6`, rather than chosen at
> random from GF(2^128)."

Bound `n/|F| → (n−7)/|F|`, by a **new** argument resting on a property with no analogue in the
standard proof: that 128 specific products `(z_0−1)…(z_6−1), …, z_0z_1…z_6` are **linearly
independent over GF(2)**, which the note calls *"unique to tower field constructions"*. [READ]

For us: this is a protocol change **and** it needs Fan–Paar-style tower-basis facts in the soundness
proof, not merely in the field implementation. We hold `Theory/BinaryTowerFanPaar.lean` and
`Theory/BinaryTowerTrace.lean`, so the ingredients exist — but it is not a port of our sumcheck, it
is a different theorem about it.


---

## 4. The honest scope — what a machine-checked Spartan-over-binary still needs

Given what the three lanes together produced today. Ordered by size, largest first.

### M1 · `[SPARTAN-pcs]` — the multilinear opening protocol. **The largest piece.**

`spartan_sound` terminates in two claimed openings, `wt̃γ(r_y)` and `z̃(r_y)`, compared against an
honest chain. Turning that into a real object needs a `Reduction` / `RbrKnowledgeSoundness` instance
discharging `SpartanOpeningProtocol`. Two candidate routes, both live in siblings today:

- **Ligerito** — `Selvage/LigeritoInterleaved.lean` (567 lines, landed today) puts the interleaved
  code in the tree and, per its own docblock, *refutes constructively* the prior claim that our
  `relDist` cannot express interleaved distance (`relDistV_eq_relDist`, by `rfl`). Still needed:
  **Diamond–Gruen 2024/1351 Thm 3.1** (proximity gaps lift from `C` to `Cᵐ`) and **AER Thm 3.6**
  (affine-line ⟹ tensor-style). The sibling note's §4 measured these as *genuinely new mathematics*
  — DG's argument is rank/row-space, ours is root-counting — so they must not be priced as a port.
- **BaseFold in characteristic two** — `Selvage/AdditiveBaseFold.lean` (838 lines, landed today),
  which ports the descent to the LCH additive split and, crucially, takes **no `FoldingData`**.

### M2 · The structure-matrix evaluation — and there are two routes, one of which is much cheaper

`Ã(r_x,r_y)` must reach the verifier. Either:

- **SPARK / offline memory checking.** ABSENT entirely: no timestamp vectors, no multiset or
  permutation check, no computation commitment. `Selvage/BinaryLookup.lean` (165 lines) is a real
  but small down-payment — it pins the one-hot/χ-vector fact and, notably, proves the char-2 hazard
  `boolean_sum_one_not_oneHot_charTwo`. This is the route Irreducible's Binius64 blueprint §1.2
  argues *against* for binary fields ("the large field infects what ought to be a bit-level
  computation").
- ⚑ **or SuperSpartan's `ñext`** — §3.2. Soundness-neutral in the IOP, and it makes M2 **not
  arise**: the verifier evaluates `M̃` from a closed form in `O(log D)`. Its prerequisite is a
  *uniform / AIR-shaped* constraint system, and `Compiler/Air.lean` has **no trace, no rows and no
  transition relation** — that notion has to be built. **But building a row/transition notion is
  ordinary work, and building a verified sparse-polynomial commitment is not.**

**This is the sharpest planning consequence in the note: the cheapest path to a machine-checked
succinct Spartan in this tree does not go through SPARK.**

### M3 · `[SPARTAN-fs]` — one transcript, and round-by-round soundness of the composed protocol

`spartan_sound` is over four independent uniform draws. The deployed object is one Fiat–Shamir
transcript. Selvage's cone (`Rbr.lean`, `SumcheckRbr.lean`, `FiatShamir.lean`, `AccRbrBcs*.lean`)
is exactly the compiler for this, but Spartan's specific two-phase round structure has to be given
a round-by-round soundness instance and then pushed through FS over an inhabited oracle and BCS at
the deployed alphabet. Not attempted; not hidden.

### M4 · Ring-switching's two preservation theorems

Diamond–Posen Thm 3.2 (completeness preserved) and Thm 3.5 (security preserved, by constructing an
emulator from the large-field one). `Selvage/RingSwitching.lean` (568 lines, landed today) carries
the interface and states explicitly that it touches no `FoldingData`. Needed because of §4.6 below.

### M5 · ⚑ Knowledge soundness — the piece easiest to miss, so name it

**Every theorem in `SpartanR1CS.lean` quantifies over a GIVEN witness `z` and bounds the probability
that an *unsatisfying* one is accepted.** That is soundness. Real Spartan is an **argument of
knowledge**: the claim is *"the verifier accepts ⟹ an extractor recovers a satisfying `z`"*, and
that requires an extractor from the witness commitment. Nothing in my file says anything about
extraction, and the composition does not sneak it in. Selvage has the vocabulary
(`Selvage/ZkExtraction.lean`, `AccExtract.lean`, `RbrKnowledgeSoundness`), so this is a wiring task
rather than new mathematics — but it is a *named* task and it is downstream of M1, since the
extractor is the PCS's.

### M6 · The field-size parameter, which is now computable rather than hand-waved

`composed_bound_is_vacuous_at_f7` makes the point sharply: at `s = t = 1` over F₇ the composed bound
is `8/7 > 1`. The bound is `(4s + 2t + 2)/|F|` in the leading term. At `s, t ≈ 25` (a ~33M-constraint
R1CS) that is `≈ 152/|F|`, so GF(2^128) gives `≈ 2^-121` and **GF(2^32) gives `≈ 2^-25`** — Ligerito's
own benchmark field is nowhere near enough for the sumchecks. This is the concrete reason
ring-switching (M4) is load-bearing: commit over the ground field, run the IOP over a large
extension.

### M7 · Padding

Hypercube padding for non-dyadic constraint/variable counts is per-deployment bookkeeping, handled
as hypotheses here exactly as `AirSumcheckQuadratic`'s `hyperIdx` precedent does. Small.

### What is NOT on this list, and deliberately

Spartan's **two sumcheck reductions**, its **zerocheck**, its **batching**, and the **hand-off
between phases** — all built, all `no sorry`, all axiom-pinned, all characteristic-free. Before
today the honest answer to "how much of Spartan do we have" would have been "the engines"; it is
now "the protocol, minus its commitment scheme and its Fiat–Shamir compilation."

---

## 5. What I built over — the vacuity trap, stated

The brief warned that `Selvage/Proximity.lean:190`'s `FoldingData` carries `two_ne : (2 : F) ≠ 0` as
a **structure field**, making the type uninhabitable in characteristic two, so everything quantified
over it is vacuously true there on a green build.

**What I built over: none of it.** Machine-checked, not asserted — I printed the full types of the
five keystones this file consumes (`mle_zero_uniform_bound`, `cubic_sumcheck_soundness`,
`quad_sumcheck_soundness`, `batch_survives_prob_le`, and my own `spartan_outer_sound` /
`spartan_inner_sound` / `spartan_sound`) and grepped them:

```
=== "Folding" mentions in the keystone types === 0
=== "CharP"   mentions in the keystone types === 0
```

[MEASURED, `lake env lean` over `#check @…`.] Binders are `[Field F] [Fintype F] [DecidableEq F]`
throughout. `Selvage.mle_lsb_recurrence` — the one step that reaches into a file which *imports*
`Proximity` — takes no `FoldingData` argument (`variable {F : Type*} [Field F]`).

The sibling lane closed the trap while I worked: `Selvage/CharTwoWall.lean` (commit `0dd9a48`) now
proves the emptiness (`foldingData_charTwo_False`), the consequence
(`foldingData_vacuous_of_charTwo`: at char 2 every predicate holds of every `FoldingData`, including
`False`), locates the wall at `0 < m`, and carries a negative control — `FoldingDataStripped`,
the same structure minus `two_ne`, **inhabited over ZMod 2** — so deleting the field cannot be
papered over. That is the right shape: the hypothesis is real (the multiplicative fold divides by
two and by `2x`), so it stays; what was fixed is the **silence**.

⚠ **And the counterpoint I have to state, because being characteristic-free is not the same as being
useful in characteristic two.** Every bound in my file is `k/|F|`. Over GF(2) or GF(2^8) they say
nothing, and `composed_bound_is_vacuous_at_f7` proves an instance of exactly that. **A
characteristic-free proof over a small field is a different flavour of vacuity from an
uninhabitable hypothesis, and it is the flavour that will not be caught by a type-emptiness
theorem.** The answer is ring-switching (M4), not a bigger claim.

---

## 6. Summary — five sentences

1. **Two of Spartan's three pieces were already ours as engines**, and the R1CS instances of both
   are now built, composed, and `no sorry`: `spartan_sound` bounds acceptance of an unsatisfying
   witness by `s/|F| + s·3/|F| + 2/|F| + t·2/|F|` against a **deployed** verifier, not an idealized
   one.
2. **The inner sumcheck is not the hard part** — its three claims are linear constraints on the
   witness word, so the landed γ-batching lemma retires them at `2/|F|` with nothing new proved.
3. **What is genuinely missing is a commitment scheme, not a reduction**: `[SPARTAN-pcs]` (the
   opening protocol, M1) and either SPARK or uniformity (M2) — plus Fiat–Shamir (M3) and knowledge
   soundness (M5), both named.
4. **Three of the ten named optimizations are free to us and one is expensive**; the sharpest
   finding is that **SuperSpartan's `ñext` is soundness-neutral and would make the sparse-commitment
   gap not arise at all**, so the cheapest path to a succinct machine-checked Spartan does not go
   through SPARK.
5. **Nothing here is downstream of the `two_ne` trap** (measured), but characteristic-freedom buys
   the *proofs* and not the *parameters* — which is the concrete, non-rhetorical reason
   ring-switching is load-bearing.
