/-
# Selvage.OutOfDomain — out-of-domain sampling (WHIR eprint 2024/1586 Lemma 4.25 /
Arc Lemma 3.4): the uniqueness pin that upgrades "δ-close to SOME codeword in a
list" to "δ-close to THE codeword with this OOD value".

An out-of-domain (OOD) point is a `z ∈ F ∖ L` — outside the image of the
evaluation domain `dom : ι ↪ F`. A codeword of `RS[F, dom, d]` is the domain
evaluation of a degree-`< d` polynomial; its OOD evaluation at `z` is that
polynomial's value at `z` (`oodEval`, via the noncomputable membership witness
`codewordPoly`; CHOICE-FREE once `d ≤ |ι|`, since the witness is then unique —
`codewordPoly_eq_of_witness`). Two DISTINCT codewords agree at fewer than `d`
points of ALL of `F` (root counting on the difference — the SAME
`card_agreeSet_lt_of_ne` that gave `Selvage/ReedSolomon.lean` its minimum distance,
here instantiated at the identity embedding `ι := F`), hence at `≤ d − 1` points
of `F ∖ L`: sampling one uniform OOD point separates any fixed distinct pair
except with probability `(d−1)/(|F|−|L|)`. Union-bounding over the
`(ℓ choose 2)` pairs of an `ℓ`-list separates the WHOLE list except with
probability `(ℓ choose 2)·(d−1)/(|F|−|L|)` — and at any separating `z`, an OOD
value `σ` determines AT MOST ONE codeword of the list (`existsUnique_of_good`):
the accumulator's claim quantifies over ONE codeword, not a list.

**What is proved here (no sorry, no axioms beyond the classical trio):**

* `exists_ood_iff` — OOD points exist iff the domain is proper
  (`|ι| < |F|`): premise inhabitation for every `z ∉ Set.range dom` below.
* `codewordPoly`/`oodEval` + spec — the witness polynomial has degree `< d`
  (unconditionally) and reproduces the word on the domain; for `d ≤ |ι|` it is
  the UNIQUE such polynomial (`codewordPoly_eq_of_witness`), so `oodEval` is
  independent of the membership witness and computable through any explicit
  witness (`oodEval_eq_of_witness`).
* **The pairwise pin** — `card_oodAgree_codeword_lt`: distinct codewords `u ≠ v`
  agree at FEWER than `d` out-of-domain points (`≤ d − 1`:
  `card_oodAgree_codeword_le`); uniform-`z` reading
  `uniformProb_oodAgree_le`: collision probability
  `≤ (d−1)/(|F|−|ι|)`. No `d ≤ |ι|` needed: distinct words force distinct
  witness polynomials outright (`codewordPoly_ne`).
* **List separation (union bound over `(ℓ choose 2)` pairs)** —
  `card_oodListBad_le`: the `z` at which SOME distinct pair of an `ℓ`-list
  collides number `≤ (ℓ choose 2)·(d−1)`; probability form
  `uniformProb_oodListBad_le`, and the headline
  `uniformProb_ood_pin_fails_le`: except with probability
  `≤ (ℓ choose 2)·(d−1)/(|F|−|ι|)`, the sampled OOD point makes
  `oodEval · z` INJECTIVE on the list. (The list bound is stated with the
  ℕ-truncated `d − 1`, equal to the paper's `d − 1` whenever `d ≥ 1`; the
  pairwise probability bound is stated in the paper-verbatim real form.)
* **The pin itself** — `oodEval_injective_of_good` / `existsUnique_of_good`: at
  a separating `z`, a claimed OOD value `σ` is realized by AT MOST ONE codeword
  of the list (`∃!`). This is the statement the accumulator consumes.
* **The constraint-channel bridge** — `oodConstraint`: the OOD evaluation claim
  `oodEval f z = σ` IS a `LinearConstraint` of `Selvage/ConstrainedCode.lean`
  (weight = Lagrange basis sampled at `z`), with
  `satisfies_oodConstraint_iff` proving the two readings agree on the code
  (for `d ≤ |ι|`), and `mem_constrainedRS_ood_iff`: the constrained code cut by
  an OOD constraint is EXACTLY "codeword + pinned OOD value". This discharges
  concretely what ConstrainedCode's docstring promised only via
  `exists_dotWt_eq`.

**What stays prose-residual — `[OOD-pin-proximity]`:** the proximity lift. WHIR
Lemma 4.25 speaks about a word `w` that is δ-CLOSE to the code: the list is the
δ-list-decoding list of `w`, and the conclusion is "δ-close to THE codeword
with the sampled OOD value". Everything list-shaped is proved here for an
ARBITRARY finite family `ws : Fin ℓ → ι → F` of codewords — which covers the
decoding list once list-decoding enumeration is wired in from the
mutual-correlated-agreement machinery of `Selvage/CorrelatedAgreement.lean` (the
same seam as `[CRS-batch-sound]` in ConstrainedCode). That wiring is future
work, carried as prose per the ReedSolomon.lean Thm 4.8 precedent: no axiom, no
placeholder `Prop`. The machine-checked kernel of the lift — the counting, the
union bound, and the at-most-one conclusion — is fully proved above.

**Keystone hygiene (ATLAS: satisfiable + teeth, BUILT, over `F₅` on
`RSExample`'s 4-point domain, `d = 2`):** `z = 4` is THE out-of-domain point
(`OODExample.four_ood`, decided; `exists_ood_iff` fires since `4 < 5`).
SATISFIABLE — `pin_separates`: the distinct codewords `xWord` (poly `X`) and
`0` take DIFFERENT OOD values `4 ≠ 0` at `z = 4`: the pin genuinely separates,
and `pin_pins_unique` runs the `∃!` end-to-end (value `4` pins exactly `xWord`
in the list `[xWord, 0]`). TEETH — the adversarial pair `xWord` vs `qWord`
(poly `2X+1`) agrees EXACTLY at `z = 4` (`4 = 2·4+1` in `F₅`):
`card_oodAgree_xWord_qWord` computes the OOD-agreement count `= 1 = d − 1`, the
general bound fires on it and is ATTAINED, not slack — and honestly quantified,
`pin_fail_prob_one`: at these toy parameters the collision probability is `1`
(`(d−1)/(|F|−|L|) = 1/1`) — a 1-point OOD space buys nothing, exactly as the
bound says (quote the pessimistic number). The good pair's collision count is
`0` (`card_oodAgree_xWord_zero`): both poles are exhibited.
-/
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Selvage.ConstrainedCode
import Selvage.Rbr

namespace Minidregg.Selvage

open Polynomial

/-! ## Out-of-domain points

An OOD point is any `z ∉ Set.range dom`; theorems below carry that hypothesis
raw. Existence is exactly properness of the domain. -/

section OodPoints

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq ι] [Field F] in
/-- Out-of-domain points exist exactly when the evaluation domain is a PROPER
subset of the field: `|ι| < |F|`. Premise inhabitation for every
`z ∉ Set.range dom` hypothesis in this file. -/
theorem exists_ood_iff [Fintype F] (dom : ι ↪ F) :
    (∃ z : F, z ∉ Set.range dom) ↔ Fintype.card ι < Fintype.card F := by
  constructor
  · rintro ⟨z, hz⟩
    have hzim : z ∉ Finset.univ.image dom := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact fun ⟨i, hi⟩ => hz ⟨i, hi⟩
    calc Fintype.card ι = (Finset.univ.image dom).card := by
          rw [Finset.card_image_of_injective _ dom.injective, Finset.card_univ]
      _ < Finset.univ.card :=
          Finset.card_lt_card ((Finset.ssubset_iff_of_subset
            (Finset.subset_univ _)).mpr ⟨z, Finset.mem_univ z, hzim⟩)
      _ = Fintype.card F := Finset.card_univ
  · intro hlt
    have hcard : (Finset.univ.image dom).card < (Finset.univ : Finset F).card := by
      rw [Finset.card_image_of_injective _ dom.injective, Finset.card_univ,
        Finset.card_univ]
      exact hlt
    obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨z, fun hmem => hz ?_⟩
    obtain ⟨i, hi⟩ := hmem
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

end OodPoints

/-! ## The witness polynomial and the OOD evaluation of a codeword

A codeword is the domain evaluation of SOME degree-`< d` polynomial
(`mem_reedSolomonCode_iff`); `codewordPoly` selects one (junk `0` off the
code), `oodEval` evaluates it. For `d ≤ |ι|` the selection is unique, so
`oodEval` is witness-independent (`oodEval_eq_of_witness`). -/

section OodEval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

open Classical in
/-- The witness polynomial of a codeword: SOME degree-`< d` polynomial whose
domain evaluations give the word (junk value `0` for non-codewords — Mathlib's
division-by-zero convention; every theorem about it carries the membership or
witness hypothesis that makes it meaningful). -/
noncomputable def codewordPoly (dom : ι ↪ F) (d : ℕ) (f : ι → F) : Polynomial F :=
  if hf : f ∈ reedSolomonCode dom d then (mem_reedSolomonCode_iff.mp hf).choose else 0

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The witness polynomial is in the degree window — unconditionally (the junk
branch is the zero polynomial, degree `⊥`). -/
theorem codewordPoly_degree_lt (dom : ι ↪ F) (d : ℕ) (f : ι → F) :
    (codewordPoly dom d f).degree < (d : WithBot ℕ) := by
  unfold codewordPoly
  split
  · exact (mem_reedSolomonCode_iff.mp ‹_›).choose_spec.1
  · simp only [degree_zero]
    exact WithBot.bot_lt_coe _

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- On the code, the witness polynomial reproduces the word at every domain
point. -/
theorem codewordPoly_eval (dom : ι ↪ F) (d : ℕ) {f : ι → F}
    (hf : f ∈ reedSolomonCode dom d) (i : ι) :
    f i = (codewordPoly dom d f).eval (dom i) := by
  unfold codewordPoly
  rw [dif_pos hf]
  exact (mem_reedSolomonCode_iff.mp hf).choose_spec.2 i

omit [DecidableEq ι] in
/-- **Uniqueness of degree-`< d` interpolants on a `≥ d`-point domain**: two
polynomials in the window agreeing on ALL domain points are equal — the
agreement set is the whole domain, and `card_agreeSet_lt_of_ne` (reused from
`Selvage/ReedSolomon.lean`, root counting) caps agreement of a DISTINCT pair
strictly below `d ≤ |ι|`. -/
theorem eq_of_degreeLT_of_agree (dom : ι ↪ F) {d : ℕ} (hd : d ≤ Fintype.card ι)
    {p q : Polynomial F} (hp : p.degree < (d : WithBot ℕ))
    (hq : q.degree < (d : WithBot ℕ))
    (h : ∀ i, p.eval (dom i) = q.eval (dom i)) : p = q := by
  by_contra hne
  have hlt := card_agreeSet_lt_of_ne dom hp hq hne
  rw [Finset.filter_true_of_mem fun i _ => h i, Finset.card_univ] at hlt
  omega

omit [DecidableEq ι] in
/-- For `d ≤ |ι|` the witness polynomial is THE polynomial: any explicit witness
pair (degree window + domain agreement) identifies it. `oodEval` is therefore
independent of the choice made in `codewordPoly`. -/
theorem codewordPoly_eq_of_witness (dom : ι ↪ F) {d : ℕ}
    (hd : d ≤ Fintype.card ι) {f : ι → F} {p : Polynomial F}
    (hp : p.degree < (d : WithBot ℕ)) (hfp : ∀ i, f i = p.eval (dom i)) :
    codewordPoly dom d f = p := by
  have hf : f ∈ reedSolomonCode dom d := mem_reedSolomonCode_iff.mpr ⟨p, hp, hfp⟩
  exact eq_of_degreeLT_of_agree dom hd (codewordPoly_degree_lt dom d f) hp
    fun i => by rw [← codewordPoly_eval dom d hf i, hfp i]

/-- **The out-of-domain evaluation** of a codeword: its witness polynomial's
value at `z`. Meaningful at `z ∉ Set.range dom` for `f` in the code (junk `0`
witness off it); choice-free once `d ≤ |ι|`. -/
noncomputable def oodEval (dom : ι ↪ F) (d : ℕ) (f : ι → F) (z : F) : F :=
  (codewordPoly dom d f).eval z

omit [DecidableEq ι] in
/-- Compute `oodEval` through any explicit witness polynomial (`d ≤ |ι|`). -/
theorem oodEval_eq_of_witness (dom : ι ↪ F) {d : ℕ} (hd : d ≤ Fintype.card ι)
    {f : ι → F} {p : Polynomial F} (hp : p.degree < (d : WithBot ℕ))
    (hfp : ∀ i, f i = p.eval (dom i)) (z : F) :
    oodEval dom d f z = p.eval z := by
  unfold oodEval
  rw [codewordPoly_eq_of_witness dom hd hp hfp]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Sanity: at an IN-domain point, `oodEval` recovers the word itself. -/
theorem oodEval_dom (dom : ι ↪ F) {d : ℕ} {f : ι → F}
    (hf : f ∈ reedSolomonCode dom d) (i : ι) :
    oodEval dom d f (dom i) = f i :=
  (codewordPoly_eval dom d hf i).symm

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Distinct codewords have distinct witness polynomials — equal witnesses would
reproduce equal words. (No `d ≤ |ι|` needed.) -/
theorem codewordPoly_ne (dom : ι ↪ F) (d : ℕ) {u v : ι → F}
    (hu : u ∈ reedSolomonCode dom d) (hv : v ∈ reedSolomonCode dom d)
    (hne : u ≠ v) : codewordPoly dom d u ≠ codewordPoly dom d v := by
  intro h
  refine hne (funext fun i => ?_)
  rw [codewordPoly_eval dom d hu i, codewordPoly_eval dom d hv i, h]

end OodEval

/-! ## The pairwise pin: distinct codewords collide at `≤ d − 1` OOD points

Root counting over ALL of `F` — `card_agreeSet_lt_of_ne` instantiated at the
identity embedding `ι := F` — then restricted to `F ∖ L`. -/

section PairwisePin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- Distinct degree-`< d` polynomials agree at fewer than `d` points of the
WHOLE field: `Selvage/ReedSolomon.lean`'s agreement-count theorem at the identity
embedding. -/
theorem card_agree_lt {d : ℕ} {p q : Polynomial F}
    (hp : p.degree < (d : WithBot ℕ)) (hq : q.degree < (d : WithBot ℕ))
    (hne : p ≠ q) :
    (Finset.univ.filter fun z : F => p.eval z = q.eval z).card < d := by
  simpa using card_agreeSet_lt_of_ne (Function.Embedding.refl F) hp hq hne

omit [DecidableEq ι] in
/-- Restricting the agreement set to out-of-domain points only shrinks it:
distinct degree-`< d` polynomials collide at fewer than `d` OOD points. -/
theorem card_oodAgree_lt (dom : ι ↪ F) {d : ℕ} {p q : Polynomial F}
    (hp : p.degree < (d : WithBot ℕ)) (hq : q.degree < (d : WithBot ℕ))
    (hne : p ≠ q) :
    (Finset.univ.filter fun z : F =>
        z ∉ Set.range dom ∧ p.eval z = q.eval z).card < d := by
  refine lt_of_le_of_lt (Finset.card_le_card fun z hz => ?_) (card_agree_lt hp hq hne)
  rw [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hz.2.2⟩

omit [DecidableEq ι] in
/-- **THE PAIRWISE PIN (count form)**: distinct codewords of `RS[F, dom, d]`
take equal OOD values at FEWER than `d` out-of-domain points. This is the fresh
constraint an OOD sample buys: agreement on `L` is already spent on `u = v`,
so `z ∉ L` probes genuinely new ground. -/
theorem card_oodAgree_codeword_lt (dom : ι ↪ F) {d : ℕ} {u v : ι → F}
    (hu : u ∈ reedSolomonCode dom d) (hv : v ∈ reedSolomonCode dom d)
    (hne : u ≠ v) :
    (Finset.univ.filter fun z : F =>
        z ∉ Set.range dom ∧ oodEval dom d u z = oodEval dom d v z).card < d :=
  card_oodAgree_lt dom (codewordPoly_degree_lt dom d u)
    (codewordPoly_degree_lt dom d v) (codewordPoly_ne dom d hu hv hne)

omit [DecidableEq ι] in
/-- The pin in the paper's `≤ d − 1` form. -/
theorem card_oodAgree_codeword_le (dom : ι ↪ F) {d : ℕ} {u v : ι → F}
    (hu : u ∈ reedSolomonCode dom d) (hv : v ∈ reedSolomonCode dom d)
    (hne : u ≠ v) :
    (Finset.univ.filter fun z : F =>
        z ∉ Set.range dom ∧ oodEval dom d u z = oodEval dom d v z).card ≤ d - 1 := by
  have h := card_oodAgree_codeword_lt dom hu hv hne
  omega

end PairwisePin

/-! ## List separation: the union bound over `(ℓ choose 2)` pairs -/

section ListSeparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- The strictly-increasing pairs of `Fin ℓ × Fin ℓ` number `ℓ choose 2` —
half the off-diagonal, by the swap bijection. -/
theorem card_filter_lt_pairs (ℓ : ℕ) :
    (Finset.univ.filter fun p : Fin ℓ × Fin ℓ => p.1 < p.2).card = ℓ.choose 2 := by
  have hswap : (Finset.univ.filter fun p : Fin ℓ × Fin ℓ => p.1 < p.2).card
      = (Finset.univ.filter fun p : Fin ℓ × Fin ℓ => p.2 < p.1).card :=
    Finset.card_equiv (Equiv.prodComm _ _) (by simp)
  have hdisj : Disjoint (Finset.univ.filter fun p : Fin ℓ × Fin ℓ => p.1 < p.2)
      (Finset.univ.filter fun p : Fin ℓ × Fin ℓ => p.2 < p.1) :=
    Finset.disjoint_filter.mpr fun p _ h1 h2 => absurd h2 (asymm h1)
  have hunion : (Finset.univ.filter fun p : Fin ℓ × Fin ℓ => p.1 < p.2)
      ∪ (Finset.univ.filter fun p : Fin ℓ × Fin ℓ => p.2 < p.1)
      = Finset.univ.offDiag := by
    rw [← Finset.filter_or]
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
    exact lt_or_lt_iff_ne
  have hcards := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hcards
  have hmul : ℓ * (ℓ - 1) = ℓ * ℓ - ℓ := by
    cases ℓ with
    | zero => simp
    | succ n => simp [Nat.mul_succ, Nat.succ_mul]
  rw [Nat.choose_two_right, hmul]
  set m := ℓ * ℓ with hm
  omega

omit [DecidableEq ι] in
/-- **List separation, count form (union bound)**: given an `ℓ`-list of
codewords, the OOD points at which SOME distinct pair collides number at most
`(ℓ choose 2)·(d − 1)` — one pairwise pin per unordered pair. (`d − 1` is
ℕ-truncated: for `d = 0` no distinct codeword pair exists and both sides
vanish; for `d ≥ 1` this is the paper's number verbatim.) -/
theorem card_oodListBad_le (dom : ι ↪ F) {d ℓ : ℕ} {ws : Fin ℓ → ι → F}
    (hws : ∀ i, ws i ∈ reedSolomonCode dom d) :
    (Finset.univ.filter fun z : F => z ∉ Set.range dom ∧
        ∃ i j : Fin ℓ, i < j ∧ ws i ≠ ws j ∧
          oodEval dom d (ws i) z = oodEval dom d (ws j) z).card
      ≤ ℓ.choose 2 * (d - 1) := by
  set pairs := Finset.univ.filter (fun p : Fin ℓ × Fin ℓ => p.1 < p.2) with hpairs
  have hsub : (Finset.univ.filter fun z : F => z ∉ Set.range dom ∧
      ∃ i j : Fin ℓ, i < j ∧ ws i ≠ ws j ∧
        oodEval dom d (ws i) z = oodEval dom d (ws j) z)
      ⊆ pairs.biUnion fun p => Finset.univ.filter fun z : F =>
          z ∉ Set.range dom ∧ ws p.1 ≠ ws p.2 ∧
            oodEval dom d (ws p.1) z = oodEval dom d (ws p.2) z := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hood, i, j, hij, hne, heq⟩ := hz
    exact Finset.mem_biUnion.mpr ⟨(i, j),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hood, hne, heq⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  have hpair : ∀ p ∈ pairs,
      (Finset.univ.filter fun z : F => z ∉ Set.range dom ∧ ws p.1 ≠ ws p.2 ∧
        oodEval dom d (ws p.1) z = oodEval dom d (ws p.2) z).card ≤ d - 1 := by
    intro p _
    by_cases hww : ws p.1 = ws p.2
    · rw [Finset.filter_false_of_mem fun z _ => by simp [hww]]
      simp
    · have hle : (Finset.univ.filter fun z : F => z ∉ Set.range dom ∧
          ws p.1 ≠ ws p.2 ∧ oodEval dom d (ws p.1) z = oodEval dom d (ws p.2) z)
          ⊆ Finset.univ.filter fun z : F => z ∉ Set.range dom ∧
            oodEval dom d (ws p.1) z = oodEval dom d (ws p.2) z := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, hz.2.1, hz.2.2.2⟩
      exact le_trans (Finset.card_le_card hle)
        (card_oodAgree_codeword_le dom (hws p.1) (hws p.2) hww)
  calc ∑ p ∈ pairs, (Finset.univ.filter fun z : F =>
        z ∉ Set.range dom ∧ ws p.1 ≠ ws p.2 ∧
          oodEval dom d (ws p.1) z = oodEval dom d (ws p.2) z).card
      ≤ pairs.card • (d - 1) := Finset.sum_le_card_nsmul _ _ _ hpair
    _ = ℓ.choose 2 * (d - 1) := by
        rw [smul_eq_mul, hpairs, card_filter_lt_pairs]

end ListSeparation

/-! ## The pin: at a separating OOD point, the value determines the codeword

Pure logic over the bad-event complement — no counting, no field structure
beyond what `oodEval` already used. -/

section Pin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq ι] in
/-- At a `z` outside every pairwise bad set, `oodEval · z` is injective on the
list: equal OOD values force equal codewords. -/
theorem oodEval_injective_of_good (dom : ι ↪ F) {d ℓ : ℕ} {ws : Fin ℓ → ι → F}
    {z : F}
    (hgood : ¬ ∃ i j : Fin ℓ, i < j ∧ ws i ≠ ws j ∧
      oodEval dom d (ws i) z = oodEval dom d (ws j) z) :
    ∀ i j : Fin ℓ, oodEval dom d (ws i) z = oodEval dom d (ws j) z → ws i = ws j := by
  intro i j heq
  by_contra hne
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hgood ⟨i, j, hij, hne, heq⟩
  · exact hne rfl
  · exact hgood ⟨j, i, hji, Ne.symm hne, heq.symm⟩

omit [DecidableEq ι] in
/-- **THE UNIQUENESS PIN**: at a separating OOD point, a claimed OOD value `σ`
is realized by exactly ONE codeword of the list (given it is realized at all).
This is what upgrades the accumulator's "δ-close to SOME codeword in the list"
to "δ-close to THE codeword with this OOD value": the claim quantifies over one
codeword, not a list. -/
theorem existsUnique_of_good (dom : ι ↪ F) {d ℓ : ℕ} {ws : Fin ℓ → ι → F}
    {z : F}
    (hgood : ¬ ∃ i j : Fin ℓ, i < j ∧ ws i ≠ ws j ∧
      oodEval dom d (ws i) z = oodEval dom d (ws j) z)
    {σ : F} (hex : ∃ i, oodEval dom d (ws i) z = σ) :
    ∃! w : ι → F, (∃ i, ws i = w) ∧ oodEval dom d w z = σ := by
  obtain ⟨i₀, hi₀⟩ := hex
  refine ⟨ws i₀, ⟨⟨i₀, rfl⟩, hi₀⟩, ?_⟩
  rintro w ⟨⟨j, rfl⟩, hj⟩
  exact oodEval_injective_of_good dom hgood j i₀ (by rw [hi₀, hj])

end Pin

/-! ## Probability forms: uniform OOD sampling

`uniformProb` (Selvage/Rbr.lean, counting — no measure theory) over the OOD
challenge space `{z : F // z ∉ Set.range dom}`; the space is `Type`-0 because
`uniformProb` is, matching the Rbr/Depth/Sumcheck precedent. -/

section Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F] [Fintype F]

omit [DecidableEq ι] [Field F] in
/-- The OOD challenge space has `|F| − |ι|` points. -/
theorem card_oodChallenge (dom : ι ↪ F) :
    Fintype.card {z : F // z ∉ Set.range dom}
      = Fintype.card F - Fintype.card ι := by
  rw [Fintype.card_subtype]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset F)) (p := fun z : F => z ∈ Set.range dom)
  have him : (Finset.univ.filter fun z : F => z ∈ Set.range dom)
      = Finset.univ.image dom := by
    ext z
    simp [Set.mem_range, eq_comm]
  rw [him, Finset.card_image_of_injective _ dom.injective, Finset.card_univ,
    Finset.card_univ] at hsplit
  omega

/-- Pointwise-equivalent events have equal `uniformProb` — the counting-only
congruence (`Selvage/Depth.lean` carries the same fact; restated privately here so
this file depends only on `Selvage/Rbr.lean`'s `uniformProb`). -/
private theorem uniformProb_congr' {C : Type} [Fintype C] {p q : C → Prop}
    (h : ∀ c, p c ↔ q c) : uniformProb C p = uniformProb C q := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeEquivRight h)]

omit [DecidableEq ι] [Field F] in
private theorem natCard_oodSubtype_eq (dom : ι ↪ F) (p : F → Prop)
    [DecidablePred p] :
    Nat.card {z : {z : F // z ∉ Set.range dom} // p z.val}
      = (Finset.univ.filter fun z : F => z ∉ Set.range dom ∧ p z).card := by
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _),
    Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [DecidableEq ι] [Field F] in
/-- Generic division step: an OOD-restricted count bound becomes a `uniformProb`
bound over the OOD challenge space. -/
private theorem uniformProb_ood_le (dom : ι ↪ F) {p : F → Prop} [DecidablePred p]
    {r : ℝ}
    (hcount : ((Finset.univ.filter fun z : F =>
      z ∉ Set.range dom ∧ p z).card : ℝ) ≤ r)
    (hlt : Fintype.card ι < Fintype.card F) :
    uniformProb {z : F // z ∉ Set.range dom} (fun z => p z.val)
      ≤ r / ((Fintype.card F : ℝ) - (Fintype.card ι : ℝ)) := by
  unfold uniformProb
  rw [natCard_oodSubtype_eq dom p, card_oodChallenge dom]
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) - (Fintype.card ι : ℝ) := by
    have : (Fintype.card ι : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hlt
    linarith
  have hcast : ((Fintype.card F - Fintype.card ι : ℕ) : ℝ)
      = (Fintype.card F : ℝ) - (Fintype.card ι : ℝ) :=
    Nat.cast_sub (le_of_lt hlt)
  rw [hcast]
  exact (div_le_div_iff_of_pos_right hpos).mpr hcount

omit [DecidableEq ι] in
/-- **The pairwise pin, probability form (WHIR Lemma 4.25 / Arc Lemma 3.4
kernel)**: a uniform out-of-domain point makes two DISTINCT codewords collide
with probability at most `(d − 1)/(|F| − |ι|)`. -/
theorem uniformProb_oodAgree_le (dom : ι ↪ F) {d : ℕ} {u v : ι → F}
    (hu : u ∈ reedSolomonCode dom d) (hv : v ∈ reedSolomonCode dom d)
    (hne : u ≠ v) (hlt : Fintype.card ι < Fintype.card F) :
    uniformProb {z : F // z ∉ Set.range dom}
      (fun z => oodEval dom d u z.val = oodEval dom d v z.val)
      ≤ ((d : ℝ) - 1) / ((Fintype.card F : ℝ) - (Fintype.card ι : ℝ)) := by
  refine uniformProb_ood_le dom
    (p := fun z : F => oodEval dom d u z = oodEval dom d v z) ?_ hlt
  have h := card_oodAgree_codeword_lt dom hu hv hne
  have h' : ((Finset.univ.filter fun z : F => z ∉ Set.range dom ∧
      oodEval dom d u z = oodEval dom d v z).card : ℝ) + 1 ≤ (d : ℝ) := by
    exact_mod_cast h
  linarith

omit [DecidableEq ι] in
/-- **List separation, probability form**: a uniform OOD point separates every
distinct pair of an `ℓ`-list of codewords except with probability
`≤ (ℓ choose 2)·(d − 1)/(|F| − |ι|)`. -/
theorem uniformProb_oodListBad_le (dom : ι ↪ F) {d ℓ : ℕ} {ws : Fin ℓ → ι → F}
    (hws : ∀ i, ws i ∈ reedSolomonCode dom d)
    (hlt : Fintype.card ι < Fintype.card F) :
    uniformProb {z : F // z ∉ Set.range dom}
      (fun z => ∃ i j : Fin ℓ, i < j ∧ ws i ≠ ws j ∧
        oodEval dom d (ws i) z.val = oodEval dom d (ws j) z.val)
      ≤ ((ℓ.choose 2 * (d - 1) : ℕ) : ℝ)
        / ((Fintype.card F : ℝ) - (Fintype.card ι : ℝ)) := by
  refine uniformProb_ood_le dom
    (p := fun z : F => ∃ i j : Fin ℓ, i < j ∧ ws i ≠ ws j ∧
      oodEval dom d (ws i) z = oodEval dom d (ws j) z) ?_ hlt
  exact_mod_cast card_oodListBad_le dom hws

omit [DecidableEq ι] in
/-- **HEADLINE — OOD sampling pins the codeword**: except with probability
`≤ (ℓ choose 2)·(d − 1)/(|F| − |ι|)` over a uniform out-of-domain `z`, the map
`oodEval · z` is INJECTIVE on the list — so by `existsUnique_of_good` a claimed
OOD value quantifies over ONE codeword, not a list. -/
theorem uniformProb_ood_pin_fails_le (dom : ι ↪ F) {d ℓ : ℕ}
    {ws : Fin ℓ → ι → F} (hws : ∀ i, ws i ∈ reedSolomonCode dom d)
    (hlt : Fintype.card ι < Fintype.card F) :
    uniformProb {z : F // z ∉ Set.range dom}
      (fun z => ¬ ∀ i j : Fin ℓ,
        oodEval dom d (ws i) z.val = oodEval dom d (ws j) z.val → ws i = ws j)
      ≤ ((ℓ.choose 2 * (d - 1) : ℕ) : ℝ)
        / ((Fintype.card F : ℝ) - (Fintype.card ι : ℝ)) := by
  have hcongr : ∀ z : {z : F // z ∉ Set.range dom},
      (¬ ∀ i j : Fin ℓ,
        oodEval dom d (ws i) z.val = oodEval dom d (ws j) z.val → ws i = ws j)
      ↔ (∃ i j : Fin ℓ, i < j ∧ ws i ≠ ws j ∧
          oodEval dom d (ws i) z.val = oodEval dom d (ws j) z.val) := by
    intro z
    constructor
    · intro hnall
      push Not at hnall
      obtain ⟨i, j, heq, hne⟩ := hnall
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact ⟨i, j, hij, hne, heq⟩
      · exact absurd rfl hne
      · exact ⟨j, i, hji, Ne.symm hne, heq.symm⟩
    · rintro ⟨i, j, hij, hne, heq⟩ hall
      exact hne (hall i j heq)
  rw [uniformProb_congr' hcongr]
  exact uniformProb_oodListBad_le dom hws hlt

end Probability

/-! ## The constraint-channel bridge: OOD claims are `LinearConstraint`s

`Selvage/ConstrainedCode.lean` promised (via `exists_dotWt_eq`) that OOD
evaluation claims live in the linear constraint channel; here the weight vector
is EXHIBITED — the Lagrange basis sampled at `z` — and the equivalence with
`oodEval` is proved on the code. The accumulator can therefore carry an OOD
pin as an ordinary `constrainedRS` constraint and γ-batch it with the rest. -/

section Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- The OOD evaluation claim `oodEval f z = σ` as a linear constraint: weight
vector = the Lagrange basis polynomials of the domain, evaluated at `z`. -/
noncomputable def oodConstraint (dom : ι ↪ F) (z σ : F) : LinearConstraint ι F where
  wt := fun i => (Lagrange.basis Finset.univ (⇑dom) i).eval z
  target := σ

omit [DecidableEq F] in
/-- The constraint pairing computes the Lagrange interpolant's value at `z`. -/
theorem dotWt_oodConstraint (dom : ι ↪ F) (z σ : F) (f : ι → F) :
    dotWt (oodConstraint dom z σ).wt f
      = (Lagrange.interpolate Finset.univ (⇑dom) f).eval z := by
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  unfold dotWt oodConstraint
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, mul_comm]

/-- On the code (`d ≤ |ι|`), the degree-`< |ι|` Lagrange interpolant IS the
witness polynomial — uniqueness of interpolants in the wider window. -/
theorem interpolate_eq_codewordPoly (dom : ι ↪ F) {d : ℕ}
    (hd : d ≤ Fintype.card ι) {f : ι → F} (hf : f ∈ reedSolomonCode dom d) :
    Lagrange.interpolate Finset.univ (⇑dom) f = codewordPoly dom d f := by
  refine eq_of_degreeLT_of_agree dom (d := Fintype.card ι) le_rfl ?_ ?_ fun i => ?_
  · simpa [Finset.card_univ] using
      Lagrange.degree_interpolate_lt (s := Finset.univ) (v := ⇑dom) f
        dom.injective.injOn
  · exact lt_of_lt_of_le (codewordPoly_degree_lt dom d f) (by exact_mod_cast hd)
  · rw [Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := ⇑dom) f
      dom.injective.injOn (Finset.mem_univ i)]
    exact codewordPoly_eval dom d hf i

/-- **The bridge**: on the code, satisfying the OOD constraint IS having the
claimed OOD value. The OOD pin enters the accumulator's constraint channel. -/
theorem satisfies_oodConstraint_iff (dom : ι ↪ F) {d : ℕ}
    (hd : d ≤ Fintype.card ι) {f : ι → F} (hf : f ∈ reedSolomonCode dom d)
    {z σ : F} :
    Satisfies f (oodConstraint dom z σ) ↔ oodEval dom d f z = σ := by
  unfold Satisfies
  rw [dotWt_oodConstraint, interpolate_eq_codewordPoly dom hd hf]
  exact Iff.rfl

/-- The constrained code cut by an OOD constraint is exactly "codeword with the
pinned OOD value" — the claim object the accumulator folds, now carrying an OOD
pin. -/
theorem mem_constrainedRS_ood_iff (dom : ι ↪ F) {d : ℕ}
    (hd : d ≤ Fintype.card ι) {z σ : F} {f : ι → F} :
    f ∈ constrainedRS dom d [oodConstraint dom z σ]
      ↔ f ∈ reedSolomonCode dom d ∧ oodEval dom d f z = σ := by
  rw [mem_constrainedRS_iff]
  constructor
  · rintro ⟨hf, hc⟩
    exact ⟨hf, (satisfies_oodConstraint_iff dom hd hf).mp
      (hc _ (List.mem_singleton_self _))⟩
  · rintro ⟨hf, hood⟩
    refine ⟨hf, fun c hc => ?_⟩
    rw [List.mem_singleton] at hc
    subst hc
    exact (satisfies_oodConstraint_iff dom hd hf).mpr hood

end Bridge

/-! ## Keystones over `F₅` (ATLAS: satisfiable + teeth, BUILT)

`RS[F₅, {0,1,2,3}, 2]` from `ReedSolomon.RSExample`: the single OOD point is
`z = 4`. Witnesses computed through `oodEval_eq_of_witness` (the polynomial is
noncomputable, its value through an explicit witness is not) and `decide`. -/

namespace OODExample

open RSExample

/-- `z = 4` is out of domain: the domain is `{0, 1, 2, 3}`. -/
theorem four_ood : (4 : ZMod 5) ∉ Set.range dom₅ := by decide

/-- Premise inhabitation, via the general iff: OOD points exist because the
domain is proper (`4 < 5`) — `exists_ood_iff` FIRES. -/
example : ∃ z : ZMod 5, z ∉ Set.range dom₅ :=
  (exists_ood_iff dom₅).mpr (by simp [ZMod.card])

/-- The degree window fits the domain: `d = 2 ≤ 4 = |ι|` — `oodEval` is
choice-free here. -/
theorem hd₅ : 2 ≤ Fintype.card (Fin 4) := by simp

/-- `xWord`'s OOD evaluation is `X`'s value: `oodEval xWord z = z`. -/
theorem oodEval_xWord (z : ZMod 5) : oodEval dom₅ 2 xWord z = z := by
  rw [oodEval_eq_of_witness dom₅ hd₅ (p := (X : Polynomial (ZMod 5)))
    (by rw [Polynomial.degree_X]; decide) (fun i => by simp [xWord, dom₅]) z,
    Polynomial.eval_X]

/-- The zero word's OOD evaluation is `0` everywhere. -/
theorem oodEval_zero (z : ZMod 5) :
    oodEval dom₅ 2 (0 : Fin 4 → ZMod 5) z = 0 := by
  rw [oodEval_eq_of_witness dom₅ hd₅ (p := (0 : Polynomial (ZMod 5)))
    (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _)
    (fun i => by simp) z, Polynomial.eval_zero]

/-- **SATISFIABLE — the pin genuinely separates**: `xWord` and `0` are distinct
codewords with DIFFERENT OOD values at `z = 4` (`4 ≠ 0`). -/
theorem pin_separates :
    xWord ≠ (0 : Fin 4 → ZMod 5) ∧
      oodEval dom₅ 2 xWord 4 ≠ oodEval dom₅ 2 (0 : Fin 4 → ZMod 5) 4 := by
  refine ⟨xWord_ne_zero, ?_⟩
  rw [oodEval_xWord, oodEval_zero]
  decide

/-- The adversarial codeword: evaluations of `2X + 1` — built to collide with
`xWord` exactly at the OOD point (`z = 2z + 1` iff `z = 4` in `F₅`). -/
def qWord : Fin 4 → ZMod 5 := fun i => 2 * (i.val : ZMod 5) + 1

theorem qWord_mem : qWord ∈ reedSolomonCode dom₅ 2 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.C 2 * Polynomial.X + Polynomial.C 1,
      lt_of_le_of_lt Polynomial.degree_linear_le (by decide),
      fun i => by simp [qWord, dom₅]⟩

theorem xWord_ne_qWord : xWord ≠ qWord := by decide

/-- `qWord`'s OOD evaluation is `2X + 1`'s value. -/
theorem oodEval_qWord (z : ZMod 5) : oodEval dom₅ 2 qWord z = 2 * z + 1 := by
  rw [oodEval_eq_of_witness dom₅ hd₅
    (p := (Polynomial.C 2 * Polynomial.X + Polynomial.C 1 : Polynomial (ZMod 5)))
    (lt_of_le_of_lt Polynomial.degree_linear_le (by decide))
    (fun i => by simp [qWord, dom₅]) z]
  simp

/-- **TEETH, attained**: the distinct pair `(xWord, qWord)` collides at EXACTLY
one OOD point (`z = 4`, where `4 = 2·4+1`): the pin bound `d − 1 = 1` is tight,
not slack. -/
theorem card_oodAgree_xWord_qWord :
    (Finset.univ.filter fun z : ZMod 5 => z ∉ Set.range dom₅ ∧
        oodEval dom₅ 2 xWord z = oodEval dom₅ 2 qWord z).card = 1 := by
  have hcongr : (Finset.univ.filter fun z : ZMod 5 => z ∉ Set.range dom₅ ∧
        oodEval dom₅ 2 xWord z = oodEval dom₅ 2 qWord z)
      = Finset.univ.filter fun z : ZMod 5 => z ∉ Set.range dom₅ ∧ z = 2 * z + 1 :=
    Finset.filter_congr fun z _ => by rw [oodEval_xWord, oodEval_qWord]
  rw [hcongr]
  decide

/-- The general pin bound FIRES on the concrete distinct pair — and is attained
(`= 1` by `card_oodAgree_xWord_qWord`). -/
example :
    (Finset.univ.filter fun z : ZMod 5 => z ∉ Set.range dom₅ ∧
        oodEval dom₅ 2 xWord z = oodEval dom₅ 2 qWord z).card ≤ 2 - 1 :=
  card_oodAgree_codeword_le dom₅ xWord_mem qWord_mem xWord_ne_qWord

/-- The good pair's OOD collision count is `0` (they agree only at `z = 0`,
which is IN-domain): both poles of the count are exhibited. -/
theorem card_oodAgree_xWord_zero :
    (Finset.univ.filter fun z : ZMod 5 => z ∉ Set.range dom₅ ∧
        oodEval dom₅ 2 xWord z = oodEval dom₅ 2 (0 : Fin 4 → ZMod 5) z).card
      = 0 := by
  have hcongr : (Finset.univ.filter fun z : ZMod 5 => z ∉ Set.range dom₅ ∧
        oodEval dom₅ 2 xWord z = oodEval dom₅ 2 (0 : Fin 4 → ZMod 5) z)
      = Finset.univ.filter fun z : ZMod 5 => z ∉ Set.range dom₅ ∧ z = 0 :=
    Finset.filter_congr fun z _ => by rw [oodEval_xWord, oodEval_zero]
  rw [hcongr]
  decide

/-- **Honest quantization (quote the pessimistic number)**: at these toy
parameters the adversarial pair collides with probability `1` — the bound
`(d−1)/(|F|−|L|) = 1/1` is met with equality, and a 1-point OOD space buys
NOTHING. The pin's security lives entirely in `|F| − |L|`. -/
theorem pin_fail_prob_one :
    uniformProb {z : ZMod 5 // z ∉ Set.range dom₅}
      (fun z => oodEval dom₅ 2 xWord z.val = oodEval dom₅ 2 qWord z.val) = 1 := by
  unfold uniformProb
  beta_reduce
  rw [natCard_oodSubtype_eq dom₅
      (fun z : ZMod 5 => oodEval dom₅ 2 xWord z = oodEval dom₅ 2 qWord z),
    card_oodAgree_xWord_qWord, card_oodChallenge dom₅]
  norm_num [ZMod.card]

/-- **THE PIN, end-to-end**: on the list `[xWord, 0]`, the OOD point `z = 4`
separates (values `4` vs `0`), so the claimed OOD value `4` pins exactly ONE
codeword — the claim quantifies over one codeword, not a list. -/
theorem pin_pins_unique :
    ∃! w : Fin 4 → ZMod 5,
      (∃ i : Fin 2, ![xWord, (0 : Fin 4 → ZMod 5)] i = w) ∧
        oodEval dom₅ 2 w 4 = 4 := by
  refine existsUnique_of_good dom₅ ?_ ⟨0, by simp [oodEval_xWord]⟩
  rintro ⟨i, j, hij, hne, heq⟩
  have h4 : (4 : ZMod 5) ≠ 0 := by decide
  fin_cases i <;> fin_cases j <;> simp_all [oodEval_xWord, oodEval_zero]

/-- The bridge keystone: the OOD pin `oodEval xWord 4 = 4` carried as an
ordinary constrained-code membership — the accumulator's claim object. -/
example : xWord ∈ constrainedRS dom₅ 2 [oodConstraint dom₅ 4 4] :=
  (mem_constrainedRS_ood_iff dom₅ hd₅).mpr ⟨xWord_mem, oodEval_xWord 4⟩

end OODExample

end Minidregg.Selvage
