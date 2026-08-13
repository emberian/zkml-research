/-
# Selvage.Depth — [OB-2] depth composition: the audit finding and the proof tower.

Target: `OB2_depth_composition` (Selvage/Rbr.lean), WARP (ePrint 2025/753) Thm B.4
via Construction B.5 + Claim B.6 + the union bound over the `t + k` unique
moves of the full trace.

**Audit finding first (teeth):** the audited statement is REFUTABLE, and this
file proves that (`OB2_depth_composition_false`). The hole is the degenerate
corner `Z = ∅`: the SR bad event's first conjunct `o.stmt ∈ Z` empties the
event, so its probability is `0`, while `εrbr` is constrained by the hypothesis
only ON `Z` — so `εrbr := fun _ => -1` satisfies the (vacuous) hypothesis and
the conclusion demands `0 ≤ (t + r.k) · (-1) < 0` (note `k_pos` forces
`t + k ≥ 1`). The paper never meets this corner: its `ε_rbr(δ)` is a `max` over
a tacitly-nonempty statement set of quantities each dominating a probability
(hence `≥ 0`). Specialization 7 of Selvage/Rbr.lean ("`ε_rbr` as an arbitrary
uniform bound") opened the hole. The one-line repair is a nonnegativity guard
on `εrbr`; `OB2_depth_composition_nonneg` below is the repaired obligation, and
the rest of the file is its proof tower.

What lands here:
* elementary counting lemmas for `uniformProb` (monotonicity, finite union
  bound, product slicing, transport along equivalences) — no measure theory;
* `wAt`/`srExtract` — Construction B.5, the backwards straightline extractor
  (`w_k := w'`, `w_{i-1} := E_rbr(tr_i, w_i)`, output `w_0`);
* `RoundBad` — the per-move RBR bad event of Def 4.2's `extract_sound`;
* `exists_roundBad_of_event` — Claim B.6, deterministic and pointwise: on ANY
  coin outcome, if the verifier accepts with `w'` in `R'_{≤δ}` while the chain
  output fails `R_{≤δ}`, some slot `a ∈ [k]` fires the per-move bad event;
* the fresh/log-hit attribution of the `k` final-prefix moves to the `t + k`
  unique-move budget, and the closed probability bound for the FRESH slots;
* `OB2_depth_composition_false` — the machine-checked refutation;
* the general lazy-`rnd` resolver (`stepOnce`/`runFrom`/`resolveIn`) and its
  uniformity kernel (`card_resolve_runFrom`) — the infrastructure the [OB-2a]
  audit identified as missing: the lazily-sampled game re-expressed from an
  arbitrary starting log, a resolver answering EVERY salted `(stmt, prefix)`
  pair, and the exact-uniformity of adaptively-scheduled fresh resolutions;
* `gameSlotBound_proved` — **[OB-2a] PROVED**: `Pr[HitBad j] ≤ εrbr δ`, by
  fixing the coin past (`splitAtGame`), pinning the hit move (`hitBad_fibre_le`),
  and pushforward slicing (`uniformProb_pushforward_le`) over the kernel;
* `OB2_depth_composition_nonneg_proved` — the repaired [OB-2′], **PROVED**
  with no remaining seam: `OB2_nonneg_of_gameSlotBound` applied to the
  discharged [OB-2a]. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Selvage.Rbr

namespace Minidregg.Selvage

/-! ## Elementary counting toolkit for `uniformProb` -/

section UniformProb

variable {C : Type} [Fintype C]

/-- The counted set, as a `Nat.card` inequality against the whole space. -/
lemma card_le_of_subtype (p : C → Prop) :
    (Nat.card {c : C // p c} : ℝ) ≤ (Fintype.card C : ℝ) := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_subtype_le p

lemma uniformProb_nonneg (p : C → Prop) : 0 ≤ uniformProb C p :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma uniformProb_le_one (p : C → Prop) : uniformProb C p ≤ 1 := by
  classical
  unfold uniformProb
  rcases Nat.eq_zero_or_pos (Fintype.card C) with h0 | hpos
  · simp [h0]
  · have hpos' : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hpos
    calc (Nat.card {c : C // p c} : ℝ) / (Fintype.card C : ℝ)
        ≤ (Fintype.card C : ℝ) / (Fintype.card C : ℝ) := by
          gcongr
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_subtype_le p
      _ = 1 := div_self (ne_of_gt hpos')

lemma uniformProb_congr {p q : C → Prop} (h : ∀ c, p c ↔ q c) :
    uniformProb C p = uniformProb C q := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeEquivRight h)]

lemma uniformProb_false {p : C → Prop} (h : ∀ c, ¬ p c) :
    uniformProb C p = 0 := by
  unfold uniformProb
  have : IsEmpty {c : C // p c} := ⟨fun x => h x.1 x.2⟩
  rw [Nat.card_of_isEmpty]
  simp

/-- Monotone counting: pointwise implication gives a card inequality. -/
lemma card_mono_of_imp {p q : C → Prop} (h : ∀ c, p c → q c) :
    (Nat.card {c : C // p c} : ℝ) ≤ (Nat.card {c : C // q c} : ℝ) := by
  classical
  have : Nat.card {c : C // p c} ≤ Nat.card {c : C // q c} :=
    Nat.card_mono (Set.toFinite {c | q c}) (fun c hc => h c hc)
  exact_mod_cast this

lemma uniformProb_mono {p q : C → Prop} (h : ∀ c, p c → q c) :
    uniformProb C p ≤ uniformProb C q := by
  classical
  unfold uniformProb
  rcases Nat.eq_zero_or_pos (Fintype.card C) with h0 | hpos
  · simp [h0]
  · have hpos' : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hpos
    gcongr
    · exact Nat.card_mono (Set.toFinite {c | q c}) (fun c hc => h c hc)

/-- Counting form of `Pr[p ∨ q] ≤ Pr[p] + Pr[q]`. -/
lemma uniformProb_or_le (p q : C → Prop) :
    uniformProb C (fun c => p c ∨ q c) ≤ uniformProb C p + uniformProb C q := by
  classical
  unfold uniformProb
  rw [← add_div]
  have hle : Nat.card {c : C // p c ∨ q c} ≤
      Nat.card {c : C // p c} + Nat.card {c : C // q c} := by
    have hunion : {c : C | p c ∨ q c} = {c : C | p c} ∪ {c : C | q c} := rfl
    calc Nat.card {c : C // p c ∨ q c}
        = ({c : C | p c} ∪ {c : C | q c} : Set C).ncard := by
          rw [← Nat.card_coe_set_eq, ← hunion]; rfl
      _ ≤ ({c : C | p c} : Set C).ncard + ({c : C | q c} : Set C).ncard :=
          Set.ncard_union_le _ _
      _ = Nat.card {c : C // p c} + Nat.card {c : C // q c} := by
          rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]; rfl
  gcongr
  exact_mod_cast hle

/-- The finite union bound over `Fin m` — the `Finset` card arithmetic behind
Thm B.4's "union bound over the at most `t + k` unique moves". -/
lemma uniformProb_exists_le : ∀ {m : ℕ} (p : Fin m → C → Prop),
    uniformProb C (fun c => ∃ i, p i c) ≤ ∑ i : Fin m, uniformProb C (p i) := by
  intro m
  induction m with
  | zero =>
    intro p
    rw [uniformProb_false (by rintro c ⟨i, -⟩; exact i.elim0)]
    simp
  | succ m ih =>
    intro p
    calc uniformProb C (fun c => ∃ i, p i c)
        = uniformProb C (fun c => p 0 c ∨ ∃ i : Fin m, p i.succ c) :=
          uniformProb_congr fun c => Fin.exists_fin_succ
      _ ≤ uniformProb C (p 0) + uniformProb C (fun c => ∃ i : Fin m, p i.succ c) :=
          uniformProb_or_le _ _
      _ ≤ uniformProb C (p 0) + ∑ i : Fin m, uniformProb C (p i.succ) := by
          have := ih (fun i => p i.succ)
          linarith
      _ = ∑ i : Fin (m + 1), uniformProb C (p i) :=
          (Fin.sum_univ_succ (fun i => uniformProb C (p i))).symm

/-- Transport along an equivalence: `uniformProb` only counts. -/
lemma uniformProb_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B)
    (p : B → Prop) : uniformProb A (fun a => p (e a)) = uniformProb B p := by
  unfold uniformProb
  rw [Nat.card_congr (e.subtypeEquiv fun a => Iff.rfl), Fintype.card_congr e]

/-- Product slicing: if every fibre over the first coordinate has conditional
probability at most `ε`, so does the whole event. The counting rendering of
"condition on everything but the fresh coin". -/
lemma uniformProb_prod_le {A B : Type} [Fintype A] [Fintype B]
    {p : A × B → Prop} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a, uniformProb B (fun b => p (a, b)) ≤ ε) :
    uniformProb (A × B) p ≤ ε := by
  classical
  unfold uniformProb at *
  rcases Nat.eq_zero_or_pos (Fintype.card B) with hB0 | hBpos
  · have hAB : Fintype.card (A × B) = 0 := by simp [Fintype.card_prod, hB0]
    simp [hAB, hε]
  rcases Nat.eq_zero_or_pos (Fintype.card A) with hA0 | hApos
  · have hAB : Fintype.card (A × B) = 0 := by simp [Fintype.card_prod, hA0]
    simp [hAB, hε]
  have hBpos' : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast hBpos
  have hABpos : (0 : ℝ) < (Fintype.card (A × B) : ℝ) := by
    rw [Fintype.card_prod]
    exact_mod_cast Nat.mul_pos hApos hBpos
  -- fibrewise decomposition of the counted set
  have hsplit : Nat.card {x : A × B // p x} =
      ∑ a : A, Nat.card {b : B // p (a, b)} := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_congr
      (⟨fun x => ⟨x.1.1, ⟨x.1.2, by cases x with | mk v hv => exact hv⟩⟩,
        fun s => ⟨(s.1, s.2.1), s.2.2⟩,
        fun x => by cases x with | mk v hv => rfl,
        fun s => rfl⟩ :
        {x : A × B // p x} ≃ (a : A) × {b : B // p (a, b)})]
    rw [Fintype.card_sigma]
    simp [Nat.card_eq_fintype_card]
  have hfib : ∀ a : A, (Nat.card {b : B // p (a, b)} : ℝ) ≤
      ε * Fintype.card B := by
    intro a
    have ha := h a
    rw [div_le_iff₀ hBpos'] at ha
    exact ha
  rw [div_le_iff₀ hABpos, hsplit, Nat.cast_sum]
  calc (∑ a : A, (Nat.card {b : B // p (a, b)} : ℝ))
      ≤ ∑ _a : A, ε * (Fintype.card B : ℝ) := Finset.sum_le_sum fun a _ => hfib a
    _ = (Fintype.card A : ℝ) * (ε * (Fintype.card B : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ε * ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := mul_left_comm _ _ _
    _ = ε * (Fintype.card (A × B) : ℝ) := by
        rw [Fintype.card_prod, Nat.cast_mul]

end UniformProb

/-! ## Splitting one coordinate out of a tuple of coins

Hand-rolled (rather than `Equiv.funSplitAt`) so the `symm` direction reduces
definitionally at both the split coordinate and the others. -/

/-- Split coordinate `i` out of a `Fin n`-indexed tuple. -/
def splitCoord {n : ℕ} {β : Type} (i : Fin n) :
    (Fin n → β) ≃ (({j : Fin n // j ≠ i} → β) × β) where
  toFun f := (fun j => f j.1, f i)
  invFun x j := if h : j = i then x.2 else x.1 ⟨j, h⟩
  left_inv f := by
    funext j
    by_cases h : j = i <;> simp [h]
  right_inv x := by
    refine Prod.ext ?_ ?_
    · funext j
      simp [j.2]
    · simp

@[simp] lemma splitCoord_symm_apply_self {n : ℕ} {β : Type} (i : Fin n)
    (x : ({j : Fin n // j ≠ i} → β) × β) : (splitCoord i).symm x i = x.2 := by
  simp [splitCoord]

@[simp] lemma splitCoord_symm_apply_ne {n : ℕ} {β : Type} {i j : Fin n}
    (h : j ≠ i) (x : ({j : Fin n // j ≠ i} → β) × β) :
    (splitCoord i).symm x j = x.1 ⟨j, h⟩ := by
  simp [splitCoord, h]

/-- Split coordinate `i` out of the FIRST factor of a product of a tuple with
anything. -/
def splitProd1 {n : ℕ} {β γ : Type} (i : Fin n) :
    ((Fin n → β) × γ) ≃ ((({j : Fin n // j ≠ i} → β) × γ) × β) where
  toFun x := ((fun j => x.1 j.1, x.2), x.1 i)
  invFun y := (fun j => if h : j = i then y.2 else y.1.1 ⟨j, h⟩, y.1.2)
  left_inv x := by
    refine Prod.ext ?_ rfl
    funext j
    by_cases h : j = i <;> simp [h]
  right_inv y := by
    refine Prod.ext (Prod.ext ?_ rfl) ?_
    · funext j
      simp [j.2]
    · simp

@[simp] lemma splitProd1_symm_fst_self {n : ℕ} {β γ : Type} (i : Fin n)
    (y : (({j : Fin n // j ≠ i} → β) × γ) × β) :
    ((splitProd1 i).symm y).1 i = y.2 := by
  simp [splitProd1]

@[simp] lemma splitProd1_symm_fst_ne {n : ℕ} {β γ : Type} {i j : Fin n}
    (h : j ≠ i) (y : (({j : Fin n // j ≠ i} → β) × γ) × β) :
    ((splitProd1 i).symm y).1 j = y.1.1 ⟨j, h⟩ := by
  simp [splitProd1, h]

@[simp] lemma splitProd1_symm_snd {n : ℕ} {β γ : Type} (i : Fin n)
    (y : (({j : Fin n // j ≠ i} → β) × γ) × β) :
    ((splitProd1 i).symm y).2 = y.1.2 := rfl

/-! ## Construction B.5 — the backwards straightline extractor -/

section Extractor

variable {r : Reduction}

/-- The Construction B.5 witness chain, indexed from the top:
`wAt rbr st rounds w' i` is `w_i`, with `w_i := w'` for `i ≥ rounds.length`
(the seed `w_k := w'` — the prover's own target-relation candidate) and
`w_i := E_rbr(st, tr_{i+1}, w_{i+1})` below it, where `tr_{i+1}` is the
transcript of the first `i + 1` completed rounds. The extractor outputs
`w_0`. -/
def wAt (rbr : RbrKnowledgeSoundness r) (st : Stmt r)
    (rounds : List (r.PMsg × r.Chal)) (w' : r.W) (i : ℕ) : r.W :=
  if h : rounds.length ≤ i then w'
  else rbr.extract st ⟨rounds.take (i + 1), none⟩ (wAt rbr st rounds w' (i + 1))
  termination_by rounds.length - i
  decreasing_by omega

lemma wAt_of_le (rbr : RbrKnowledgeSoundness r) (st : Stmt r)
    (rounds : List (r.PMsg × r.Chal)) (w' : r.W) {i : ℕ}
    (h : rounds.length ≤ i) : wAt rbr st rounds w' i = w' := by
  unfold wAt
  simp [h]

lemma wAt_of_lt (rbr : RbrKnowledgeSoundness r) (st : Stmt r)
    (rounds : List (r.PMsg × r.Chal)) (w' : r.W) {i : ℕ}
    (h : i < rounds.length) :
    wAt rbr st rounds w' i =
      rbr.extract st ⟨rounds.take (i + 1), none⟩ (wAt rbr st rounds w' (i + 1)) := by
  conv_lhs => unfold wAt
  simp [Nat.not_le.mpr h]

/-- **Construction B.5**: the straightline state-restoration extractor. It
reads only the output statement, the prover messages, the candidate witness
`w'`, and the final challenges — the game trace argument is unused, exactly as
in the paper. `w_k := w'`; `w_{i-1} := E_rbr(𝕚, 𝕩, 𝕪, (π₁,ρ₁,…,π_i,ρ_i), w_i)`;
output `w_0`. -/
def srExtract (rbr : RbrKnowledgeSoundness r) (s : ℕ) : SrExtractor r s :=
  fun o ρs _log => wAt rbr o.stmt (List.ofFn fun i => (o.πs i, ρs i)) o.w' 0

/-! ## The per-move RBR bad event, and Claim B.6 -/

/-- The per-move RBR bad event — the event of Def 4.2's `extract_sound`, as a
predicate of the prefix `rs`, the pending prover message `π`, and the fresh
challenge `ρ`: SOME knowledge-state witness survives at the extended transcript
while the round extractor's output dies at the shorter one. -/
def RoundBad (rbr : RbrKnowledgeSoundness r) (δ : ℝ) (st : Stmt r)
    (rs : List (r.PMsg × r.Chal)) (π : r.PMsg) (ρ : r.Chal) : Prop :=
  ∃ w : r.W,
    rbr.kstate.state δ st ⟨rs, some π⟩
      (rbr.extract st ⟨rs ++ [(π, ρ)], none⟩ w) = false ∧
    rbr.kstate.state δ st ⟨rs ++ [(π, ρ)], none⟩ w = true

/-- Def 4.2's round bound, re-stated against `RoundBad`. -/
lemma uniformProb_roundBad_le (rbr : RbrKnowledgeSoundness r) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (st : Stmt r) (i : Fin r.k)
    {rs : List (r.PMsg × r.Chal)} (hlen : rs.length = (i : ℕ)) (π : r.PMsg) :
    uniformProb r.Chal (RoundBad rbr δ st rs π) ≤ rbr.err i st δ :=
  rbr.extract_sound δ hδ st i rs hlen π

/-- Per-round knowledge errors are nonnegative on the paper's `δ` range: each
dominates a `uniformProb` (Def 4.2 at any prefix of the right length). This is
why the paper never needs the nonnegativity guard explicitly — and why the
repaired [OB-2′] guard is free for every nonempty `Z`
(`εrbr_nonneg_of_nonempty`). -/
lemma err_nonneg (rbr : RbrKnowledgeSoundness r) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (i : Fin r.k) (st : Stmt r) :
    0 ≤ rbr.err i st δ := by
  obtain ⟨π₀⟩ := r.pmsgNonempty
  obtain ⟨ρ₀⟩ := r.chalNonempty
  exact le_trans (uniformProb_nonneg _)
    (rbr.extract_sound δ hδ st i (List.replicate (i : ℕ) (π₀, ρ₀))
      (List.length_replicate) π₀)

/-- For nonempty `Z`, any uniform bound on the per-round errors over `Z` is
automatically nonnegative on `δ ∈ (0, δ*)` — the repaired [OB-2′] guard costs
nothing outside the refutable `Z = ∅` corner. -/
lemma εrbr_nonneg_of_nonempty (rbr : RbrKnowledgeSoundness r)
    {Z : Set (Stmt r)} (hZ : Z.Nonempty) {εrbr : ℝ → ℝ}
    (hdom : ∀ (i : Fin r.k) (st : Stmt r), st ∈ Z →
      ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, rbr.err i st δ ≤ εrbr δ) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, 0 ≤ εrbr δ := by
  intro δ hδ
  obtain ⟨st, hst⟩ := hZ
  exact le_trans (err_nonneg rbr hδ ⟨0, r.k_pos⟩ st)
    (hdom ⟨0, r.k_pos⟩ st hst δ hδ)

/-- **Claim B.6, the backwards descent** (deterministic, pointwise). From a
knowledge-state witness alive at level `i` of the chain, either some completed
round `a` fires the per-move bad event (with the chain witness `w_{a+1}` as the
existential witness), or the chain walks all the way down and `w_0` is alive at
the empty transcript. Uses `prover_monotone` at every step — the one clause of
Def 4.1 the union bound leans on. -/
lemma chain_descend (rbr : RbrKnowledgeSoundness r) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (st : Stmt r)
    {rounds : List (r.PMsg × r.Chal)} (hlen : rounds.length = r.k) (w' : r.W) :
    ∀ i : ℕ, i ≤ r.k →
      rbr.kstate.state δ st ⟨rounds.take i, none⟩ (wAt rbr st rounds w' i) = true →
      (∃ (a : Fin r.k) (π : r.PMsg) (ρ : r.Chal),
          rounds[(a : ℕ)]? = some (π, ρ) ∧
          RoundBad rbr δ st (rounds.take (a : ℕ)) π ρ) ∨
        rbr.kstate.state δ st ⟨rounds.take 0, none⟩ (wAt rbr st rounds w' 0) = true := by
  intro i
  induction i with
  | zero => exact fun _ h0 => Or.inr h0
  | succ i ih =>
    intro hik htrue
    have hi : i < rounds.length := by omega
    have hik' : i ≤ r.k := by omega
    have htake : rounds.take (i + 1) = rounds.take i ++ [rounds[i]'hi] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      rfl
    have hw : wAt rbr st rounds w' i =
        rbr.extract st ⟨rounds.take (i + 1), none⟩ (wAt rbr st rounds w' (i + 1)) :=
      wAt_of_lt rbr st rounds w' hi
    cases hval : rbr.kstate.state δ st ⟨rounds.take i, some (rounds[i]'hi).1⟩
        (wAt rbr st rounds w' i) with
    | false =>
      -- the per-move bad event fires at slot `i`, witnessed by `w_{i+1}`
      refine Or.inl ⟨⟨i, by omega⟩, (rounds[i]'hi).1, (rounds[i]'hi).2,
        by rw [List.getElem?_eq_getElem hi], ⟨wAt rbr st rounds w' (i + 1), ?_, ?_⟩⟩
      · rw [← htake, ← hw]
        exact hval
      · rw [← htake]
        exact htrue
    | true =>
      -- prover monotonicity walks the truth down past the pending message
      have hlt : (rounds.take i).length < r.k := by
        rw [List.length_take]
        omega
      have hmon := rbr.kstate.prover_monotone δ hδ st (rounds.take i)
        (wAt rbr st rounds w' i) hlt
      cases h0 : rbr.kstate.state δ st ⟨rounds.take i, none⟩
          (wAt rbr st rounds w' i) with
      | false =>
        have := hmon h0 (rounds[i]'hi).1
        rw [hval] at this
        exact absurd this (by simp)
      | true => exact ih hik' h0

/-- **Claim B.6** (pointwise): on ANY outcome where the verifier accepts the
full transcript with the prover's candidate `w'` in `R'_{≤δ}` while the
Construction B.5 output `w_0` fails `R_{≤δ}`, some slot `a ∈ [k]` fires the
per-move bad event at the length-`a` prefix of the final transcript. -/
lemma exists_roundBad_of_event (rbr : RbrKnowledgeSoundness r) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (st : Stmt r)
    (πs : Fin r.k → r.PMsg) (ρs : Fin r.k → r.Chal) (w' : r.W)
    (hacc : ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
      r.verify st.idx st.x st.y πs ρs = some (x', y') ∧
      RelaxedMem r.R' δ st.idx x' y' w')
    (hfail : ¬ RelaxedMem r.R δ st.idx st.x st.y
      (wAt rbr st (List.ofFn fun i => (πs i, ρs i)) w' 0)) :
    ∃ a : Fin r.k,
      RoundBad rbr δ st ((List.ofFn fun i => (πs i, ρs i)).take (a : ℕ))
        (πs a) (ρs a) := by
  set rounds := List.ofFn fun i => (πs i, ρs i) with hrounds
  have hlen : rounds.length = r.k := by simp [hrounds]
  have htop : rbr.kstate.state δ st ⟨rounds.take r.k, none⟩
      (wAt rbr st rounds w' r.k) = true := by
    rw [wAt_of_le rbr st rounds w' (le_of_eq hlen), ← hlen, List.take_length]
    exact (rbr.kstate.full_iff δ hδ st πs ρs w').mpr hacc
  rcases chain_descend rbr hδ st hlen w' r.k (le_refl _) htop with
    ⟨a, π, ρ, hget, hbad⟩ | h0
  · have hgetfn : rounds[(a : ℕ)]? = some (πs a, ρs a) := by
      rw [hrounds]
      rw [List.getElem?_eq_getElem (by simp [a.isLt])]
      simp
    rw [hgetfn] at hget
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj hget
    exact ⟨a, h1.symm ▸ h2.symm ▸ hbad⟩
  · have h0' : rbr.kstate.state δ st Transcript.empty
        (wAt rbr st rounds w' 0) = true := by
      simpa [Transcript.empty] using h0
    exact absurd ((rbr.kstate.empty_iff δ hδ st (wAt rbr st rounds w' 0)).mp h0')
      hfail

end Extractor

/-! ## Teeth: the audited [OB-2] statement is refutable

`OB2_depth_composition` quantifies over ALL statement sets `Z` and ALL bound
functions `εrbr`, constraining `εrbr` only ON `Z`. At `Z = ∅` the hypothesis is
vacuous, so `εrbr := fun _ => -1` qualifies — and the conclusion then demands
`Pr[..] ≤ (t + k) · (-1) < 0` (`k_pos` forces `t + k ≥ 1`), against a
probability that is nonnegative by construction. Any single inhabited
`Reduction` + `RbrKnowledgeSoundness` pair therefore refutes the statement; we
exhibit the smallest one. The paper never meets this corner: its
`ε_rbr(δ) = max_{i,(𝕚,𝕩,𝕪) ∈ Z} ε_i ` is a max over a tacitly nonempty `Z` of
quantities that each dominate a probability (Def 4.2), hence are `≥ 0`.
Specialization 7 of Selvage/Rbr.lean (arbitrary uniform bound in place of the max)
opened the hole; `OB2_depth_composition_nonneg` below is the one-guard
repair. -/

section Teeth

/-- `Δ(u, u) = 0` — the disagreement set of a word with itself is empty. -/
lemma fracHamming_self {A : Type} {n : ℕ} (u : Fin n → A) :
    fracHamming u u = 0 := by
  unfold fracHamming
  have : IsEmpty {i : Fin n // u i ≠ u i} := ⟨fun x => x.2 rfl⟩
  rw [Nat.card_of_isEmpty]
  simp

/-- The smallest `Reduction`: all types `Unit`, one round, boolean challenges,
both relations `True`, verifier always accepting. -/
def trivialReduction : Reduction where
  Idx := Unit
  X := Unit
  A := Unit
  X' := Unit
  A' := Unit
  W := Unit
  n := 1
  n' := 1
  n_pos := one_pos
  n'_pos := one_pos
  R := fun _ _ _ _ => True
  R' := fun _ _ _ _ => True
  k := 1
  k_pos := one_pos
  PMsg := Unit
  Chal := Bool
  pmsgNonempty := ⟨()⟩
  chalFintype := inferInstance
  chalNonempty := ⟨true⟩
  δstar := 1
  δstar_pos := one_pos
  δstar_le_one := le_refl 1
  verify := fun _ _ _ _ _ => some ((), fun _ => ())

/-- The constant-`true` knowledge state function for `trivialReduction`:
both relations are `True`, so every clause of Def 4.1 is satisfied. -/
def trivialKState : KStateFn trivialReduction where
  state := fun _ _ _ _ => true
  empty_iff := by
    intro δ hδ st w
    refine ⟨fun _ => ⟨st.y, trivial, ?_⟩, fun _ => rfl⟩
    rw [fracHamming_self]
    exact le_of_lt hδ.1
  prover_monotone := by
    intro δ hδ st rs w hlen h
    simp at h
  full_iff := by
    intro δ hδ st πs ρs w
    refine ⟨fun _ => ⟨(), fun _ => (), rfl, ⟨fun _ => (), trivial, ?_⟩⟩,
      fun _ => rfl⟩
    rw [fracHamming_self]
    exact le_of_lt hδ.1

/-- RBR knowledge soundness for `trivialReduction`, with error `1` — every
probability is at most `1`. -/
def trivialRbr : RbrKnowledgeSoundness trivialReduction where
  kstate := trivialKState
  extract := fun _ _ w => w
  err := fun _ _ _ => 1
  extractTime := fun _ => 0
  extract_sound := by
    intro δ hδ st i rs hlen π
    exact uniformProb_le_one _

/-- A statement of the trivial reduction. -/
def trivialStmt : Stmt trivialReduction := ⟨(), (), fun _ => ()⟩

/-- The do-nothing state-restoration prover at salt size 0. -/
def trivialProver : SrProver trivialReduction 0 where
  move := fun _ => ⟨trivialStmt, []⟩
  out := fun _ => ⟨trivialStmt, fun _ => (), fun _ => Fin.elim0, ()⟩

/-- **The audited [OB-2] statement is FALSE.** Instantiate at `Z = ∅`,
`εrbr = -1` (the hypothesis is vacuous off `Z`), move budget `t = 0`: the
claimed bound is `(0 + 1) · (-1) = -1`, but `uniformProb` is nonnegative.
The repaired obligation is `OB2_depth_composition_nonneg` below. -/
theorem OB2_depth_composition_false : ¬ OB2_depth_composition := by
  intro h
  obtain ⟨E, hE⟩ := h trivialReduction trivialRbr ∅ (fun _ => -1)
    (fun i st hst => ((Set.mem_empty_iff_false st).mp hst).elim)
  have hbound := hE 0 0 (1 / 2)
    (by
      rw [Set.mem_Ioo]
      exact ⟨by norm_num, by show (1 : ℝ) / 2 < (1 : ℝ); norm_num⟩)
    trivialProver
  have hcontra := le_trans (uniformProb_nonneg _) hbound
  norm_num [show trivialReduction.k = 1 from rfl] at hcontra

end Teeth

/-! ## The state-restoration side: naming the moving parts

`srTrace`/`srFinalChal` are fixed by the audited statement; here we name the
derived objects the proof walks over: the adversary's output `srOut`, the final
full-transcript rounds `srRounds`, and — for each final-prefix slot `a ∈ [k]` —
whether its lazily-sampled response was FRESH (`find?` misses the trace: the
response is the coin `d a`) or a LOG HIT (first answered at game move `j`).
This is exactly Thm B.4's attribution of the `k` output-prefix moves to the
`t + k` unique moves of the full trace. -/

section StateRestoration

open Classical

variable {r : Reduction} {s t : ℕ}

/-- The adversary's final output on game coins `c` (Def B.1, step 2) — the
`o := P.out (log.map Prod.snd)` of the audited event, named. -/
noncomputable def srOut (P : SrProver r s) (c : Fin t → r.Chal) : SrOutput r s :=
  P.out ((srTrace P c).map Prod.snd)

/-- The final full-transcript rounds `(π_i, ρ_i)_{i ∈ [k]}` on coins `(c, d)`. -/
noncomputable def srRounds (P : SrProver r s) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) : List (r.PMsg × r.Chal) :=
  List.ofFn fun i => ((srOut P c).πs i, srFinalChal P c d i)

/-- `srFinalChal`, unfolded against the named `srOut`. -/
lemma srFinalChal_def (P : SrProver r s) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) (i : Fin r.k) :
    srFinalChal P c d i =
      match (srTrace P c).find?
          (fun e => decide (e.1 = (srOut P c).query i)) with
      | some e => e.2
      | none => d i := rfl

/-- A never-queried final prefix is answered by its own fresh coin. -/
lemma srFinalChal_of_none (P : SrProver r s) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) (i : Fin r.k)
    (h : (srTrace P c).find? (fun e => decide (e.1 = (srOut P c).query i)) =
      none) : srFinalChal P c d i = d i := by
  rw [srFinalChal_def, h]

/-- `srFinalChal P c d i` reads `d` only at index `i`. -/
lemma srFinalChal_congr (P : SrProver r s) (c : Fin t → r.Chal)
    {d d' : Fin r.k → r.Chal} (i : Fin r.k) (h : d i = d' i) :
    srFinalChal P c d i = srFinalChal P c d' i := by
  cases hf : (srTrace P c).find? (fun e => decide (e.1 = (srOut P c).query i)) with
  | some e => rw [srFinalChal_def, srFinalChal_def, hf]
  | none => rw [srFinalChal_def, srFinalChal_def, hf, h]

/-- Auxiliary: a fold that appends one entry per step grows by the step
count. -/
lemma foldl_length_aux {α β : Type} (f : List α → β → List α)
    (hf : ∀ L b, (f L b).length = L.length + 1) :
    ∀ (js : List β) (L : List α), (js.foldl f L).length = L.length + js.length := by
  intro js
  induction js with
  | nil => intro L; simp
  | cons j js ih =>
    intro L
    rw [List.foldl_cons, ih, hf]
    simp only [List.length_cons]
    omega

/-- The game trace records exactly `t` move–response pairs (repeats
included). -/
lemma srTrace_length (P : SrProver r s) (c : Fin t → r.Chal) :
    (srTrace P c).length = t := by
  unfold srTrace
  rw [foldl_length_aux _ ?_ _ _]
  · simp
  · intro L j
    dsimp only
    simp

/-! ### Trace structure: prefix determinism and per-step shape

Scaffolding banked toward **[OB-2a]** (`GameSlotBound`, below): the lazily-
sampled game reads its coins in step order, each at most once — these lemmas
expose that structure of `srTrace`'s fold: the first `j` entries are a fold
over the first `j` step indices (`srTrace_take`), and they depend only on the
coins below `j` (`srTrace_take_agree`) — i.e. the move made at any step `j` is
a function of `c_{<j}` alone. This is the backbone `GameSlotBound`'s proof
plan needs for a general lazy-rnd resolver's uniformity argument (see
`GameSlotBound`'s doc comment for exactly what is still missing and why these
lemmas alone don't close it: `srOut`, hence which slot `a` and its earlier
challenges, is a function of ALL of `c`, not just `c_{<j}`). `splitProd1`
below is the coordinate-splitting equivalence such a proof would slice
`c_j` out with, mirroring `splitCoord`'s role in `freshBad_le`. -/

/-- The one-step function of the lazily-sampled SR game, named. -/
noncomputable def stepFn (P : SrProver r s) (c : Fin t → r.Chal)
    (log : List (SrMove r s × r.Chal)) (j : Fin t) :
    List (SrMove r s × r.Chal) :=
  let q := P.move (log.map Prod.snd)
  let ρ := match log.find? (fun e => decide (e.1 = q)) with
    | some e => e.2
    | none => c j
  log ++ [(q, ρ)]

lemma srTrace_eq_foldl (P : SrProver r s) (c : Fin t → r.Chal) :
    srTrace P c = List.foldl (stepFn P c) [] (List.finRange t) := rfl

/-- The step appends exactly one entry. -/
lemma stepFn_eq (P : SrProver r s) (c : Fin t → r.Chal)
    (log : List (SrMove r s × r.Chal)) (j : Fin t) :
    stepFn P c log j = log ++ [(P.move (log.map Prod.snd),
      match log.find? (fun e => decide (e.1 = P.move (log.map Prod.snd))) with
      | some e => e.2
      | none => c j)] := rfl

lemma foldl_stepFn_prefix (P : SrProver r s) (c : Fin t → r.Chal) :
    ∀ (js : List (Fin t)) (L : List (SrMove r s × r.Chal)),
      L <+: List.foldl (stepFn P c) L js := by
  intro js
  induction js with
  | nil => intro L; simp
  | cons j js ih =>
    intro L
    rw [List.foldl_cons]
    exact List.IsPrefix.trans
      (by rw [stepFn_eq]; exact List.prefix_append _ _) (ih _)

lemma foldl_stepFn_length (P : SrProver r s) (c : Fin t → r.Chal)
    (js : List (Fin t)) (L : List (SrMove r s × r.Chal)) :
    (List.foldl (stepFn P c) L js).length = L.length + js.length :=
  foldl_length_aux _ (fun L j => by rw [stepFn_eq]; simp) js L

/-- The first `j` trace entries are the fold over the first `j` step
indices. -/
lemma srTrace_take (P : SrProver r s) (c : Fin t → r.Chal) {j : ℕ}
    (hj : j ≤ t) :
    (srTrace P c).take j =
      List.foldl (stepFn P c) [] ((List.finRange t).take j) := by
  set X := List.foldl (stepFn P c) [] ((List.finRange t).take j) with hX
  have hsplit : srTrace P c =
      List.foldl (stepFn P c) X ((List.finRange t).drop j) := by
    conv_lhs => rw [srTrace_eq_foldl, ← List.take_append_drop j (List.finRange t)]
    rw [List.foldl_append]
  have hpre : X <+: srTrace P c := by
    rw [hsplit]
    exact foldl_stepFn_prefix P c _ _
  have hlen : X.length = j := by
    rw [hX, foldl_stepFn_length]
    simp [hj]
  calc (srTrace P c).take j = (srTrace P c).take X.length := by rw [hlen]
    _ = X := (List.prefix_iff_eq_take.mp hpre).symm

/-- Agreement of the coins below `j` fixes the first `j` trace entries. -/
lemma srTrace_take_agree (P : SrProver r s) {c c' : Fin t → r.Chal} {j : ℕ}
    (hj : j ≤ t) (h : ∀ i : Fin t, (i : ℕ) < j → c i = c' i) :
    (srTrace P c).take j = (srTrace P c').take j := by
  rw [srTrace_take P c hj, srTrace_take P c' hj]
  have hgen : ∀ (js : List (Fin t)), (∀ i ∈ js, c i = c' i) →
      ∀ L, List.foldl (stepFn P c) L js = List.foldl (stepFn P c') L js := by
    intro js
    induction js with
    | nil => intro _ L; rfl
    | cons x js ih =>
      intro hmem L
      rw [List.foldl_cons, List.foldl_cons]
      have hx : stepFn P c L x = stepFn P c' L x := by
        rw [stepFn_eq, stepFn_eq, hmem x List.mem_cons_self]
      rw [hx]
      exact ih (fun i hi => hmem i (List.mem_cons_of_mem _ hi)) _
  apply hgen
  intro i hi
  apply h
  obtain ⟨m, hm, hget⟩ := List.mem_iff_getElem.mp hi
  have hmlt : m < (List.take j (List.finRange t)).length := hm
  have hmj : m < j := by
    rw [List.length_take] at hmlt
    omega
  rw [List.getElem_take, List.getElem_finRange] at hget
  rw [← hget]
  simpa using hmj

/-- `find?` hit gives a first-occurrence index (within the list length). -/
lemma exists_findIdx?_of_find? {α : Type} (p : α → Bool) :
    ∀ (l : List α) (e : α), l.find? p = some e →
      ∃ n : ℕ, l.findIdx? p = some n ∧ n < l.length := by
  intro l
  induction l with
  | nil => intro e h; simp at h
  | cons x l ih =>
    intro e h
    by_cases hpx : p x
    · exact ⟨0, by simp [List.findIdx?_cons, hpx], by simp⟩
    · rw [List.find?_cons_of_neg (by simpa using hpx)] at h
      obtain ⟨n, hn, hlt⟩ := ih e h
      refine ⟨n + 1, ?_, by simp; omega⟩
      rw [List.findIdx?_cons]
      simp [hpx, hn]

/-! ### The union-cover events -/

/-- The per-slot bad event at final-prefix slot `a`: the output statement lands
in `Z` and the per-move RBR bad event fires at the length-`a` prefix of the
final transcript, with pending message `π_{a+1}` and response `ρ_{a+1}`. -/
def slotBad (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) (δ : ℝ)
    (P : SrProver r s) (a : Fin r.k)
    (ω : (Fin t → r.Chal) × (Fin r.k → r.Chal)) : Prop :=
  (srOut P ω.1).stmt ∈ Z ∧
  RoundBad rbr δ (srOut P ω.1).stmt ((srRounds P ω.1 ω.2).take (a : ℕ))
    ((srOut P ω.1).πs a) (srFinalChal P ω.1 ω.2 a)

/-- Slot `a`'s final-prefix query was never made during the game: its response
is the fresh coin `d a`. -/
def freshAt (P : SrProver r s) (a : Fin r.k) (c : Fin t → r.Chal) : Prop :=
  (srTrace P c).find? (fun e => decide (e.1 = (srOut P c).query a)) = none

/-- Slot `a`'s final-prefix query WAS made during the game, first at move `j`:
its response is the coin that answered move `j`. -/
def hitAt (P : SrProver r s) (a : Fin r.k) (j : Fin t)
    (c : Fin t → r.Chal) : Prop :=
  (srTrace P c).findIdx? (fun e => decide (e.1 = (srOut P c).query a)) =
    some (j : ℕ)

/-- Cover event, fresh side: slot `a` fires and its response coin `d a` is
fresh — one of the `k` "output prefix" unique moves of Thm B.4. -/
def FreshBad (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) (δ : ℝ)
    (P : SrProver r s) (a : Fin r.k)
    (ω : (Fin t → r.Chal) × (Fin r.k → r.Chal)) : Prop :=
  freshAt P a ω.1 ∧ slotBad rbr Z δ P a ω

/-- Cover event, log-hit side: SOME slot fires whose response was first
sampled at game move `j` — one of the `t` "game move" unique moves of
Thm B.4. -/
def HitBad (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) (δ : ℝ)
    (P : SrProver r s) (j : Fin t)
    (ω : (Fin t → r.Chal) × (Fin r.k → r.Chal)) : Prop :=
  ∃ a : Fin r.k, hitAt P a j ω.1 ∧ slotBad rbr Z δ P a ω

/-- **The pointwise cover** (Claim B.6 + unique-move attribution): every
outcome in the Def B.2 bad event lies in some `FreshBad a` or some
`HitBad j`. -/
lemma cover (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (P : SrProver r s) :
    ∀ ω : (Fin t → r.Chal) × (Fin r.k → r.Chal),
      ((srOut P ω.1).stmt ∈ Z ∧
        ¬ RelaxedMem r.R δ (srOut P ω.1).stmt.idx (srOut P ω.1).stmt.x
          (srOut P ω.1).stmt.y
          (srExtract rbr s (srOut P ω.1) (srFinalChal P ω.1 ω.2)
            (srTrace P ω.1)) ∧
        ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
          r.verify (srOut P ω.1).stmt.idx (srOut P ω.1).stmt.x
            (srOut P ω.1).stmt.y (srOut P ω.1).πs (srFinalChal P ω.1 ω.2) =
            some (x', y') ∧
          RelaxedMem r.R' δ (srOut P ω.1).stmt.idx x' y' (srOut P ω.1).w') →
      (∃ a : Fin r.k, FreshBad rbr Z δ P a ω) ∨
        (∃ j : Fin t, HitBad rbr Z δ P j ω) := by
  rintro ω ⟨hz, hfail, hacc⟩
  obtain ⟨a, hbad⟩ := exists_roundBad_of_event rbr hδ (srOut P ω.1).stmt
    (srOut P ω.1).πs (srFinalChal P ω.1 ω.2) (srOut P ω.1).w' hacc hfail
  cases hfind : (srTrace P ω.1).find?
      (fun e => decide (e.1 = (srOut P ω.1).query a)) with
  | none => exact Or.inl ⟨a, hfind, hz, hbad⟩
  | some e =>
    obtain ⟨n, hn, hlt⟩ := exists_findIdx?_of_find? _ _ _ hfind
    rw [srTrace_length] at hlt
    exact Or.inr ⟨⟨n, hlt⟩, a, hn, hz, hbad⟩

/-! ### The fresh-slot bound -/

/-- **The fresh-slot bound**: `Pr[FreshBad a] ≤ εrbr δ`. Counting rendering of
the easy half of Thm B.4's per-unique-move argument: condition on everything
except the fresh coin `d a` (the trace, the output, the pending message, and
the earlier final challenges are all determined by the other coordinates), and
the response at slot `a` IS `d a` — Def 4.2's round bound applies with fixed
statement, prefix, and pending message. -/
lemma freshBad_le (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) {εrbr : ℝ → ℝ} (hnn : 0 ≤ εrbr δ)
    (hdom : ∀ (i : Fin r.k) (st : Stmt r), st ∈ Z → rbr.err i st δ ≤ εrbr δ)
    (P : SrProver r s) (a : Fin r.k) :
    uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal))
      (FreshBad rbr Z δ P a) ≤ εrbr δ := by
  classical
  -- move the fresh coin `d a` out as the last product coordinate
  have hsplit : uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal))
      (FreshBad rbr Z δ P a) =
      uniformProb (((Fin t → r.Chal) × ({j : Fin r.k // j ≠ a} → r.Chal)) ×
          r.Chal)
        (fun x => FreshBad rbr Z δ P a
          (x.1.1, (splitCoord a).symm (x.1.2, x.2))) :=
    (uniformProb_equiv
      ((((Equiv.refl (Fin t → r.Chal)).prodCongr (splitCoord a)).trans
        (Equiv.prodAssoc _ _ _).symm).symm)
      (FreshBad rbr Z δ P a)).symm
  rw [hsplit]
  apply uniformProb_prod_le hnn
  intro ω₁
  by_cases hf : freshAt P a ω₁.1
  swap
  · rw [uniformProb_false (by rintro ρ ⟨hfr, -⟩; exact hf hfr)]
    exact hnn
  by_cases hz : (srOut P ω₁.1).stmt ∈ Z
  swap
  · rw [uniformProb_false (by rintro ρ ⟨-, hzz, -⟩; exact hz hzz)]
    exact hnn
  obtain ⟨ρ₀⟩ := r.chalNonempty
  -- the earlier rounds are independent of the split coordinate
  have hRS : ∀ ρ : r.Chal,
      (srRounds P ω₁.1 ((splitCoord a).symm (ω₁.2, ρ))).take (a : ℕ) =
      (srRounds P ω₁.1 ((splitCoord a).symm (ω₁.2, ρ₀))).take (a : ℕ) := by
    intro ρ
    apply List.ext_getElem
    · simp [srRounds]
    · intro i h1 h2
      have hia : i < (a : ℕ) := by
        simpa [srRounds] using h1
      simp only [srRounds, List.getElem_take, List.getElem_ofFn]
      refine congrArg _ (srFinalChal_congr P _ _ ?_)
      have hne : (⟨i, by omega⟩ : Fin r.k) ≠ a := by
        intro hcontra
        have := congrArg Fin.val hcontra
        simp at this
        omega
      rw [splitCoord_symm_apply_ne hne, splitCoord_symm_apply_ne hne]
  -- the response at slot `a` is exactly the split coordinate
  have hresp : ∀ ρ : r.Chal,
      srFinalChal P ω₁.1 ((splitCoord a).symm (ω₁.2, ρ)) a = ρ := by
    intro ρ
    rw [srFinalChal_of_none P _ _ _ hf]
    simp
  have hlen : ((srRounds P ω₁.1
      ((splitCoord a).symm (ω₁.2, ρ₀))).take (a : ℕ)).length = (a : ℕ) := by
    simp [srRounds]
  calc uniformProb r.Chal (fun ρ => FreshBad rbr Z δ P a
        (ω₁.1, (splitCoord a).symm (ω₁.2, ρ)))
      = uniformProb r.Chal (RoundBad rbr δ (srOut P ω₁.1).stmt
          ((srRounds P ω₁.1 ((splitCoord a).symm (ω₁.2, ρ₀))).take (a : ℕ))
          ((srOut P ω₁.1).πs a)) := by
        apply uniformProb_congr
        intro ρ
        constructor
        · rintro ⟨-, -, hb⟩
          rw [hresp ρ, hRS ρ] at hb
          exact hb
        · intro hb
          refine ⟨hf, hz, ?_⟩
          rw [hresp ρ, hRS ρ]
          exact hb
    _ ≤ rbr.err a (srOut P ω₁.1).stmt δ :=
        uniformProb_roundBad_le rbr hδ _ a hlen _
    _ ≤ εrbr δ := hdom a _ hz

end StateRestoration

/-! ## Counting toolkit, part II: fibre decomposition and pushforward slicing

The three counting moves the game-slot bound needs beyond part I: splitting a
product count over its first coordinate, partitioning a count by the value of a
map, and the **pushforward slicing** lemma — if a map has exactly-uniform
fibres for every value of the tested coin, an event that tests the coin against
a per-value small set is small. This is the counting rendering of "the
adaptively-resolved values are jointly uniform and independent of the tested
coin", the eager-`rnd` fact the paper uses silently. -/

section UniformProbII

variable {C : Type} [Fintype C]

/-- Fibrewise decomposition of a counted product subtype over the first
coordinate. -/
lemma card_subtype_prod {A B : Type} [Fintype A] [Fintype B] (p : A × B → Prop) :
    Nat.card {x : A × B // p x} = ∑ a : A, Nat.card {b : B // p (a, b)} := by
  classical
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr
    (⟨fun x => ⟨x.1.1, ⟨x.1.2, by cases x with | mk v hv => exact hv⟩⟩,
      fun s => ⟨(s.1, s.2.1), s.2.2⟩,
      fun x => by cases x with | mk v hv => rfl,
      fun s => rfl⟩ :
      {x : A × B // p x} ≃ (a : A) × {b : B // p (a, b)})]
  rw [Fintype.card_sigma]
  simp [Nat.card_eq_fintype_card]

/-- Partition a counted subtype by the value of a map. -/
lemma card_subtype_fiber_decomp {W V : Type} [Fintype W] [Fintype V]
    (f : W → V) (p : W → Prop) :
    Nat.card {w : W // p w} = ∑ v : V, Nat.card {w : W // f w = v ∧ p w} := by
  classical
  have e : {w : W // p w} ≃ (v : V) × {w : W // f w = v ∧ p w} :=
    { toFun := fun x => ⟨f x.1, ⟨x.1, rfl, x.2⟩⟩
      invFun := fun s => ⟨s.2.1, s.2.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun s => by
        obtain ⟨v, w, hf, hp⟩ := s
        subst hf
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]

/-- Constraining a tuple of coins on a `Finset` of coordinates leaves exactly
the unconstrained coordinates free. -/
lemma card_pi_eq_on {K : Type} [Fintype K] [DecidableEq K]
    (S : Finset K) (u : K → C) :
    Nat.card {d : K → C // ∀ i ∈ S, d i = u i} =
      Fintype.card C ^ (Fintype.card K - S.card) := by
  classical
  have e : {d : K → C // ∀ i ∈ S, d i = u i} ≃ ({i : K // i ∉ S} → C) :=
    { toFun := fun d j => d.1 j.1
      invFun := fun g =>
        ⟨fun i => if h : i ∈ S then u i else g ⟨i, h⟩, fun i hi => dif_pos hi⟩
      left_inv := fun d => by
        apply Subtype.ext
        funext i
        by_cases h : i ∈ S
        · simp [h, d.2 i h]
        · simp [h]
      right_inv := fun g => by
        funext j
        simp [j.2] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl]
  congr 1
  exact Fintype.card_coe S

/-- Indicator-sum form of a subtype count. -/
lemma sum_ite_card (p : C → Prop) [DecidablePred p] :
    ∑ ρ : C, (if p ρ then (1 : ℝ) else 0) = (Nat.card {ρ : C // p ρ} : ℝ) := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Pushforward slicing.** If for every value `ρ` of the tested coin the map
`f ρ : W → V` has exactly-uniform fibres, and every instance `G v` of the
tested event is small over the coin, then the joint event `G (f ρ w) ρ` is
small — even though `f ρ w` may depend on `ρ` in an arbitrary (adversarial)
way. The double-counting that replaces the paper's "condition on `rnd`
everywhere except the queried point". -/
lemma uniformProb_pushforward_le {W V : Type} [Fintype W] [Fintype V]
    {ε : ℝ} (hε : 0 ≤ ε) (f : C → W → V) (G : V → C → Prop)
    (hunif : ∀ (ρ : C) (v : V),
      (Nat.card {w : W // f ρ w = v} : ℝ) * (Fintype.card V : ℝ) =
        (Fintype.card W : ℝ))
    (hG : ∀ v : V, uniformProb C (G v) ≤ ε) :
    uniformProb (C × W) (fun x => G (f x.1 x.2) x.1) ≤ ε := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card C) with hC0 | hCpos
  · unfold uniformProb
    have : Fintype.card (C × W) = 0 := by simp [Fintype.card_prod, hC0]
    simp [this, hε]
  rcases Nat.eq_zero_or_pos (Fintype.card W) with hW0 | hWpos
  · unfold uniformProb
    have : Fintype.card (C × W) = 0 := by simp [Fintype.card_prod, hW0]
    simp [this, hε]
  obtain ⟨ρ₀⟩ : Nonempty C := Fintype.card_pos_iff.mp hCpos
  obtain ⟨w₀⟩ : Nonempty W := Fintype.card_pos_iff.mp hWpos
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨f ρ₀ w₀⟩
  have hC' : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hCpos
  have hW' : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast hWpos
  have hV' : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hVpos
  -- fibre size, in ℝ
  have hfib : ∀ (ρ : C) (v : V), (Nat.card {w : W // f ρ w = v} : ℝ) =
      (Fintype.card W : ℝ) / (Fintype.card V : ℝ) := by
    intro ρ v
    rw [eq_div_iff (ne_of_gt hV')]
    exact hunif ρ v
  -- instance counts, in ℝ
  have hGcard : ∀ v : V, (Nat.card {ρ : C // G v ρ} : ℝ) ≤ ε * Fintype.card C := by
    intro v
    have := hG v
    unfold uniformProb at this
    rw [div_le_iff₀ hC'] at this
    exact this
  -- the count
  have hcount : (Nat.card {x : C × W // G (f x.1 x.2) x.1} : ℝ) ≤
      ε * ((Fintype.card C : ℝ) * (Fintype.card W : ℝ)) := by
    have h1 : Nat.card {x : C × W // G (f x.1 x.2) x.1} =
        ∑ ρ : C, Nat.card {w : W // G (f ρ w) ρ} :=
      card_subtype_prod _
    have h2 : ∀ ρ : C, Nat.card {w : W // G (f ρ w) ρ} =
        ∑ v : V, Nat.card {w : W // f ρ w = v ∧ G (f ρ w) ρ} := fun ρ =>
      card_subtype_fiber_decomp (f ρ) _
    have h3 : ∀ (ρ : C) (v : V), (Nat.card {w : W // f ρ w = v ∧ G (f ρ w) ρ} : ℝ) =
        if G v ρ then (Fintype.card W : ℝ) / (Fintype.card V : ℝ) else 0 := by
      intro ρ v
      by_cases hg : G v ρ
      · rw [if_pos hg, ← hfib ρ v]
        congr 1
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro w
        constructor
        · rintro ⟨he, -⟩; exact he
        · intro he; exact ⟨he, he ▸ hg⟩
      · rw [if_neg hg]
        have : IsEmpty {w : W // f ρ w = v ∧ G (f ρ w) ρ} :=
          ⟨fun w => hg (w.2.1 ▸ w.2.2)⟩
        rw [Nat.card_of_isEmpty]
        simp
    calc (Nat.card {x : C × W // G (f x.1 x.2) x.1} : ℝ)
        = ∑ ρ : C, ∑ v : V, (Nat.card {w : W // f ρ w = v ∧ G (f ρ w) ρ} : ℝ) := by
          rw [h1]
          push_cast
          exact Finset.sum_congr rfl fun ρ _ => by rw [h2 ρ]; push_cast; rfl
      _ = ∑ ρ : C, ∑ v : V,
            ((Fintype.card W : ℝ) / (Fintype.card V : ℝ)) *
              (if G v ρ then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun v _ => ?_
          rw [h3 ρ v]
          by_cases hg : G v ρ <;> simp [hg]
      _ = ∑ v : V, ((Fintype.card W : ℝ) / (Fintype.card V : ℝ)) *
            (Nat.card {ρ : C // G v ρ} : ℝ) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun v _ => by
            rw [← Finset.mul_sum, sum_ite_card]
      _ ≤ ∑ _v : V, ((Fintype.card W : ℝ) / (Fintype.card V : ℝ)) *
            (ε * Fintype.card C) := by
          refine Finset.sum_le_sum fun v _ => ?_
          have := hGcard v
          have hWV : (0 : ℝ) ≤ (Fintype.card W : ℝ) / (Fintype.card V : ℝ) :=
            le_of_lt (div_pos hW' hV')
          exact mul_le_mul_of_nonneg_left this hWV
      _ = ε * ((Fintype.card C : ℝ) * (Fintype.card W : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
            mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt hV')]
          ring
  unfold uniformProb
  rw [div_le_iff₀ (by
    rw [Fintype.card_prod]
    exact_mod_cast Nat.mul_pos hCpos hWpos)]
  calc (Nat.card {x : C × W // G (f x.1 x.2) x.1} : ℝ)
      ≤ ε * ((Fintype.card C : ℝ) * (Fintype.card W : ℝ)) := hcount
    _ = ε * (Fintype.card (C × W) : ℝ) := by rw [Fintype.card_prod]; push_cast; ring

end UniformProbII

/-! ## The general lazy-`rnd` resolver and its uniformity kernel

The infrastructure the [OB-2a] diagnosis identified as missing. The game is
re-expressed as a fold over a coin LIST from an arbitrary starting log
(`stepOnce`/`runFrom`), the resolver `resolveIn` answers EVERY salted
`(stmt, prefix)` pair from a log with a fallback coin (with `srFinalChal` as
its designated-final-query instantiation), and `card_resolve_runFrom` is the
resolver's uniformity: over the future coins, the joint resolution of any set
of pairwise-distinct not-yet-queried points is EXACTLY uniform — the response
coin of a fresh query is committed positionally, so its value is uniform no
matter when (or whether) the adversary chooses to make the query. This is the
lazy-sampling rendering of the paper's eager total `rnd`. -/

section LazyRnd

open Classical

variable {r : Reduction} {s : ℕ}

/-- One step of the lazily-sampled SR game from an arbitrary log, consuming
one coin positionally: the strategy's next move is answered from the log if it
repeats an earlier move, else with the given coin. `stepFn P c L j` is
`stepOnce P L (c j)`. -/
noncomputable def stepOnce (P : SrProver r s) (L : List (SrMove r s × r.Chal))
    (ρ : r.Chal) : List (SrMove r s × r.Chal) :=
  let q := P.move (L.map Prod.snd)
  let ρ' := match L.find? (fun e => decide (e.1 = q)) with
    | some e => e.2
    | none => ρ
  L ++ [(q, ρ')]

/-- The lazily-sampled game run from an arbitrary starting log on a list of
coins, consumed positionally in order. -/
noncomputable def runFrom (P : SrProver r s) (L : List (SrMove r s × r.Chal))
    (cs : List r.Chal) : List (SrMove r s × r.Chal) :=
  cs.foldl (stepOnce P) L

/-- `srTrace` is `runFrom` at the empty log on the tuple of game coins. -/
lemma srTrace_eq_runFrom {t : ℕ} (P : SrProver r s) (c : Fin t → r.Chal) :
    srTrace P c = runFrom P [] (List.ofFn c) := by
  rw [runFrom, List.ofFn_eq_map, List.foldl_map]
  rfl

@[simp] lemma runFrom_nil (P : SrProver r s) (L : List (SrMove r s × r.Chal)) :
    runFrom P L [] = L := rfl

lemma runFrom_cons (P : SrProver r s) (L : List (SrMove r s × r.Chal))
    (ρ : r.Chal) (cs : List r.Chal) :
    runFrom P L (ρ :: cs) = runFrom P (stepOnce P L ρ) cs := rfl

lemma runFrom_append (P : SrProver r s) (L : List (SrMove r s × r.Chal))
    (cs cs' : List r.Chal) :
    runFrom P L (cs ++ cs') = runFrom P (runFrom P L cs) cs' :=
  List.foldl_append

lemma stepOnce_eq (P : SrProver r s) (L : List (SrMove r s × r.Chal))
    (ρ : r.Chal) :
    stepOnce P L ρ = L ++ [(P.move (L.map Prod.snd),
      match L.find? (fun e => decide (e.1 = P.move (L.map Prod.snd))) with
      | some e => e.2
      | none => ρ)] := rfl

/-- The game only appends to its log. -/
lemma runFrom_eq_append (P : SrProver r s) (cs : List r.Chal) :
    ∀ L, ∃ M, runFrom P L cs = L ++ M := by
  induction cs with
  | nil => intro L; exact ⟨[], by simp⟩
  | cons ρ cs ih =>
    intro L
    obtain ⟨M, hM⟩ := ih (stepOnce P L ρ)
    exact ⟨_, by rw [runFrom_cons, hM, stepOnce_eq, List.append_assoc]⟩

/-- **The general lazy-`rnd` resolver**: the response recorded for a query in
a log (first occurrence), else the fallback coin. -/
noncomputable def resolveIn (L : List (SrMove r s × r.Chal)) (q : SrMove r s)
    (fb : r.Chal) : r.Chal :=
  match L.find? (fun e => decide (e.1 = q)) with
  | some e => e.2
  | none => fb

/-- `srFinalChal` is the resolver at the `i`-th designated final query. -/
lemma srFinalChal_eq_resolveIn {t : ℕ} (P : SrProver r s) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) (i : Fin r.k) :
    srFinalChal P c d i =
      resolveIn (srTrace P c) ((srOut P c).query i) (d i) := rfl

lemma find?_eq_none_of_forall_ne {L : List (SrMove r s × r.Chal)}
    {q : SrMove r s} (h : ∀ e ∈ L, e.1 ≠ q) :
    L.find? (fun e => decide (e.1 = q)) = none :=
  List.find?_eq_none.mpr (fun e he => by simpa using h e he)

lemma resolveIn_of_forall_ne {L : List (SrMove r s × r.Chal)} {q : SrMove r s}
    (h : ∀ e ∈ L, e.1 ≠ q) (fb : r.Chal) : resolveIn L q fb = fb := by
  unfold resolveIn
  rw [find?_eq_none_of_forall_ne h]

/-- A query absent from a leading log segment resolves in the tail. -/
lemma resolveIn_append_of_ne {L M : List (SrMove r s × r.Chal)}
    {q : SrMove r s} (h : ∀ e ∈ L, e.1 ≠ q) (fb : r.Chal) :
    resolveIn (L ++ M) q fb = resolveIn M q fb := by
  unfold resolveIn
  rw [List.find?_append, find?_eq_none_of_forall_ne h, Option.none_or]

/-- A query found in a leading log segment resolves there — later entries
cannot change a first occurrence. -/
lemma resolveIn_append_left {L M : List (SrMove r s × r.Chal)}
    {q : SrMove r s} {e : SrMove r s × r.Chal}
    (h : L.find? (fun e => decide (e.1 = q)) = some e) (fb : r.Chal) :
    resolveIn (L ++ M) q fb = e.2 := by
  unfold resolveIn
  rw [List.find?_append, h, Option.some_or]

lemma resolveIn_cons_self {M : List (SrMove r s × r.Chal)} (q : SrMove r s)
    (ρ : r.Chal) (fb : r.Chal) : resolveIn ((q, ρ) :: M) q fb = ρ := by
  unfold resolveIn
  rw [List.find?_cons_of_pos (by simp)]

lemma resolveIn_found {L : List (SrMove r s × r.Chal)} {q : SrMove r s}
    {e : SrMove r s × r.Chal}
    (h : L.find? (fun e => decide (e.1 = q)) = some e) (fb : r.Chal) :
    resolveIn L q fb = e.2 := by
  unfold resolveIn
  rw [h]

/-- Once a query is on the log, later game steps cannot change its
resolution. -/
lemma resolveIn_runFrom_found (P : SrProver r s)
    {L : List (SrMove r s × r.Chal)} {q : SrMove r s}
    {e : SrMove r s × r.Chal}
    (h : L.find? (fun e => decide (e.1 = q)) = some e) (cs : List r.Chal)
    (fb : r.Chal) : resolveIn (runFrom P L cs) q fb = e.2 := by
  obtain ⟨M, hM⟩ := runFrom_eq_append P cs L
  rw [hM]
  exact resolveIn_append_left h fb

/-- Head-splitting equivalence for a tuple of coins, definitionally reducing
in both directions. -/
def consSplit (m : ℕ) (C D : Type) :
    ((Fin (m + 1) → C) × D) ≃ (C × ((Fin m → C) × D)) where
  toFun x := (x.1 0, (Fin.tail x.1, x.2))
  invFun y := (Fin.cons y.1 y.2.1, y.2.2)
  left_inv x := by
    refine Prod.ext ?_ rfl
    exact Fin.cons_self_tail x.1
  right_inv y := by
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · show Fin.cons (α := fun _ => C) y.1 y.2.1 0 = y.1
      exact Fin.cons_zero _ _
    · show Fin.tail (α := fun _ => C) (Fin.cons y.1 y.2.1) = y.2.1
      exact Fin.tail_cons _ _

/-- Peel the first coin off a `Fin (m+1)`-indexed coin tuple in a product
count. -/
lemma card_subtype_pi_succ {C D : Type} [Fintype C] [Fintype D] {m : ℕ}
    (p : (Fin (m + 1) → C) × D → Prop) :
    Nat.card {x : (Fin (m + 1) → C) × D // p x} =
      ∑ ρ : C, Nat.card {w : (Fin m → C) × D // p (Fin.cons ρ w.1, w.2)} := by
  classical
  have h : ∀ x : (Fin (m + 1) → C) × D,
      p x ↔ (fun y : C × ((Fin m → C) × D) =>
        p (Fin.cons y.1 y.2.1, y.2.2)) (consSplit m C D x) := by
    intro x
    show p x ↔ p (Fin.cons (x.1 0) (Fin.tail x.1), x.2)
    rw [Fin.cons_self_tail]
  rw [Nat.card_congr ((consSplit m C D).subtypeEquiv
    (q := fun y : C × ((Fin m → C) × D) => p (Fin.cons y.1 y.2.1, y.2.2)) h),
    card_subtype_prod]

/-- **The lazy-`rnd` uniformity kernel.** Fix a strategy, a family of pairwise
distinct query points `Q i` none of which is on the starting log, and target
values `u i` on a slot set `S`. Over the future coins (positional game coins
and per-slot fallback coins), the event "every `Q i`, `i ∈ S`, resolves to
`u i`" has EXACTLY the uniform count: each constrained slot cuts the space by
one factor of `|Chal|`. The deferred-decision fact the paper reads off its
eager total `rnd`: a fresh query's response is uniform no matter when — or
whether — the adversary chooses to make the query, because the response coin
is committed positionally, not per-point. -/
lemma card_resolve_runFrom (P : SrProver r s) (Q : Fin r.k → SrMove r s)
    (u : Fin r.k → r.Chal) :
    ∀ (m : ℕ) (L : List (SrMove r s × r.Chal)) (S : Finset (Fin r.k)),
      (∀ i ∈ S, ∀ e ∈ L, e.1 ≠ Q i) →
      (∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → Q i ≠ Q i') →
      Nat.card {x : (Fin m → r.Chal) × (Fin r.k → r.Chal) //
          ∀ i ∈ S, resolveIn (runFrom P L (List.ofFn x.1)) (Q i) (x.2 i) = u i} =
        Fintype.card r.Chal ^ (m + (r.k - S.card)) := by
  intro m
  induction m with
  | zero =>
    intro L S hfresh _hdist
    have hcongr : ∀ x : (Fin 0 → r.Chal) × (Fin r.k → r.Chal),
        (∀ i ∈ S, resolveIn (runFrom P L (List.ofFn x.1)) (Q i) (x.2 i) = u i) ↔
        (∀ i ∈ S, x.2 i = u i) := by
      intro x
      rw [List.ofFn_zero, runFrom_nil]
      constructor
      · intro h i hi
        have := h i hi
        rwa [resolveIn_of_forall_ne (hfresh i hi)] at this
      · intro h i hi
        rw [resolveIn_of_forall_ne (hfresh i hi)]
        exact h i hi
    rw [Nat.card_congr (Equiv.subtypeEquivRight hcongr), card_subtype_prod]
    refine Eq.trans (Finset.sum_congr rfl fun a _ =>
      (rfl : Nat.card {b : Fin r.k → r.Chal // ∀ i ∈ S, b i = u i} =
        Nat.card {b : Fin r.k → r.Chal // ∀ i ∈ S, b i = u i})) ?_
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have hA : Fintype.card (Fin 0 → r.Chal) = 1 := by
      rw [Fintype.card_fun]
      simp
    rw [hA, one_mul, card_pi_eq_on S u]
    congr 1
    rw [Fintype.card_fin]
    omega
  | succ m ih =>
    intro L S hfresh hdist
    have hofn : ∀ (ρ : r.Chal) (cs : Fin m → r.Chal),
        List.ofFn (Fin.cons ρ cs : Fin (m + 1) → r.Chal) =
          ρ :: List.ofFn cs := by
      intro ρ cs
      rw [List.ofFn_succ]
      simp
    rw [card_subtype_pi_succ]
    -- peel the consumed head coin into a `stepOnce`
    have hpeel : ∀ ρ : r.Chal,
        Nat.card {w : (Fin m → r.Chal) × (Fin r.k → r.Chal) //
            ∀ i ∈ S, resolveIn (runFrom P L (List.ofFn (Fin.cons ρ w.1)))
              (Q i) (w.2 i) = u i} =
        Nat.card {w : (Fin m → r.Chal) × (Fin r.k → r.Chal) //
            ∀ i ∈ S, resolveIn (runFrom P (stepOnce P L ρ) (List.ofFn w.1))
              (Q i) (w.2 i) = u i} := by
      intro ρ
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro w
      rw [hofn ρ w.1, runFrom_cons]
    refine Eq.trans (Finset.sum_congr rfl fun ρ _ => hpeel ρ) ?_
    by_cases hhit : ∃ i₀ ∈ S, Q i₀ = P.move (L.map Prod.snd)
    · -- the step queries a constrained fresh point: its response coin is pinned
      obtain ⟨i₀, hi₀S, hQi₀⟩ := hhit
      have hmiss : L.find?
          (fun e => decide (e.1 = P.move (L.map Prod.snd))) = none :=
        find?_eq_none_of_forall_ne (fun e he => hQi₀ ▸ hfresh i₀ hi₀S e he)
      have hstep' : ∀ ρ : r.Chal,
          stepOnce P L ρ = L ++ [(P.move (L.map Prod.snd), ρ)] := by
        intro ρ
        rw [stepOnce_eq, hmiss]
      have hres : ∀ (ρ : r.Chal) (cs : Fin m → r.Chal) (fb : r.Chal),
          resolveIn (runFrom P (stepOnce P L ρ) (List.ofFn cs)) (Q i₀) fb =
            ρ := by
        intro ρ cs fb
        obtain ⟨M, hM⟩ :=
          runFrom_eq_append P (List.ofFn cs) (stepOnce P L ρ)
        rw [hM, hstep', List.append_assoc, List.singleton_append,
          resolveIn_append_of_ne (hfresh i₀ hi₀S) fb, ← hQi₀,
          resolveIn_cons_self (Q i₀) ρ fb]
      have hkS : S.card ≤ r.k := by
        have := Finset.card_le_univ S
        rwa [Fintype.card_fin] at this
      have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨i₀, hi₀S⟩
      have hfib : ∀ ρ : r.Chal,
          Nat.card {w : (Fin m → r.Chal) × (Fin r.k → r.Chal) //
              ∀ i ∈ S, resolveIn (runFrom P (stepOnce P L ρ) (List.ofFn w.1))
                (Q i) (w.2 i) = u i} =
            if ρ = u i₀ then
              Fintype.card r.Chal ^ (m + (r.k - S.card) + 1) else 0 := by
        intro ρ
        by_cases hρ : ρ = u i₀
        · rw [if_pos hρ]
          have hiff : ∀ w : (Fin m → r.Chal) × (Fin r.k → r.Chal),
              (∀ i ∈ S, resolveIn (runFrom P (stepOnce P L ρ) (List.ofFn w.1))
                (Q i) (w.2 i) = u i) ↔
              (∀ i ∈ S.erase i₀,
                resolveIn (runFrom P (stepOnce P L ρ) (List.ofFn w.1))
                  (Q i) (w.2 i) = u i) := by
            intro w
            constructor
            · intro h i hi
              exact h i (Finset.mem_of_mem_erase hi)
            · intro h i hi
              by_cases hii : i = i₀
              · subst hii
                rw [hres ρ w.1 (w.2 i)]
                exact hρ
              · exact h i (Finset.mem_erase.mpr ⟨hii, hi⟩)
          rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
          have hfresh' : ∀ i ∈ S.erase i₀, ∀ e ∈ stepOnce P L ρ,
              e.1 ≠ Q i := by
            intro i hi e he
            rw [hstep'] at he
            rcases List.mem_append.mp he with he | he
            · exact hfresh i (Finset.mem_of_mem_erase hi) e he
            · rw [List.mem_singleton] at he
              subst he
              have hne : i₀ ≠ i := fun hc =>
                (Finset.mem_erase.mp hi).1 hc.symm
              exact fun hc =>
                hdist i₀ hi₀S i (Finset.mem_of_mem_erase hi) hne
                  (hQi₀.trans hc)
          have hdist' : ∀ i ∈ S.erase i₀, ∀ i' ∈ S.erase i₀, i ≠ i' →
              Q i ≠ Q i' := fun i hi i' hi' hne =>
            hdist i (Finset.mem_of_mem_erase hi) i'
              (Finset.mem_of_mem_erase hi') hne
          rw [ih (stepOnce P L ρ) (S.erase i₀) hfresh' hdist',
            Finset.card_erase_of_mem hi₀S]
          congr 1
          omega
        · rw [if_neg hρ]
          have : IsEmpty {w : (Fin m → r.Chal) × (Fin r.k → r.Chal) //
              ∀ i ∈ S, resolveIn (runFrom P (stepOnce P L ρ) (List.ofFn w.1))
                (Q i) (w.2 i) = u i} := by
            refine ⟨fun w => hρ ?_⟩
            have := w.2 i₀ hi₀S
            rwa [hres ρ w.1.1 (w.1.2 i₀)] at this
          rw [Nat.card_of_isEmpty]
      refine Eq.trans (Finset.sum_congr rfl fun ρ _ => hfib ρ) ?_
      rw [Finset.sum_ite_eq' Finset.univ (u i₀)
        (fun _ => Fintype.card r.Chal ^ (m + (r.k - S.card) + 1)),
        if_pos (Finset.mem_univ _)]
      congr 1
      omega
    · -- the step queries no constrained point: every future stays uniform
      push Not at hhit
      have hfresh' : ∀ (ρ : r.Chal), ∀ i ∈ S, ∀ e ∈ stepOnce P L ρ,
          e.1 ≠ Q i := by
        intro ρ i hi e he
        rw [stepOnce_eq] at he
        rcases List.mem_append.mp he with he | he
        · exact hfresh i hi e he
        · rw [List.mem_singleton] at he
          subst he
          exact Ne.symm (hhit i hi)
      refine Eq.trans (Finset.sum_congr rfl fun ρ _ =>
        ih (stepOnce P L ρ) S (hfresh' ρ) hdist) ?_
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← pow_succ']
      congr 1
      omega

lemma runFrom_length (P : SrProver r s) (cs : List r.Chal) :
    ∀ L, (runFrom P L cs).length = L.length + cs.length := by
  induction cs with
  | nil => intro L; simp
  | cons ρ cs ih =>
    intro L
    rw [runFrom_cons, ih, stepOnce_eq]
    simp
    omega

lemma find?_isSome_of_exists {L : List (SrMove r s × r.Chal)} {q : SrMove r s}
    (h : ∃ e ∈ L, e.1 = q) :
    ∃ e', L.find? (fun e => decide (e.1 = q)) = some e' := by
  obtain ⟨e, he, heq⟩ := h
  cases hf : L.find? (fun e => decide (e.1 = q)) with
  | some e' => exact ⟨e', rfl⟩
  | none =>
    have := List.find?_eq_none.mp hf e he
    simp only [decide_eq_true_eq] at this
    exact absurd heq this

end LazyRnd

/-! ## Splitting the game coins at a position

`splitGame j` carves the game-coin tuple into the past `c_{<j}`, the tested
coin `c_j`, and the future `c_{>j}`; `ofFn_splitGame_symm` is the list-level
decomposition that hands the past to `runFrom` as a completed log and the
future to the uniformity kernel as its coin list. -/

/-- Split the game-coin tuple at position `j`. Hand-rolled so both directions
reduce definitionally at every coordinate. -/
def splitGame {C : Type} {t : ℕ} (j : Fin t) :
    (Fin t → C) ≃ ((Fin (j : ℕ) → C) × C × (Fin (t - (j : ℕ) - 1) → C)) where
  toFun c := (fun i => c ⟨(i : ℕ), lt_trans i.2 j.2⟩, c j,
    fun i => c ⟨(j : ℕ) + 1 + (i : ℕ), by omega⟩)
  invFun y i :=
    if h : (i : ℕ) < (j : ℕ) then y.1 ⟨(i : ℕ), h⟩
    else if h' : (i : ℕ) = (j : ℕ) then y.2.1
    else y.2.2 ⟨(i : ℕ) - (j : ℕ) - 1, by omega⟩
  left_inv c := by
    funext i
    by_cases h : (i : ℕ) < (j : ℕ)
    · simp only [dif_pos h]
    · by_cases h' : (i : ℕ) = (j : ℕ)
      · simp only [dif_neg h, dif_pos h']
        exact congrArg c (Fin.ext h'.symm)
      · simp only [dif_neg h, dif_neg h']
        exact congrArg c
          (Fin.ext (show (j : ℕ) + 1 + ((i : ℕ) - (j : ℕ) - 1) = (i : ℕ) by
            omega))
  right_inv y := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      show dite _ _ _ = _
      rw [dif_pos i.2]
    · show dite _ _ _ = _
      rw [dif_neg (lt_irrefl _), dif_pos rfl]
    · funext i
      show dite _ _ _ = _
      rw [dif_neg (show ¬((j : ℕ) + 1 + (i : ℕ) < (j : ℕ)) by omega),
        dif_neg (show ¬((j : ℕ) + 1 + (i : ℕ) = (j : ℕ)) by omega)]
      exact congrArg y.2.2
        (Fin.ext (show (j : ℕ) + 1 + (i : ℕ) - (j : ℕ) - 1 = (i : ℕ) by
          omega))

lemma splitGame_symm_apply_lt {C : Type} {t : ℕ} (j : Fin t)
    (y : (Fin (j : ℕ) → C) × C × (Fin (t - (j : ℕ) - 1) → C)) (i : Fin t)
    (h : (i : ℕ) < (j : ℕ)) :
    (splitGame j).symm y i = y.1 ⟨(i : ℕ), h⟩ := dif_pos h

lemma splitGame_symm_apply_self {C : Type} {t : ℕ} (j : Fin t)
    (y : (Fin (j : ℕ) → C) × C × (Fin (t - (j : ℕ) - 1) → C)) :
    (splitGame j).symm y j = y.2.1 :=
  (dif_neg (lt_irrefl _)).trans (dif_pos rfl)

lemma splitGame_symm_apply_gt {C : Type} {t : ℕ} (j : Fin t)
    (y : (Fin (j : ℕ) → C) × C × (Fin (t - (j : ℕ) - 1) → C)) (i : Fin t)
    (h : (j : ℕ) < (i : ℕ)) :
    (splitGame j).symm y i =
      y.2.2 ⟨(i : ℕ) - (j : ℕ) - 1, by omega⟩ :=
  (dif_neg (by omega)).trans (dif_neg (by omega))

/-- The coin tuple, as a list: past coins, then the tested coin, then the
future coins. -/
lemma ofFn_splitGame_symm {C : Type} {t : ℕ} (j : Fin t)
    (y : (Fin (j : ℕ) → C) × C × (Fin (t - (j : ℕ) - 1) → C)) :
    List.ofFn ((splitGame j).symm y) =
      List.ofFn y.1 ++ y.2.1 :: List.ofFn y.2.2 := by
  have hj := j.2
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons]
    omega
  · intro n h1 h2
    rw [List.getElem_ofFn]
    rcases Nat.lt_trichotomy n (j : ℕ) with hn | hn | hn
    · rw [List.getElem_append_left (by simpa using hn), List.getElem_ofFn]
      exact splitGame_symm_apply_lt j y ⟨n, by simpa using h1⟩ hn
    · rw [List.getElem_append_right (by simpa using le_of_eq hn.symm)]
      have hidx : n - (List.ofFn y.1).length = 0 := by
        simp only [List.length_ofFn]
        omega
      simp only [hidx, List.getElem_cons_zero]
      have hfin : (⟨n, by simpa using h1⟩ : Fin t) = j := Fin.ext hn
      rw [hfin]
      exact splitGame_symm_apply_self j y
    · rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega)]
      have hidx : n - (List.ofFn y.1).length = (n - (j : ℕ) - 1) + 1 := by
        simp only [List.length_ofFn]
        omega
      simp only [hidx, List.getElem_cons_succ, List.getElem_ofFn]
      exact splitGame_symm_apply_gt j y ⟨n, by simpa using h1⟩ hn

/-- `splitGame` extended over the product with the final-prefix coins, which
ride along untouched. -/
def splitAtGame {C D : Type} {t : ℕ} (j : Fin t) :
    ((Fin t → C) × D) ≃
      ((Fin (j : ℕ) → C) × C × (Fin (t - (j : ℕ) - 1) → C) × D) where
  toFun x := ((splitGame j x.1).1, (splitGame j x.1).2.1,
    (splitGame j x.1).2.2, x.2)
  invFun y := ((splitGame j).symm (y.1, y.2.1, y.2.2.1), y.2.2.2)
  left_inv x := by
    refine Prod.ext ?_ rfl
    exact (splitGame j).symm_apply_apply x.1
  right_inv y := by
    show (((splitGame j) ((splitGame j).symm (y.1, y.2.1, y.2.2.1))).1,
      ((splitGame j) ((splitGame j).symm (y.1, y.2.1, y.2.2.1))).2.1,
      ((splitGame j) ((splitGame j).symm (y.1, y.2.1, y.2.2.1))).2.2,
      y.2.2.2) = y
    rw [(splitGame j).apply_symm_apply (y.1, y.2.1, y.2.2.1)]

/-! ## Structure of the designated final queries -/

section QueryStructure

variable {r : Reduction} {s : ℕ}

lemma SrOutput.query_stmt (o : SrOutput r s) (i : Fin r.k) :
    (o.query i).stmt = o.stmt := rfl

lemma SrOutput.query_pfx_length (o : SrOutput r s) (i : Fin r.k) :
    (o.query i).pfx.length = (i : ℕ) + 1 := by
  show (((List.finRange r.k).take ((i : ℕ) + 1)).map _).length = _
  rw [List.length_map, List.length_take, List.length_finRange]
  omega

/-- A shorter designated query is the truncation of a longer one: same
statement, prefix of the prefix. -/
lemma SrOutput.query_le (o : SrOutput r s) {i a : Fin r.k}
    (h : (i : ℕ) ≤ (a : ℕ)) :
    o.query i = ⟨(o.query a).stmt, (o.query a).pfx.take ((i : ℕ) + 1)⟩ := by
  show (⟨o.stmt, _⟩ : SrMove r s) = ⟨o.stmt, _⟩
  congr 1
  show ((List.finRange r.k).take ((i : ℕ) + 1)).map
      (fun l => (o.πs l, o.σs l)) =
    (((List.finRange r.k).take ((a : ℕ) + 1)).map
      (fun l => (o.πs l, o.σs l))).take ((i : ℕ) + 1)
  rw [← List.map_take, List.take_take, Nat.min_eq_left (by omega)]

/-- The entries of a designated query's prefix are the output's messages and
salts. -/
lemma SrOutput.query_pfx_getElem (o : SrOutput r s) (a : Fin r.k) {n : ℕ}
    (hn : n < (a : ℕ) + 1) (hk : n < r.k) :
    (o.query a).pfx[n]'(by rw [SrOutput.query_pfx_length]; omega) =
      (o.πs ⟨n, hk⟩, o.σs ⟨n, hk⟩) := by
  show (((List.finRange r.k).take ((a : ℕ) + 1)).map
    (fun l => (o.πs l, o.σs l)))[n]'_ = _
  rw [List.getElem_map, List.getElem_take, List.getElem_finRange]
  rfl

end QueryStructure

/-! ## The game-slot bound

The per-fibre argument closing [OB-2a]. Fix the coin past `p = c_{<j}`: the
move `mv` made at step `j` is a function of `p` alone. On the `HitBad j` event
the output's hit query IS `mv` (content equality via `hitAt`), so the hit slot
`a`, the statement, the pending message, and the sub-prefix queries
`Q i = (mv.stmt, mv.pfx.take (i+1))` are ALL fixed by `p`; the tested response
is the fresh coin `c_j`; and the earlier-round challenges are resolutions of
the pairwise-distinct (by length) sub-prefix queries — either already on the
past log (constants) or jointly exactly-uniform over the future coins by the
lazy-`rnd` kernel. Pushforward slicing then yields Def 4.2's round bound. -/

section GameSlot

open Classical

variable {r : Reduction} {s : ℕ}

/-- **The per-fibre game-slot bound.** `Lp` is the fixed past log (the caller
instantiates it as the game run on the past coins); on each fibre over the
past, `Pr[HitBad j] ≤ εrbr δ`. -/
lemma hitBad_fibre_le (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r))
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) {εrbr : ℝ → ℝ}
    (hnn : 0 ≤ εrbr δ)
    (hdom : ∀ (i : Fin r.k) (st : Stmt r), st ∈ Z → rbr.err i st δ ≤ εrbr δ)
    {t : ℕ} (P : SrProver r s) (j : Fin t) (p : Fin (j : ℕ) → r.Chal)
    (Lp : List (SrMove r s × r.Chal)) (hLplen : Lp.length = (j : ℕ))
    (hTr : ∀ (ρ : r.Chal) (cs : Fin (t - (j : ℕ) - 1) → r.Chal),
      srTrace P ((splitGame j).symm (p, ρ, cs)) =
        runFrom P (stepOnce P Lp ρ) (List.ofFn cs)) :
    uniformProb
      (r.Chal × (Fin (t - (j : ℕ) - 1) → r.Chal) × (Fin r.k → r.Chal))
      (fun b => HitBad rbr Z δ P j ((splitAtGame j).symm (p, b))) ≤
      εrbr δ := by
  classical
  obtain ⟨ρ₀⟩ := r.chalNonempty
  set mv := P.move (Lp.map Prod.snd) with hmv
  -- the trace on the fibre, split at the step-`j` entry
  have hTsplit : ∀ (ρ : r.Chal) (cs : Fin (t - (j : ℕ) - 1) → r.Chal),
      ∃ M, srTrace P ((splitGame j).symm (p, ρ, cs)) =
        Lp ++ ((mv, match Lp.find? (fun e => decide (e.1 = mv)) with
          | some e => e.2
          | none => ρ) :: M) := by
    intro ρ cs
    obtain ⟨M, hM⟩ := runFrom_eq_append P (List.ofFn cs) (stepOnce P Lp ρ)
    refine ⟨M, ?_⟩
    rw [hTr ρ cs, hM, stepOnce_eq, ← hmv, List.append_assoc,
      List.singleton_append]
  -- on the event, the hit query is `mv` and no past entry made it
  have hquery : ∀ (ρ : r.Chal) (cs : Fin (t - (j : ℕ) - 1) → r.Chal)
      (a' : Fin r.k),
      hitAt P a' j ((splitGame j).symm (p, ρ, cs)) →
      (srOut P ((splitGame j).symm (p, ρ, cs))).query a' = mv ∧
      (∀ e ∈ Lp, e.1 ≠ mv) := by
    intro ρ cs a' hhit
    have hhit' : (srTrace P ((splitGame j).symm (p, ρ, cs))).findIdx?
        (fun e => decide (e.1 =
          (srOut P ((splitGame j).symm (p, ρ, cs))).query a')) =
        some (j : ℕ) := hhit
    rw [List.findIdx?_eq_some_iff_getElem] at hhit'
    obtain ⟨hjlt, hpj, hmin⟩ := hhit'
    obtain ⟨M, hM⟩ := hTsplit ρ cs
    have hget1 : (srTrace P ((splitGame j).symm (p, ρ, cs)))[(j : ℕ)]'hjlt =
        (mv, match Lp.find? (fun e => decide (e.1 = mv)) with
          | some e => e.2
          | none => ρ) := by
      simp only [hM]
      rw [List.getElem_append_right (by omega)]
      have hidx : (j : ℕ) - Lp.length = 0 := by omega
      simp only [hidx, List.getElem_cons_zero]
    have hTj1 :=  of_decide_eq_true hpj
    rw [hget1] at hTj1
    have hq : (srOut P ((splitGame j).symm (p, ρ, cs))).query a' = mv :=
      hTj1.symm
    refine ⟨hq, ?_⟩
    intro e he heq
    obtain ⟨n, hn, hgetn⟩ := List.mem_iff_getElem.mp he
    have hmn := hmin n (by omega)
    have hTn : (srTrace P ((splitGame j).symm (p, ρ, cs)))[n]'(by omega) =
        Lp[n]'hn := by
      simp only [hM]
      exact List.getElem_append_left hn
    rw [hTn, hgetn] at hmn
    simp only [decide_eq_true_eq] at hmn
    exact hmn (heq.trans hq.symm)
  -- guards, all functions of the past alone
  by_cases hgd : (∃ a : ℕ, a < r.k ∧ mv.pfx.length = a + 1) ∧
      mv.stmt ∈ Z ∧ (∀ e ∈ Lp, e.1 ≠ mv)
  case neg =>
    refine le_trans (le_of_eq (uniformProb_false ?_)) hnn
    rintro ⟨ρ, cs, d⟩ ⟨a', hhit, hz, hbad⟩
    obtain ⟨hq, hcl⟩ := hquery ρ cs a' hhit
    refine hgd ⟨⟨(a' : ℕ), a'.2, ?_⟩, ?_, hcl⟩
    · rw [← hq]
      exact SrOutput.query_pfx_length _ a'
    · rw [← hq]
      exact hz
  case pos =>
  obtain ⟨⟨a, hak, hlen⟩, hZ, hclean⟩ := hgd
  -- the sub-prefix queries of `mv` and their fresh-slot set
  set Qq : Fin r.k → SrMove r s :=
    fun i => ⟨mv.stmt, mv.pfx.take ((i : ℕ) + 1)⟩ with hQq
  set S : Finset (Fin r.k) := Finset.univ.filter
    (fun i => (i : ℕ) < a ∧ ∀ e ∈ Lp, e.1 ≠ Qq i) with hS
  have hQlen : ∀ i : Fin r.k, (i : ℕ) < a → (Qq i).pfx.length = (i : ℕ) + 1 := by
    intro i hia
    show (mv.pfx.take ((i : ℕ) + 1)).length = (i : ℕ) + 1
    rw [List.length_take, hlen]
    omega
  have hdist : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → Qq i ≠ Qq i' := by
    intro i hi i' hi' hne hc
    have h1 := hQlen i (Finset.mem_filter.mp hi).2.1
    have h2 := hQlen i' (Finset.mem_filter.mp hi').2.1
    rw [hc] at h1
    have := h1.symm.trans h2
    exact hne (Fin.ext (by omega))
  have hQmv : ∀ i : Fin r.k, (i : ℕ) < a → Qq i ≠ mv := by
    intro i hia hc
    have h1 := hQlen i hia
    rw [hc, hlen] at h1
    omega
  have hstep : ∀ ρ : r.Chal, stepOnce P Lp ρ = Lp ++ [(mv, ρ)] := by
    intro ρ
    rw [stepOnce_eq, ← hmv, find?_eq_none_of_forall_ne hclean]
  have hfreshS : ∀ (ρ : r.Chal), ∀ i ∈ S, ∀ e ∈ stepOnce P Lp ρ,
      e.1 ≠ Qq i := by
    intro ρ i hi e he
    rw [hstep ρ] at he
    rcases List.mem_append.mp he with he | he
    · exact (Finset.mem_filter.mp hi).2.2 e he
    · rw [List.mem_singleton] at he
      subst he
      exact fun hc => hQmv i (Finset.mem_filter.mp hi).2.1 hc.symm
  have hkS : S.card ≤ r.k := by
    have := Finset.card_le_univ S
    rwa [Fintype.card_fin] at this
  -- pushforward slicing: the resolved values are the pushforward map, the
  -- round-bad event is the tested predicate
  refine le_trans (uniformProb_mono ?_) (uniformProb_pushforward_le hnn
    (fun ρ w (i : {i : Fin r.k // i ∈ S}) =>
      resolveIn (runFrom P (stepOnce P Lp ρ) (List.ofFn w.1))
        (Qq i.1) (w.2 i.1))
    (fun v ρ => RoundBad rbr δ mv.stmt
      (List.ofFn fun i : Fin a =>
        ((mv.pfx[(i : ℕ)]'(by omega)).1,
          if h : (⟨(i : ℕ), by omega⟩ : Fin r.k) ∈ S
          then v ⟨⟨(i : ℕ), by omega⟩, h⟩
          else resolveIn Lp (Qq ⟨(i : ℕ), by omega⟩) ρ₀))
      ((mv.pfx[a]'(by omega)).1) ρ)
    ?_ ?_)
  · -- containment: the event implies the sliced predicate
    rintro ⟨ρ, cs, d⟩ ⟨a', hhit, hz, hbad⟩
    obtain ⟨hq, -⟩ := hquery ρ cs a' hhit
    have ha' : (a' : ℕ) = a := by
      have := SrOutput.query_pfx_length
        (srOut P ((splitGame j).symm (p, ρ, cs))) a'
      rw [hq, hlen] at this
      omega
    obtain rfl : a' = ⟨a, hak⟩ := Fin.ext ha'
    obtain ⟨M, hM⟩ := hTsplit ρ cs
    simp only [find?_eq_none_of_forall_ne hclean] at hM
    -- re-type the bad event into fibre vocabulary
    have hbad' : RoundBad rbr δ
        (srOut P ((splitGame j).symm (p, ρ, cs))).stmt
        ((srRounds P ((splitGame j).symm (p, ρ, cs)) d).take a)
        ((srOut P ((splitGame j).symm (p, ρ, cs))).πs ⟨a, hak⟩)
        (srFinalChal P ((splitGame j).symm (p, ρ, cs)) d ⟨a, hak⟩) := hbad
    have hstmt : (srOut P ((splitGame j).symm (p, ρ, cs))).stmt = mv.stmt := by
      rw [← hq]
      rfl
    have hfin : srFinalChal P ((splitGame j).symm (p, ρ, cs)) d ⟨a, hak⟩ =
        ρ := by
      rw [srFinalChal_eq_resolveIn, hq, hM,
        resolveIn_append_of_ne hclean, resolveIn_cons_self]
    have hπ : (srOut P ((splitGame j).symm (p, ρ, cs))).πs ⟨a, hak⟩ =
        (mv.pfx[a]'(by omega)).1 := by
      have hg := SrOutput.query_pfx_getElem
        (srOut P ((splitGame j).symm (p, ρ, cs))) ⟨a, hak⟩
        (n := a) (by omega) hak
      simp only [hq] at hg
      rw [hg]
    have hrounds : (srRounds P ((splitGame j).symm (p, ρ, cs)) d).take a =
        List.ofFn (fun i : Fin a =>
          ((mv.pfx[(i : ℕ)]'(by omega)).1,
            if _h : (⟨(i : ℕ), by omega⟩ : Fin r.k) ∈ S
            then resolveIn (runFrom P (stepOnce P Lp ρ) (List.ofFn cs))
              (Qq ⟨(i : ℕ), by omega⟩) (d ⟨(i : ℕ), by omega⟩)
            else resolveIn Lp (Qq ⟨(i : ℕ), by omega⟩) ρ₀)) := by
      apply List.ext_getElem
      · simp only [List.length_take, srRounds, List.length_ofFn]
        omega
      · intro n h1 h2
        have hna : n < a := by
          simp only [List.length_take, srRounds, List.length_ofFn] at h1
          omega
        have hnk : n < r.k := by omega
        rw [List.getElem_take]
        show (srRounds P ((splitGame j).symm (p, ρ, cs)) d)[n]'(by
          simp only [srRounds, List.length_ofFn]; omega) = _
        simp only [srRounds, List.getElem_ofFn]
        -- messages agree
        have hg := SrOutput.query_pfx_getElem
          (srOut P ((splitGame j).symm (p, ρ, cs))) ⟨a, hak⟩
          (n := n) (by omega) hnk
        simp only [hq] at hg
        -- the `n`-th designated query is the fixed sub-prefix query
        have hqn : (srOut P ((splitGame j).symm (p, ρ, cs))).query ⟨n, hnk⟩ =
            Qq ⟨n, hnk⟩ := by
          rw [SrOutput.query_le _ (a := ⟨a, hak⟩) (by show n ≤ a; omega), hq]
        refine Prod.ext ?_ ?_
        · show (srOut P ((splitGame j).symm (p, ρ, cs))).πs ⟨n, hnk⟩ =
            (mv.pfx[n]'(by omega)).1
          rw [hg]
        · show srFinalChal P ((splitGame j).symm (p, ρ, cs)) d ⟨n, hnk⟩ =
            if _h : (⟨n, hnk⟩ : Fin r.k) ∈ S
            then resolveIn (runFrom P (stepOnce P Lp ρ) (List.ofFn cs))
              (Qq ⟨n, hnk⟩) (d ⟨n, hnk⟩)
            else resolveIn Lp (Qq ⟨n, hnk⟩) ρ₀
          rw [srFinalChal_eq_resolveIn, hqn]
          by_cases hmem : (⟨n, hnk⟩ : Fin r.k) ∈ S
          · rw [dif_pos hmem, hTr ρ cs]
          · rw [dif_neg hmem]
            have hex : ∃ e ∈ Lp, e.1 = Qq ⟨n, hnk⟩ := by
              by_contra hne
              refine hmem ?_
              rw [hS]
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
              · show n < a
                omega
              · intro e he heq
                exact hne ⟨e, he, heq⟩
            obtain ⟨e', hfind⟩ := find?_isSome_of_exists hex
            rw [hM, resolveIn_append_left hfind, resolveIn_found hfind]
    rw [hstmt, hfin, hπ, hrounds] at hbad'
    exact hbad'
  · -- exact uniformity of the resolved values, from the kernel
    intro ρ v
    have hiff : ∀ w : (Fin (t - (j : ℕ) - 1) → r.Chal) × (Fin r.k → r.Chal),
        ((fun (i : {i : Fin r.k // i ∈ S}) =>
          resolveIn (runFrom P (stepOnce P Lp ρ) (List.ofFn w.1))
            (Qq i.1) (w.2 i.1)) = v) ↔
        (∀ i ∈ S, resolveIn (runFrom P (stepOnce P Lp ρ) (List.ofFn w.1))
          (Qq i) (w.2 i) = if h : i ∈ S then v ⟨i, h⟩ else ρ₀) := by
      intro w
      constructor
      · intro h i hi
        rw [dif_pos hi]
        exact congrFun h ⟨i, hi⟩
      · intro h
        funext i
        have := h i.1 i.2
        rw [dif_pos i.2] at this
        exact this
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),
      card_resolve_runFrom P Qq
        (fun i : Fin r.k => if h : i ∈ S then v ⟨i, h⟩ else ρ₀)
        (t - (j : ℕ) - 1) (stepOnce P Lp ρ) S (hfreshS ρ) hdist,
      Fintype.card_fun, Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  · -- each instance of the tested event is one RBR round bound
    intro v
    refine le_trans (uniformProb_roundBad_le rbr hδ mv.stmt ⟨a, hak⟩ ?_ _)
      (hdom ⟨a, hak⟩ mv.stmt hZ)
    simp

end GameSlot

/-! ## The repaired obligation, the remaining seam, and the assembly -/

/-- **[OB-2′] Loss-free depth composition, repaired** (WARP 2025/753, Thm B.4):
identical to the audited `OB2_depth_composition` EXCEPT for one added guard,
`0 ≤ εrbr δ` on the quantified range — the guard whose absence makes the
original refutable (`OB2_depth_composition_false`). For nonempty `Z` the guard
is free: `εrbr` dominates some `err i st δ`, which dominates a `uniformProb`,
hence is nonnegative. The paper's `ε_rbr := max_{i, Z} ε_i` always satisfies it
whenever the max exists. -/
def OB2_depth_composition_nonneg : Prop :=
  ∀ (r : Reduction) (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r))
    (εrbr : ℝ → ℝ),
    (∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, 0 ≤ εrbr δ) →
    (∀ (i : Fin r.k) (st : Stmt r), st ∈ Z →
      ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, rbr.err i st δ ≤ εrbr δ) →
    StraightlineSrKnowledgeSoundness r Z
      (fun _s t δ => ((t : ℝ) + (r.k : ℝ)) * εrbr δ)

/-- **[OB-2a] — the game-slot bound. PROVED: `gameSlotBound_proved` below.**

`Pr[HitBad j] ≤ εrbr δ`. This is the harder half of the union bound (the `t`
"game move" slots, vs. the `k` "output prefix" slots closed by `freshBad_le`).
The audit that named this seam diagnosed a genuine INFRASTRUCTURE GAP, and
the closure is exactly the diagnosed missing piece; both are recorded here.

**The gap (as diagnosed).** `slotBad`/`HitBad` test the round-bad event using
`(srOut P c).stmt` and `srRounds`/`srFinalChal` — machinery built to answer
only the `k` DESIGNATED final-output-prefix queries. `srOut P c` — and hence
which `a` matches, and the earlier-round challenges instantiating `RoundBad`
— are functions of ALL of `c` including `c_{>j}`, so the `freshBad_le` recipe
(fix `c_{≠j}`, vary `c_j`) does not hold them fixed: the adversary's
post-move-`j` behavior may depend on `c_j` adversarially. The paper sidesteps
this by invoking its eager total `rnd` at the hit move's OWN sub-prefixes; the
lazy rendering needs a GENERAL resolver over every salted `(stmt, prefix)`
pair, plus a uniformity argument for values resolved at adversarially-chosen
later times.

**The closure.** `resolveIn` (with `stepOnce`/`runFrom`) is that general
resolver, with `srFinalChal` as its designated-query instantiation
(`srFinalChal_eq_resolveIn`). The two facts that close the bound:
* on the event, `hitAt` forces content equality between the output's hit
  query and the move `mv` made at step `j` — a function of `c_{<j}` alone —
  which pins the statement, the hit slot `a` (by prefix length), the pending
  message, and the sub-prefix queries (`hitBad_fibre_le`'s `hquery`); the
  tested response is the fresh coin `c_j` itself;
* the earlier-round challenges are `resolveIn`-resolutions of the pairwise-
  distinct (by prefix length) sub-prefix queries: those on the past log are
  constants of the fibre, and the rest are JOINTLY EXACTLY UNIFORM over the
  future coins no matter when — or whether — the adversary queries them,
  because response coins are committed positionally
  (`card_resolve_runFrom`). Pushforward slicing
  (`uniformProb_pushforward_le`) then reduces `Pr[HitBad j]` to Def 4.2's
  round bound at the pinned statement/prefix/message — the same double
  counting the paper performs by conditioning on `rnd` off the queried point.

(`stepFn`/`srTrace_take`/`srTrace_take_agree`/`splitProd1` above were banked
toward this argument; the landed proof factors the same content through
`runFrom`'s list-recursion instead, where the induction is native.) -/
def GameSlotBound : Prop :=
  ∀ (r : Reduction) (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r))
    (εrbr : ℝ → ℝ) (δ : ℝ), δ ∈ Set.Ioo (0 : ℝ) r.δstar →
    0 ≤ εrbr δ →
    (∀ (i : Fin r.k) (st : Stmt r), st ∈ Z → rbr.err i st δ ≤ εrbr δ) →
    ∀ (s t : ℕ) (P : SrProver r s) (j : Fin t),
      uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal))
        (HitBad rbr Z δ P j) ≤ εrbr δ

/-- **Thm B.4, assembled**: the repaired [OB-2′] holds given the game-slot
bound [OB-2a]. Everything else is closed: Construction B.5 (`srExtract`),
Claim B.6 (`exists_roundBad_of_event`), the fresh/log-hit attribution
(`cover`), the fresh-slot bound (`freshBad_le`), and the
`k · ε + t · ε = (t + k) · ε` union-bound arithmetic. -/
theorem OB2_nonneg_of_gameSlotBound (H : GameSlotBound) :
    OB2_depth_composition_nonneg := by
  intro r rbr Z εrbr hnn hdom
  refine ⟨fun s => srExtract rbr s, ?_⟩
  intro s t δ hδ P
  have hnnδ : 0 ≤ εrbr δ := hnn δ hδ
  have hdomδ : ∀ (i : Fin r.k) (st : Stmt r), st ∈ Z →
      rbr.err i st δ ≤ εrbr δ := fun i st hst => hdom i st hst δ hδ
  refine le_trans (uniformProb_mono (cover rbr Z hδ P)) ?_
  refine le_trans (uniformProb_or_le _ _) ?_
  refine le_trans (add_le_add
    (uniformProb_exists_le fun a => FreshBad rbr Z δ P a)
    (uniformProb_exists_le fun j => HitBad rbr Z δ P j)) ?_
  refine le_trans (add_le_add
    (Finset.sum_le_sum fun a _ => freshBad_le rbr Z hδ hnnδ hdomδ P a)
    (Finset.sum_le_sum fun j _ =>
      H r rbr Z εrbr δ hδ hnnδ hdomδ s t P j)) ?_
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- **[OB-2a] discharged: the game-slot bound holds.** Assembled from the
split of the coin space at slot `j` (`splitAtGame`), the per-fibre bound
(`hitBad_fibre_le`), and the general lazy-`rnd` resolver's uniformity kernel
(`card_resolve_runFrom`) that the per-fibre bound rides. -/
theorem gameSlotBound_proved : GameSlotBound := by
  intro r rbr Z εrbr δ hδ hnn hdom s t P j
  classical
  have heq := uniformProb_equiv
    ((splitAtGame (C := r.Chal) (D := Fin r.k → r.Chal) j).symm)
    (HitBad rbr Z δ P j)
  rw [← heq]
  refine uniformProb_prod_le hnn ?_
  intro p
  refine hitBad_fibre_le rbr Z hδ hnn hdom P j p
    (runFrom P [] (List.ofFn p)) ?_ ?_
  · rw [runFrom_length]
    simp
  · intro ρ cs
    rw [srTrace_eq_runFrom, ofFn_splitGame_symm, runFrom_append, runFrom_cons]

/-- **[OB-2′] holds**: the repaired loss-free depth composition (WARP
2025/753, Thm B.4), fully discharged — no remaining seam. -/
theorem OB2_depth_composition_nonneg_proved : OB2_depth_composition_nonneg :=
  OB2_nonneg_of_gameSlotBound gameSlotBound_proved

/-! ## Ledger

* `OB2_depth_composition_false` — **PROVED**: the audited [OB-2] statement is
  refutable (`Z = ∅`, `εrbr = -1`, `t = 0`; the sign of the claimed bound).
* `OB2_depth_composition_nonneg` — **[OB-2′]**, the one-guard repair
  (`0 ≤ εrbr δ`); free for nonempty `Z` (`εrbr_nonneg_of_nonempty`, itself
  backed by `err_nonneg`).
* `srExtract` — Construction B.5, **DEFINED** (backwards chain `wAt`).
* `exists_roundBad_of_event` — Claim B.6, **PROVED** deterministically and
  pointwise (via `chain_descend`; the only Def 4.1 clauses used are exactly the
  paper's: `full_iff` at the top, `prover_monotone` per step, `empty_iff` at
  the bottom).
* `cover` — the fresh/log-hit attribution of the `k` output-prefix moves onto
  the `t + k` unique-move budget, **PROVED**.
* `freshBad_le` — the per-slot bound for the `k` fresh slots, **PROVED** by
  product slicing on the fresh coin.
* `stepOnce`/`runFrom`/`resolveIn` — the general lazy-`rnd` resolver the
  [OB-2a] audit called for: the game as a fold over a coin list from an
  arbitrary starting log, and resolution of EVERY salted `(stmt, prefix)`
  pair (`srFinalChal` is the designated-query instantiation,
  `srFinalChal_eq_resolveIn`).
* `card_resolve_runFrom` — **PROVED**, the resolver's uniformity kernel:
  joint resolutions of pairwise-distinct not-yet-queried points are EXACTLY
  uniform over the future coins — the lazy-sampling rendering of the eager
  total `rnd`'s independence, by induction on the coin list.
* `uniformProb_pushforward_le` — **PROVED**, pushforward slicing: exactly-
  uniform fibres + per-value small tested events ⟹ small joint event; the
  counting form of "condition on `rnd` everywhere except the queried point".
* `GameSlotBound` — **[OB-2a], PROVED** (`gameSlotBound_proved`): the
  per-slot bound for the `t` game slots, via `splitAtGame` (fix the coin
  past), `hitBad_fibre_le` (on the event, `hitAt`'s content equality pins
  slot, statement, pending message, and sub-prefix queries to the fixed
  step-`j` move; the tested response is the fresh coin `c_j`), the kernel,
  and pushforward slicing. See `GameSlotBound`'s doc comment for the recorded
  gap diagnosis and its closure.
* `OB2_nonneg_of_gameSlotBound` — **PROVED**: [OB-2a] ⟹ [OB-2′], with the
  loss-free `(t + k) · ε_rbr(δ)` arithmetic.
* `OB2_depth_composition_nonneg_proved` — **[OB-2′] PROVED, no remaining
  seam**. `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`. -/

end Minidregg.Selvage
