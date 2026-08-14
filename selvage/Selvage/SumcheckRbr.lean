/-
# Selvage.SumcheckRbr — sumcheck as an actual round-by-round reduction

`Selvage/SumcheckReduction.lean` proves the adaptive whole-transcript bound.
This file supplies the missing kernel object underneath that theorem: a WARP
`Reduction`, its `KStateFn`, and its `RbrKnowledgeSoundness` instance.

The knowledge state says three things about a transcript prefix:

* every completed prover polynomial has the advertised degree and Boolean sum;
* the prover claim and honest truth still agree after the completed rounds; and
* a dangling prover polynomial, when present, already passes the local checks.

Consequently a prover message cannot resurrect a dead state.  A fresh verifier
challenge can resurrect it only by making two distinct degree-`d` polynomials
agree.  `sumcheckRound_prob` prices exactly that event at `d / |F|`.  The
extractor is the identity on the unit witness: this reduction establishes
statement preservation, while witness-bearing protocols compose it with their
own codeword/table extraction state.

This is the IOR/full-message resolution.  Fiat--Shamir/BCS compilation and
oracle query consistency remain separate layers, as in `Rbr.lean` and
`HalfThresholdFriTranscript.lean`.
-/
import Selvage.SumcheckReduction

namespace Minidregg.Selvage

open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Transcript execution -/

/-- The prover claim after a chronological list of completed sumcheck rounds.
The fold is memoryless: each round replaces the incoming claim by `g(r)`. -/
def scRunClaim (H : F) : List (Polynomial F × F) → F
  | [] => H
  | (g, r) :: rs => scRunClaim (g.eval r) rs

/-- Completed-round validity: degree bound and the Boolean sum equation at
every step of the chronological run. -/
def scRunValid (d : ℕ) : F → List (Polynomial F × F) → Prop
  | _, [] => True
  | H, (g, r) :: rs =>
      g.degree < ((d + 1 : ℕ) : WithBot ℕ) ∧
      g.eval 0 + g.eval 1 = H ∧
      scRunValid d (g.eval r) rs

@[simp] theorem scRunClaim_append_single (H : F)
    (rs : List (Polynomial F × F)) (g : Polynomial F) (r : F) :
    scRunClaim H (rs ++ [(g, r)]) = g.eval r := by
  induction rs generalizing H with
  | nil => rfl
  | cons e rs ih =>
      rcases e with ⟨g', r'⟩
      simpa [scRunClaim] using ih (g'.eval r')

theorem scRunValid_append_single (d : ℕ) (H : F)
    (rs : List (Polynomial F × F)) (g : Polynomial F) (r : F) :
    scRunValid d H (rs ++ [(g, r)]) ↔
      scRunValid d H rs ∧
      g.degree < ((d + 1 : ℕ) : WithBot ℕ) ∧
      g.eval 0 + g.eval 1 = scRunClaim H rs := by
  induction rs generalizing H with
  | nil => simp [scRunValid, scRunClaim]
  | cons e rs ih =>
      rcases e with ⟨g', r'⟩
      simp only [List.cons_append, scRunValid, scRunClaim]
      rw [ih]
      tauto

/-- Read the completed challenges as a total stream, padded by zero. -/
def scSchedule (rs : List (Polynomial F × F)) : ℕ → F :=
  fun j => (rs[j]?.map Prod.snd).getD 0

theorem scSchedule_append_lt (rs : List (Polynomial F × F))
    (e : Polynomial F × F) {j : ℕ} (hj : j < rs.length) :
    scSchedule (rs ++ [e]) j = scSchedule rs j := by
  unfold scSchedule
  rw [List.getElem?_append_left hj]

theorem scSchedule_append_self (rs : List (Polynomial F × F))
    (g : Polynomial F) (r : F) :
    scSchedule (rs ++ [(g, r)]) rs.length = r := by
  unfold scSchedule
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

/-- The honest polynomial selected at the next round of a prefix. -/
def scHonestAt (honest : (ℕ → F) → ℕ → Polynomial F)
    (rs : List (Polynomial F × F)) : Polynomial F :=
  honest (scSchedule rs) rs.length

/-- The honest truth after a completed prefix. -/
def scTruthAfter (S : F) (honest : (ℕ → F) → ℕ → Polynomial F)
    (rs : List (Polynomial F × F)) : F :=
  scChain S (honest (scSchedule rs)) (scSchedule rs) rs.length

/-- Appending a round evaluates the honest polynomial selected by the earlier
challenge prefix at the new challenge. -/
theorem scTruthAfter_append_single {S : F}
    {honest : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable honest) (rs : List (Polynomial F × F))
    (g : Polynomial F) (r : F) :
    scTruthAfter S honest (rs ++ [(g, r)]) = (scHonestAt honest rs).eval r := by
  unfold scTruthAfter scHonestAt
  simp only [List.length_append, List.length_singleton, scChain]
  rw [scSchedule_append_self]
  have hh := hpm (scSchedule (rs ++ [(g, r)])) (scSchedule rs) rs.length
    (fun j hj => scSchedule_append_lt rs (g, r) hj)
  rw [hh]

/-- Prefix-measurability transports the next honest polynomial from a list
schedule to any total challenge stream agreeing below the next round. -/
theorem scHonestAt_eq_of_prefix
    {honest : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable honest) (rs : List (Polynomial F × F))
    (χ : ℕ → F) (hpre : ∀ j, j < rs.length → scSchedule rs j = χ j) :
    scHonestAt honest rs = honest χ rs.length := by
  exact hpm (scSchedule rs) χ rs.length hpre

/-- The truth after a list prefix is unchanged when both the honest prover and
challenge stream are transported to an agreeing total schedule. -/
theorem scTruthAfter_eq_of_prefix {S : F}
    {honest : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable honest) (rs : List (Polynomial F × F))
    (χ : ℕ → F) (hpre : ∀ j, j < rs.length → scSchedule rs j = χ j) :
    scTruthAfter S honest rs = scChain S (honest χ) χ rs.length := by
  unfold scTruthAfter
  cases hlen : rs.length with
  | zero => rfl
  | succ n =>
      rw [scChain, scChain]
      have hn : n < rs.length := by omega
      rw [hpm (scSchedule rs) χ n
        (fun j hj => hpre j (lt_trans hj hn)), hpre n hn]

/-! ## The reduction and knowledge state -/

/-- The state proposition at every transcript shape.  A pending message is
checked but not yet evaluated; therefore adding it can never turn `false` into
`true`. -/
def SumcheckRbrStateProp (d : ℕ) (S : F)
    (honest : (ℕ → F) → ℕ → Polynomial F) (H : F)
    (rs : List (Polynomial F × F)) (pending : Option (Polynomial F)) : Prop :=
  scRunValid d H rs ∧
  scRunClaim H rs = scTruthAfter S honest rs ∧
  match pending with
  | none => True
  | some g =>
      g.degree < ((d + 1 : ℕ) : WithBot ℕ) ∧
      g.eval 0 + g.eval 1 = scRunClaim H rs

/-- The degree-`d`, `k`-round sumcheck reduction for fixed true total `S` and
fixed adaptive honest family.  The implicit words and witness are unit: this
component preserves the scalar claim. -/
@[reducible] noncomputable def sumcheckReduction (k d : ℕ) (hk : 0 < k) (S : F)
    (honest : (ℕ → F) → ℕ → Polynomial F) : Reduction where
  Idx := Unit
  X := F
  A := Unit
  X' := F × F
  A' := Unit
  W := Unit
  n := 1
  n' := 1
  n_pos := by decide
  n'_pos := by decide
  R := fun _ H _ _ => H = S
  R' := fun _ out _ _ => out.1 = out.2
  k := k
  k_pos := hk
  PMsg := Polynomial F
  Chal := F
  pmsgNonempty := ⟨0⟩
  chalFintype := inferInstance
  chalNonempty := ⟨0⟩
  δstar := 1
  δstar_pos := by norm_num
  δstar_le_one := le_rfl
  verify := by
    classical
    exact fun _ H _ πs ρs =>
      let rs := List.ofFn fun i => (πs i, ρs i)
      if scRunValid d H rs then
        some ((scRunClaim H rs, scTruthAfter S honest rs), fun _ => ())
      else none

open Classical in
/-- The Def-4.1 knowledge state for sumcheck. -/
noncomputable def sumcheckKState (k d : ℕ) (hk : 0 < k) (S : F)
    (honest : (ℕ → F) → ℕ → Polynomial F) :
    KStateFn (sumcheckReduction k d hk S honest) where
  state := fun _δ st tr _w =>
    decide (SumcheckRbrStateProp d S honest st.x tr.rounds tr.pending)
  empty_iff := by
    intro δ hδ st w
    simp only [decide_eq_true_eq]
    constructor
    · intro hs
      refine ⟨st.y, ?_, ?_⟩
      · exact hs.2.1
      · rw [fracHamming_self]
        exact hδ.1.le
    · rintro ⟨ystar, hR, hdist⟩
      exact ⟨by trivial, hR, by trivial⟩
  prover_monotone := by
    intro δ hδ st rs w hlen hdead g
    rw [decide_eq_false_iff_not] at hdead ⊢
    intro halive
    apply hdead
    exact ⟨halive.1, halive.2.1, trivial⟩
  full_iff := by
    intro δ hδ st πs ρs w
    simp only [decide_eq_true_eq]
    let rs : List (Polynomial F × F) := List.ofFn fun i => (πs i, ρs i)
    change SumcheckRbrStateProp d S honest st.x rs none ↔ _
    constructor
    · rintro ⟨hvalid, halign, hpending⟩
      refine ⟨(scRunClaim st.x rs, scTruthAfter S honest rs),
        (fun _ => ()), ?_, ?_⟩
      · simp [sumcheckReduction, rs, hvalid]
      · refine ⟨(fun _ => ()), ?_, ?_⟩
        · exact halign
        · rw [fracHamming_self]
          exact hδ.1.le
    · rintro ⟨x', y', hver, hrel⟩
      change (if scRunValid d st.x rs then
          some ((scRunClaim st.x rs, scTruthAfter S honest rs), fun _ => ())
        else none) = some (x', y') at hver
      by_cases hv : scRunValid d st.x rs
      · rw [if_pos hv] at hver
        have hx : x' = (scRunClaim st.x rs, scTruthAfter S honest rs) :=
          congrArg Prod.fst (Option.some.inj hver).symm
        subst x'
        obtain ⟨ystar, htarget, hdist⟩ := hrel
        exact ⟨hv, htarget, trivial⟩
      · rw [if_neg hv] at hver
        contradiction

open Classical in
/-- The state field, exposed for round proofs. -/
theorem sumcheckKState_state_eq (k d : ℕ) (hk : 0 < k) (S : F)
    (honest : (ℕ → F) → ℕ → Polynomial F) (δ : ℝ)
    (st : Stmt (sumcheckReduction k d hk S honest))
    (tr : Transcript (Polynomial F) F) (w : Unit) :
    (sumcheckKState k d hk S honest).state δ st tr w =
      decide (SumcheckRbrStateProp d S honest st.x tr.rounds tr.pending) := rfl

/-! ## Def-4.2 round-by-round soundness -/

/-- Sumcheck's native RBR instance.  The per-round error is exactly
`d / |F|`; no union bound is inserted here. -/
noncomputable def sumcheckRbrKnowledgeSound (k d : ℕ) (hk : 0 < k) (S : F)
    (honest : (ℕ → F) → ℕ → Polynomial F)
    (hpm : PrefixMeasurable honest)
    (hdeg : ∀ rs : List (Polynomial F × F), rs.length < k →
      (scHonestAt honest rs).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hcheck : ∀ rs : List (Polynomial F × F), rs.length < k →
      (scHonestAt honest rs).eval 0 + (scHonestAt honest rs).eval 1 =
        scTruthAfter S honest rs) :
    RbrKnowledgeSoundness (sumcheckReduction k d hk S honest) where
  kstate := sumcheckKState k d hk S honest
  extract := fun _st _tr _w => ()
  err := fun _i _st _δ => (d : ℝ) / Fintype.card F
  extractTime := fun _ => 0
  extract_sound := by
    classical
    intro δ hδ st i rs hlen g
    have hi : rs.length < k := by
      rw [hlen]
      exact i.isLt
    by_cases hgdeg : g.degree < ((d + 1 : ℕ) : WithBot ℕ)
    · by_cases hgcheck : g.eval 0 + g.eval 1 = scRunClaim st.x rs
      · by_cases hfalse : scRunClaim st.x rs ≠
            (scHonestAt honest rs).eval 0 + (scHonestAt honest rs).eval 1
        · refine le_trans (uniformProb_mono ?_)
            (sumcheckRound_prob (hdeg rs hi) hgdeg hgcheck hfalse)
          intro r hev
          obtain ⟨w, hdead, halive⟩ := hev
          rw [sumcheckKState_state_eq, decide_eq_true_eq] at halive
          have halive' : SumcheckRbrStateProp d S honest st.x
              (rs ++ [(g, r)]) none := halive
          have hagree : g.eval r = (scHonestAt honest rs).eval r := by
            have h := halive'.2.1
            rw [scRunClaim_append_single,
              scTruthAfter_append_single hpm] at h
            exact h
          exact hagree
        · refine le_trans (le_of_eq (uniformProb_false fun r hev => ?_))
            (by positivity)
          obtain ⟨w, hdead, halive⟩ := hev
          rw [sumcheckKState_state_eq, decide_eq_false_iff_not] at hdead
          rw [sumcheckKState_state_eq, decide_eq_true_eq] at halive
          have halive' : SumcheckRbrStateProp d S honest st.x
              (rs ++ [(g, r)]) none := halive
          have hv := (scRunValid_append_single d st.x rs g r).mp halive'.1
          have heq : scRunClaim st.x rs = scTruthAfter S honest rs :=
            (not_ne_iff.mp hfalse).trans (hcheck rs hi)
          apply hdead
          exact ⟨hv.1, heq, hgdeg, hgcheck⟩
      · refine le_trans (le_of_eq (uniformProb_false fun r hev => ?_))
          (by positivity)
        obtain ⟨w, hdead, halive⟩ := hev
        rw [sumcheckKState_state_eq, decide_eq_true_eq] at halive
        have halive' : SumcheckRbrStateProp d S honest st.x
            (rs ++ [(g, r)]) none := halive
        have hv := (scRunValid_append_single d st.x rs g r).mp halive'.1
        exact hgcheck hv.2.2
    · refine le_trans (le_of_eq (uniformProb_false fun r hev => ?_))
        (by positivity)
      obtain ⟨w, hdead, halive⟩ := hev
      rw [sumcheckKState_state_eq, decide_eq_true_eq] at halive
      have halive' : SumcheckRbrStateProp d S honest st.x
          (rs ++ [(g, r)]) none := halive
      have hv := (scRunValid_append_single d st.x rs g r).mp halive'.1
      exact hgdeg hv.2.1

/-- The instance's error field computes to the advertised one-round price. -/
@[simp] theorem sumcheckRbr_err (k d : ℕ) (hk : 0 < k) (S : F)
    (honest : (ℕ → F) → ℕ → Polynomial F)
    (hpm : PrefixMeasurable honest)
    (hdeg : ∀ rs : List (Polynomial F × F), rs.length < k →
      (scHonestAt honest rs).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hcheck : ∀ rs : List (Polynomial F × F), rs.length < k →
      (scHonestAt honest rs).eval 0 + (scHonestAt honest rs).eval 1 =
        scTruthAfter S honest rs)
    (i : Fin k) (st : Stmt (sumcheckReduction k d hk S honest)) (δ : ℝ) :
    (sumcheckRbrKnowledgeSound k d hk S honest hpm hdeg hcheck).err i st δ =
      (d : ℝ) / Fintype.card F := rfl

end Minidregg.Selvage
