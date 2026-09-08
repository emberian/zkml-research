/- Two external arity-eight rounds on existing binary tower levels 0,3,6.
There is one fresh scalar per external round. Input and middle-word
functions state the commitment timing before the respective fresh scalar. -/
import Selvage.ArityEightSampling

namespace Minidregg.Selvage.ArityEight.TwoRound
open scoped Classical

/-- Five actual words at the three external checkpoints. Only the first
scalar may affect the second input; both scalars may affect the final word. -/
structure Words (F : Type) (ι : ℕ → Type) where
  source : ι 0 → F
  input0 : ι 3 → F
  middle : F → ι 3 → F
  input1 : F → ι 6 → F
  final : F → F → ι 6 → F

section Tower
variable {F : Type} [Field F] {ell : ℕ}

/-- Three consecutive existing folds, evaluated at one scalar and its powers. -/
def block0 (T : FoldingTower F (PowerTwoFriLevels ell) 6) (s : Words F (PowerTwoFriLevels ell))
    (a : F) : PowerTwoFriLevels ell 3 → F :=
  fun i => fold8 (T.data 0 (by decide)) (T.data 1 (by decide)) (T.data 2 (by decide))
    s.source a i + a^8*s.input0 i

def block1 (T : FoldingTower F (PowerTwoFriLevels ell) 6) (s : Words F (PowerTwoFriLevels ell))
    (a b : F) : PowerTwoFriLevels ell 6 → F :=
  fun i => fold8 (T.data 3 (by decide)) (T.data 4 (by decide)) (T.data 5 (by decide))
    (s.middle a) b i + b^8*s.input1 a i

/-- Only actual sampled equations and final RS membership are accepted. -/
def Accepts [DecidableEq F] (T : FoldingTower F (PowerTwoFriLevels ell) 6)
    (s : Words F (PowerTwoFriLevels ell)) (d q : ℕ) (hell : 6 ≤ ell)
    (r : F × F) (seed : Fin q → PowerTwoFriLevels ell 1) : Prop :=
  s.final r.1 r.2 ∈ reedSolomonCode (T.dom 6) d ∧
  (∀ a, s.middle r.1 (powerTwoCoherentRound hell (⟨2,by decide⟩ : Fin 6) seed a) =
    block0 T s r.1 (powerTwoCoherentRound hell (⟨2,by decide⟩ : Fin 6) seed a)) ∧
  (∀ a, s.final r.1 r.2 (powerTwoCoherentRound hell (⟨5,by decide⟩ : Fin 6) seed a) =
    block1 T s r.1 r.2 (powerTwoCoherentRound hell (⟨5,by decide⟩ : Fin 6) seed a))

/-- The second exceptional event matters only when its prefix-selected source
is far. This avoids imposing a far-middle premise on the adversary. -/
def BadChallenge [DecidableEq F] (T : FoldingTower F (PowerTwoFriLevels ell) 6)
    (s : Words F (PowerTwoFriLevels ell)) (d : ℕ) (ρ₀ ρ₁ : ℝ) (r : F × F) : Prop :=
  close ρ₀ (reedSolomonCode (T.dom 3) (8*d)) (block0 T s r.1) ∨
  (¬close ρ₁ (reedSolomonCode (T.dom 3) (8*d)) (s.middle r.1) ∧
    close ρ₁ (reedSolomonCode (T.dom 6) d) (block1 T s r.1 r.2))

end Tower

section Probability
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {ell : ℕ}

/-- A first-coordinate event has its exact marginal when the discarded factor is nonempty. -/
theorem uniform_fst {A B : Type} [Fintype A] [Fintype B] [Nonempty B] (p : A → Prop) :
    uniformProb (A × B) (fun x => p x.1) = uniformProb A p := by
  let e := Equiv.prodComm A B
  calc
    _ = uniformProb (B × A) (fun x => p x.2) := by
      simpa [e] using uniformProb_equiv e (fun x => p x.2)
    _ = _ := uniformProb_prod_snd p

/-- The two fresh challenge errors add. The second input and source may
change with the first challenge, but not with the second challenge. -/
theorem bad_challenge_bound (T : FoldingTower F (PowerTwoFriLevels ell) 6)
    (s : Words F (PowerTwoFriLevels ell)) {d : ℕ} (hd : 1 ≤ d) {ρ₀ ρ₁ : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁)
    (hrate₀ : (8*d:ℕ) < (1-2*ρ₀)*(Fintype.card (PowerTwoFriLevels ell 3):ℝ))
    (hrate₁ : (d:ℝ) < (1-2*ρ₁)*(Fintype.card (PowerTwoFriLevels ell 6):ℝ))
    (hfar : ¬close ρ₀ (reedSolomonCode (T.dom 0) (64*d)) s.source) :
    uniformProb (F × F) (BadChallenge T s d ρ₀ ρ₁) ≤
      ((8*Fintype.card (PowerTwoFriLevels ell 3):ℕ):ℝ)/Fintype.card F +
      ((8*Fintype.card (PowerTwoFriLevels ell 6):ℕ):ℝ)/Fintype.card F := by
  classical
  have hf : ¬close ρ₀ (reedSolomonCode (T.dom 0) (8*(8*d))) s.source := by
    simpa only [show 8*(8*d)=64*d by omega] using hfar
  have h₀ := fold8_injected_uniform_sound (T.data 0 (by decide)) (T.data 1 (by decide))
    (T.data 2 (by decide)) (d := 8*d) (by omega) hρ₀ hrate₀ s.source s.input0 hf
  have h₁ : uniformProb (F × F)
      (fun r => ¬close ρ₁ (reedSolomonCode (T.dom 3) (8*d)) (s.middle r.1) ∧
        close ρ₁ (reedSolomonCode (T.dom 6) d) (block1 T s r.1 r.2)) ≤
      ((8*Fintype.card (PowerTwoFriLevels ell 6):ℕ):ℝ)/Fintype.card F := by
    apply uniformProb_prod_le (by positivity)
    intro a
    by_cases hf : close ρ₁ (reedSolomonCode (T.dom 3) (8*d)) (s.middle a)
    · rw [uniformProb_false (fun _ h => h.1 hf)]
      positivity
    · exact le_trans (uniformProb_mono fun _ h => h.2)
        (fold8_injected_uniform_sound (T.data 3 (by decide)) (T.data 4 (by decide))
          (T.data 5 (by decide)) hd hρ₁ hrate₁ (s.middle a) (s.input1 a) hf)
  have hsplit := uniformProb_or_le
    (fun r : F × F => close ρ₀ (reedSolomonCode (T.dom 3) (8*d)) (block0 T s r.1))
    (fun r : F × F => ¬close ρ₁ (reedSolomonCode (T.dom 3) (8*d)) (s.middle r.1) ∧
      close ρ₁ (reedSolomonCode (T.dom 6) d) (block1 T s r.1 r.2))
  rw [uniform_fst (B := F) (fun a => close ρ₀ (reedSolomonCode (T.dom 3) (8*d)) (block0 T s a))] at hsplit
  change uniformProb (F × F) (BadChallenge T s d ρ₀ ρ₁) ≤ _ at hsplit
  change uniformProb F (fun a => close ρ₀ (reedSolomonCode (T.dom 3) (8*d))
    (block0 T s a)) ≤ _ at h₀
  linarith

omit [Fintype F] in
/-- Off the explicit challenge events, terminal membership forces an actual
far transition. The choice is made after the challenge pair is fixed. -/
theorem earliest_transition_cover (T : FoldingTower F (PowerTwoFriLevels ell) 6)
    (s : Words F (PowerTwoFriLevels ell)) {d : ℕ} {ρ₀ ρ₁ τ : ℝ}
    (hgap₀ : ρ₁+τ ≤ ρ₀) (hgap₁ : τ ≤ ρ₁) (r : F × F)
    (hgood : ¬BadChallenge T s d ρ₀ ρ₁ r)
    (hfinal : s.final r.1 r.2 ∈ reedSolomonCode (T.dom 6) d) :
    τ ≤ relDist (s.middle r.1) (block0 T s r.1) ∨
      τ ≤ relDist (s.final r.1 r.2) (block1 T s r.1 r.2) := by
  by_cases hm : close ρ₁ (reedSolomonCode (T.dom 3) (8*d)) (s.middle r.1)
  · left
    by_contra hd
    have hlt := lt_of_not_ge hd
    obtain ⟨w,hw,hclose⟩ := hm
    apply hgood
    left
    refine ⟨w,hw,?_⟩
    have htri := relDist_triangle (block0 T s r.1) (s.middle r.1) w
    rw [relDist_comm (block0 T s r.1) (s.middle r.1)] at htri
    linarith
  · right
    by_contra hd
    have hlt := lt_of_not_ge hd
    apply hgood
    right
    refine ⟨hm,s.final r.1 r.2,hfinal,?_⟩
    rw [relDist_comm]
    linarith

omit [Fintype F] in
set_option maxHeartbeats 800000 in
/-- Both rounds share one query vector. Selecting the far transition costs
one column-sampling tail, rather than summing two tails. -/
theorem coherent_query_bound (T : FoldingTower F (PowerTwoFriLevels ell) 6)
    (s : Words F (PowerTwoFriLevels ell)) (d q : ℕ) (hell : 6 ≤ ell)
    {ρ₀ ρ₁ τ : ℝ} (hτ : τ ≤ 1) (hgap₀ : ρ₁+τ ≤ ρ₀) (hgap₁ : τ ≤ ρ₁)
    (r : F × F) (hgood : ¬BadChallenge T s d ρ₀ ρ₁ r) :
    uniformProb (Fin q → PowerTwoFriLevels ell 1) (Accepts T s d q hell r) ≤ (1-τ)^q := by
  by_cases hf : s.final r.1 r.2 ∈ reedSolomonCode (T.dom 6) d
  · rcases earliest_transition_cover T s hgap₀ hgap₁ r hgood hf with h₀ | h₁
    · refine le_trans (uniformProb_mono fun seed h => h.2.1) ?_
      exact le_trans (powerTwoCoherentRound_uniform_le hell (⟨2,by decide⟩ : Fin 6)
        (fun Q : Fin q → PowerTwoFriLevels ell 3 =>
          ∀ a, s.middle r.1 (Q a) = block0 T s r.1 (Q a)))
        (point_query_miss q h₀)
    · refine le_trans (uniformProb_mono fun seed h => h.2.2) ?_
      exact le_trans (powerTwoCoherentRound_uniform_le hell (⟨5,by decide⟩ : Fin 6)
        (fun Q : Fin q → PowerTwoFriLevels ell 6 =>
          ∀ a, s.final r.1 r.2 (Q a) = block1 T s r.1 r.2 (Q a)))
        (point_query_miss q h₁)
  · rw [uniformProb_false (fun _ h => hf h.1)]
    exact pow_nonneg (sub_nonneg.mpr hτ) _

/-- Full two-round terminal soundness, derived from actual folds, prefix
challenge bounds and the existing coherent query sampler. -/
theorem sound (T : FoldingTower F (PowerTwoFriLevels ell) 6)
    (s : Words F (PowerTwoFriLevels ell)) {d : ℕ} (hd : 1 ≤ d) (q : ℕ) (hell : 6 ≤ ell)
    {ρ₀ ρ₁ τ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (hτ : τ ≤ 1)
    (hgap₀ : ρ₁+τ ≤ ρ₀) (hgap₁ : τ ≤ ρ₁)
    (hrate₀ : (8*d:ℕ) < (1-2*ρ₀)*(Fintype.card (PowerTwoFriLevels ell 3):ℝ))
    (hrate₁ : (d:ℝ) < (1-2*ρ₁)*(Fintype.card (PowerTwoFriLevels ell 6):ℝ))
    (hfar : ¬close ρ₀ (reedSolomonCode (T.dom 0) (64*d)) s.source) :
    uniformProb ((F × F) × (Fin q → PowerTwoFriLevels ell 1))
      (fun x => Accepts T s d q hell x.1 x.2) ≤
      ((8*Fintype.card (PowerTwoFriLevels ell 3):ℕ):ℝ)/Fintype.card F +
      ((8*Fintype.card (PowerTwoFriLevels ell 6):ℕ):ℝ)/Fintype.card F + (1-τ)^q := by
  let bad := BadChallenge T s d ρ₀ ρ₁
  have hb := bad_challenge_bound T s hd hρ₀ hρ₁ hrate₀ hrate₁ hfar
  have hq : uniformProb ((F × F) × (Fin q → PowerTwoFriLevels ell 1))
      (fun x => ¬bad x.1 ∧ Accepts T s d q hell x.1 x.2) ≤ (1-τ)^q := by
    apply uniformProb_prod_le (pow_nonneg (sub_nonneg.mpr hτ) _)
    intro r
    by_cases hbad : bad r
    · rw [uniformProb_false (fun _ h => h.1 hbad)]
      exact pow_nonneg (sub_nonneg.mpr hτ) _
    · exact le_trans (uniformProb_mono fun _ h => h.2)
        (coherent_query_bound T s d q hell hτ hgap₀ hgap₁ r hbad)
  have hsplit : uniformProb ((F × F) × (Fin q → PowerTwoFriLevels ell 1))
      (fun x => Accepts T s d q hell x.1 x.2) ≤
      uniformProb ((F × F) × (Fin q → PowerTwoFriLevels ell 1)) (fun x => bad x.1) +
      uniformProb ((F × F) × (Fin q → PowerTwoFriLevels ell 1))
        (fun x => ¬bad x.1 ∧ Accepts T s d q hell x.1 x.2) := by
    refine le_trans (uniformProb_mono fun x hx => ?_) (uniformProb_or_le _ _)
    by_cases hbad : bad x.1
    · exact Or.inl hbad
    · exact Or.inr ⟨hbad,hx⟩
  rw [uniform_fst (B := Fin q → PowerTwoFriLevels ell 1) bad] at hsplit
  change uniformProb (F × F) bad ≤ _ at hb
  linarith

end Probability
end Minidregg.Selvage.ArityEight.TwoRound


/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.uniform_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.uniform_fst

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.bad_challenge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.bad_challenge_bound

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.earliest_transition_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.earliest_transition_cover

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.coherent_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.coherent_query_bound

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.sound
