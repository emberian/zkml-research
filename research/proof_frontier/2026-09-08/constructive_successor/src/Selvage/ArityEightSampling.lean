/- A single arity-eight transition with a next word selected after beta,
before independent query seeds. The conclusion prices crossing from a far
source into a close next word while all sampled equations pass. -/
import Selvage.ArityEightFold
import Selvage.HalfThresholdFriCoherent

namespace Minidregg.Selvage.ArityEight
open scoped Classical

section Sampling
variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype ι] [Nonempty ι]

/-- The next word can depend on the challenge, but has no query-seed argument. -/
def Crossing (C : Submodule F (ι → F)) (δ : ℝ)
    (literal next : F → ι → F) (q : ℕ) (x : F × (Fin q → ι)) : Prop :=
  close δ C (next x.1) ∧ ∀ a, next x.1 (x.2 a) = literal x.1 (x.2 a)

omit [Field F] [Fintype F] in
/-- Finite column counting in the existing uniform probability interface. -/
theorem point_query_miss (q : ℕ) {f g : ι → F} {τ : ℝ}
    (hfar : τ ≤ relDist f g) :
    uniformProb (Fin q → ι) (fun s => ∀ a, f (s a) = g (s a)) ≤ (1-τ)^q := by
  classical
  unfold uniformProb
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa [Fintype.card_fun] using column_sampling_bridge_pr q hfar

set_option maxHeartbeats 800000 in
/-- Finite challenge/query composition. The challenge bound will be discharged
by the actual arity-eight source-farness theorem below. -/
theorem sampled_crossing_of_challenge_bound
    (C : Submodule F (ι → F)) (literal next : F → ι → F)
    (q : ℕ) {θ δ τ ε : ℝ} (hτ : τ ≤ 1) (hgap : δ+τ ≤ θ) (hε : 0 ≤ ε)
    (hchallenge : uniformProb F (fun β => close θ C (literal β)) ≤ ε) :
    uniformProb (F × (Fin q → ι)) (Crossing C δ literal next q) ≤ ε+(1-τ)^q := by
  classical
  let bad : F → Prop := fun β => close θ C (literal β)
  have heps : 0 ≤ (1-τ)^q := pow_nonneg (sub_nonneg.mpr hτ) _
  have hsplit : uniformProb (F × (Fin q → ι)) (Crossing C δ literal next q) ≤
      uniformProb (F × (Fin q → ι)) (fun x => bad x.1) +
      uniformProb (F × (Fin q → ι))
        (fun x => ¬bad x.1 ∧ Crossing C δ literal next q x) := by
    refine le_trans (uniformProb_mono fun x hx => ?_) (uniformProb_or_le _ _)
    by_cases hb : bad x.1
    · exact Or.inl hb
    · exact Or.inr ⟨hb,hx⟩
  have hb : uniformProb (F × (Fin q → ι)) (fun x => bad x.1) ≤ ε := by
    let e := Equiv.prodComm F (Fin q → ι)
    calc
      _ = uniformProb ((Fin q → ι) × F) (fun x => bad x.2) := by
        simpa [e] using uniformProb_equiv e (fun x => bad x.2)
      _ ≤ ε := uniformProb_prod_le hε (fun _ => hchallenge)
  have hq : uniformProb (F × (Fin q → ι))
      (fun x => ¬bad x.1 ∧ Crossing C δ literal next q x) ≤ (1-τ)^q := by
    apply uniformProb_prod_le heps
    intro β
    by_cases hb : bad β
    · rw [uniformProb_false]
      · exact heps
      · intro s hs
        exact hs.1 hb
    · by_cases hn : close δ C (next β)
      · have hdist : τ ≤ relDist (next β) (literal β) := by
          by_contra h
          have hlt := lt_of_not_ge h
          obtain ⟨c, hc, hnc⟩ := hn
          apply hb
          refine ⟨c,hc,?_⟩
          have htri := relDist_triangle (literal β) (next β) c
          rw [relDist_comm (literal β) (next β)] at htri
          linarith
        exact le_trans (uniformProb_mono fun _ hs => hs.2.2)
          (point_query_miss q hdist)
      · rw [uniformProb_false]
        · exact heps
        · intro s hs
          exact hn hs.2.1
  linarith
end Sampling

section ActualFold
variable {F ι₀ ι₁ ι₂ ι₃ : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
variable [Nonempty ι₀] [Nonempty ι₃]
variable {dom₀ : ι₀ ↪ F} {dom₁ : ι₁ ↪ F} {dom₂ : ι₂ ↪ F} {dom₃ : ι₃ ↪ F}

/-- Actual source farness discharges the coefficient non-CA premise. -/
theorem fold8_uniform_sound
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) {d : ℕ} (hd : 1 ≤ d) {θ : ℝ}
    (hθ : 0 < θ) (hrate : (d:ℝ) < (1-2*θ)*(Fintype.card ι₃:ℝ))
    (f : ι₀ → F) (hfar : ¬close θ (reedSolomonCode dom₀ (8*d)) f) :
    uniformProb F (fun β => close θ (reedSolomonCode dom₃ d) (fold8 D₀ D₁ D₂ f β)) ≤
      ((7*Fintype.card ι₃:ℕ):ℝ)/Fintype.card F := by
  simpa only [fold8_eq_curve] using arity8_curve_sound dom₃ hd hθ hrate
    (components D₀ D₁ D₂ f) (fun h => hfar (reconstruction D₀ D₁ D₂ d θ f h))

/-- Fixed-prefix input injection costs degree eight. The arbitrary injected
word is fixed before beta; the next committed word may depend on beta. -/
theorem fold8_injected_uniform_sound
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) {d : ℕ} (hd : 1 ≤ d) {θ : ℝ}
    (hθ : 0 < θ) (hrate : (d:ℝ) < (1-2*θ)*(Fintype.card ι₃:ℝ))
    (f : ι₀ → F) (g : ι₃ → F)
    (hfar : ¬close θ (reedSolomonCode dom₀ (8*d)) f) :
    uniformProb F (fun β => close θ (reedSolomonCode dom₃ d)
      (fun i => fold8 D₀ D₁ D₂ f β i + β^8*g i)) ≤
      ((8*Fintype.card ι₃:ℕ):ℝ)/Fintype.card F := by
  simpa only [fold8_eq_curve] using arity8_injected_curve_sound dom₃ hd hθ hrate
    (components D₀ D₁ D₂ f) g (fun h => hfar (reconstruction D₀ D₁ D₂ d θ f h))

/-- One real arity-eight transition: one beta, then the next word, then q
uniform row seeds with replacement. This is a crossing bound, not an
unproved multi-round Fiat--Shamir or runtime correspondence assertion. -/
theorem fold8_sampled_crossing
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) {d : ℕ} (hd : 1 ≤ d) {θ δ τ : ℝ}
    (hθ : 0 < θ) (hrate : (d:ℝ) < (1-2*θ)*(Fintype.card ι₃:ℝ))
    (hτ : τ ≤ 1) (hgap : δ+τ ≤ θ)
    (f : ι₀ → F) (next : F → ι₃ → F) (q : ℕ)
    (hfar : ¬close θ (reedSolomonCode dom₀ (8*d)) f) :
    uniformProb (F × (Fin q → ι₃))
      (Crossing (reedSolomonCode dom₃ d) δ (fold8 D₀ D₁ D₂ f) next q) ≤
      ((7*Fintype.card ι₃:ℕ):ℝ)/Fintype.card F + (1-τ)^q :=
  sampled_crossing_of_challenge_bound _ _ _ q hτ hgap (by positivity)
    (fold8_uniform_sound D₀ D₁ D₂ hd hθ hrate f hfar)

/-- The same sampled transition with a pre-beta injected word, as in a
matching-height input addition. No independence between beta and beta^8. -/
theorem fold8_injected_sampled_crossing
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) {d : ℕ} (hd : 1 ≤ d) {θ δ τ : ℝ}
    (hθ : 0 < θ) (hrate : (d:ℝ) < (1-2*θ)*(Fintype.card ι₃:ℝ))
    (hτ : τ ≤ 1) (hgap : δ+τ ≤ θ)
    (f : ι₀ → F) (g : ι₃ → F) (next : F → ι₃ → F) (q : ℕ)
    (hfar : ¬close θ (reedSolomonCode dom₀ (8*d)) f) :
    uniformProb (F × (Fin q → ι₃))
      (Crossing (reedSolomonCode dom₃ d) δ
        (fun β i => fold8 D₀ D₁ D₂ f β i + β^8*g i) next q) ≤
      ((8*Fintype.card ι₃:ℕ):ℝ)/Fintype.card F + (1-τ)^q :=
  sampled_crossing_of_challenge_bound _ _ _ q hτ hgap (by positivity)
    (fold8_injected_uniform_sound D₀ D₁ D₂ hd hθ hrate f g hfar)
end ActualFold
end Minidregg.Selvage.ArityEight

/-- info: 'Minidregg.Selvage.ArityEight.point_query_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.point_query_miss

/-- info: 'Minidregg.Selvage.ArityEight.sampled_crossing_of_challenge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.sampled_crossing_of_challenge_bound

/-- info: 'Minidregg.Selvage.ArityEight.fold8_uniform_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold8_uniform_sound

/-- info: 'Minidregg.Selvage.ArityEight.fold8_injected_uniform_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold8_injected_uniform_sound

/-- info: 'Minidregg.Selvage.ArityEight.fold8_sampled_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold8_sampled_crossing

/-- info: 'Minidregg.Selvage.ArityEight.fold8_injected_sampled_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold8_injected_sampled_crossing

