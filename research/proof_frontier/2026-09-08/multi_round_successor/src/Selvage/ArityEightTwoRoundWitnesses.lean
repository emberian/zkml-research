/- A small actual-carrier two-round schedule with a far source and a genuinely
prefix-dependent injected input. All domains come from existing certified roots. -/
import Selvage.ArityEightTwoRound
import Selvage.BabyBearFoldingTower

namespace Minidregg.Selvage.ArityEight.TwoRound
open scoped Classical

section PolynomialControls
variable {F ι κ : Type*} [Field F] {dom : ι ↪ F} {domSq : κ ↪ F}

/-- Even monomials fold to the corresponding monomial on the squared domain. -/
theorem fold_even_power (D : FoldingData F dom domSq) (k : ℕ) (β : F) :
    fold D (fun i => (dom i)^(2*k)) β = fun i => (domSq i)^k := by
  funext i
  have he : Even (2*k) := ⟨k,by omega⟩
  simp only [fold,foldEven,foldOdd,D.dom_neg,he.neg_pow,sub_self,zero_div,mul_zero,add_zero]
  have hs := D.domSq_sq (D.sec i)
  rw [D.sq_sec] at hs
  rw [hs,←pow_mul]
  field_simp [D.two_ne]
  ring

variable {ι₀ ι₁ ι₂ ι₃ : Type*}
variable {dom₀ : ι₀ ↪ F} {dom₁ : ι₁ ↪ F} {dom₂ : ι₂ ↪ F} {dom₃ : ι₃ ↪ F}

/-- Three real folds divide an exponent by eight, without any challenge dependence. -/
theorem fold8_power (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (k : ℕ) (β : F) :
    fold8 D₀ D₁ D₂ (fun i => (dom₀ i)^(8*k)) β = fun i => (dom₃ i)^k := by
  unfold fold8
  rw [show 8*k=2*(4*k) by omega,fold_even_power]
  rw [show 4*k=2*(2*k) by omega,fold_even_power,fold_even_power]

end PolynomialControls

namespace Witnesses
open BabyBearExt4 Polynomial
noncomputable section

/-- 128→16→2 is a positive-degree two-block schedule over the actual carrier. -/
def smallTower : FoldingTower Ext4 (PowerTwoFriLevels 7) 6 :=
  PowerTwoRootFolding.tower (TwoAdic.omega_primitive 7 (by decide))
    MultiplicativeTower.two_ne_zero (by decide)

def farWord : PowerTwoFriLevels 7 0 → Ext4 := fun i => (smallTower.dom 0 i)^64

/-- The high-degree source cannot lie in the degree-below-64 code. -/
theorem farWord_not_mem : farWord ∉ reedSolomonCode (smallTower.dom 0) 64 := by
  intro hw
  obtain ⟨p,hp,heval⟩ := mem_reedSolomonCode_iff.mp hw
  have hne : (X^64 : Polynomial Ext4) ≠ p := by
    intro heq
    rw [←heq] at hp
    norm_num at hp
  have hcard := card_agreeSet_lt_of_ne (smallTower.dom 0) (d := 65)
    (p := (X^64 : Polynomial Ext4)) (by norm_num) (q := p) (hp.trans (by norm_num)) hne
  have hall : (Finset.univ.filter fun i =>
      (X^64 : Polynomial Ext4).eval (smallTower.dom 0 i) = p.eval (smallTower.dom 0 i)) =
      Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    simpa [farWord] using heval i
  rw [hall,Finset.card_univ] at hcard
  norm_num [PowerTwoFriLevels] at hcard

/-- The farness premise is positive and derived from existing RS minimum distance. -/
theorem farWord_far : ¬close (1/5:ℝ) (reedSolomonCode (smallTower.dom 0) 64) farWord := by
  rintro ⟨w,hw,hclose⟩
  have hmem : farWord ∈ reedSolomonCode (smallTower.dom 0) 65 :=
    mem_reedSolomonCode_iff.mpr ⟨X^64,by norm_num,fun i => by simp [farWord]⟩
  have hw' : w ∈ reedSolomonCode (smallTower.dom 0) 65 := by
    obtain ⟨p,hp,heval⟩ := mem_reedSolomonCode_iff.mp hw
    exact mem_reedSolomonCode_iff.mpr ⟨p,hp.trans (by norm_num),heval⟩
  have h := reedSolomonCode_minDist (smallTower.dom 0) 65 farWord hmem w hw'
    (fun heq => farWord_not_mem (heq ▸ hw))
  norm_num [PowerTwoFriLevels] at h
  linarith

/-- The second injected word changes with the first challenge; the final
constant changes with both. The middle word is the exact first fold. -/
def words : Words Ext4 (PowerTwoFriLevels 7) where
  source := farWord
  input0 := fun _ => 0
  middle _ i := (smallTower.dom 3 i)^8
  input1 a _ := a
  final a b _ := 1+b^8*a

theorem second_input_not_fixed : words.input1 0 ≠ words.input1 1 := by
  intro h
  have heq := congrFun h 0
  exact zero_ne_one heq

theorem first_block_exact (a : Ext4) : block0 smallTower words a = words.middle a := by
  unfold block0
  change (fun i => fold8 _ _ _ (fun i => (smallTower.dom 0 i)^64) a i + a^8*0) = _
  simp only [mul_zero,add_zero]
  exact fold8_power (smallTower.data 0 (by decide)) (smallTower.data 1 (by decide))
    (smallTower.data 2 (by decide)) 8 a

theorem second_block_exact (a b : Ext4) :
    block1 smallTower words a b = fun i => smallTower.dom 6 i+b^8*a := by
  have h := fold8_power (smallTower.data 3 (by decide)) (smallTower.data 4 (by decide))
    (smallTower.data 5 (by decide)) 1 b
  simp only [mul_one,pow_one] at h
  unfold block1
  change (fun i => fold8 _ _ _ (fun i => (smallTower.dom 3 i)^8) b i + b^8*a) = _
  rw [h]

theorem terminal_mem (r : Ext4 × Ext4) :
    words.final r.1 r.2 ∈ reedSolomonCode (smallTower.dom 6) 1 :=
  mem_reedSolomonCode_one_iff.mpr (fun _ _ => rfl)

theorem terminal_domain_zero : smallTower.dom 6 (0 : PowerTwoFriLevels 7 6) = 1 := by
  change (PowerTwoRootFolding.levelRoot (TwoAdic.omega 7) 6)^0 = 1
  simp

theorem terminal_domain_one : smallTower.dom 6 (1 : PowerTwoFriLevels 7 6) = -1 := by
  have h := PowerTwoRootFolding.levelRoot_half_turn
    (TwoAdic.omega_primitive 7 (by decide)) 6 (by decide)
  simpa [smallTower,PowerTwoRootFolding.tower,PowerTwoRootFolding.domain] using h

/-- Both external rounds accept the all-zero coherent query vector. -/
theorem zero_seed_accepts (r : Ext4 × Ext4) (q : ℕ) :
    Accepts smallTower words 1 q (by decide) r (fun _ => 0) := by
  refine ⟨terminal_mem r,?_,?_⟩
  · intro a
    rw [first_block_exact]
  · intro a
    rw [second_block_exact]
    have hz : powerTwoCoherentRound (show 6 ≤ 7 by decide) (⟨5,by decide⟩ : Fin 6)
        (fun _ : Fin q => (0 : PowerTwoFriLevels 7 1)) a = 0 := by
      apply Fin.ext
      simp [powerTwoCoherentRound,powerTwoRoundIndex]
    rw [hz]
    change 1+r.2^8*r.1 = smallTower.dom 6 0+r.2^8*r.1
    rw [terminal_domain_zero]

/-- The same legal terminal word rejects the second round at seed one. -/
theorem one_seed_rejects (r : Ext4 × Ext4) :
    ¬Accepts smallTower words 1 1 (by decide) r (fun _ => 1) := by
  intro h
  have heq := h.2.2 0
  rw [second_block_exact] at heq
  have hi : powerTwoCoherentRound (show 6 ≤ 7 by decide) (⟨5,by decide⟩ : Fin 6)
      (fun _ : Fin 1 => (1 : PowerTwoFriLevels 7 1)) 0 = 1 := by
    apply Fin.ext
    norm_num [powerTwoCoherentRound,powerTwoRoundIndex]
  rw [hi] at heq
  change 1+r.2^8*r.1 = smallTower.dom 6 1+r.2^8*r.1 at heq
  rw [terminal_domain_one] at heq
  have htwo : (2:Ext4)=0 := by linear_combination heq
  exact MultiplicativeTower.two_ne_zero htwo

/-- Every source, degree, rate, gap and timing premise of the two-round
soundness statement fires on this inhabited small schedule. -/
theorem sound_fires (q : ℕ) :
    uniformProb ((Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 7 1))
      (fun x => Accepts smallTower words 1 q (by decide) x.1 x.2) ≤
      (144:ℝ)/(modulus^4:ℕ)+(9/10:ℝ)^q := by
  have h := sound smallTower words (d := 1) (by decide) q (by decide)
    (ρ₀ := (1/5:ℝ)) (ρ₁ := (1/10:ℝ)) (τ := (1/10:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [PowerTwoFriLevels]) (by norm_num [PowerTwoFriLevels]) farWord_far
  have hc : Fintype.card Ext4 = modulus^4 := ext4_card
  rw [hc] at h
  norm_num [PowerTwoFriLevels] at h ⊢
  convert h using 1
  ring

end
end Witnesses
end Minidregg.Selvage.ArityEight.TwoRound

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.fold_even_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.fold_even_power

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.fold8_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.fold8_power

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.farWord_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.farWord_not_mem

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.farWord_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.farWord_far

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.second_input_not_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.second_input_not_fixed

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.first_block_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.first_block_exact

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.second_block_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.second_block_exact

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.terminal_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.terminal_mem

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.terminal_domain_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.terminal_domain_zero

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.terminal_domain_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.terminal_domain_one

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.zero_seed_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.zero_seed_accepts

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.one_seed_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.one_seed_rejects

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.sound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.sound_fires
