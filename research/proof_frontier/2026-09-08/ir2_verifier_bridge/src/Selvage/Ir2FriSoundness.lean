/- Fresh-randomness proximity theorem for the observed IR2 FRI profile.
This event retains initial input equality, four width-eight folds, one width-four
fold, and the native one-coefficient terminal polynomial. -/
import Selvage.Ir2FriProjection
import Selvage.Ir2FriNativeEvent

namespace Minidregg.Selvage.Ir2Fri
open BabyBearExt4 Ir2FriSchedule
open scoped Classical
noncomputable section
set_option maxRecDepth 100000

/-- The exact scalar-word consistency event represented by the canonical packed
row projection. Word extraction/binding and PCS batching are separate bridges. -/
def Accepts (s : Words) (q : ℕ) (r : Fin 5 → Ext4) (raw : Fin q → Fin (2^17)) : Prop :=
  Terminal s r ∧ QueryAccepts (initialMask s) (stepMasks s r) q raw

/-- Native sample_bits(17) applied to fresh uniform actual BabyBear words.
This definition does not identify a Fiat--Shamir sponge with fresh randomness. -/
def FreshAccepts (s : Words) (q : ℕ) (r : Fin 5 → Ext4) (raw : Fin q → BabyBear) : Prop :=
  Accepts s q r (fun a => BabyBearModuloSampling.sampleBits 17 (raw a))

/-- The exact native modulo bias increases the ideal tail by at most θ/p. -/
def queryTail (θ : ℝ) : ℝ :=
  (((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(1-θ)+1/(modulus:ℝ)

/-- On a good challenge vector, all q coherent trajectories survive with this
single cumulative tail; no independence between rounds is assumed. -/
theorem fresh_tail (s : Words) (q : ℕ) {θ : ℝ} (hθmax : θ < 7/16)
    (hfar : ¬close θ (reedSolomonCode (domain 0) (degree 0)) s.input)
    (r : Fin 5 → Ext4) (hgood : ¬∃ j, BadRound s θ j r) :
    uniformProb (Fin q → BabyBear) (FreshAccepts s q r) ≤ (queryTail θ)^q := by
  have hremain : 0 ≤ 1-θ := by linarith
  have htail : 0 ≤ queryTail θ := by unfold queryTail modulus; positivity
  by_cases ht : Terminal s r
  · have hm := terminal_mass s θ hfar r hgood ht
    rw [weightAt_eq_counted] at hm
    have hc : (0:ℝ) < Fintype.card (Index 5) := by norm_num [Index,stage]
    have hf : terminalFraction (initialMask s) (stepMasks s r) ≤ 1-θ := by
      exact ((div_lt_iff₀ hc).mpr hm).le
    have hn : 0 ≤ terminalFraction (initialMask s) (stepMasks s r) := by
      rw [←raw_probability_exact]
      exact uniformProb_nonneg _
    have hbase : 0 ≤ (((modulus-1:ℕ):ℝ)/(modulus:ℝ))*
        terminalFraction (initialMask s) (stepMasks s r)+1/(modulus:ℝ) := by positivity
    have hb : (((modulus-1:ℕ):ℝ)/(modulus:ℝ))*
        terminalFraction (initialMask s) (stepMasks s r)+1/(modulus:ℝ) ≤ queryTail θ := by
      unfold queryTail
      have hc0 : 0 ≤ (((modulus-1:ℕ):ℝ)/(modulus:ℝ)) := by norm_num [modulus]
      linarith [mul_le_mul_of_nonneg_left hf hc0]
    exact le_trans (uniformProb_mono fun _ h => h.2)
      ((fresh_query_bound (initialMask s) (stepMasks s r) q).trans
        (pow_le_pow_left₀ hbase hb q))
  · rw [uniformProb_false (fun _ h => ht h.1)]
    exact pow_nonneg htail q

/-- Source-degree 16384 on the actual order-131072 subgroup, with prefix-adaptive
committed words, a constant terminal word, five independent Ext4 challenges,
and 38 (or q) independent fresh base-field sample words. The initial word is
the alpha-reduced PCS input, not the separately committed first FRI word. -/
theorem fresh_sound (s : Words) (q : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθmax : θ < 7/16)
    (hfar : ¬close θ (reedSolomonCode (domain 0) (degree 0)) s.input) :
    uniformProb ((Fin 5 → Ext4) × (Fin q → BabyBear))
      (fun x => FreshAccepts s q x.1 x.2) ≤
      (131064:ℝ)/(modulus^4:ℕ)+(queryTail θ)^q := by
  let bad : (Fin 5 → Ext4) → Prop := fun r => ∃ j, BadRound s θ j r
  have hb := bad_schedule_bound s hθ hθmax
  have hremain : 0 ≤ 1-θ := by linarith
  have ht : 0 ≤ queryTail θ := by unfold queryTail modulus; positivity
  have hq : uniformProb ((Fin 5 → Ext4) × (Fin q → BabyBear))
      (fun x => ¬bad x.1 ∧ FreshAccepts s q x.1 x.2) ≤ (queryTail θ)^q := by
    apply uniformProb_prod_le (pow_nonneg ht q)
    intro r
    by_cases hbad : bad r
    · rw [uniformProb_false (fun _ h => h.1 hbad)]
      exact pow_nonneg ht q
    · exact le_trans (uniformProb_mono fun _ h => h.2) (fresh_tail s q hθmax hfar r hbad)
  have hsplit : uniformProb ((Fin 5 → Ext4) × (Fin q → BabyBear))
      (fun x => FreshAccepts s q x.1 x.2) ≤
      uniformProb ((Fin 5 → Ext4) × (Fin q → BabyBear)) (fun x => bad x.1)+
      uniformProb ((Fin 5 → Ext4) × (Fin q → BabyBear))
        (fun x => ¬bad x.1 ∧ FreshAccepts s q x.1 x.2) := by
    refine le_trans (uniformProb_mono fun x hx => ?_) (uniformProb_or_le _ _)
    by_cases hbad : bad x.1
    · exact Or.inl hbad
    · exact Or.inr ⟨hbad,hx⟩
  rw [ArityEight.TwoRound.uniform_fst (B := Fin q → BabyBear) bad] at hsplit
  change uniformProb (Fin 5 → Ext4) bad ≤ _ at hb
  linarith

/-- Concrete observed query count and a source-proximity radius strictly inside
full unique decoding for the actual rate 1/8. No PoW or cryptographic term is credited. -/
theorem fresh_38 (s : Words)
    (hfar : ¬close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0)) s.input) :
    uniformProb ((Fin 5 → Ext4) × (Fin 38 → BabyBear))
      (fun x => FreshAccepts s 38 x.1 x.2) ≤
      (131064:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38 := by
  convert fresh_sound s 38 (by norm_num : (0:ℝ)<2/5) (by norm_num : (2/5:ℝ)<7/16) hfar using 1
  norm_num [queryTail]

/-- Same final check written with the literal native P3 row interpolation kernel. -/
def NativeFreshAccepts (s : Words) (q : ℕ) (r : Fin 5 → Ext4) (raw : Fin q → BabyBear) : Prop :=
  Terminal s r ∧ NativeQueryAccepts s r q
    (fun a => BabyBearModuloSampling.sampleBits 17 (raw a))

/-- This equivalence is proved for arbitrary field values, rows and challenges;
it is not inferred from the one successful runtime replay. -/
theorem native_fresh_iff (s : Words) (q : ℕ) (r : Fin 5 → Ext4) (raw : Fin q → BabyBear) :
    NativeFreshAccepts s q r raw ↔ FreshAccepts s q r raw := by
  unfold NativeFreshAccepts FreshAccepts Accepts
  rw [native_query_iff_counted]

/-- The observed query count, actual native row kernel and actual biased fresh
query-word law, conditional on an extracted far PCS input and prefix-fixed words. -/
theorem native_fresh_38 (s : Words)
    (hfar : ¬close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0)) s.input) :
    uniformProb ((Fin 5 → Ext4) × (Fin 38 → BabyBear))
      (fun x => NativeFreshAccepts s 38 x.1 x.2) ≤
      (131064:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38 := by
  rw [uniformProb_congr (fun (x : (Fin 5 → Ext4) × (Fin 38 → BabyBear)) => native_fresh_iff s 38 x.1 x.2)]
  exact fresh_38 s hfar

end
end Minidregg.Selvage.Ir2Fri

/-- info: 'Minidregg.Selvage.Ir2Fri.fresh_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.fresh_tail

/-- info: 'Minidregg.Selvage.Ir2Fri.fresh_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.fresh_sound

/-- info: 'Minidregg.Selvage.Ir2Fri.fresh_38' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.fresh_38

/-- info: 'Minidregg.Selvage.Ir2Fri.native_fresh_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_fresh_iff

/-- info: 'Minidregg.Selvage.Ir2Fri.native_fresh_38' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_fresh_38

