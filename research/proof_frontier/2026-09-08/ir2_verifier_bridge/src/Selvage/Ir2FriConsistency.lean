/- Exact supplied-mask consistency for the concrete [3,3,3,3,2] replay.
No word, code, farness, or desired probability-bound hypothesis is hidden here. -/
import Selvage.Ir2FriSchedule

namespace Minidregg.Selvage.Ir2FriSchedule
open scoped BigOperators Classical

/-- A caller supplies the actual next-word/native-fold equality at each next-row index. -/
abbrev Mask := (n : Fin 5) → Index (n+1) → Prop

/-- Average the previous consistency weights over the actual projected fibre. -/
noncomputable def projectWeight (n : Fin 5) (w : Index n → ℝ) (k : Index (n+1)) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => project n i = k), w i)/(radix n:ℝ)

/-- The initial reduced-input/committed-word equality masks source weights; every later
fibre average is masked by its supplied next-row equation. -/
noncomputable def weight (initial : Index 0 → Prop) (mask : Mask) : (n : ℕ) → n ≤ 5 → Index n → ℝ
  | 0, _, i => if initial i then 1 else 0
  | n+1, hn, k => if mask ⟨n,by omega⟩ k then
      projectWeight ⟨n,by omega⟩ (weight initial mask n (by omega)) k else 0

/-- The same supplied equations pulled back to one full natural source index. -/
def sourceChecks (initial : Index 0 → Prop) (mask : Mask) : (n : ℕ) → n ≤ 5 → Index 0 → Prop
  | 0, _, i => initial i
  | n+1, hn, i => sourceChecks initial mask n (by omega) i ∧
      mask ⟨n,by omega⟩ (naturalIndex (n+1) i)

/-- Statement-first exact counting contract at every prefix and terminal subset. -/
def MassContract (initial : Index 0 → Prop) (mask : Mask) : Prop := ∀ n (hn : n ≤ 5) (S : Finset (Index n)),
  consistencyMass (weight initial mask n hn) S * (2:ℝ)^(stage n) =
    ((Finset.univ.filter fun i => sourceChecks initial mask n hn i ∧ naturalIndex n i ∈ S).card:ℝ)

/-- This recurrence exposes precisely the caller's next-row equality mask. -/
theorem weight_succ (initial : Index 0 → Prop) (mask : Mask) (n : Fin 5) :
    weight initial mask (n+1) (by omega) = fun k =>
      if mask n k then projectWeight n (weight initial mask n (by omega)) k else 0 := rfl

/-- Projected subset mass is the preimage mass divided by the actual round radix. -/
theorem projectWeight_mass (n : Fin 5) (w : Index n → ℝ) (S : Finset (Index (n+1))) :
    consistencyMass (projectWeight n w) S =
      consistencyMass w (Finset.univ.filter fun i => project n i ∈ S)/(radix n:ℝ) := by
  unfold consistencyMass projectWeight
  rw [←Finset.sum_div]
  exact congrArg (fun x : ℝ => x/(radix n:ℝ))
    (Finset.sum_fiberwise_eq_sum_filter Finset.univ S (project n) w)

theorem projectWeight_nonneg (n : Fin 5) (w : Index n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (k : Index (n+1)) : 0 ≤ projectWeight n w k := by
  exact div_nonneg (Finset.sum_nonneg fun i _ => hw i) (by positivity)

/-- The proved fibre count ensures projected bounded weights stay bounded. -/
theorem projectWeight_le_one (n : Fin 5) (w : Index n → ℝ) (hw : ∀ i, w i ≤ 1)
    (k : Index (n+1)) : projectWeight n w k ≤ 1 := by
  have hm := consistencyMass_le_card w hw (Finset.univ.filter fun i => project n i = k)
  rw [project_fiber_card] at hm
  have hr : (0:ℝ) < radix n := by exact_mod_cast radix_positive n
  exact (div_le_one hr).mpr hm

theorem weight_nonneg (initial : Index 0 → Prop) (mask : Mask) (n : ℕ) (hn : n ≤ 5) :
    ∀ i, 0 ≤ weight initial mask n hn i := by
  induction n with
  | zero => intro i; unfold weight; split_ifs <;> norm_num
  | succ n ih =>
    intro i
    rw [weight]
    split_ifs
    · exact projectWeight_nonneg _ _ (ih (by omega)) _
    · exact le_rfl

theorem weight_le_one (initial : Index 0 → Prop) (mask : Mask) (n : ℕ) (hn : n ≤ 5) :
    ∀ i, weight initial mask n hn i ≤ 1 := by
  induction n with
  | zero => intro i; unfold weight; split_ifs <;> norm_num
  | succ n ih =>
    intro i
    rw [weight]
    split_ifs
    · exact projectWeight_le_one _ _ (ih (by omega)) _
    · norm_num

/-- One mask step retains exactly its passing fibre preimage mass. -/
theorem weight_mass_succ (initial : Index 0 → Prop) (mask : Mask) (n : Fin 5) (S : Finset (Index (n+1))) :
    consistencyMass (weight initial mask (n+1) (by omega)) S =
      consistencyMass (weight initial mask n (by omega))
        (Finset.univ.filter fun i => project n i ∈ S ∧ mask n (project n i))/(radix n:ℝ) := by
  have hm : consistencyMass (weight initial mask (n+1) (by omega)) S =
      consistencyMass (projectWeight n (weight initial mask n (by omega))) (S.filter (mask n)) := by
    rw [weight_succ]
    simp [consistencyMass,Finset.sum_filter]
  rw [hm,projectWeight_mass]
  simp only [Finset.mem_filter]

/-- The exact source count is derived for the supplied masks, with no event-bound premise. -/
theorem consistency_mass_exact (initial : Index 0 → Prop) (mask : Mask) : MassContract initial mask := by
  intro n
  induction n with
  | zero =>
    intro hn S
    change (∑ i ∈ S, if initial i then (1:ℝ) else 0) * (2:ℝ)^0 =
      ((Finset.univ.filter fun i => initial i ∧ naturalIndex 0 i ∈ S).card:ℝ)
    simp only [pow_zero,mul_one,naturalIndex_zero]
    have hs : (Finset.univ.filter fun i => initial i ∧ i ∈ S) = S.filter initial := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact and_comm
    rw [Finset.sum_boole,hs]
  | succ n ih =>
    intro hn S
    let j : Fin 5 := ⟨n,by omega⟩
    have hfactor : (2:ℝ)^(stage (n+1)) = (radix j:ℝ)*(2:ℝ)^(stage n) := by
      exact_mod_cast stage_factor j
    rw [weight_mass_succ initial mask j,hfactor]
    have h := ih (by omega) (Finset.univ.filter fun i =>
      project j i ∈ S ∧ mask j (project j i))
    have hset : (Finset.univ.filter fun i => sourceChecks initial mask n (by omega) i ∧
        naturalIndex n i ∈ (Finset.univ.filter fun k => project j k ∈ S ∧ mask j (project j k))) =
        (Finset.univ.filter fun i => sourceChecks initial mask (n+1) hn i ∧ naturalIndex (n+1) i ∈ S) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,sourceChecks]
      rw [project_naturalIndex]
      dsimp [j]
      tauto
    rw [hset] at h
    rw [←h]
    have hr : (radix j:ℝ) ≠ 0 := by exact_mod_cast (radix_positive j).ne'
    field_simp
    rfl

/-- Prefix checks are exactly the conjunction of the supplied round masks. -/
theorem sourceChecks_iff_all (initial : Index 0 → Prop) (mask : Mask) (n : ℕ) (hn : n ≤ 5) (i : Index 0) :
    sourceChecks initial mask n hn i ↔ initial i ∧ ∀ j : Fin n,
      mask ⟨j,by omega⟩ (naturalIndex (j+1) i) := by
  induction n with
  | zero => simp [sourceChecks]
  | succ n ih =>
    rw [sourceChecks,Fin.forall_fin_succ',ih (by omega)]
    tauto

/-- Normalized mass of all currently consistent source trajectories. -/
noncomputable def terminalFraction (initial : Index 0 → Prop) (mask : Mask) : ℝ :=
  consistencyMass (weight initial mask 5 le_rfl) Finset.univ / (Fintype.card (Index 5):ℝ)

/-- One uniform full natural source index survives with exactly the terminal mass fraction. -/
theorem source_probability_exact (initial : Index 0 → Prop) (mask : Mask) :
    uniformProb (Index 0) (sourceChecks initial mask 5 le_rfl) = terminalFraction initial mask := by
  have h := consistency_mass_exact initial mask 5 le_rfl Finset.univ
  simp only [Finset.mem_univ,and_true] at h
  unfold uniformProb terminalFraction
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,←h]
  norm_num [Index,stage]
  ring

/-- One raw query checks the initial reduced-input equality and every later row equation. -/
def rawSurvives (initial : Index 0 → Prop) (mask : Mask) (raw : Fin (2^17)) : Prop :=
  initial (sourceIndex raw) ∧ ∀ n : Fin 5, mask n (runtimeIndex (n+1) raw)

/-- The exact native consistency checks for a batch of full-source raw queries. -/
def QueryAccepts (initial : Index 0 → Prop) (mask : Mask) (q : ℕ)
    (raw : Fin q → Fin (2^17)) : Prop :=
  (∀ a, initial (sourceIndex (raw a))) ∧
    ∀ n : Fin 5, ∀ a, mask n (runtimeIndex (n+1) (raw a))

/-- Batch checks are the conjunction of their full single-query paths. -/
theorem QueryAccepts_iff_all (initial : Index 0 → Prop) (mask : Mask) (q : ℕ)
    (raw : Fin q → Fin (2^17)) :
    QueryAccepts initial mask q raw ↔ ∀ a, rawSurvives initial mask (raw a) := by
  constructor
  · rintro ⟨hi,hm⟩ a
    exact ⟨hi a,fun n => hm n a⟩
  · intro h
    exact ⟨fun a => (h a).1,fun n a => (h a).2 n⟩

/-- Exact runtime-to-natural predicate correspondence, including the initial equality. -/
theorem rawSurvives_iff_sourceChecks (initial : Index 0 → Prop) (mask : Mask)
    (raw : Fin (2^17)) :
    rawSurvives initial mask raw ↔ sourceChecks initial mask 5 le_rfl (sourceIndex raw) := by
  rw [sourceChecks_iff_all]
  simp only [rawSurvives,runtimeIndex_eq_naturalIndex]

/-- A uniform raw source query has exactly the same terminal consistency fraction. -/
theorem raw_probability_exact (initial : Index 0 → Prop) (mask : Mask) :
    uniformProb (Fin (2^17)) (rawSurvives initial mask) = terminalFraction initial mask := by
  calc
    _ = uniformProb (Fin (2^17)) (fun raw => sourceChecks initial mask 5 le_rfl (sourceEquiv raw)) :=
      uniformProb_congr (rawSurvives_iff_sourceChecks initial mask)
    _ = uniformProb (Index 0) (sourceChecks initial mask 5 le_rfl) :=
      uniformProb_equiv sourceEquiv _
    _ = _ := source_probability_exact initial mask

/-- q shared coherent trajectories are independent only across full raw source coordinates. -/
theorem coherent_query_exact (initial : Index 0 → Prop) (mask : Mask) (q : ℕ) :
    uniformProb (Fin q → Fin (2^17)) (QueryAccepts initial mask q) =
      (terminalFraction initial mask)^q := by
  calc
    _ = uniformProb (Fin q → Fin (2^17))
        (fun raw => ∀ a, rawSurvives initial mask (raw a)) :=
      uniformProb_congr (QueryAccepts_iff_all initial mask q)
    _ = _ := by
      rw [ArityEight.Schedule.uniformProb_all_coordinates q (rawSurvives initial mask),
        raw_probability_exact]

/-- The same concrete event under q fresh uniform actual BabyBear words,
with the vendor canonical modulo bias retained exactly. -/
theorem fresh_query_exact (initial : Index 0 → Prop) (mask : Mask) (q : ℕ) :
    uniformProb (Fin q → BabyBearExt4.BabyBear)
      (fun x => QueryAccepts initial mask q (fun a => BabyBearModuloSampling.sampleBits 17 (x a))) =
      ((((BabyBearExt4.modulus-1:ℕ):ℝ)/BabyBearExt4.modulus * terminalFraction initial mask) +
        (if rawSurvives initial mask 0 then 1/(BabyBearExt4.modulus:ℝ) else 0))^q := by
  calc
    _ = uniformProb (Fin q → BabyBearExt4.BabyBear)
        (fun x => ∀ a, rawSurvives initial mask (BabyBearModuloSampling.sampleBits 17 (x a))) :=
      uniformProb_congr (fun x => QueryAccepts_iff_all initial mask q _)
    _ = _ := by
      rw [BabyBearModuloSampling.fresh_bits_independent_exact 17 (by decide) q
        (rawSurvives initial mask),raw_probability_exact]
      rfl

/-- Conservative actual fresh-base query law, retaining the initial equality and modulo bias. -/
theorem fresh_query_bound (initial : Index 0 → Prop) (mask : Mask) (q : ℕ) :
    uniformProb (Fin q → BabyBearExt4.BabyBear)
      (fun x => QueryAccepts initial mask q (fun a => BabyBearModuloSampling.sampleBits 17 (x a))) ≤
      ((((BabyBearExt4.modulus-1:ℕ):ℝ)/BabyBearExt4.modulus * terminalFraction initial mask) +
        1/(BabyBearExt4.modulus:ℝ))^q := by
  calc
    _ = uniformProb (Fin q → BabyBearExt4.BabyBear)
        (fun x => ∀ a, rawSurvives initial mask (BabyBearModuloSampling.sampleBits 17 (x a))) :=
      uniformProb_congr (fun x => QueryAccepts_iff_all initial mask q _)
    _ ≤ _ := BabyBearModuloSampling.fresh_bits_independent_bound 17 (by decide) q
      (rawSurvives initial mask) (terminalFraction initial mask) (raw_probability_exact initial mask).le

/-- The initial weights are exactly the carried-value/source-word equality indicator. -/
theorem weight_zero (initial : Index 0 → Prop) (mask : Mask) :
    weight initial mask 0 (by decide) = fun i => if initial i then 1 else 0 := rfl

/-- Concrete supplied masks: the first four rounds pass and the final row must be zero. -/
def finalZeroMask : Mask := fun n k => n.val < 4 ∨ k.val = 0

/-- The actual full-source zero query passes these supplied masks. -/
theorem final_zero_accepts : rawSurvives (fun _ => True) finalZeroMask 0 := by
  refine ⟨trivial,?_⟩
  intro n
  fin_cases n <;> unfold finalZeroMask <;> decide

/-- Raw bit 16 reaches natural terminal row one, which the same masks reject. -/
theorem final_zero_rejects :
    ¬rawSurvives (fun _ => True) finalZeroMask (⟨2^16,by decide⟩ : Fin (2^17)) := by
  intro h
  have hf := h.2 ⟨4,by decide⟩
  have hn : ¬finalZeroMask ⟨4,by decide⟩
      (runtimeIndex 5 (⟨2^16,by decide⟩ : Fin (2^17))) := by
    unfold finalZeroMask
    decide
  exact hn hf

/-- Statement-first inhabited counting premises include both actual-source acceptance poles. -/
def PremisesInhabited : Prop := ∃ (initial : Index 0 → Prop) (mask : Mask),
  MassContract initial mask ∧ rawSurvives initial mask 0 ∧
    ¬rawSurvives initial mask (⟨2^16,by decide⟩ : Fin (2^17))

theorem premises_inhabited : PremisesInhabited :=
  ⟨fun _ => True,finalZeroMask,consistency_mass_exact _ _,final_zero_accepts,final_zero_rejects⟩

/-- Teeth for the observed 38-query verifier: omitting the initial carried-value
check accepts a batch that the complete consistency predicate rejects. -/
theorem initial_omission_falsifier :
    QueryAccepts (fun _ => True) (fun _ _ => True) 38 (fun _ => 0) ∧
    ¬QueryAccepts (fun _ => False) (fun _ _ => True) 38 (fun _ => 0) := by
  constructor
  · exact ⟨fun _ => trivial,fun _ _ => trivial⟩
  · intro h
    exact h.1 0

end Minidregg.Selvage.Ir2FriSchedule

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.weight_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.weight_succ

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.projectWeight_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.projectWeight_mass

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.projectWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.projectWeight_nonneg

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.projectWeight_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.projectWeight_le_one

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.weight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.weight_nonneg

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.weight_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.weight_le_one

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.weight_mass_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.weight_mass_succ

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.consistency_mass_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.consistency_mass_exact

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.sourceChecks_iff_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.sourceChecks_iff_all

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.source_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.source_probability_exact

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.QueryAccepts_iff_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.QueryAccepts_iff_all

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.rawSurvives_iff_sourceChecks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.rawSurvives_iff_sourceChecks

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.raw_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.raw_probability_exact

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.coherent_query_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.coherent_query_exact

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.fresh_query_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.fresh_query_exact

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.fresh_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.fresh_query_bound

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.weight_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.weight_zero

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.final_zero_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.final_zero_accepts

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.final_zero_rejects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.final_zero_rejects

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.premises_inhabited

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.initial_omission_falsifier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.initial_omission_falsifier

