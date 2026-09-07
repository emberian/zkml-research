/-
A closed source-equation window theorem at Q83. Ghost records contain source
messages and small factors; they are not the host's ciphertext state format.
The theorem constructs the quotient-ring phase and derives its bounded lift.
The output is exact mathematical phase/round-half-up, not the Rust scaler.
Bounded source coefficients are explicit ghost premises; sampler, RNS, NTT,
serialization, admitted provenance and decoder refinement remain unproved.
No confidentiality or restricted release claim.
-/
import Theory.BfvNoiseSource
import Assurance.ResidentBfvSourcePhase

namespace Minidregg.Assurance.ResidentBfvSourceWindow
set_option autoImplicit false
open Minidregg.Theory.BfvPhaseAlgebra
open Minidregg.Theory.BfvNoiseSource
open Minidregg.Theory.IntegerWindowNoise (Row Fresh centered rounded queryL1 queryL1_le)
open Minidregg.Assurance.ResidentBfvWindowNoise
open Minidregg.Assurance.ResidentBfvSourcePhase (Q N R delta delta_inverse)

abbrev Coeffs := Fin N → Int
structure Input where
  message : Coeffs
  u : Coeffs
  e1 : Coeffs
  e2 : Coeffs

def Bounded (v : Coeffs) : Prop := ∀ j, |v j| ≤ support

def Allowed (x : Input) : Prop := Bounded x.u ∧ Bounded x.e1 ∧ Bounded x.e2 ∧
  ∀ j : Fin 577, |x.message (prefixIndex N 576 (by decide) j)| ≤ coordinateBound

noncomputable def inputCipher (s e : Coeffs) (a : R) (x : Input) : CipherPair R :=
  encrypt (keygen (ringVector Q N s) a (ringVector Q N e))
    (ringVector Q N x.u) (ringVector Q N x.e1) (ringVector Q N x.e2)
    (encodeRing Q N t32 delta x.message)

def inputRow (s e : Coeffs) (x : Input) : Row 577 :=
  integerRow Q N t32 576 (by decide) x.message (integerNoise s e x.u x.e1 x.e2)

noncomputable def accumulator (s e : Coeffs) (a : R) (xs : List Input) : CipherPair R :=
  (xs.map (inputCipher s e a)).sum

noncomputable def phaseMap (s : Coeffs) (query : Fin 577 → Int) : CipherPair R →+ ZMod Q :=
  Minidregg.Theory.BfvPhaseAlgebra.readoutPhase Q N (ringVector Q N s)
    (AdjoinRoot.mk (modulus Q N) (reverseQuery Q 576 (fun j => (query j : ZMod Q)))) 576

noncomputable def outputLift (s e : Coeffs) (a : R) (xs : List Input) (query : Fin 577 → Int) : Int :=
  (phaseMap s query (accumulator s e a xs)).val

def SourceWindowCorrectness : Prop :=
  ∀ (s e : Coeffs) (a : R) (xs : List Input) (query : Fin 577 → Int),
    Bounded s → Bounded e → (∀ x ∈ xs, Allowed x) → xs.length ≤ window →
    (∀ j, |query j| ≤ coordinateBound) →
    centered t32 (rounded q83 t32 (outputLift s e a xs query)) =
      Minidregg.Theory.IntegerWindowNoise.readoutScore query (xs.map (inputRow s e))

def SourceWindow32Correctness : Prop :=
  ∀ (s e : Coeffs) (a : R) (xs : List Input) (query : Fin 577 → Int),
    Bounded s → Bounded e → (∀ x ∈ xs, Allowed x) → xs.length ≤ 32 →
    (∀ j, |query j| ≤ coordinateBound) →
    centered t32 (rounded q83 t32 (outputLift s e a xs query)) =
      Minidregg.Theory.IntegerWindowNoise.readoutScore query (xs.map (inputRow s e))

def scoreBudget32 : Int := 32 * queryBudget * coordinateBound

theorem margin32 : 2 * t32 * 32 * queryBudget * (freshBound + 1) < q83 := by decide

theorem exact32_budgets :
    2 * t32 * 32 * queryBudget * (freshBound + 1) = 66002138248631957244608 ∧
    scoreBudget32 = 297805856 ∧ 2 * scoreBudget32 < t32 := by decide

theorem input_fresh (s e : Coeffs) (x : Input)
    (hs : Bounded s) (he : Bounded e) (hx : Allowed x) :
    Fresh q83 t32 freshBound (inputRow s e x) := by
  apply integerRow_fresh Q N t32 freshBound 576 (by decide)
  intro j
  exact integerNoise_bound s e x.u x.e1 x.e2 support (by decide) hs he hx.1 hx.2.1 hx.2.2.1 j

theorem input_phase (s e : Coeffs) (a : R) (x : Input) (query : Fin 577 → Int) :
    phaseMap s query (inputCipher s e a x) =
      (Minidregg.Theory.IntegerWindowNoise.rowPhase query (inputRow s e x) : ZMod Q) := by
  exact encrypted_integer_row Q N (ringVector Q N s) a (ringVector Q N e)
    (ringVector Q N x.u) (ringVector Q N x.e1) (ringVector Q N x.e2) t32 delta
    x.message (integerNoise s e x.u x.e1 x.e2) 576 query (by decide) (by decide)
    delta_inverse (noise_coefficient_lift Q N s e x.u x.e1 x.e2)

theorem accumulator_phase (s e : Coeffs) (a : R) (xs : List Input) (query : Fin 577 → Int) :
    phaseMap s query (accumulator s e a xs) =
      (Minidregg.Theory.IntegerWindowNoise.readoutPhase query (xs.map (inputRow s e)) : ZMod Q) := by
  induction xs with
  | nil => simp [accumulator, Minidregg.Theory.IntegerWindowNoise.readoutPhase]
  | cons x xs ih =>
    change phaseMap s query (inputCipher s e a x + accumulator s e a xs) = _
    rw [map_add, input_phase, ih]
    simp only [Minidregg.Theory.IntegerWindowNoise.readoutPhase, List.map_cons, List.sum_cons, Int.cast_add]

theorem output_lift_exists (s e : Coeffs) (a : R) (xs : List Input) (query : Fin 577 → Int) :
    ∃ wrap : Int, outputLift s e a xs query =
      Minidregg.Theory.IntegerWindowNoise.readoutPhase query (xs.map (inputRow s e)) + q83 * wrap := by
  have h := accumulator_phase s e a xs query
  have hv : (outputLift s e a xs query : ZMod Q) =
      (Minidregg.Theory.IntegerWindowNoise.readoutPhase query (xs.map (inputRow s e)) : ZMod Q) := by
    simpa [outputLift] using h
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (Minidregg.Theory.IntegerWindowNoise.readoutPhase query (xs.map (inputRow s e)))
    (outputLift s e a xs query) Q).mp hv.symm
  obtain ⟨wrap, hw⟩ := hd
  exact ⟨wrap, by change _ = _ + (Q : Int) * wrap; linarith⟩

theorem rows_actual_premises (s e : Coeffs) (xs : List Input) (query : Fin 577 → Int)
    (hs : Bounded s) (he : Bounded e) (ha : ∀ x ∈ xs, Allowed x)
    (hlen : xs.length ≤ window) (hq : ∀ j, |query j| ≤ coordinateBound) :
    ActualPremises (xs.map (inputRow s e)) query := by
  refine ⟨?_, by simpa using hlen, hq, ?_⟩
  · intro row hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact input_fresh s e x hs he (ha x hx)
  · intro row hr j
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact (ha x hx).2.2.2 j

theorem source_window_correctness : SourceWindowCorrectness := by
  intro s e a xs query hs he ha hlen hq
  obtain ⟨wrap, hw⟩ := output_lift_exists s e a xs query
  rw [hw]
  exact actual_signed_window (xs.map (inputRow s e)) query wrap
    (rows_actual_premises s e xs query hs he ha hlen hq)

/-- Concrete capacity32 contract for the useful577-coordinate learner.
The smaller window's own noise and signed-range margins are used. -/
theorem source_window32_correctness : SourceWindow32Correctness := by
  intro s e a xs query hs he ha hlen hq
  have h128 : xs.length ≤ window := hlen.trans (by decide)
  have hp := rows_actual_premises s e xs query hs he ha h128 hq
  have hL : queryL1 query ≤ queryBudget := queryL1_le query coordinateBound hq
  have hlen' : (xs.map (inputRow s e)).length ≤ 32 := by simpa only [List.length_map] using hlen
  have hn : ((xs.map (inputRow s e)).length : Int) ≤ 32 := by exact_mod_cast hlen'
  have h0 : 0 ≤ queryL1 query := Finset.sum_nonneg (by intro j _; exact abs_nonneg _)
  have hb := Minidregg.Theory.IntegerWindowNoise.readout_score_bound query
    (xs.map (inputRow s e)) coordinateBound hp.2.2.2
  have hscore : |Minidregg.Theory.IntegerWindowNoise.readoutScore query (xs.map (inputRow s e))| ≤ scoreBudget32 := by
    calc
      _ ≤ ((xs.map (inputRow s e)).length : Int) * (queryL1 query * coordinateBound) := hb
      _ ≤ (32 : Int) * (queryBudget * coordinateBound) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_right hL (by decide))
          (mul_nonneg h0 (by decide)) (by decide)
      _ = scoreBudget32 := by unfold scoreBudget32; ring
  obtain ⟨wrap, hw⟩ := output_lift_exists s e a xs query
  rw [hw]
  apply Minidregg.Theory.IntegerWindowNoise.window_signed_correctness
    q83 t32 freshBound queryBudget 32 (by decide) (by decide) (by decide) margin32
    (xs.map (inputRow s e)) query wrap hp.1 hlen' hL
  have hnwrap := exact32_budgets.2.2
  omega

/-- A nonzero full-support premise inhabitant at the support edge. The
arithmetic bound allows correlated/repeated factors; it assumes no sampling
independence and makes no typical-key or security claim. -/
def twenties : Coeffs := fun _ => 20
def oneInput : Input := ⟨fun _ => 1, twenties, twenties, twenties⟩
def inputs : List Input := List.replicate window oneInput

theorem twenties_bounded : Bounded twenties := by
  intro j
  change |(20 : Int)| ≤ 20
  norm_num

theorem one_allowed : Allowed oneInput := by
  refine ⟨twenties_bounded, twenties_bounded, twenties_bounded, ?_⟩
  intro j
  change |(1 : Int)| ≤ 127
  norm_num

theorem rows_nonzero_score :
    Minidregg.Theory.IntegerWindowNoise.readoutScore witnessQuery
      (inputs.map (inputRow twenties twenties)) = -128 := by
  have hr : Minidregg.Theory.IntegerWindowNoise.rowScore witnessQuery (inputRow twenties twenties oneInput) = -1 := by
    unfold Minidregg.Theory.IntegerWindowNoise.rowScore
    simp [witnessQuery, inputRow, integerRow, oneInput]
  simp [Minidregg.Theory.IntegerWindowNoise.readoutScore, inputs, hr, window]

theorem full_window_nonzero_subject :
    centered t32 (rounded q83 t32 (outputLift twenties twenties 7 inputs witnessQuery)) = -128 := by
  have ha : ∀ x ∈ inputs, Allowed x := by
    intro x hx
    have heq : x = oneInput := by simpa [inputs, window] using hx
    rw [heq]
    exact one_allowed
  have h := source_window_correctness twenties twenties 7 inputs witnessQuery
    twenties_bounded twenties_bounded ha (by simp [inputs]) witness_premises.2.2.1
  exact h.trans rows_nonzero_score

def inputs32 : List Input := List.replicate 32 oneInput

theorem rows32_nonzero_score :
    Minidregg.Theory.IntegerWindowNoise.readoutScore witnessQuery
      (inputs32.map (inputRow twenties twenties)) = -32 := by
  have hr : Minidregg.Theory.IntegerWindowNoise.rowScore witnessQuery (inputRow twenties twenties oneInput) = -1 := by
    unfold Minidregg.Theory.IntegerWindowNoise.rowScore
    simp [witnessQuery, inputRow, integerRow, oneInput]
  simp [Minidregg.Theory.IntegerWindowNoise.readoutScore, inputs32, hr]

theorem window32_nonzero_subject :
    centered t32 (rounded q83 t32 (outputLift twenties twenties 7 inputs32 witnessQuery)) = -32 := by
  have ha : ∀ x ∈ inputs32, Allowed x := by
    intro x hx
    have heq : x = oneInput := by simpa [inputs32] using hx
    rw [heq]
    exact one_allowed
  have h := source_window32_correctness twenties twenties 7 inputs32 witnessQuery
    twenties_bounded twenties_bounded ha (by simp [inputs32]) witness_premises.2.2.1
  exact h.trans rows32_nonzero_score

theorem window32_ciphertext_nonzero : accumulator twenties twenties 7 inputs32 ≠ 0 := by
  intro hz
  have h := window32_nonzero_subject
  simp only [outputLift, hz, map_zero, ZMod.val_zero, Nat.cast_zero] at h
  have hzero : centered t32 (rounded q83 t32 0) = 0 := by decide
  rw [hzero] at h
  omega

def oversizedInput : Input := ⟨fun _ => 128, twenties, twenties, twenties⟩

theorem oversized_message_refused : ¬Allowed oversizedInput := by
  intro h
  have hm := h.2.2.2 (0 : Fin 577)
  change |(128 : Int)| ≤ 127 at hm
  norm_num at hm

/-- The existing worst-case N expansion is attained, not a guessed heuristic. -/
theorem convolution_constant_last (n : Nat) (hn : 0 < n) (S : Int) :
    convolution (fun _ : Fin n => S) (fun _ : Fin n => S) ⟨n - 1, by omega⟩ = (n : Int) * S ^ 2 := by
  unfold convolution
  have h : ∀ i : Fin n, i.val ≤ (⟨n - 1, by omega⟩ : Fin n).val := by intro i; have := i.isLt; dsimp; omega
  simp only [h, if_true]
  simp [pow_two]

theorem actual_fresh_bound_attained :
    integerNoise twenties twenties twenties twenties twenties ⟨4095, by decide⟩ = 3276820 := by
  have hc := convolution_constant_last N (by decide) 20
  change convolution (fun _ : Fin N => (20 : Int)) (fun _ : Fin N => 20)
    ⟨4095, by decide⟩ = (4096 : Int) * 20 ^ 2 at hc
  unfold integerNoise twenties
  rw [hc]
  norm_num

theorem smaller_global_noise_bound_fails :
    ¬(∀ j, |integerNoise twenties twenties twenties twenties twenties j| ≤ freshBound - 1) := by
  intro h
  have hj := h ⟨4095, by decide⟩
  rw [actual_fresh_bound_attained, actual_fresh_bound] at hj
  norm_num at hj

theorem cyclic_sign_is_false :
    convolution (fun i : Fin 2 => if i = 1 then (1 : Int) else 0)
      (fun i : Fin 2 => if i = 1 then (1 : Int) else 0) 0 = -1 := by decide

/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.margin32' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.margin32
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.exact32_budgets' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.exact32_budgets
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.input_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.input_fresh
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.input_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.input_phase
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.accumulator_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.accumulator_phase
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.output_lift_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.output_lift_exists
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.rows_actual_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.rows_actual_premises
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.source_window_correctness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.source_window_correctness
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.source_window32_correctness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.source_window32_correctness
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.twenties_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.twenties_bounded
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.one_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.one_allowed
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.rows_nonzero_score' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.rows_nonzero_score
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.full_window_nonzero_subject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.full_window_nonzero_subject
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.rows32_nonzero_score' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.rows32_nonzero_score
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.window32_nonzero_subject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.window32_nonzero_subject
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.window32_ciphertext_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.window32_ciphertext_nonzero
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.oversized_message_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.oversized_message_refused
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.convolution_constant_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.convolution_constant_last
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.actual_fresh_bound_attained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.actual_fresh_bound_attained
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.smaller_global_noise_bound_fails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.smaller_global_noise_bound_fails
/-- info: 'Minidregg.Assurance.ResidentBfvSourceWindow.cyclic_sign_is_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourceWindow.cyclic_sign_is_false

end Minidregg.Assurance.ResidentBfvSourceWindow
