/-
A closed source-equation window theorem at Q83. Ghost records contain source
messages and small factors; they are not the host's ciphertext state format.
The theorem constructs the quotient-ring phase and derives its bounded lift.
Only coefficient bounds and literal source-operation correspondence remain
at the sampler/Rust boundary. No confidentiality or restricted release claim.
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

/-- A nonzero full-support premise inhabitant at the support edge. The
arithmetic bound allows correlated/repeated factors; it assumes no sampling
independence and makes no typical-key or security claim. -/
def twenties : Coeffs := fun _ => 20
def oneInput : Input := ⟨fun _ => 1, twenties, twenties, twenties⟩
def inputs : List Input := List.replicate window oneInput

theorem twenties_bounded : Bounded twenties := by intro j; decide

theorem one_allowed : Allowed oneInput := by
  exact ⟨twenties_bounded, twenties_bounded, twenties_bounded, by intro j; decide⟩

theorem rows_nonzero_score :
    Minidregg.Theory.IntegerWindowNoise.readoutScore witnessQuery
      (inputs.map (inputRow twenties twenties)) = -128 := by
  have hr : Minidregg.Theory.IntegerWindowNoise.rowScore witnessQuery (inputRow twenties twenties oneInput) = -1 := by
    unfold Minidregg.Theory.IntegerWindowNoise.rowScore
    simp [witnessQuery, inputRow, integerRow, oneInput]
  simp [Minidregg.Theory.IntegerWindowNoise.readoutScore, inputs, hr, window]

theorem full_window_nonzero_subject :
    centered t32 (rounded q83 t32 (outputLift twenties twenties 7 inputs witnessQuery)) = -128 := by
  have h := source_window_correctness twenties twenties 7 inputs witnessQuery
    twenties_bounded twenties_bounded
    (by intro x hx; have heq : x = oneInput := by simpa [inputs, window] using hx; subst x; exact one_allowed)
    (by simp [inputs]) witness_premises.2.2.1
  simpa [rows_nonzero_score] using h

/-- The existing worst-case N expansion is attained, not a guessed heuristic. -/
theorem convolution_constant_last (n : Nat) (hn : 0 < n) (S : Int) :
    convolution (fun _ : Fin n => S) (fun _ : Fin n => S) ⟨n - 1, by omega⟩ = (n : Int) * S ^ 2 := by
  unfold convolution
  have h : ∀ i : Fin n, i.val ≤ (⟨n - 1, by omega⟩ : Fin n).val := by intro i; have := i.isLt; dsimp; omega
  simp only [h, if_true]
  simp [pow_two]

theorem actual_fresh_bound_attained :
    integerNoise twenties twenties twenties twenties twenties ⟨4095, by decide⟩ = 3276820 := by
  unfold integerNoise twenties
  rw [convolution_constant_last N (by decide) 20, convolution_constant_last N (by decide) 20]
  norm_num [N]

theorem cyclic_sign_is_false :
    convolution (fun i : Fin 2 => if i = 1 then (1 : Int) else 0)
      (fun i : Fin 2 => if i = 1 then (1 : Int) else 0) 0 = -1 := by decide

end Minidregg.Assurance.ResidentBfvSourceWindow
