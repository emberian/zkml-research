/-
# The RS proximity-generator premise, discharged on the full unique-decoding radius

`Selvage.ReedSolomon.reedSolomonCode_hasMutualCorrelatedAgreement` takes
`IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d) B err` as the hypothesis `hPG`.
ArkLib (4d9d67b) proves the BCIKS20 unique-decoding correlated agreement for affine lines,
`ProximityGap.RS_correlatedAgreement_affineLines_uniqueDecodingRegime`, at every radius up to
`Code.relativeUniqueDecodingRadius = (1 - d/n)/2`, with error `n/q`. This file transports that
statement across four definitional seams and feeds it to the Selvage corollary:

* `reedSolomonCode_eq_arklib`: the two RS submodules are equal (both are the image of
  `Polynomial.degreeLT F d` under evaluation on the embedding).
* `relDist_eq_relHammingDist`: Selvage's real relative distance is the cast of ArkLib's `ℚ≥0` one.
* `close_iff_relDistFromCode_le`: Selvage's existential δ-ball equals ArkLib's infimum distance
  to the code, at a nonnegative radius.
* `affineGenerator_pr_eq_card` / `pr_eq_toReal_uniform`: Selvage's weighted seed sum for the
  `(1, z)` generator equals ArkLib/VCVio's uniform `Pr{z ← $ᵗ F}`, through the count.

The δ-interval this yields is `(0, (1 - d/n)/2)`: the whole unique-decoding radius, against the
one-third band `d < (1 - 3δ)n` of `Selvage.ProximityGapUDSharp`. The error is `n/q` against that
file's `(⌊δn⌋+1)/q`, so the two are incomparable packages and both stay.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding
import Selvage.ReedSolomon
import Mathlib.Tactic.NormNum.Prime

namespace Minidregg.Selvage.ArkLibUD

open NNReal ProximityGap Code

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Seam 1: the code -/

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- The two Reed–Solomon submodules are the same submodule of `ι → F`. -/
theorem reedSolomonCode_eq_arklib (dom : ι ↪ F) (d : ℕ) :
    reedSolomonCode dom d = ReedSolomon.code dom d := by
  unfold reedSolomonCode ReedSolomon.code
  congr 1

/-! ## Seam 2: the distance -/

omit [DecidableEq ι] [Field F] [Fintype F] in
/-- Selvage's `relDist` is the real cast of ArkLib's `ℚ≥0`-valued relative Hamming distance. -/
theorem relDist_eq_relHammingDist [Nonempty ι] (f g : ι → F) :
    relDist f g = ((relHammingDist f g : ℚ≥0) : ℝ) := by
  simp [relDist, relHammingDist]

/-- Selvage's δ-ball around a code is ArkLib's `δᵣ(w, C) ≤ δ`. -/
theorem close_iff_relDistFromCode_le [Nonempty ι] (δ : ℝ≥0) (C : Submodule F (ι → F))
    (w : ι → F) :
    close (δ : ℝ) C w ↔ relDistFromCode w (C : Set (ι → F)) ≤ δ := by
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  constructor
  · rintro ⟨u, hu, h⟩
    refine ⟨u, hu, ?_⟩
    rw [relDist_eq_relHammingDist] at h
    exact_mod_cast h
  · rintro ⟨u, hu, h⟩
    refine ⟨u, hu, ?_⟩
    rw [relDist_eq_relHammingDist]
    exact_mod_cast h

/-! ## Seam 3: the probability -/

open Classical in
/-- The `(1, z)` generator's probability is a count over uniform `z`. -/
theorem affineGenerator_pr_eq_card (E : (Fin 2 → F) → Prop) :
    (affineGenerator F).pr E
      = ((Finset.univ.filter fun z : F => E ![1, z]).card : ℝ) / (Fintype.card F : ℝ) := by
  unfold ProximityGenerator.pr
  calc
    ∑ ω ∈ Finset.univ.filter (fun ω : (affineGenerator F).Seed => E ((affineGenerator F).gen ω)),
        (affineGenerator F).weight ω
        = ∑ _ω ∈ Finset.univ.filter (fun z : F => E ![1, z]), ((Fintype.card F : ℝ))⁻¹ :=
          Finset.sum_congr rfl fun _ _ => rfl
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- Selvage's probability is the real value of VCVio's uniform probability of the same event. -/
theorem pr_eq_toReal_uniform [SampleableType F] (P : F → Prop) :
    (affineGenerator F).pr (fun r => P (r 1))
      = (Pr{let z ← $ᵗ F}[P z]).toReal := by
  classical
  rw [affineGenerator_pr_eq_card, SampleableType.prEvent_uniformSample_eq_ofReal,
    ENNReal.toReal_ofReal (by positivity)]
  rfl

/-! ## Seam 4: the agreement conclusion -/

omit [DecidableEq ι] [Fintype F] in
/-- ArkLib's `jointAgreement` at a radius `δ ∈ ℝ≥0` gives Selvage's `CorrelatedAgreement`. -/
theorem correlatedAgreement_of_jointAgreement [Nonempty ι] {C : Submodule F (ι → F)}
    {δ : ℝ≥0} {f : Fin 2 → ι → F}
    (h : jointAgreement (C : Set (ι → F)) δ f) :
    CorrelatedAgreement C (δ : ℝ) f := by
  obtain ⟨S, hS, v, hv⟩ := h
  refine ⟨S, ?_, fun i => ⟨v i, (hv i).1, fun x hx => ?_⟩⟩
  · have hS' : (((1 - δ : ℝ≥0) * (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hS
    have hsub : (1 : ℝ) - δ ≤ ((1 - δ : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_sub_def]; exact le_max_left _ _
    push_cast at hS'
    nlinarith [hsub, (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)]
  · have := (hv i).2 hx
    simp only [Finset.mem_filter] at this
    exact this.2.symm

/-! ## The discharge -/

/-- **`hPG` discharged on the full unique-decoding radius.** The `(1, z)` generator is a
proximity generator for `RS[F, dom, d]` with bound `B = 1 − relUDR` and constant error `n/q`.
Proof: ArkLib's BCIKS20 unique-decoding correlated agreement, carried across the four seams. -/
theorem reedSolomonCode_isProximityGenerator_relUDR [Nonempty ι] (dom : ι ↪ F) (d : ℕ) :
    IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      (1 - (relativeUniqueDecodingRadius
              (ι := ι) (F := F) (C := (ReedSolomon.code dom d : Set (ι → F))) : ℝ))
      (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) := by
  let _ : SampleableType F := SampleableType.ofFintype F
  intro f δ hδ0 hδlt hpr
  set δ' : ℝ≥0 := ⟨δ, hδ0.le⟩ with hδ'def
  have hδ'R : (δ' : ℝ) = δ := rfl
  have hle : δ' ≤ relativeUniqueDecodingRadius
      (ι := ι) (F := F) (C := (ReedSolomon.code dom d : Set (ι → F))) := by
    rw [← NNReal.coe_le_coe, hδ'R]; linarith
  have hCA := RS_correlatedAgreement_affineLines_uniqueDecodingRegime
    (deg := d) (domain := dom) hle
  rw [errorBound_eq_n_div_q_of_le_relUDR hle] at hCA
  have hev : ∀ z : F, close δ (reedSolomonCode dom d) (comb ((affineGenerator F).gen z) f)
      ↔ relDistFromCode (f 0 + z • f 1) ((ReedSolomon.code dom d : Set (ι → F))) ≤ δ' := by
    intro z
    have hcomb : comb ((affineGenerator F).gen z) f = f 0 + z • f 1 :=
      funext fun x => by rw [comb_affineGenerator]; rfl
    rw [hcomb, ← hδ'R, close_iff_relDistFromCode_le, reedSolomonCode_eq_arklib]
  classical
  have hcount : (affineGenerator F).pr (fun r => close δ (reedSolomonCode dom d) (comb r f))
      = ((Finset.univ.filter fun z : F => relDistFromCode (f 0 + z • f 1)
          ((ReedSolomon.code dom d : Set (ι → F))) ≤ δ').card : ℝ) / (Fintype.card F : ℝ) := by
    rw [affineGenerator_pr_eq_card]
    have hf : (Finset.univ.filter fun z : F =>
          close δ (reedSolomonCode dom d) (comb ![1, z] f))
        = Finset.univ.filter fun z : F => relDistFromCode (f 0 + z • f 1)
            ((ReedSolomon.code dom d : Set (ι → F))) ≤ δ' :=
      Finset.filter_congr (fun z _ => hev z)
    rw [hf]
  rw [hcount] at hpr
  have hprob : Pr{let z ← $ᵗ F}[relDistFromCode (f 0 + z • f 1)
        ((ReedSolomon.code dom d : Set (ι → F))) ≤ δ']
      > (((Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) := by
    rw [gt_iff_lt, SampleableType.prEvent_uniformSample_eq_ofReal, ← ENNReal.ofReal_coe_nnreal]
    have hpos : (0 : ℝ) < ((Finset.univ.filter fun z : F => relDistFromCode (f 0 + z • f 1)
        ((ReedSolomon.code dom d : Set (ι → F))) ≤ δ').card : ℝ) / (Fintype.card F : ℝ) :=
      lt_of_le_of_lt (by positivity) hpr
    rw [ENNReal.ofReal_lt_ofReal_iff (by convert hpos using 3)]
    push_cast
    convert hpr using 3
  exact correlatedAgreement_of_jointAgreement (by
    rw [← reedSolomonCode_eq_arklib] at hCA
    simpa [reedSolomonCode_eq_arklib] using hCA (f : WordStack F (Fin 2) ι) hprob)

/-- **WHIR Corollary 4.11 on the full unique-decoding radius, with no `hPG` left.** -/
theorem reedSolomonCode_hasMutualCorrelatedAgreement_relUDR [Nonempty ι] (dom : ι ↪ F)
    (d : ℕ) :
    HasMutualCorrelatedAgreement (affineGenerator F) (reedSolomonCode dom d)
      (max (1 - (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2)
        (1 - (relativeUniqueDecodingRadius
              (ι := ι) (F := F) (C := (ReedSolomon.code dom d : Set (ι → F))) : ℝ)))
      (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) :=
  reedSolomonCode_hasMutualCorrelatedAgreement (affineGenerator F) dom d
    (reedSolomonCode_isProximityGenerator_relUDR dom d)
    (fun _ _ _ => le_rfl) (fun _ _ => by positivity)

/-- The same, in closed form: for `0 < d ≤ n` the bound is `B⋆ = (1 + d/n)/2`, so the
δ-interval is `(0, (1 − d/n)/2)`, the whole unique-decoding radius, at error `n/q`. -/
theorem reedSolomonCode_hasMutualCorrelatedAgreement_UD [Nonempty ι] (dom : ι ↪ F)
    {d : ℕ} [NeZero d] (hd : d ≤ Fintype.card ι) :
    HasMutualCorrelatedAgreement (affineGenerator F) (reedSolomonCode dom d)
      ((1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2)
      (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) := by
  have h := reedSolomonCode_hasMutualCorrelatedAgreement_relUDR dom d
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hr : (relativeUniqueDecodingRadius
      (ι := ι) (F := F) (C := (ReedSolomon.code dom d : Set (ι → F))) : ℝ)
        = (1 - (d : ℝ) / (Fintype.card ι : ℝ)) / 2 := by
    rw [ReedSolomon.relativeUniqueDecodingRadius_RS_eq hd]
    have hdn : (d : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast Fintype.card_pos)]; exact_mod_cast hd
    rw [NNReal.coe_div, NNReal.coe_sub hdn]
    push_cast
    ring
  rw [hr] at h
  have hmax : max (1 - (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2)
      (1 - (1 - (d : ℝ) / (Fintype.card ι : ℝ)) / 2)
        = (1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2 := by
    rw [max_eq_right]
    · ring
    · have : ((d : ℝ) - 1) / (Fintype.card ι : ℝ) ≤ (d : ℝ) / (Fintype.card ι : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hn.le
      linarith
  rwa [hmax] at h

/-! ## Inhabitation: the interval is nonempty, extends past the one-third band, and the error is
below one, at a concrete code (`F₁₀₁`, `n = 16`, `d = 5`). -/

/-- `δ = 5/16` lies inside `(0, (1 − 5/16)/2) = (0, 11/32)` and outside the one-third band
`5 < (1 − 3δ)·16`, which needs `δ < 11/48`; the error `16/101` is below one. -/
example : (0 : ℝ) < 5 / 16 ∧ (5 / 16 : ℝ) < 1 - (1 + (5 : ℝ) / 16) / 2 ∧
    ¬ ((5 : ℝ) < (1 - 3 * (5 / 16)) * 16) ∧ (16 : ℝ) / 101 < 1 := by
  norm_num

instance fact_prime_101 : Fact (Nat.Prime 101) := ⟨by norm_num⟩

/-- The closed theorem fires at that code. -/
theorem udWitness :
    HasMutualCorrelatedAgreement (affineGenerator (ZMod 101))
      (reedSolomonCode (Fin.castLEEmb (by norm_num : 16 ≤ 101) : Fin 16 ↪ ZMod 101) 5)
      ((1 + (5 : ℝ) / 16) / 2) (fun _ => (16 : ℝ) / 101) := by
  have h := reedSolomonCode_hasMutualCorrelatedAgreement_UD (ι := Fin 16) (F := ZMod 101)
    (Fin.castLEEmb (by norm_num : 16 ≤ 101) : Fin 16 ↪ ZMod 101) (d := 5) (by simp)
  simpa [ZMod.card] using h

end Minidregg.Selvage.ArkLibUD

#print axioms Minidregg.Selvage.ArkLibUD.reedSolomonCode_isProximityGenerator_relUDR
#print axioms Minidregg.Selvage.ArkLibUD.reedSolomonCode_hasMutualCorrelatedAgreement_UD
#print axioms Minidregg.Selvage.ArkLibUD.udWitness
