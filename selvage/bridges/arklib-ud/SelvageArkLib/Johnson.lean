/-
# Mutual correlated agreement up to the Johnson radius, imported from ArkLib

`Selvage.JohnsonRegime.mutualCA_johnson` reaches the Johnson radius only conditionally: it takes
the WHIR Conjecture 4.12 implication `hconj` and a proximity-generator premise `hPG`.
ArkLib (4d9d67b) proves the Johnson affine-line MCA bound directly,
`ReedSolomon.mcaError_affineLine_johnson_le` (DKT26, no `hHab`, no `hPG`): for RS of dimension
`D + 1` on `n` points and slack `η > 0`, the MCA error at radius `1 − (√(D/n) + η)` is at most
`min 1 (E₀ / q)`, `E₀ = johnsonExceptionCount n D ⌈(√(D/n) + η) n⌉₊ η`.

Seams, beyond the code equality of `SelvageArkLib.UniqueDecoding`:

* `projected_mem_iff`: ArkLib's projected-code membership on `T` is Selvage's
  `∃ u ∈ C, AgreesOn T w u`.
* `mutualCAFailure_iff_isMCA`: Selvage's `MutualCAFailure` at the `(1, z)` seed is ArkLib's
  `IsMCA (AffineLineGenerator F)` at `z` (both: a set of `≥ (1−δ)n` coordinates where the
  combination agrees with a codeword and some input agrees with none).
* `pr_mutualCAFailure_eq`: Selvage's weighted seed sum is the real value of VCVio's uniform
  probability of that event; `mcaError` is a supremum over input pairs, so the pair at hand is
  below it.

Results: `reedSolomonCode_hasMutualCorrelatedAgreement_johnson` (MCA with `B⋆ = √(D/n) + η`)
and `..._sqrtRate`, the conclusion of `mutualCA_johnson` at Selvage's own `B = √((D+1)/n)`
with no `hconj`/`hPG`, whenever `η ≤ √((D+1)/n) − √(D/n)`. The error is a constant in `δ`.

Comparison with Selvage's `ProximityGapUDSharp` (`udSharp_hasMutualCorrelatedAgreement`: MCA in
the one-third band at `(⌊δn⌋+1)/q`), at `n = 16`, dimension 5, `η = 1/8`: the Johnson error is
exactly `3358/q`; inside the band the sharp error is at most `4/q`, so the band wins there; the
Johnson bound reaches `δ = 3/8`, past the band's `11/48` and the unique-decoding radius `11/32`.
-/
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability
import SelvageArkLib.UniqueDecoding
import Selvage.ProximityGapUDSharp

namespace Minidregg.Selvage.ArkLibJohnson

open NNReal ENNReal CoreDefinitions LinearCode ReedSolomon.HiddenDerivative
open Minidregg.Selvage.ArkLibUD (reedSolomonCode_eq_arklib affineGenerator_pr_eq_card)

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Seam: the event -/

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- ArkLib's projected-code membership is Selvage's agreement with some codeword. -/
theorem projected_mem_iff (C : Submodule F (ι → F)) (T : Finset ι) (w : ι → F) :
    projectedWord w T ∈ projectedCodeSubmod C T ↔ ∃ u ∈ C, AgreesOn T w u := by
  rw [mem_projectedCodeSubmod_iff]
  constructor
  · rintro ⟨u, hu, heq⟩
    exact ⟨u, hu, fun x hx => congrFun heq ⟨x, hx⟩⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu, funext fun x => h x.1 x.2⟩

omit [Fintype ι] [DecidableEq ι] in
theorem affineCombination_eq (f : Fin 2 → ι → F) (z : F) (x : ι) :
    (∑ j, AffineLineGenerator F z j • f j x) = comb ((affineGenerator F).gen z) f x := by
  rw [comb_affineGenerator]
  simp [Fin.sum_univ_two, smul_eq_mul]

omit [DecidableEq ι] in
/-- **The failure events coincide** at every radius, input pair and seed. -/
theorem mutualCAFailure_iff_isMCA (C : Submodule F (ι → F)) (δ : ℝ) (f : Fin 2 → ι → F)
    (z : F) :
    MutualCAFailure C δ f ((affineGenerator F).gen z) ↔
      IsMCA (AffineLineGenerator F) C z f δ := by
  unfold MutualCAFailure IsMCA
  dsimp only
  constructor
  · rintro ⟨S, hS, ⟨u, hu, hagree⟩, i, hi⟩
    refine ⟨S, by linarith, (projected_mem_iff C S _).mpr ⟨u, hu, fun x hx => ?_⟩, i,
      fun hmem => ?_⟩
    · exact (affineCombination_eq f z x).trans (hagree x hx)
    · obtain ⟨u', hu', h'⟩ := (projected_mem_iff C S _).mp hmem
      exact hi u' hu' h'
  · rintro ⟨T, hT, hmem, j, hj⟩
    obtain ⟨u, hu, hagree⟩ := (projected_mem_iff C T _).mp hmem
    refine ⟨T, by linarith, ⟨u, hu, fun x hx => ?_⟩, j,
      fun u' hu' h' => hj ((projected_mem_iff C T _).mpr ⟨u', hu', h'⟩)⟩
    exact (affineCombination_eq f z x).symm.trans (hagree x hx)

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Selvage's MCA failure is monotone in the radius (as `JohnsonMcaBridge`'s lemma). -/
theorem mutualCAFailure_mono {C : Submodule F (ι → F)} {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂)
    (f : Fin 2 → ι → F) (r : Fin 2 → F) :
    MutualCAFailure C δ₁ f r → MutualCAFailure C δ₂ f r := by
  rintro ⟨S, hS, hcomb, hinput⟩
  refine ⟨S, ?_, hcomb, hinput⟩
  have hn : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  nlinarith

/-! ## Seam: the probability -/

omit [DecidableEq ι] in
theorem pr_mutualCAFailure_eq [SampleableType F] (C : Submodule F (ι → F)) (δ : ℝ)
    (f : Fin 2 → ι → F) :
    (affineGenerator F).pr (MutualCAFailure C δ f) =
      (Pr{let z ← $ᵗ F}[IsMCA (AffineLineGenerator F) C z f δ]).toReal := by
  classical
  rw [affineGenerator_pr_eq_card, SampleableType.prEvent_uniformSample_eq_ofReal,
    ENNReal.toReal_ofReal (by positivity)]
  congr 3
  exact Finset.filter_congr fun z _ => mutualCAFailure_iff_isMCA C δ f z

/-! ## The Johnson bound -/

/-- ArkLib's Johnson error mass `E₀ / q`. -/
noncomputable def johnsonError (n D : ℕ) (eta : ℝ) (F : Type) [Fintype F] : ℝ :=
  johnsonExceptionCount n D ⌈johnsonAgreement n D eta * n⌉₊ eta / (Fintype.card F : ℝ)

omit [DecidableEq F] in
theorem johnsonError_nonneg (n D : ℕ) (eta : ℝ) : 0 ≤ johnsonError n D eta F := by
  unfold johnsonError johnsonExceptionCount johnsonTheta
  positivity

/-- **The Johnson MCA bound for Selvage's failure event**, at every radius up to
`1 − (√(D/n) + η)`. -/
theorem pr_mutualCAFailure_le_johnson {n D : ℕ} {eta : ℝ} (domain : Fin n ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta) (f : Fin 2 → Fin n → F) {δ : ℝ}
    (hδ : δ ≤ 1 - johnsonAgreement n D eta) :
    (affineGenerator F).pr (MutualCAFailure (reedSolomonCode domain (D + 1)) δ f) ≤
      min 1 (johnsonError n D eta F) := by
  let _ : SampleableType F := SampleableType.ofFintype F
  set δJ := 1 - johnsonAgreement n D eta
  have hJ := ReedSolomon.mcaError_affineLine_johnson_le domain hD hDn heta
  have hfin : min 1 (ENNReal.ofReal (johnsonError n D eta F)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
  calc (affineGenerator F).pr (MutualCAFailure (reedSolomonCode domain (D + 1)) δ f)
      ≤ (affineGenerator F).pr (MutualCAFailure (reedSolomonCode domain (D + 1)) δJ f) :=
        ProximityGenerator.pr_mono _ fun r => mutualCAFailure_mono hδ f r
    _ = (Pr{let z ← $ᵗ F}[IsMCA (AffineLineGenerator F)
          (ReedSolomon.code domain (D + 1)) z f δJ]).toReal := by
        rw [pr_mutualCAFailure_eq, reedSolomonCode_eq_arklib]
    _ ≤ (mcaError (AffineLineGenerator F) (ReedSolomon.code domain (D + 1)) δJ).toReal :=
        ENNReal.toReal_mono (ne_top_of_le_ne_top hfin hJ)
          (le_iSup (fun U : Fin 2 → Fin n → F =>
            Pr{let z ← $ᵗ F}[IsMCA (AffineLineGenerator F)
              (ReedSolomon.code domain (D + 1)) z U δJ]) f)
    _ ≤ (min 1 (ENNReal.ofReal (johnsonError n D eta F))).toReal :=
        ENNReal.toReal_mono hfin hJ
    _ = min 1 (johnsonError n D eta F) := by
        rw [ENNReal.toReal_min ENNReal.one_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_one,
          ENNReal.toReal_ofReal (johnsonError_nonneg n D eta)]

/-- **Mutual correlated agreement up to the Johnson radius, unconditional.** -/
theorem reedSolomonCode_hasMutualCorrelatedAgreement_johnson {n D : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta) :
    HasMutualCorrelatedAgreement (affineGenerator F) (reedSolomonCode domain (D + 1))
      (johnsonAgreement n D eta) (fun _ => min 1 (johnsonError n D eta F)) :=
  fun f _δ _ hδ => pr_mutualCAFailure_le_johnson domain hD hDn heta f hδ.le

/-- **`mutualCA_johnson`'s conclusion without `hconj` or `hPG`**, at Selvage's bound
`B = √(d/n)` for `d = D + 1` (so `1 − B` is `JohnsonRegime.johnsonRadius (d/n)`), for any slack
`η` that fits between `√(D/n)` and `√((D+1)/n)`. -/
theorem reedSolomonCode_hasMutualCorrelatedAgreement_sqrtRate {n D : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (heta_le : eta ≤ Real.sqrt (((D + 1 : ℕ) : ℝ) / n) - Real.sqrt ((D : ℝ) / n)) :
    HasMutualCorrelatedAgreement (affineGenerator F) (reedSolomonCode domain (D + 1))
      (Real.sqrt (((D + 1 : ℕ) : ℝ) / (Fintype.card (Fin n) : ℝ)))
      (fun _ => min 1 (johnsonError n D eta F)) := by
  intro f δ _ hδ
  apply pr_mutualCAFailure_le_johnson domain hD hDn heta f
  rw [Fintype.card_fin] at hδ
  unfold johnsonAgreement johnsonRhoMinus
  linarith

/-! ## Selvage's one-third band, as MCA, for the comparison -/

omit [DecidableEq ι] [DecidableEq F] in
theorem rsUdSharpError_mono {δ₁ δ₂ : ℝ} (_h0 : 0 < δ₁) (h : δ₁ ≤ δ₂) :
    rsUdSharpError ι F δ₁ ≤ rsUdSharpError ι F δ₂ := by
  unfold rsUdSharpError
  have hn : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  have hfl : Nat.floor (δ₁ * (Fintype.card ι : ℝ)) ≤ Nat.floor (δ₂ * (Fintype.card ι : ℝ)) :=
    Nat.floor_le_floor (by nlinarith)
  gcongr

/-- Selvage's `ProximityGapUDSharp` carried to MCA by WHIR Lemma 4.10. -/
theorem udSharp_hasMutualCorrelatedAgreement [Nonempty ι] (dom : ι ↪ F) (d : ℕ) :
    HasMutualCorrelatedAgreement (affineGenerator F) (reedSolomonCode dom d)
      (max (1 - (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2)
        ((2 + (d : ℝ) / (Fintype.card ι : ℝ)) / 3))
      (rsUdSharpError ι F) :=
  reedSolomonCode_hasMutualCorrelatedAgreement (affineGenerator F) dom d
    (reedSolomonCode_isProximityGenerator_UD_sharp dom d)
    (fun h0 h _ => rsUdSharpError_mono h0 h) (fun _ _ => by unfold rsUdSharpError; positivity)

/-! ## Witness: `n = 16`, dimension `5`, `η = 1/8` -/

theorem sqrt_quarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem rho_witness : johnsonRhoMinus 16 4 = 1 / 4 := by
  unfold johnsonRhoMinus; norm_num

theorem agreement_witness : johnsonAgreement 16 4 (1 / 8) = 5 / 8 := by
  unfold johnsonAgreement; rw [rho_witness, sqrt_quarter]; norm_num

theorem m_witness : johnsonM 16 4 (1 / 8) = 3 := by
  unfold johnsonM; rw [rho_witness, sqrt_quarter]; norm_num

theorem mu_witness : johnsonMu 16 4 (1 / 8) = 6 := by
  unfold johnsonMu johnsonT; rw [m_witness, rho_witness, sqrt_quarter]; norm_num

theorem h_witness : johnsonH 16 4 (1 / 8) = 16 := by
  unfold johnsonH johnsonT
  rw [m_witness, rho_witness]
  have : ⌈((3 : ℕ) + 1 / 2 : ℝ) ^ 2 / (3 * (1 / 4))⌉₊ = 17 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  rw [this]

theorem threshold_witness : ⌈johnsonAgreement 16 4 (1 / 8) * (16 : ℕ)⌉₊ = 10 := by
  rw [agreement_witness]; norm_num

omit [Field F] [DecidableEq F] in
/-- **The Johnson error mass at the witness is `3358/q`.** -/
theorem johnsonError_witness : johnsonError 16 4 (1 / 8) F = 3358 / (Fintype.card F : ℝ) := by
  unfold johnsonError johnsonExceptionCount johnsonTheta
  rw [threshold_witness, mu_witness, h_witness]
  norm_num

/-- The witness radius `3/8` is past the unique-decoding radius `11/32` and the one-third band
`11/48` of dimension 5 on 16 points. -/
theorem witness_radius : 1 - johnsonAgreement 16 4 (1 / 8) = 3 / 8 ∧
    (11 / 32 : ℝ) < 3 / 8 ∧ (1 - (5 : ℝ) / 16) / 2 = 11 / 32 ∧
    (1 - (5 : ℝ) / 16) / 3 = 11 / 48 := by
  rw [agreement_witness]; norm_num

omit [DecidableEq F] in
/-- Inside the band the sharp error is at most `4/q`, below the Johnson `3358/q`. -/
theorem udSharp_le_johnson_witness {δ : ℝ} (h0 : 0 ≤ δ) (hband : δ < 11 / 48) :
    rsUdSharpError (Fin 16) F δ ≤ 4 / (Fintype.card F : ℝ) ∧
      4 / (Fintype.card F : ℝ) < johnsonError 16 4 (1 / 8) F := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨?_, ?_⟩
  · unfold rsUdSharpError
    rw [Fintype.card_fin]
    have hfl : Nat.floor (δ * ((16 : ℕ) : ℝ)) ≤ 3 :=
      Nat.lt_succ_iff.mp ((Nat.floor_lt (by positivity)).mpr (by push_cast; linarith))
    have : ((Nat.floor (δ * ((16 : ℕ) : ℝ)) : ℝ) + 1) ≤ 4 := by exact_mod_cast Nat.succ_le_succ hfl
    exact div_le_div_of_nonneg_right this hq.le
  · rw [johnsonError_witness]
    exact div_lt_div_of_pos_right (by norm_num) hq

/-- The slack hypothesis of `..._sqrtRate` is inhabited at `n = 16`, `D = 4`: `η = 1/32`. -/
theorem heta_le_witness :
    (1 / 32 : ℝ) ≤ Real.sqrt (((4 + 1 : ℕ) : ℝ) / (16 : ℕ)) - Real.sqrt ((4 : ℕ) / (16 : ℕ)) := by
  have h4 : Real.sqrt (((4 : ℕ) : ℝ) / (16 : ℕ)) = 1 / 2 := by
    rw [show (((4 : ℕ) : ℝ) / (16 : ℕ)) = 1 / 4 by norm_num, sqrt_quarter]
  have h5 : (17 / 32 : ℝ) ≤ Real.sqrt (((4 + 1 : ℕ) : ℝ) / (16 : ℕ)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; norm_num
  rw [h4]; linarith

section Instance

instance : Fact (Nat.Prime 1000003) := ⟨by norm_num⟩

/-- A 16-point domain in `ZMod 1000003`. -/
def witnessDomain : Fin 16 ↪ ZMod 1000003 :=
  ⟨fun i => (i : ZMod 1000003), fun i j h => by
    have hi := i.isLt; have hj := j.isLt
    have := (ZMod.natCast_eq_natCast_iff' i.val j.val 1000003).mp h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact Fin.ext this⟩

/-- **The bound fires and is below one**: dimension 5 on 16 points of `ZMod 1000003`, every
input pair, at the radius `3/8` past unique decoding. -/
theorem johnson_witness (f : Fin 2 → Fin 16 → ZMod 1000003) :
    (affineGenerator (ZMod 1000003)).pr
        (MutualCAFailure (reedSolomonCode witnessDomain (4 + 1)) (3 / 8) f) ≤
      3358 / 1000003 := by
  have h := pr_mutualCAFailure_le_johnson (D := 4) (eta := 1 / 8) witnessDomain (by norm_num)
    (by norm_num) (by norm_num) f (δ := 3 / 8) (by rw [agreement_witness]; norm_num)
  rw [johnsonError_witness, ZMod.card] at h
  refine h.trans (min_le_right _ _) |>.trans_eq ?_
  norm_num

end Instance

end Minidregg.Selvage.ArkLibJohnson

/-- info: 'Minidregg.Selvage.ArkLibJohnson.reedSolomonCode_hasMutualCorrelatedAgreement_johnson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArkLibJohnson.reedSolomonCode_hasMutualCorrelatedAgreement_johnson
/-- info: 'Minidregg.Selvage.ArkLibJohnson.reedSolomonCode_hasMutualCorrelatedAgreement_sqrtRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArkLibJohnson.reedSolomonCode_hasMutualCorrelatedAgreement_sqrtRate
/-- info: 'Minidregg.Selvage.ArkLibJohnson.johnson_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArkLibJohnson.johnson_witness
/-- info: 'Minidregg.Selvage.ArkLibJohnson.udSharp_le_johnson_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArkLibJohnson.udSharp_le_johnson_witness
