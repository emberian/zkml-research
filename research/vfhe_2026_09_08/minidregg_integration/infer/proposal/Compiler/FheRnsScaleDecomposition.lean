/-
# fhe.rs RNS scale: the selected-lift and fixed-correction seams

Statement first. RnsScaler's integer output is S-v*gamma+w. Its exact reference
on the SELECTED lift is S-v*gamma+round(C/d), where C is the weighted residual
correction. Thus output-reference = w-round(C/d), with no hidden cross term.
When d divides n*M (the BFV downscale case), gamma is exact and the code's
ceil-directed fixed omega corrections give a one-sided approximation: under an
explicit error bound, the rounded result equals the reference or reference+1.

This file proves integer identities and bounds, NOT that Rust's wrapping-U256,
NTT, pointer accesses or generated machine code implements them. Those are tested
on retained coefficient fixtures in the accompanying research lane. A captured
numeric witness is a theorem about the stated integers, not a Lean execution of
Rust. The first BFVScaleLiftRefinement patch and its explicit unsigned convention
are preserved; this file identifies why an actual engine needs more premises.

ATLAS poles: an exact witness, a sharp +1 witness, direction and magnitude
falsifiers, and the source-decomposition premise is inhabited for arbitrary
integer Garner data. No crypto assumptions and no emitted checker claims.
-/
import Compiler.BFVScaleLiftRefinement

namespace Minidregg.Compiler.FheRnsScale
set_option autoImplicit false
open scoped BigOperators

def roundDiv (x d : ℤ) : ℤ := (2 * x + d) / (2 * d)

def selectedLift {L : ℕ} (M : ℤ) (r g : Fin L → ℤ) (v : ℤ) : ℤ :=
  (∑ i, r i * g i) - v * M

def integerPart {L : ℕ} (r omega : Fin L → ℤ) (v gamma : ℤ) : ℤ :=
  (∑ i, r i * omega i) - v * gamma

def correction {L : ℕ} (M n d : ℤ) (r g omega : Fin L → ℤ) (v gamma : ℤ) : ℤ :=
  (∑ i, r i * (n * g i - d * omega i)) - v * (n * M - d * gamma)

/-- The proposed exact source-algebra refinement, before approximation or machine-word lowering. -/
def GarnerScaleDecomposition : Prop :=
  ∀ {L : ℕ} (M n d : ℤ) (r g omega : Fin L → ℤ) (v gamma w : ℤ),
    0 < d →
    integerPart r omega v gamma + w - roundDiv (n * selectedLift M r g v) d =
      w - roundDiv (correction M n d r g omega v gamma) d

/-- The one-sided corrected result can differ by ONE, including at valid rounding boundaries. -/
def OneSidedRoundingRefinement : Prop :=
  ∀ (d B C T : ℤ), 0 < d → 0 < B →
    0 ≤ d * T - B * C → d * T - B * C ≤ d * B →
    roundDiv C d ≤ roundDiv T B ∧ roundDiv T B ≤ roundDiv C d + 1

theorem round_add_multiple (d k r : ℤ) (hd : 0 < d) :
    roundDiv (d * k + r) d = k + roundDiv r d := by
  unfold roundDiv
  have h : 2 * (d * k + r) + d = (2 * r + d) + k * (2 * d) := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by omega)]
  ring

/-- Exact algebra for any integer chosen-lift index v; CRT correctness is separate. -/
theorem garner_identity {L : ℕ} (M n d : ℤ) (r g omega : Fin L → ℤ) (v gamma : ℤ) :
    n * selectedLift M r g v =
      d * integerPart r omega v gamma + correction M n d r g omega v gamma := by
  have hs : n * (∑ i, r i * g i) =
      d * (∑ i, r i * omega i) + ∑ i, r i * (n * g i - d * omega i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  dsimp [selectedLift, integerPart, correction]
  nlinarith [hs]

/-- Universal inhabitation of the claimed source decomposition, with no trusted rounding assumption. -/
theorem garnerScaleDecomposition : GarnerScaleDecomposition := by
  intro L M n d r g omega v gamma w hd
  rw [garner_identity M n d r g omega v gamma, round_add_multiple _ _ _ hd]
  ring

/-- The exact reference is the first tranche's nearest-ties-up function. -/
theorem roundDiv_eq_nearest (x d : ℤ) (hd : 0 < d) :
    roundDiv x d = BFVScaleLift.nearest d 1 x := by
  rw [BFVScaleLift.nearest_eq_doubled d 1 x hd]
  simp [roundDiv]

/-- Common-denominator arithmetic proves the approximation interval, including negative C,T. -/
theorem oneSidedRoundingRefinement : OneSidedRoundingRefinement := by
  intro d B C T hd hB he0 he1
  let D := 2 * B * d
  let A := (2 * C + d) * B
  let F := (2 * T + B) * d
  have hD : 0 < D := by dsimp [D]; positivity
  have hAF : A ≤ F := by dsimp [A, F]; nlinarith
  have hFA : F ≤ A + D := by dsimp [A, F, D]; nlinarith
  have hA : A / D = roundDiv C d := by
    have hden : D = (2 * d) * B := by dsimp [D]; ring
    rw [hden]
    exact Int.mul_ediv_mul_of_pos_left _ _ hB
  have hF : F / D = roundDiv T B := by
    exact Int.mul_ediv_mul_of_pos_left _ _ hd
  rw [← hA, ← hF]
  constructor
  · exact Int.ediv_le_ediv hD hAF
  · calc
      F / D ≤ (A + D) / D := Int.ediv_le_ediv hD hFA
      _ = A / D + 1 := by simpa using Int.add_mul_ediv_right A 1 (ne_of_gt hD)

/-- Ceiling division works on negative x too. -/
def ceilDiv (x d : ℤ) : ℤ := (x + d - 1) / d

/-- The exact directed error in a ceil-rounded fixed-point projection. -/
theorem ceil_error (x d : ℤ) (hd : 0 < d) :
    0 ≤ d * ceilDiv x d - x ∧ d * ceilDiv x d - x ≤ d - 1 := by
  have he := Int.mul_ediv_add_emod (x + d - 1) d
  have hr0 := Int.emod_nonneg (x + d - 1) (ne_of_gt hd)
  have hrd := Int.emod_lt_of_pos (x + d - 1) hd
  unfold ceilDiv
  constructor <;> omega

/-- Positive residues preserve the direction of each ceil approximation. The sum bound
is an explicit finite-precision condition, not an assumption that corrections are exact. -/
theorem weighted_ceil_error {L : ℕ} (d B : ℤ) (r theta : Fin L → ℤ)
    (hd : 0 < d) (_hB : 0 < B) (hr : ∀ i, 0 ≤ r i) (hs : (∑ i, r i) ≤ B) :
    0 ≤ d * (∑ i, r i * ceilDiv (B * theta i) d) - B * (∑ i, r i * theta i) ∧
    d * (∑ i, r i * ceilDiv (B * theta i) d) - B * (∑ i, r i * theta i) ≤ d * B := by
  have heq : d * (∑ i, r i * ceilDiv (B * theta i) d) - B * (∑ i, r i * theta i) =
      ∑ i, r i * (d * ceilDiv (B * theta i) d - B * theta i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hr i) (ceil_error _ _ hd).1
  · calc
      _ ≤ ∑ i, r i * d := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hr i)
        have hi := (ceil_error (B * theta i) d hd).2
        omega
      _ = d * ∑ i, r i := by rw [← Finset.sum_mul]; ring
      _ ≤ d * B := mul_le_mul_of_nonneg_left hs hd.le

/-- This is the mathematical case used by BFV downscale when gamma has no fractional part.
It still explicitly assumes the source's fixed sum equals these ceil projections. -/
theorem ceil_corrected_rounding {L : ℕ} (d B : ℤ) (r theta : Fin L → ℤ)
    (hd : 0 < d) (hB : 0 < B) (hr : ∀ i, 0 ≤ r i) (hs : (∑ i, r i) ≤ B) :
    roundDiv (∑ i, r i * theta i) d ≤
      roundDiv (∑ i, r i * ceilDiv (B * theta i) d) B ∧
    roundDiv (∑ i, r i * ceilDiv (B * theta i) d) B ≤
      roundDiv (∑ i, r i * theta i) d + 1 := by
  exact oneSidedRoundingRefinement d B _ _ hd hB
    (weighted_ceil_error d B r theta hd hB hr hs).1
    (weighted_ceil_error d B r theta hd hB hr hs).2

/-- Nonzero exact and sharp +1 witnesses inhabit the actual approximation premises. -/
theorem approximation_premise_inhabited :
    (0 : ℤ) ≤ 31 * 4 - 8 * 15 ∧ 31 * 4 - 8 * 15 ≤ 31 * 8 ∧
    roundDiv 15 31 = 0 ∧ roundDiv 4 8 = 1 ∧ roundDiv 31 31 = 1 ∧ roundDiv 8 8 = 1 := by decide

/-- A missing error magnitude bound permits a two-unit discrepancy. -/
theorem magnitude_falsifier :
    (0 : ℤ) ≤ 31 * 16 - 8 * 0 ∧ roundDiv 0 31 = 0 ∧ roundDiv 16 8 = 2 := by decide

/-- A missing direction premise permits downward error. -/
theorem direction_falsifier : roundDiv 16 31 = 1 ∧ roundDiv 3 8 = 0 := by decide

/-- A fixed-point correction mismatch survives every exact linear algebra identity. -/
theorem correction_falsifier :
    integerPart ![(1 : ℤ)] ![(0 : ℤ)] 0 0 + 1 - roundDiv (1 * selectedLift 31 ![1] ![15] 0) 31 = 1 := by decide


/-- Captured source-model integers from the actual N4096/Q109/t1032193 full-coefficient
fixture. This theorem checks the arithmetic only; the Rust observation is in the log. -/
theorem captured_rounding_discrepancy :
    (1032193 : ℤ) * 108454153028594899284870262370752 = 649033470896967801447398927572993 * (19828208824) + (-12869059249093027111048317839460229453071096) ∧
    roundDiv ((1032193 : ℤ) * 108454153028594899284870262370752) 649033470896967801447398927572993 = 172480 ∧
    (19828208824 : ℤ) + roundDiv (-3373565569180285022339419298656072646576590230548) (2^127) = 172481 ∧
    172481 = 172480 + 1 := by decide

/-- The captured case satisfies the approximation interval while violating EXACT rounding. -/
theorem captured_error_bound :
    (0 : ℤ) ≤ 649033470896967801447398927572993 * (-3373565569180285022339419298656072646576590230548) - (2^127) * (-12869059249093027111048317839460229453071096) ∧
    649033470896967801447398927572993 * (-3373565569180285022339419298656072646576590230548) - (2^127) * (-12869059249093027111048317839460229453071096) ≤ 649033470896967801447398927572993 * (2^127) := by decide


/-- The exact missing premise is characterized in both directions. -/
theorem output_exact_iff {L : ℕ} (M n d : ℤ) (r g omega : Fin L → ℤ)
    (v gamma w : ℤ) (hd : 0 < d) :
    integerPart r omega v gamma + w = roundDiv (n * selectedLift M r g v) d ↔
      w = roundDiv (correction M n d r g omega v gamma) d := by
  have h := garnerScaleDecomposition M n d r g omega v gamma w hd
  omega

/-- Conditional source-level BFV downscale bound. gamma is exact when d divides n*M;
the machine-word proof must still show that Rust computes the stated w without
truncation/overflow and that the residue vector has these nonnegative ranges. -/
theorem downscale_discrepancy_bound {L : ℕ} (M n d B : ℤ) (r g omega : Fin L → ℤ)
    (v gamma w : ℤ) (hd : 0 < d) (hB : 0 < B)
    (hr : ∀ i, 0 ≤ r i) (hs : (∑ i, r i) ≤ B) (hgamma : n * M = d * gamma)
    (hw : w = roundDiv (∑ i, r i * ceilDiv (B * (n * g i - d * omega i)) d) B) :
    roundDiv (n * selectedLift M r g v) d ≤ integerPart r omega v gamma + w ∧
    integerPart r omega v gamma + w ≤ roundDiv (n * selectedLift M r g v) d + 1 := by
  have h := garnerScaleDecomposition M n d r g omega v gamma w hd
  have hb := ceil_corrected_rounding d B r (fun i => n * g i - d * omega i) hd hB hr hs
  have hc : correction M n d r g omega v gamma = ∑ i, r i * (n * g i - d * omega i) := by
    simp [correction, hgamma]
  rw [hc] at h
  dsimp only at hb
  rw [← hw] at hb
  omega


/-- Integer semantics of the source's U256 correction branch: wrap modulo 2^256,
extract sign at bit191, complement negative values, shift, then as_u128. -/
def wordCorrection (T : ℤ) : ℤ :=
  let m := T % (2^256)
  if 0 < m / (2^191) then
    -(((((2^256 - 1 - m) / (2^126)) % (2^128)) + 1) / 2)
  else
    ((((m / (2^126)) % (2^128)) + 1) / 2)

/-- The asymmetric positive/negative branch really is nearest, ties toward +infinity,
provided the signed correction accumulator stays within the source's sign range. -/
theorem wordCorrection_correct (T : ℤ) (hlo : -(2^191) < T) (hhi : T < 2^191) :
    wordCorrection T = roundDiv T (2^127) := by
  norm_num [wordCorrection, roundDiv] at *
  split_ifs <;> omega

/-- The sign-range premise is necessary; overflowing it misinterprets a positive value. -/
theorem wordCorrection_range_falsifier :
    wordCorrection (2^191) ≠ roundDiv (2^191) (2^127) := by decide

/-- Integer semantics of the source's unsigned Garner quotient computation. -/
def wordV (T : ℤ) (s : ℕ) : ℤ :=
  ((((T % (2^256)) / (2^(s-1))) % (2^128)) + 1) / 2

/-- The six-limb deployed multiplication basis selects shift126. -/
theorem wordV126_correct (T : ℤ) (hlo : 0 ≤ T) (hhi : T < 2^191) :
    wordV T 126 = roundDiv T (2^126) := by
  norm_num [wordV, roundDiv] at *
  omega

/-- The three-limb deployed input basis selects shift127. -/
theorem wordV127_correct (T : ℤ) (hlo : 0 ≤ T) (hhi : T < 2^191) :
    wordV T 127 = roundDiv T (2^127) := by
  norm_num [wordV, roundDiv] at *
  omega


/-! The actual six-limb RNS parameter instance. Constants are recomputed from the
pinned source formulas by the executable oracle, and their key equalities are
checked below. This does not prove a Rust constructor or compiler correct. -/
def deployedQ : ℤ := 649033470896967801447398927572993
def deployedP : ℤ := 63657017601423447469844788570668366246758260020405327828579335270495845505447102168432641
def deployedT : ℤ := 1032193
def deployedGamma : ℤ := 101237194868023629673163772448739743344356924690180564813783041
def deployedBase : Fin 6 → ℤ := ![68719403009, 68719230977, 137438822401, 4611686018427322369, 4611686018427289601, 4611686018427215873]
def deployedGarner : Fin 6 → ℤ := ![49037120553824136751471610970179393072176137091181796717020811372647357566880381557122380, 1678211177128952460179172917767188642834258683901782735384020213647964006859770168663068, 63355891585998488225053046745657179957901415044592626502739270319195492231051266635172902, 16345698358795518933445101438143739868436081405198092169255547765528282324992654626990799, 41657891712229139002088137383142800072204860956687580803848903181082692123087596133229341, 18896239416294107037297296257114797126722026879654104557489452959385748263469637384119434]
def deployedOmega : Fin 6 → ℤ := ![77986382591119874064921855321526527381868595827415916824020267, 2668949918962272755740805946941502886286373228576567292954653, 100758297894020147554024975409120330178423098053670234523689029, 25995447357658063166494866421566043447166475144685359547976399, 66250796219640414915292195382615713228017713407091191535059741, 30051710622670116563016618864449112911308518409102424717649034]
def deployedThetaF : Fin 6 → ℤ := ![40236327986558578738024106521970757913, 26673667195148591677074894140064778585, (-66909995181707170415099000391450818675), 0, 0, 0]
def deployedThetaG : Fin 6 → ℤ := ![65532709816543261120686144690911786053, 2242744370786562493162848562050193381, 84668169981889996386106782933101050135, 21844225256251488268626182502778273331, 55671183346706527600677455323602830952, 25252742418526011728271541561382024741]

/-- The actual downscaler gamma is integral; its fractional correction is zero. -/
theorem deployed_gamma_exact : deployedT * deployedP = deployedQ * deployedGamma := by decide

/-- All six precomputed theta values have precisely the directed ceiling semantics. -/
theorem deployed_thetaF_exact : ∀ i : Fin 6,
    deployedThetaF i = ceilDiv ((2^127) *
      (deployedT * deployedGarner i - deployedQ * deployedOmega i)) deployedQ := by decide

/-- Range checks on the instantiated fixed-point constants; no default fields or placeholders. -/
theorem deployed_fixed_ranges :
    (∀ i : Fin 6, |deployedThetaF i| ≤ (2^127 : ℤ)) ∧
    (∀ i : Fin 6, 0 ≤ deployedThetaG i ∧ deployedThetaG i ≤ (2^127 : ℤ)) ∧
    (∑ i : Fin 6, deployedBase i) < (2^64 : ℤ) := by decide

/-- Canonical per-limb residues imply the mass bound needed by both U256 accumulators. -/
theorem deployed_residue_mass (r : Fin 6 → ℤ)
    (hr : ∀ i, 0 ≤ r i ∧ r i < deployedBase i) :
    0 ≤ (∑ i, r i) ∧ (∑ i, r i) < (2^64 : ℤ) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (hr i).1)
  · calc
      _ ≤ ∑ i, deployedBase i := Finset.sum_le_sum (fun i _ => (hr i).2.le)
      _ < (2^64 : ℤ) := deployed_fixed_ranges.2.2

/-- A general weighted accumulator range lemma, with signed fixed-point constants. -/
theorem weighted_accumulator_bound {L : ℕ} (r theta : Fin L → ℤ) (S K : ℤ)
    (hr : ∀ i, 0 ≤ r i) (ht : ∀ i, |theta i| ≤ K)
    (hs : (∑ i, r i) < S) (hK : 0 < K) : |∑ i, r i * theta i| < S * K := by
  calc
    _ ≤ ∑ i, |r i * theta i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, r i * K := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hr i)]
      exact mul_le_mul_of_nonneg_left (ht i) (hr i)
    _ = (∑ i, r i) * K := by rw [Finset.sum_mul]
    _ < S * K := mul_lt_mul_of_pos_right hs hK

/-- The actual signed correction accumulator cannot overflow its sign range. -/
theorem deployed_correction_range (r : Fin 6 → ℤ)
    (hr : ∀ i, 0 ≤ r i ∧ r i < deployedBase i) :
    |∑ i, r i * deployedThetaF i| < (2^191 : ℤ) := by
  have h := weighted_accumulator_bound r deployedThetaF (2^64) (2^127)
    (fun i => (hr i).1) deployed_fixed_ranges.1 (deployed_residue_mass r hr).2 (by positivity)
  convert h using 1

/-- The actual unsigned Garner accumulator fits the range used by wordV126_correct. -/
theorem deployed_garner_range (r : Fin 6 → ℤ)
    (hr : ∀ i, 0 ≤ r i ∧ r i < deployedBase i) :
    0 ≤ (∑ i, r i * deployedThetaG i) ∧ (∑ i, r i * deployedThetaG i) < (2^191 : ℤ) := by
  have hn : 0 ≤ (∑ i, r i * deployedThetaG i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hr i).1 (deployed_fixed_ranges.2.1 i).1)
  refine ⟨hn, ?_⟩
  have ht : ∀ i, |deployedThetaG i| ≤ (2^127 : ℤ) := by
    intro i
    rw [abs_of_nonneg (deployed_fixed_ranges.2.1 i).1]
    exact (deployed_fixed_ranges.2.1 i).2
  have h := weighted_accumulator_bound r deployedThetaG (2^64) (2^127)
    (fun i => (hr i).1) ht (deployed_residue_mass r hr).2 (by positivity)
  rw [abs_of_nonneg hn] at h
  convert h using 1

def deployedV (r : Fin 6 → ℤ) : ℤ := wordV (∑ i, r i * deployedThetaG i) 126
def deployedW (r : Fin 6 → ℤ) : ℤ := wordCorrection (∑ i, r i * deployedThetaF i)
def deployedOutput (r : Fin 6 → ℤ) : ℤ :=
  integerPart r deployedOmega (deployedV r) deployedGamma + deployedW r

/-- The actual word branch computes exactly the fixed-point rounded correction. -/
theorem deployedW_correct (r : Fin 6 → ℤ)
    (hr : ∀ i, 0 ≤ r i ∧ r i < deployedBase i) :
    deployedW r = roundDiv (∑ i, r i * deployedThetaF i) (2^127) := by
  rcases abs_lt.mp (deployed_correction_range r hr) with ⟨hlo, hhi⟩
  exact wordCorrection_correct _ hlo hhi

/-- The actual unsigned word branch computes exactly its fixed-point lift index. -/
theorem deployedV_correct (r : Fin 6 → ℤ)
    (hr : ∀ i, 0 ≤ r i ∧ r i < deployedBase i) :
    deployedV r = roundDiv (∑ i, r i * deployedThetaG i) (2^126) := by
  exact wordV126_correct _ (deployed_garner_range r hr).1 (deployed_garner_range r hr).2

/-- Universal instantiated source-ARITHMETIC envelope over ALL canonical six-limb inputs.
The reference uses the source-selected lift. A proof of Rust's modular arithmetic,
array interpretation and generated code is still required for implementation refinement. -/
theorem deployed_source_arithmetic_envelope (r : Fin 6 → ℤ)
    (hr : ∀ i, 0 ≤ r i ∧ r i < deployedBase i) :
    roundDiv (deployedT * selectedLift deployedP r deployedGarner (deployedV r)) deployedQ ≤
      deployedOutput r ∧
    deployedOutput r ≤
      roundDiv (deployedT * selectedLift deployedP r deployedGarner (deployedV r)) deployedQ + 1 := by
  apply downscale_discrepancy_bound deployedP deployedT deployedQ (2^127)
    r deployedGarner deployedOmega (deployedV r) deployedGamma (deployedW r)
    (by decide) (by positivity) (fun i => (hr i).1)
  · have h := (deployed_residue_mass r hr).2
    norm_num at h ⊢
    omega
  · exact deployed_gamma_exact
  · rw [deployedW_correct r hr]
    congr 1


/-- Deterministic source arithmetic: the output binds the actual fixed correction.
The one-unit envelope is diagnostic and must not become verifier freedom. -/
theorem deployed_output_exact (r : Fin 6 → ℤ)
    (hr : ∀ i, 0 ≤ r i ∧ r i < deployedBase i) :
    deployedOutput r = integerPart r deployedOmega
      (roundDiv (∑ i, r i * deployedThetaG i) (2^126)) deployedGamma +
      roundDiv (∑ i, r i * deployedThetaF i) (2^127) := by
  unfold deployedOutput
  rw [deployedV_correct r hr, deployedW_correct r hr]

/-- Actual canonical residues from the captured full-coefficient Rust fixture. -/
def capturedResidues : Fin 6 → ℤ := ![9675007914, 2505552642, 57236360992, 4252961403400044537, 411888490947559416, 2145767979390943224]

/-- Nonvacuous source-instance witness, sharpness, and a falsifier for strict nearest
rounding of the source-selected lift, all checked independently by the Lean kernel. -/
theorem deployed_witness_inhabited :
    (∀ i : Fin 6, 0 ≤ capturedResidues i ∧ capturedResidues i < deployedBase i) ∧
    selectedLift deployedP capturedResidues deployedGarner (deployedV capturedResidues) =
      108454153028594899284870262370752 ∧
    deployedOutput capturedResidues = 172481 ∧
    roundDiv (deployedT * selectedLift deployedP capturedResidues deployedGarner
      (deployedV capturedResidues)) deployedQ = 172480 := by decide

/-- Kernel-checked reconstruction of the pinned constructor constants: the full
basis product, each Garner CRT selector and range, the nearest omega projection,
and the nearest fixed-point Garner projection. This validates the numeric table. -/
theorem deployed_constructor_constants :
    deployedP = ∏ i : Fin 6, deployedBase i ∧
    (∀ i : Fin 6, 0 ≤ deployedGarner i ∧ deployedGarner i < deployedP ∧
      (∀ j : Fin 6, deployedGarner i % deployedBase j = if i = j then 1 else 0)) ∧
    (∀ i : Fin 6, deployedOmega i = roundDiv (deployedT * deployedGarner i) deployedQ) ∧
    (∀ i : Fin 6, deployedThetaG i = roundDiv ((2^126) * deployedGarner i) deployedP) := by decide

end Minidregg.Compiler.FheRnsScale

/-- info: 'Minidregg.Compiler.FheRnsScale.round_add_multiple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.round_add_multiple
/-- info: 'Minidregg.Compiler.FheRnsScale.garner_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.garner_identity
/-- info: 'Minidregg.Compiler.FheRnsScale.garnerScaleDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.garnerScaleDecomposition
/-- info: 'Minidregg.Compiler.FheRnsScale.roundDiv_eq_nearest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.roundDiv_eq_nearest
/-- info: 'Minidregg.Compiler.FheRnsScale.oneSidedRoundingRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.oneSidedRoundingRefinement
/-- info: 'Minidregg.Compiler.FheRnsScale.ceil_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.ceil_error
/-- info: 'Minidregg.Compiler.FheRnsScale.weighted_ceil_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.weighted_ceil_error
/-- info: 'Minidregg.Compiler.FheRnsScale.ceil_corrected_rounding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.ceil_corrected_rounding
/-- info: 'Minidregg.Compiler.FheRnsScale.approximation_premise_inhabited' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.approximation_premise_inhabited
/-- info: 'Minidregg.Compiler.FheRnsScale.magnitude_falsifier' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.magnitude_falsifier
/-- info: 'Minidregg.Compiler.FheRnsScale.direction_falsifier' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.direction_falsifier
/-- info: 'Minidregg.Compiler.FheRnsScale.correction_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.correction_falsifier
/-- info: 'Minidregg.Compiler.FheRnsScale.captured_rounding_discrepancy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.captured_rounding_discrepancy
/-- info: 'Minidregg.Compiler.FheRnsScale.captured_error_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.captured_error_bound
/-- info: 'Minidregg.Compiler.FheRnsScale.output_exact_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.output_exact_iff
/-- info: 'Minidregg.Compiler.FheRnsScale.downscale_discrepancy_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.downscale_discrepancy_bound
/-- info: 'Minidregg.Compiler.FheRnsScale.wordCorrection_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.wordCorrection_correct
/-- info: 'Minidregg.Compiler.FheRnsScale.wordCorrection_range_falsifier' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.wordCorrection_range_falsifier
/-- info: 'Minidregg.Compiler.FheRnsScale.wordV126_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.wordV126_correct
/-- info: 'Minidregg.Compiler.FheRnsScale.wordV127_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.wordV127_correct
/-- info: 'Minidregg.Compiler.FheRnsScale.deployed_gamma_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployed_gamma_exact
/-- info: 'Minidregg.Compiler.FheRnsScale.deployed_thetaF_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployed_thetaF_exact
/-- info: 'Minidregg.Compiler.FheRnsScale.deployed_fixed_ranges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployed_fixed_ranges
/-- info: 'Minidregg.Compiler.FheRnsScale.deployed_residue_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployed_residue_mass
/-- info: 'Minidregg.Compiler.FheRnsScale.weighted_accumulator_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.weighted_accumulator_bound
/-- info: 'Minidregg.Compiler.FheRnsScale.deployed_correction_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployed_correction_range
/-- info: 'Minidregg.Compiler.FheRnsScale.deployed_garner_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployed_garner_range
/-- info: 'Minidregg.Compiler.FheRnsScale.deployedW_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployedW_correct
/-- info: 'Minidregg.Compiler.FheRnsScale.deployedV_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployedV_correct
/-- info: 'Minidregg.Compiler.FheRnsScale.deployed_source_arithmetic_envelope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployed_source_arithmetic_envelope
/-- info: 'Minidregg.Compiler.FheRnsScale.deployed_output_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployed_output_exact
/-- info: 'Minidregg.Compiler.FheRnsScale.deployed_witness_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployed_witness_inhabited
/-- info: 'Minidregg.Compiler.FheRnsScale.deployed_constructor_constants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsScale.deployed_constructor_constants
