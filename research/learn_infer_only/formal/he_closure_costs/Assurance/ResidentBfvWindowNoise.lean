/-
Actual Q83/window arithmetic instantiation of Theory.IntegerWindowNoise.
This is a source-equation theorem, NOT an implementation or security theorem.
The caller still owes fresh-sampler/coefficient equations, the modular RNS
phase/readout bridge, queue admission/currentness and a protected release.

Statement-first: ActualPremises and SignedWindowClaim precede proof work.
Positive premise inhabitant: 128 nonzero 577-coordinate rows, nonzero error
and a negative one-coordinate query. Teeth: same-plaintext replacement
leaves exact expiry debt and eventually misdecodes at these actual moduli.
-/
import Theory.IntegerWindowNoise

namespace Minidregg.Assurance.ResidentBfvWindowNoise
set_option autoImplicit false
open Minidregg.Theory.IntegerWindowNoise
open scoped BigOperators

def q83 : Int := 9671406214650060397780993
def t32 : Int := 4294828033
def ringDegree : Nat := 4096
def width : Nat := 577
def window : Nat := 128
def support : Int := 20
def coordinateBound : Int := 127
def freshBound : Int := 2 * (ringDegree : Int) * support ^ 2 + support
def queryBudget : Int := (width : Int) * coordinateBound
def scoreBudget : Int := (window : Int) * queryBudget * coordinateBound

def ActualPremises (xs : List (Row width)) (query : Fin width → Int) : Prop :=
  (∀ x ∈ xs, Fresh q83 t32 freshBound x) ∧ xs.length ≤ window ∧
  (∀ j, |query j| ≤ coordinateBound) ∧
  (∀ x ∈ xs, ∀ j, |x.message j| ≤ coordinateBound)

def SignedWindowClaim : Prop :=
  ∀ (xs : List (Row width)) (query : Fin width → Int) (wrap : Int),
    ActualPremises xs query →
    centered t32 (rounded q83 t32 (readoutPhase query xs + q83 * wrap)) = readoutScore query xs

theorem actual_modulus_product : (2199023190017 : Int) * 4398046486529 = q83 := by decide
theorem actual_fresh_bound : freshBound = 3276820 := by decide
theorem actual_query_budget : queryBudget = 73279 := by decide
theorem actual_score_budget : scoreBudget = 1191223424 := by decide
theorem actual_margin_lhs :
    2 * t32 * (window : Int) * queryBudget * (freshBound + 1) = 264008552994527828978432 := by decide
theorem actual_margin : 2 * t32 * (window : Int) * queryBudget * (freshBound + 1) < q83 := by decide
theorem actual_score_nonwrap : 2 * scoreBudget < t32 := by decide
theorem actual_polynomial_nonwrap : 2 * (width - 1) < ringDegree := by decide

/-- The sampler's support supplies this deterministic coefficient bound,
conditional on the two signed-convolution source expansions. -/
theorem actual_public_key_noise_bound
    (a b c d : Fin ringDegree → Int) (neg₁ neg₂ : Fin ringDegree → Bool) (e : Int)
    (ha : ∀ j, |a j| ≤ support) (hb : ∀ j, |b j| ≤ support)
    (hc : ∀ j, |c j| ≤ support) (hd : ∀ j, |d j| ≤ support) (he : |e| ≤ support) :
    |signedProductSum a b neg₁ + e + signedProductSum c d neg₂| ≤ freshBound := by
  exact public_key_noise_bound a b c d neg₁ neg₂ e support (by decide) ha hb hc hd he

theorem actual_window_correctness : WindowCorrectness q83 t32 freshBound queryBudget window := by
  exact window_correctness q83 t32 freshBound queryBudget window
    (by decide) (by decide) (by decide) actual_margin

theorem actual_signed_window : SignedWindowClaim := by
  intro xs query wrap h
  rcases h with ⟨hf, hlen, hquery, hm⟩
  have hL : queryL1 query ≤ queryBudget := queryL1_le query coordinateBound hquery
  have hscore := readout_score_bound query xs coordinateBound hm
  have hn : (xs.length : Int) ≤ window := by exact_mod_cast hlen
  have h0 : 0 ≤ queryL1 query := Finset.sum_nonneg (by intro j _; exact abs_nonneg _)
  have hM : |readoutScore query xs| ≤ scoreBudget := by
    calc
      |readoutScore query xs| ≤ (xs.length : Int) * (queryL1 query * coordinateBound) := by
        simpa only [mul_assoc] using hscore
      _ ≤ (window : Int) * (queryBudget * coordinateBound) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_right hL (by decide))
          (mul_nonneg h0 (by decide)) (by decide)
      _ = scoreBudget := by simp only [scoreBudget, mul_assoc]
  apply window_signed_correctness q83 t32 freshBound queryBudget window
    (by decide) (by decide) (by decide) actual_margin xs query wrap hf hlen hL
  have := actual_score_nonwrap
  omega

def firstCoordinate : Fin width := ⟨0, by decide⟩

def witnessQuery (j : Fin width) : Int := if j = firstCoordinate then -1 else 0
def witnessRow : Row width where
  message := fun j => if j = firstCoordinate then 1 else 0
  error := fun j => if j = firstCoordinate then 1 else 0
  phase := fun j => q83 * (if j = firstCoordinate then 1 else 0) / t32 + (if j = firstCoordinate then 1 else 0)
def witnessWindow : List (Row width) := List.replicate window witnessRow

theorem witness_fresh : Fresh q83 t32 freshBound witnessRow := by
  intro j
  constructor
  · rfl
  · by_cases hj : j = firstCoordinate <;> simp [witnessRow, hj, freshBound, ringDegree, support]

theorem witness_premises : ActualPremises witnessWindow witnessQuery := by
  constructor
  · intro x hx
    have h : x = witnessRow := by simpa [witnessWindow, window] using hx
    subst x
    exact witness_fresh
  constructor
  · simp [witnessWindow]
  constructor
  · intro j
    by_cases hj : j = firstCoordinate <;> simp [witnessQuery, hj, coordinateBound]
  · intro x hx j
    have h : x = witnessRow := by simpa [witnessWindow, window] using hx
    subst x
    by_cases hj : j = firstCoordinate <;> simp [witnessRow, hj, coordinateBound]

theorem witness_row_score : rowScore witnessQuery witnessRow = -1 := by
  simp [rowScore, witnessQuery, witnessRow]

theorem witness_score : readoutScore witnessQuery witnessWindow = -128 := by
  simp [readoutScore, witnessWindow, witness_row_score, window]

theorem witness_nonzero_error : witnessRow.error firstCoordinate = 1 := by decide

theorem premise_inhabitation :
    ∃ xs query, ActualPremises xs query ∧ readoutScore query xs = -128 :=
  ⟨witnessWindow, witnessQuery, witness_premises, witness_score⟩

theorem honest_signed_readout (wrap : Int) :
    centered t32 (rounded q83 t32 (readoutPhase witnessQuery witnessWindow + q83 * wrap)) = -128 := by
  rw [actual_signed_window witnessWindow witnessQuery wrap witness_premises, witness_score]

/-- Replacing each expired zero phase by another valid zero phase 1 leaves
one unit of debt per expiry, despite both decrypting to the same plaintext.
This abstract scalar falsifier is distinct from the executed BFV fixtures. -/
def wrongExpiryDebt : Nat → Int
  | 0 => 0
  | n + 1 => wrongExpiryDebt n - 1

theorem wrong_expiry_debt (n : Nat) : wrongExpiryDebt n = -(n : Int) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wrongExpiryDebt, ih]; omega

theorem replacement_same_plaintext : rounded q83 t32 0 = 0 ∧ rounded q83 t32 1 = 0 := by decide

def failureStep : Nat := (q83 / (2 * t32) + 1).toNat

theorem wrong_expiry_actual_misses :
    centered t32 (rounded q83 t32 (wrongExpiryDebt failureStep)) = -1 := by
  rw [wrong_expiry_debt]
  decide

theorem wrong_expiry_not_exact_queue : wrongExpiryDebt failureStep ≠ 0 := by
  rw [wrong_expiry_debt]
  decide

/-- Removing the noise-budget premise admits a valid floor-encoded row
whose error changes the output. This tiny arithmetic control is not BFV. -/
def excessiveNoise : Row 1 := ⟨fun _ => 0, fun _ => 3, fun _ => 3⟩
theorem omitted_margin_fails :
    Fresh 17 3 3 excessiveNoise ∧
    centered 3 (rounded 17 3 (readoutPhase (fun _ => 1) [excessiveNoise])) ≠
      readoutScore (fun _ => 1) [excessiveNoise] := by
  unfold Fresh
  decide

/-- A valid modular decoding statement does not imply an unbounded signed
integer output: the strict nonwrap bound is a separate real premise. -/
def wrappedMessage : Row 1 := ⟨fun _ => 2, fun _ => 0, fun _ => 11⟩
theorem omitted_signed_range_fails :
    Fresh 17 3 0 wrappedMessage ∧
    2 * (3 : Int) * 1 * 1 * (0 + 1) < 17 ∧
    centered 3 (rounded 17 3 (readoutPhase (fun _ => 1) [wrappedMessage])) ≠
      readoutScore (fun _ => 1) [wrappedMessage] := by
  unfold Fresh
  decide

/- Axiom closure pins: mathematical Lean foundations only; no added axioms. -/
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_modulus_product' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_modulus_product
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_fresh_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_fresh_bound
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_query_budget' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_query_budget
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_score_budget' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_score_budget
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_margin_lhs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_margin_lhs
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_margin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_margin
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_score_nonwrap' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_score_nonwrap
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_polynomial_nonwrap' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_polynomial_nonwrap
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_public_key_noise_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_public_key_noise_bound
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_window_correctness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_window_correctness
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.actual_signed_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.actual_signed_window
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.witness_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.witness_fresh
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.witness_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.witness_premises
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.witness_row_score' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.witness_row_score
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.witness_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.witness_score
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.witness_nonzero_error' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.witness_nonzero_error
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.premise_inhabitation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.premise_inhabitation
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.honest_signed_readout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.honest_signed_readout
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.wrong_expiry_debt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.wrong_expiry_debt
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.replacement_same_plaintext' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.replacement_same_plaintext
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.wrong_expiry_actual_misses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.wrong_expiry_actual_misses
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.wrong_expiry_not_exact_queue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.wrong_expiry_not_exact_queue
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.omitted_margin_fails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.omitted_margin_fails
/-- info: 'Minidregg.Assurance.ResidentBfvWindowNoise.omitted_signed_range_fails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowNoise.omitted_signed_range_fails

end Minidregg.Assurance.ResidentBfvWindowNoise
