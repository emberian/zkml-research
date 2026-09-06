/-
Statement-first target: a bounded current list of floor-encoded rows has a
history-independent signed readout margin. This is integer algebra under
explicit source-phase equations, NOT a Rust/RNS or cryptographic theorem.

ATLAS obligations: WindowCorrectness below is the keystone Prop. The concrete
Assurance module supplies actual-parameter arithmetic, nonzero positive
inhabitation, and a wrong-expiry / same-plaintext falsifier. A ciphertext
queue theorem can supply the current list and its length, but its modular
phase-to-integer-lift correspondence remains an explicit implementation floor.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace Minidregg.Theory.IntegerWindowNoise
set_option autoImplicit false
open scoped BigOperators

structure Row (r : Nat) where
  message : Fin r → Int
  error : Fin r → Int
  phase : Fin r → Int

def Fresh {r : Nat} (q t E : Int) (x : Row r) : Prop :=
  ∀ j, x.phase j = q * x.message j / t + x.error j ∧ |x.error j| ≤ E

def queryL1 {r : Nat} (query : Fin r → Int) : Int := ∑ j, |query j|
def rowPhase {r : Nat} (query : Fin r → Int) (x : Row r) : Int :=
  ∑ j, query j * x.phase j
def rowScore {r : Nat} (query : Fin r → Int) (x : Row r) : Int :=
  ∑ j, query j * x.message j
def readoutPhase {r : Nat} (query : Fin r → Int) (xs : List (Row r)) : Int :=
  (xs.map (rowPhase query)).sum
def readoutScore {r : Nat} (query : Fin r → Int) (xs : List (Row r)) : Int :=
  (xs.map (rowScore query)).sum

/-- Exact integer round-half-up; strict margins exclude ties. -/
def rounded (q t phase : Int) : Int := (2 * t * phase + q) / (2 * q)
def centered (t value : Int) : Int :=
  if 2 * (value % t) < t then value % t else value % t - t

/-- The current window, not elapsed lifetime, bounds the release error.
The arbitrary integer wrap permits a source/RNS readout lift modulo q. -/
def WindowCorrectness (q t E L : Int) (W : Nat) : Prop :=
  ∀ (r : Nat) (xs : List (Row r)) (query : Fin r → Int) (wrap : Int),
    (∀ x ∈ xs, Fresh q t E x) → xs.length ≤ W → queryL1 query ≤ L →
    rounded q t (readoutPhase query xs + q * wrap) % t = readoutScore query xs % t

theorem floor_scaled_residual (q t m e : Int) :
    t * (q * m / t + e) - q * m = t * e - (q * m % t) := by
  have h := Int.mul_ediv_add_emod (q * m) t
  nlinarith

theorem fresh_residual_bound (q t E m e : Int) (ht : 0 < t)
    (he : |e| ≤ E) :
    |t * (q * m / t + e) - q * m| ≤ t * (E + 1) := by
  rw [floor_scaled_residual]
  have hmod0 : 0 ≤ q * m % t := Int.emod_nonneg _ (ne_of_gt ht)
  have hmodlt : q * m % t < t := Int.emod_lt_of_pos _ ht
  calc
    |t * e - q * m % t| ≤ |t * e| + |q * m % t| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (t * e) (-(q * m % t))
    _ = t * |e| + q * m % t := by rw [abs_mul, abs_of_pos ht, abs_of_nonneg hmod0]
    _ ≤ t * E + t := by
      have := mul_le_mul_of_nonneg_left he ht.le
      omega
    _ = t * (E + 1) := by ring

theorem row_scaled_residual {r : Nat} (q t : Int)
    (query : Fin r → Int) (x : Row r) :
    t * rowPhase query x - q * rowScore query x =
      ∑ j, query j * (t * x.phase j - q * x.message j) := by
  simp only [rowPhase, rowScore, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem row_residual_bound {r : Nat} (q t E : Int) (ht : 0 < t)
    (query : Fin r → Int) (x : Row r) (hx : Fresh q t E x) :
    |t * rowPhase query x - q * rowScore query x| ≤ queryL1 query * (t * (E + 1)) := by
  rw [row_scaled_residual]
  calc
    |∑ j, query j * (t * x.phase j - q * x.message j)| ≤
        ∑ j, |query j * (t * x.phase j - q * x.message j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |query j| * |t * x.phase j - q * x.message j| := by simp only [abs_mul]
    _ ≤ ∑ j, |query j| * (t * (E + 1)) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [(hx j).1]
      exact fresh_residual_bound q t E (x.message j) (x.error j) ht (hx j).2
    _ = queryL1 query * (t * (E + 1)) := by rw [queryL1, Finset.sum_mul]

theorem list_residual_bound {r : Nat} (q t E : Int) (ht : 0 < t)
    (query : Fin r → Int) (xs : List (Row r))
    (hf : ∀ x ∈ xs, Fresh q t E x) :
    |t * readoutPhase query xs - q * readoutScore query xs| ≤
      (xs.length : Int) * (queryL1 query * (t * (E + 1))) := by
  induction xs with
  | nil => simp [readoutPhase, readoutScore]
  | cons x xs ih =>
    have hx := row_residual_bound q t E ht query x (hf x (by simp))
    have hs := ih (by intro y hy; exact hf y (by simp [hy]))
    have heq : t * readoutPhase query (x :: xs) - q * readoutScore query (x :: xs) =
        (t * rowPhase query x - q * rowScore query x) +
        (t * readoutPhase query xs - q * readoutScore query xs) := by
      simp only [readoutPhase, readoutScore, List.map_cons, List.sum_cons]
      ring
    rw [heq]
    have ha := abs_add_le (t * rowPhase query x - q * rowScore query x)
      (t * readoutPhase query xs - q * readoutScore query xs)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem rounded_exact_of_residual (q t p m : Int) (hq : 0 < q)
    (hmargin : 2 * |t * p - q * m| < q) : rounded q t p = m := by
  have hlow : m * (2 * q) ≤ 2 * t * p + q := by
    have := neg_abs_le (t * p - q * m)
    nlinarith
  have hhigh : 2 * t * p + q < (m + 1) * (2 * q) := by
    have := le_abs_self (t * p - q * m)
    nlinarith
  have h2q : 0 < 2 * q := by omega
  unfold rounded
  have hlo := (Int.le_ediv_iff_mul_le h2q).mpr hlow
  have hhi := (Int.ediv_lt_iff_lt_mul h2q).mpr hhigh
  omega

theorem window_correctness (q t E L : Int) (W : Nat)
    (hq : 0 < q) (ht : 0 < t) (hE : 0 ≤ E)
    (hbudget : 2 * t * (W : Int) * L * (E + 1) < q) :
    WindowCorrectness q t E L W := by
  intro r xs query wrap hf hlen hquery
  have hres := list_residual_bound q t E ht query xs hf
  have hqn : 0 ≤ queryL1 query := Finset.sum_nonneg (by intro j _; exact abs_nonneg _)
  have hte : 0 ≤ t * (E + 1) := mul_nonneg ht.le (by omega)
  have hn : (xs.length : Int) ≤ W := by exact_mod_cast hlen
  have hb1 : (xs.length : Int) * (queryL1 query * (t * (E + 1))) ≤
      (W : Int) * (L * (t * (E + 1))) := by
    apply mul_le_mul hn
    · exact mul_le_mul_of_nonneg_right hquery hte
    · exact mul_nonneg hqn hte
    · exact_mod_cast Nat.zero_le W
  have hb : 2 * |t * readoutPhase query xs - q * readoutScore query xs| < q := by
    nlinarith
  have heq : t * (readoutPhase query xs + q * wrap) -
      q * (readoutScore query xs + t * wrap) =
      t * readoutPhase query xs - q * readoutScore query xs := by ring
  have hround := rounded_exact_of_residual q t
    (readoutPhase query xs + q * wrap) (readoutScore query xs + t * wrap) hq (by rw [heq]; exact hb)
  rw [hround]
  simp [Int.add_emod]

theorem centered_exact (t m : Int) (hm : 2 * |m| < t) :
    centered t m = m := by
  unfold centered
  by_cases hnonneg : 0 ≤ m
  · have hmt : m < t := by have := le_abs_self m; omega
    rw [Int.emod_eq_of_lt hnonneg hmt]
    rw [if_pos (by rwa [abs_of_nonneg hnonneg] at hm)]
  · have hmneg : m < 0 := by omega
    have hmlo : 0 ≤ m + t := by have := neg_abs_le m; omega
    have hmhi : m + t < t := by omega
    have hmod : m % t = m + t := by
      have h := Int.emod_eq_of_lt hmlo hmhi
      simpa [Int.add_emod] using h
    rw [hmod, if_neg (by rw [abs_of_neg hmneg] at hm; omega)]
    omega

theorem window_signed_correctness (q t E L : Int) (W : Nat)
    (hq : 0 < q) (ht : 0 < t) (hE : 0 ≤ E)
    (hbudget : 2 * t * (W : Int) * L * (E + 1) < q)
    {r : Nat} (xs : List (Row r)) (query : Fin r → Int) (wrap : Int)
    (hf : ∀ x ∈ xs, Fresh q t E x) (hlen : xs.length ≤ W)
    (hquery : queryL1 query ≤ L) (hscore : 2 * |readoutScore query xs| < t) :
    centered t (rounded q t (readoutPhase query xs + q * wrap)) = readoutScore query xs := by
  have h := window_correctness q t E L W hq ht hE hbudget r xs query wrap hf hlen hquery
  unfold centered
  rw [h]
  exact centered_exact t (readoutScore query xs) hscore

theorem signed_query_split {r : Nat} (query value : Fin r → Int) :
    (∑ j, query j * value j) =
      (∑ j, max (query j) 0 * value j) - (∑ j, max (-query j) 0 * value j) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hq : query j = max (query j) 0 - max (-query j) 0 := by omega
  calc query j * value j = (max (query j) 0 - max (-query j) 0) * value j := congrArg (· * value j) hq
       _ = _ := by ring

theorem readout_positive_negative_split {r : Nat} (query : Fin r → Int) (xs : List (Row r)) :
    readoutPhase query xs = readoutPhase (fun j => max (query j) 0) xs -
      readoutPhase (fun j => max (-query j) 0) xs := by
  induction xs with
  | nil => simp [readoutPhase]
  | cons x xs ih =>
    have hr := signed_query_split query x.phase
    change rowPhase query x = rowPhase (fun j => max (query j) 0) x -
      rowPhase (fun j => max (-query j) 0) x at hr
    simp only [readoutPhase, List.map_cons, List.sum_cons] at ih ⊢
    linarith

/-- Splitting a signed query does not double its total amplification budget. -/
theorem split_queryL1 {r : Nat} (query : Fin r → Int) :
    queryL1 (fun j => max (query j) 0) + queryL1 (fun j => max (-query j) 0) = queryL1 query := by
  unfold queryL1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_of_nonneg (le_max_right _ _), abs_of_nonneg (le_max_right _ _)]
  change max (query j) 0 + max (-query j) 0 = |query j|
  by_cases h : 0 ≤ query j
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by omega)]
    omega
  · rw [abs_of_neg (by omega), max_eq_right (by omega), max_eq_left (by omega)]
    omega

theorem floor_encoding_shift (q t m k : Int) (ht : t ≠ 0) :
    q * (m + t * k) / t = q * m / t + q * k := by
  have h : q * (m + t * k) = q * m + (q * k) * t := by ring
  rw [h, Int.add_mul_ediv_right _ _ ht]

/-- Exact finite-sum correction: division does not commute with addition. -/
theorem floor_carry_exact (q t : Int) (ms : List Int) (ht : 0 < t) :
    (ms.map (fun m => q * m / t)).sum - q * ms.sum / t =
      -((ms.map (fun m => q * m % t)).sum / t) := by
  have hid : q * ms.sum =
      (ms.map (fun m => q * m / t)).sum * t + (ms.map (fun m => q * m % t)).sum := by
    induction ms with
    | nil => simp
    | cons m ms ih =>
      have h := Int.mul_ediv_add_emod (q * m) t
      simp only [List.map_cons, List.sum_cons]
      nlinarith
  rw [hid]
  rw [mul_comm ((ms.map (fun m => q * m / t)).sum) t]
  rw [Int.mul_add_ediv_left _ _ (ne_of_gt ht)]
  ring

theorem floor_carry_bounds (q t : Int) (ms : List Int) (ht : 0 < t) (hms : ms ≠ []) :
    -((ms.length : Int) - 1) ≤ (ms.map (fun m => q * m / t)).sum - q * ms.sum / t ∧
      (ms.map (fun m => q * m / t)).sum - q * ms.sum / t ≤ 0 := by
  have hr : 0 ≤ (ms.map (fun m => q * m % t)).sum ∧
      (ms.map (fun m => q * m % t)).sum ≤ (ms.length : Int) * (t - 1) := by
    clear hms
    induction ms with
    | nil => simp
    | cons m ms ih =>
      have h0 := Int.emod_nonneg (q * m) (ne_of_gt ht)
      have hlt := Int.emod_lt_of_pos (q * m) ht
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      constructor <;> nlinarith [ih.1, ih.2]
  have hn : (0 : Int) < ms.length := by cases ms <;> simp_all
  have hd0 : 0 ≤ (ms.map (fun m => q * m % t)).sum / t := Int.ediv_nonneg hr.1 ht.le
  have hdlt : (ms.map (fun m => q * m % t)).sum / t < (ms.length : Int) :=
    (Int.ediv_lt_iff_lt_mul ht).mpr (by nlinarith [hr.2])
  rw [floor_carry_exact q t ms ht]
  omega

theorem queryL1_le {r : Nat} (query : Fin r → Int) (B : Int)
    (hquery : ∀ j, |query j| ≤ B) : queryL1 query ≤ (r : Int) * B := by
  unfold queryL1
  calc (∑ j, |query j|) ≤ ∑ _j : Fin r, B := Finset.sum_le_sum (by intro j _; exact hquery j)
       _ = _ := by simp

theorem row_score_bound {r : Nat} (query : Fin r → Int) (x : Row r) (B : Int)
    (hm : ∀ j, |x.message j| ≤ B) : |rowScore query x| ≤ queryL1 query * B := by
  unfold rowScore
  calc |∑ j, query j * x.message j| ≤ ∑ j, |query j * x.message j| := Finset.abs_sum_le_sum_abs _ _
       _ = ∑ j, |query j| * |x.message j| := by simp only [abs_mul]
       _ ≤ ∑ j, |query j| * B := by
         apply Finset.sum_le_sum
         intro j _
         exact mul_le_mul_of_nonneg_left (hm j) (abs_nonneg _)
       _ = queryL1 query * B := by rw [queryL1, Finset.sum_mul]

theorem readout_score_bound {r : Nat} (query : Fin r → Int) (xs : List (Row r)) (B : Int)
    (hm : ∀ x ∈ xs, ∀ j, |x.message j| ≤ B) :
    |readoutScore query xs| ≤ (xs.length : Int) * (queryL1 query * B) := by
  induction xs with
  | nil => simp [readoutScore]
  | cons x xs ih =>
    have hx := row_score_bound query x B (hm x (by simp))
    have hs := ih (by intro y hy; exact hm y (by simp [hy]))
    change |rowScore query x + readoutScore query xs| ≤ _
    have ha := abs_add_le (rowScore query x) (readoutScore query xs)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

def signedProductSum {n : Nat} (a b : Fin n → Int) (negative : Fin n → Bool) : Int :=
  ∑ j, if negative j then -(a j * b j) else a j * b j

/-- Each negacyclic coefficient has n signed products. The caller must supply
that coefficient expansion; no Rust polynomial representation is modeled. -/
theorem signedProductSum_bound {n : Nat} (a b : Fin n → Int) (negative : Fin n → Bool)
    (S : Int) (hS : 0 ≤ S) (ha : ∀ j, |a j| ≤ S) (hb : ∀ j, |b j| ≤ S) :
    |signedProductSum a b negative| ≤ (n : Int) * S ^ 2 := by
  unfold signedProductSum
  calc |∑ j, if negative j then -(a j * b j) else a j * b j| ≤
        ∑ j, |if negative j then -(a j * b j) else a j * b j| := Finset.abs_sum_le_sum_abs _ _
       _ = ∑ j, |a j| * |b j| := by
         apply Finset.sum_congr rfl
         intro j _
         cases negative j <;> simp [abs_mul]
       _ ≤ ∑ _j : Fin n, S ^ 2 := by
         apply Finset.sum_le_sum
         intro j _
         simpa [pow_two] using mul_le_mul (ha j) (hb j) (abs_nonneg (b j)) hS
       _ = _ := by simp

theorem public_key_noise_bound {n : Nat}
    (a b c d : Fin n → Int) (neg₁ neg₂ : Fin n → Bool) (e S : Int)
    (hS : 0 ≤ S) (ha : ∀ j, |a j| ≤ S) (hb : ∀ j, |b j| ≤ S)
    (hc : ∀ j, |c j| ≤ S) (hd : ∀ j, |d j| ≤ S) (he : |e| ≤ S) :
    |signedProductSum a b neg₁ + e + signedProductSum c d neg₂| ≤
      2 * (n : Int) * S ^ 2 + S := by
  have h₁ := signedProductSum_bound a b neg₁ S hS ha hb
  have h₂ := signedProductSum_bound c d neg₂ S hS hc hd
  have h₃ := abs_add_le (signedProductSum a b neg₁) e
  have h₄ := abs_add_le (signedProductSum a b neg₁ + e) (signedProductSum c d neg₂)
  nlinarith

/- Axiom closure pins: mathematical Lean foundations only; no added axioms. -/
/-- info: 'Minidregg.Theory.IntegerWindowNoise.floor_scaled_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.floor_scaled_residual
/-- info: 'Minidregg.Theory.IntegerWindowNoise.fresh_residual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.fresh_residual_bound
/-- info: 'Minidregg.Theory.IntegerWindowNoise.row_scaled_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.row_scaled_residual
/-- info: 'Minidregg.Theory.IntegerWindowNoise.row_residual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.row_residual_bound
/-- info: 'Minidregg.Theory.IntegerWindowNoise.list_residual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.list_residual_bound
/-- info: 'Minidregg.Theory.IntegerWindowNoise.rounded_exact_of_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.rounded_exact_of_residual
/-- info: 'Minidregg.Theory.IntegerWindowNoise.window_correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.window_correctness
/-- info: 'Minidregg.Theory.IntegerWindowNoise.centered_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.centered_exact
/-- info: 'Minidregg.Theory.IntegerWindowNoise.window_signed_correctness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.window_signed_correctness
/-- info: 'Minidregg.Theory.IntegerWindowNoise.signed_query_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.signed_query_split
/-- info: 'Minidregg.Theory.IntegerWindowNoise.readout_positive_negative_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.readout_positive_negative_split
/-- info: 'Minidregg.Theory.IntegerWindowNoise.split_queryL1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.split_queryL1
/-- info: 'Minidregg.Theory.IntegerWindowNoise.floor_encoding_shift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.floor_encoding_shift
/-- info: 'Minidregg.Theory.IntegerWindowNoise.floor_carry_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.floor_carry_exact
/-- info: 'Minidregg.Theory.IntegerWindowNoise.floor_carry_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.floor_carry_bounds
/-- info: 'Minidregg.Theory.IntegerWindowNoise.queryL1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.queryL1_le
/-- info: 'Minidregg.Theory.IntegerWindowNoise.row_score_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.row_score_bound
/-- info: 'Minidregg.Theory.IntegerWindowNoise.readout_score_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.readout_score_bound
/-- info: 'Minidregg.Theory.IntegerWindowNoise.signedProductSum_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.signedProductSum_bound
/-- info: 'Minidregg.Theory.IntegerWindowNoise.public_key_noise_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.IntegerWindowNoise.public_key_noise_bound

end Minidregg.Theory.IntegerWindowNoise
