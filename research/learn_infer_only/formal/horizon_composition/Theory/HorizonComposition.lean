import Mathlib

/-! Finite hybrid arithmetic only. No cryptographic experiment implementation. -/
namespace Minidregg.Theory.HorizonComposition
open Finset

def Node (B : ℕ) : ℕ → Type
  | 0 => Unit
  | H + 1 => Unit ⊕ (Fin B × Node B H)

instance nodeFintype (B : ℕ) : (H : ℕ) → Fintype (Node B H)
  | 0 => inferInstanceAs (Fintype Unit)
  | H+1 => letI := nodeFintype B H
      inferInstanceAs (Fintype (Unit ⊕ (Fin B × Node B H)))

def root (B : ℕ) : (H : ℕ) → Node B H
  | 0 => ()
  | _ + 1 => Sum.inl ()

def sub {B H : ℕ} {α : Type} (f : Node B (H + 1) → α) (b : Fin B) : Node B H → α :=
  fun n => f (Sum.inr (b,n))

structure Frame where
  realLeft : ℚ
  idealLeft : ℚ
  idealRight : ℚ
  realRight : ℚ
  deriving DecidableEq

def Frame.gap (f : Frame) : ℚ := f.realLeft - f.realRight
def Frame.leftGap (f : Frame) : ℚ := f.realLeft - f.idealLeft
def Frame.rightGap (f : Frame) : ℚ := f.realRight - f.idealRight
def Frame.middleGap (f : Frame) : ℚ := f.idealLeft - f.idealRight
def Frame.probabilities (f : Frame) : Prop :=
  f.realLeft ∈ Set.Icc 0 1 ∧ f.idealLeft ∈ Set.Icc 0 1 ∧
  f.idealRight ∈ Set.Icc 0 1 ∧ f.realRight ∈ Set.Icc 0 1

def Coherent {B : ℕ} : {H : ℕ} → (Node B H → Frame) → Prop
  | 0, f => (f (root B 0)).middleGap = 0
  | H+1, f => (f (root B (H+1))).middleGap =
      ∑ b : Fin B, (sub f b (root B H)).gap ∧ ∀ b, Coherent (sub f b)

/-- Statement-first keystone: the local coherent-frame obligations force the
complete sum; the terminal-zero obligation is part of `Coherent`, not erased. -/
def TelescopingClaim : Prop := ∀ (B H : ℕ) (f : Node B H → Frame),
  Coherent f → (f (root B H)).gap = ∑ n, ((f n).leftGap - (f n).rightGap)

theorem frame_decomposition (f : Frame) :
    f.gap = f.leftGap + f.middleGap - f.rightGap := by
  unfold Frame.gap Frame.leftGap Frame.middleGap Frame.rightGap
  ring

theorem sum_nodes_succ {B H : ℕ} {α : Type} [AddCommMonoid α]
    (f : Node B (H+1) → α) :
    (∑ n, f n) = f (root B (H+1)) + ∑ b : Fin B, ∑ n, sub f b n := by
  change (∑ n : Unit ⊕ (Fin B × Node B H), f n) = _
  simp [root, sub, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem telescoping : TelescopingClaim := by
  intro B H
  induction H with
  | zero =>
    intro f h
    have hmid : (f (root B 0)).middleGap = 0 := h
    have step := frame_decomposition (f (root B 0))
    rw [hmid, add_zero] at step
    simpa [Node, root] using step
  | succ H ih =>
    intro f h
    rcases h with ⟨hm, hc⟩
    rw [sum_nodes_succ]
    have children : (∑ b : Fin B, (sub f b (root B H)).gap) =
        ∑ b : Fin B, ∑ n, ((sub f b n).leftGap - (sub f b n).rightGap) := by
      apply Finset.sum_congr rfl
      intro b _
      exact ih (sub f b) (hc b)
    have step := frame_decomposition (f (root B (H+1)))
    rw [hm,children] at step
    simp only [sub] at step ⊢
    linarith

def nodeCount (B H : ℕ) : ℕ := ∑ d ∈ range (H+1), B^d

theorem nodeCount_succ (B H : ℕ) : nodeCount B (H+1) = 1 + B * nodeCount B H := by
  unfold nodeCount
  rw [Finset.sum_range_succ']
  simp only [pow_zero, pow_succ', ← Finset.mul_sum]
  omega

theorem card_nodes (B H : ℕ) : Fintype.card (Node B H) = nodeCount B H := by
  induction H with
  | zero => simp [Node, nodeCount]
  | succ H ih =>
    have h := sum_nodes_succ (B:=B) (H:=H) (fun _ => (1:ℕ))
    simpa [nodeCount_succ, sub, ih] using h

theorem nodeCount_pos (B H : ℕ) : 0 < nodeCount B H := by
  rw [← card_nodes]
  letI : Nonempty (Node B H) := ⟨root B H⟩
  exact Fintype.card_pos

def Frame.realTest (f : Frame) (right : Bool) : ℚ :=
  if right then 1 - f.realRight else f.realLeft
def Frame.idealTest (f : Frame) (right : Bool) : ℚ :=
  if right then 1 - f.idealRight else f.idealLeft

/-- Complementing the right output bit reverses that Real-minus-Ideal gap. -/
theorem side_sum (f : Frame) :
    (∑ s : Bool, (f.realTest s - f.idealTest s)) = f.leftGap - f.rightGap := by
  simp [Frame.realTest, Frame.idealTest, Frame.leftGap, Frame.rightGap]
  ring

def average {α : Type} [Fintype α] (f : α → ℚ) : ℚ :=
  (∑ a, f a) / Fintype.card α

def uniformGap {B H : ℕ} (f : Node B H → Frame) : ℚ :=
  average (fun x : Node B H × Bool => (f x.1).realTest x.2) -
  average (fun x : Node B H × Bool => (f x.1).idealTest x.2)

def UniformClaim : Prop := ∀ (B H : ℕ) (f : Node B H → Frame),
  Coherent f → uniformGap f = (f (root B H)).gap / (2 * nodeCount B H)

theorem uniform_side_average : UniformClaim := by
  intro B H f hf
  unfold uniformGap average
  rw [← sub_div, ← Finset.sum_sub_distrib, Fintype.sum_prod_type]
  simp_rw [side_sum]
  rw [← telescoping B H f hf]
  simp [Fintype.card_prod, card_nodes, mul_comm]

theorem uniform_gap_zero_iff {B H : ℕ} (f : Node B H → Frame) (hf : Coherent f) :
    uniformGap f = 0 ↔ (f (root B H)).gap = 0 := by
  have hpos : (nodeCount B H : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (nodeCount_pos B H))
  rw [uniform_side_average B H f hf]
  simp [div_eq_zero_iff,hpos]

theorem complemented_probabilities (f : Frame) (hf : f.probabilities) (s : Bool) :
    f.realTest s ∈ Set.Icc 0 1 ∧ f.idealTest s ∈ Set.Icc 0 1 := by
  rcases hf with ⟨⟨h0,h1⟩,⟨h2,h3⟩,⟨h4,h5⟩,⟨h6,h7⟩⟩
  cases s <;> simp only [Frame.realTest, Frame.idealTest, Bool.false_eq_true,
    ↓reduceIte, Set.mem_Icc]
  · exact ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
  · constructor <;> constructor <;> linarith

def depth {B : ℕ} : {H : ℕ} → Node B H → ℕ
  | 0, _ => 0
  | _+1, Sum.inl _ => 0
  | _+1, Sum.inr (_,n) => depth n + 1

theorem depth_le {B H : ℕ} (n : Node B H) : depth n ≤ H := by
  induction H with
  | zero => simp [depth]
  | succ H ih =>
    cases n with
    | inl u => simp [depth]
    | inr p => simpa [depth] using Nat.succ_le_succ (ih p.2)

/-- Count a depth using existing finite sums of indicators. -/
def levelCount (B H d : ℕ) : ℕ := ∑ n : Node B H, if depth n = d then 1 else 0

theorem levelCount_zero (B H : ℕ) : levelCount B H 0 = 1 := by
  cases H with
  | zero => simp [levelCount, Node, depth]
  | succ H =>
    unfold levelCount
    rw [sum_nodes_succ]
    simp [root, sub, depth]

theorem levelCount_succ (B H d : ℕ) :
    levelCount B (H+1) (d+1) = B * levelCount B H d := by
  unfold levelCount
  rw [sum_nodes_succ]
  simp [root, sub, depth]

theorem levelCount_exact (B H d : ℕ) (hd : d ≤ H) : levelCount B H d = B^d := by
  induction H generalizing d with
  | zero =>
    have : d=0 := by omega
    subst d
    simp [levelCount_zero]
  | succ H ih =>
    cases d with
    | zero => simp [levelCount_zero]
    | succ d => rw [levelCount_succ, ih d (by omega), pow_succ']

def depthWeight (B H d : ℕ) : ℚ := (levelCount B H d : ℚ) / nodeCount B H

theorem uniform_depth_weight (B H d : ℕ) (hd : d ≤ H) :
    depthWeight B H d = (B:ℚ)^d / nodeCount B H := by
  simp [depthWeight, levelCount_exact B H d hd]

theorem depth_weights_sum_one (B H : ℕ) :
    (∑ d ∈ range (H+1), depthWeight B H d) = 1 := by
  have hpos : (nodeCount B H : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (nodeCount_pos B H))
  simp_rw [depthWeight]
  rw [← Finset.sum_div]
  have hn : (∑ d ∈ range (H+1), (levelCount B H d:ℚ)) = nodeCount B H := by
    norm_cast
    apply Finset.sum_congr rfl
    intro d hd
    exact levelCount_exact B H d (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hd))
  rw [hn,div_self hpos]

theorem uniform_depth_probability (B H d : ℕ) :
    average (fun n : Node B H => if depth n = d then (1:ℚ) else 0) = depthWeight B H d := by
  simp [average, depthWeight, levelCount, card_nodes]

def depthGapSum {B H : ℕ} (f : Node B H → Frame) (d : ℕ) : ℚ :=
  ∑ n, if depth n = d then (f n).leftGap - (f n).rightGap else 0

theorem sum_depth_gaps {B H : ℕ} (f : Node B H → Frame) :
    (∑ d ∈ range (H+1), depthGapSum f d) = ∑ n, ((f n).leftGap - (f n).rightGap) := by
  unfold depthGapSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp [Finset.mem_range, depth_le n]

def depthSideMean {B H : ℕ} (f : Node B H → Frame) (d : ℕ) : ℚ :=
  depthGapSum f d / (2 * levelCount B H d)

/-- Each depth must carry mass B^d/N_H, not 1/(H+1). -/
theorem weighted_depth_average {B H : ℕ} (hB : 0 < B) (f : Node B H → Frame) :
    (∑ d ∈ range (H+1), depthWeight B H d * depthSideMean f d) = uniformGap f := by
  have hpos : (nodeCount B H : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (nodeCount_pos B H))
  have heq : (∑ d ∈ range (H+1), depthWeight B H d * depthSideMean f d) =
      (∑ d ∈ range (H+1), depthGapSum f d) / (2 * nodeCount B H) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : d ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    have hlevel : (levelCount B H d:ℚ) ≠ 0 := by
      rw [levelCount_exact B H d hd']
      exact_mod_cast (Nat.ne_of_gt (pow_pos hB d))
    unfold depthWeight depthSideMean
    field_simp
  rw [heq,sum_depth_gaps]
  unfold uniformGap average
  rw [← sub_div, ← Finset.sum_sub_distrib, Fintype.sum_prod_type]
  simp_rw [side_sum]
  simp [Fintype.card_prod, card_nodes, mul_comm]

/-- Additional selector positions have constant test output 0 in both worlds.
This defines only their measure-level gap, not a source-valid SIM adversary. -/
def paddedGap {B H : ℕ} (f : Node B H → Frame) (k : ℕ) : ℚ :=
  average (Sum.elim (fun x : Node B H × Bool => (f x.1).realTest x.2) (fun _ : Fin k => 0)) -
  average (Sum.elim (fun x : Node B H × Bool => (f x.1).idealTest x.2) (fun _ : Fin k => 0))

theorem padded_uniform_average {B H : ℕ} (f : Node B H → Frame) (hf : Coherent f) (k : ℕ) :
    paddedGap f k = (f (root B H)).gap / (2 * nodeCount B H + k) := by
  unfold paddedGap average
  rw [← sub_div, ← Finset.sum_sub_distrib, Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,sub_self,Finset.sum_const_zero,add_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [side_sum]
  rw [← telescoping B H f hf]
  simp [Fintype.card_sum,Fintype.card_prod,card_nodes,mul_comm]

def dyadicSize (B H : ℕ) : ℕ := 2 ^ Nat.clog 2 (2 * nodeCount B H)

theorem dyadic_size_bounds (B H : ℕ) :
    2 * nodeCount B H ≤ dyadicSize B H ∧ dyadicSize B H < 4 * nodeCount B H := by
  have hn := nodeCount_pos B H
  have ht : 1 < 2 * nodeCount B H := by omega
  have hc := Nat.clog_pos (b:=2) (by omega) ht
  have hlt := Nat.pow_pred_clog_lt_self (b:=2) (by omega) ht
  have he : (Nat.clog 2 (2*nodeCount B H)).pred+1 = Nat.clog 2 (2*nodeCount B H) :=
    Nat.succ_pred_eq_of_pos hc
  constructor
  · exact Nat.le_pow_clog (by omega) _
  · unfold dyadicSize
    rw [← he, pow_succ]
    omega

theorem dyadic_padding_average {B H : ℕ} (f : Node B H → Frame) (hf : Coherent f) :
    paddedGap f (dyadicSize B H - 2 * nodeCount B H) =
      (f (root B H)).gap / (dyadicSize B H : ℚ) := by
  rw [padded_uniform_average f hf]
  have hn := (dyadic_size_bounds B H).1
  have he : (2*nodeCount B H : ℚ) + (dyadicSize B H - 2*nodeCount B H : ℕ) = dyadicSize B H := by
    exact_mod_cast (Nat.add_sub_of_le hn)
  rw [he]

theorem padded_choice_cardinality (B H : ℕ) :
    Fintype.card ((Node B H × Bool) ⊕ Fin (dyadicSize B H - 2*nodeCount B H)) =
      dyadicSize B H := by
  have hn := (dyadic_size_bounds B H).1
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,card_nodes]
  omega

/-- Cardinality of fixed-length bit vectors. No implementation of a sampler or
the source's dummy experiment is supplied by this cardinality theorem. -/
theorem bit_vector_cardinality (B H : ℕ) :
    Fintype.card (Fin (Nat.clog 2 (2*nodeCount B H)) → Bool) = dyadicSize B H := by
  simp [dyadicSize]

theorem one_branch_count (H : ℕ) : nodeCount 1 H = H+1 := by simp [nodeCount]

/-- A finite resource inequality, not an asymptotic/PPT definition. -/
theorem branching_count_bound (B H : ℕ) (hB : 2 ≤ B) : nodeCount B H + 1 ≤ 2 * B^H := by
  induction H with
  | zero => simp [nodeCount]
  | succ H ih =>
    rw [nodeCount_succ,pow_succ']
    have hm := Nat.mul_le_mul_left B ih
    nlinarith

theorem polynomial_obligation_envelope (B H parameter exponent : ℕ)
    (hB : 2 ≤ B) (hpow : B^H ≤ parameter^exponent) :
    dyadicSize B H < 8 * parameter^exponent := by
  have hn := branching_count_bound B H hB
  have hm := (dyadic_size_bounds B H).2
  omega

theorem logarithmic_horizon_linear_envelope (B parameter : ℕ)
    (hB : 2 ≤ B) (hp : 0 < parameter) :
    dyadicSize B (Nat.log B parameter) < 8 * parameter := by
  simpa using polynomial_obligation_envelope B (Nat.log B parameter) parameter 1 hB
    (by simpa using Nat.pow_log_le_self B (Nat.ne_of_gt hp))

end Minidregg.Theory.HorizonComposition

/-- info: 'Minidregg.Theory.HorizonComposition.frame_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.frame_decomposition
/-- info: 'Minidregg.Theory.HorizonComposition.sum_nodes_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.sum_nodes_succ
/-- info: 'Minidregg.Theory.HorizonComposition.telescoping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.telescoping
/-- info: 'Minidregg.Theory.HorizonComposition.nodeCount_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.nodeCount_succ
/-- info: 'Minidregg.Theory.HorizonComposition.card_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.card_nodes
/-- info: 'Minidregg.Theory.HorizonComposition.nodeCount_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.nodeCount_pos
/-- info: 'Minidregg.Theory.HorizonComposition.side_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.side_sum
/-- info: 'Minidregg.Theory.HorizonComposition.uniform_side_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.uniform_side_average
/-- info: 'Minidregg.Theory.HorizonComposition.uniform_gap_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.uniform_gap_zero_iff
/-- info: 'Minidregg.Theory.HorizonComposition.complemented_probabilities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.complemented_probabilities
/-- info: 'Minidregg.Theory.HorizonComposition.depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.depth_le
/-- info: 'Minidregg.Theory.HorizonComposition.levelCount_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.levelCount_zero
/-- info: 'Minidregg.Theory.HorizonComposition.levelCount_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.levelCount_succ
/-- info: 'Minidregg.Theory.HorizonComposition.levelCount_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.levelCount_exact
/-- info: 'Minidregg.Theory.HorizonComposition.uniform_depth_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.uniform_depth_weight
/-- info: 'Minidregg.Theory.HorizonComposition.depth_weights_sum_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.depth_weights_sum_one
/-- info: 'Minidregg.Theory.HorizonComposition.uniform_depth_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.uniform_depth_probability
/-- info: 'Minidregg.Theory.HorizonComposition.sum_depth_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.sum_depth_gaps
/-- info: 'Minidregg.Theory.HorizonComposition.weighted_depth_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.weighted_depth_average
/-- info: 'Minidregg.Theory.HorizonComposition.padded_uniform_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.padded_uniform_average
/-- info: 'Minidregg.Theory.HorizonComposition.dyadic_size_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.dyadic_size_bounds
/-- info: 'Minidregg.Theory.HorizonComposition.dyadic_padding_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.dyadic_padding_average
/-- info: 'Minidregg.Theory.HorizonComposition.padded_choice_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.padded_choice_cardinality
/-- info: 'Minidregg.Theory.HorizonComposition.bit_vector_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.bit_vector_cardinality
/-- info: 'Minidregg.Theory.HorizonComposition.one_branch_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.one_branch_count
/-- info: 'Minidregg.Theory.HorizonComposition.branching_count_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.branching_count_bound
/-- info: 'Minidregg.Theory.HorizonComposition.polynomial_obligation_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.polynomial_obligation_envelope
/-- info: 'Minidregg.Theory.HorizonComposition.logarithmic_horizon_linear_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.logarithmic_horizon_linear_envelope
