/- Fresh-coin logarithmic-derivative extraction for the actual arity-one byte
bus. Main/table data, including multiplicities, are fixed before the coins;
permutation witnesses are deliberately not part of this fixed data. -/
import Compiler.NativeNibbleBus
import Selvage.LogupStar
import Selvage.BabyBearFullUD
namespace Minidregg.Compiler.ByteLogUpDefect
open Minidregg.Compiler Minidregg.Selvage
open Minidregg.Selvage.BabyBearExt4 (Ext4 ext4_card)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

def embed : BabyBear →+* Ext4 := algebraMap Minidregg.Selvage.BabyBearExt4.BabyBear Ext4
def tableKeys : Finset BabyBear := (Finset.range 16).image fun (i : Nat) => (i : BabyBear)
def support (sends : List BabyBear) : Finset BabyBear := sends.toFinset ∪ tableKeys
abbrev Index (sends : List BabyBear) := {x : BabyBear // x∈support sends}
def point (sends : List BabyBear) (i : Index sends) : Ext4 := embed i.val
def expected (sends : List BabyBear) (i : Index sends) : Ext4 := (sends.count i.val : Ext4)
def claimed (sends : List BabyBear) (m : Nat → Nat) (i : Index sends) : Ext4 :=
  ((NativeNibbleBus.receives m).count i.val : Ext4)
def rational (xs : List BabyBear) (α : Ext4) : Ext4 :=
  (xs.map fun x => (α-embed x)⁻¹).sum
def Pole (sends : List BabyBear) (α : Ext4) : Prop := ∃ i : Index sends,α-point sends i=0
def Defect (sends : List BabyBear) (m : Nat → Nat) : Polynomial Ext4 :=
  logupDefect (point sends) (expected sends) (claimed sends m)
def Bad (sends : List BabyBear) (m : Nat → Nat) (α : Ext4) : Prop :=
  Pole sends α ∨ (¬NativeNibbleBus.ExactField sends m ∧ (Defect sends m).eval α=0)

def Sound : Prop := ∀ sends m α,
  rational sends α=rational (NativeNibbleBus.receives m) α →
  NativeNibbleBus.ExactField sends m ∨ Bad sends m α

theorem point_injective (sends : List BabyBear) : Function.Injective (point sends) := by
  intro a b h
  exact Subtype.ext (embed.injective h)

theorem receive_mem (sends : List BabyBear) (m : Nat → Nat) (x : BabyBear)
    (hx : x∈NativeNibbleBus.receives m) : x∈support sends := by
  apply Finset.mem_union_right
  have h := NativeNibbleBus.receive_range m x hx
  apply Finset.mem_image.mpr
  exact ⟨x.val,Finset.mem_range.mpr h,ZMod.natCast_zmod_val x⟩

theorem exact_iff (sends : List BabyBear) (m : Nat → Nat) :
    NativeNibbleBus.ExactField sends m ↔ claimed sends m=expected sends := by
  constructor
  · intro h
    funext i
    have hh := congrArg embed (h i.val)
    simpa only [map_natCast] using hh.symm
  · intro h x
    by_cases hx : x∈support sends
    · have hh := congrFun h ⟨x,hx⟩
      apply embed.injective
      simpa only [map_natCast] using hh.symm
    · have hs : x∉sends := fun hm => hx (Finset.mem_union_left _ (List.mem_toFinset.mpr hm))
      have hr : x∉NativeNibbleBus.receives m := fun hm => hx (receive_mem sends m x hm)
      simp [List.count_eq_zero.mpr hs,List.count_eq_zero.mpr hr]

theorem rational_histogram (xs sends : List BabyBear) (α : Ext4)
    (hxs : ∀ x∈xs,x∈support sends) :
    rational xs α=logupLogDerivative (point sends)
      (fun i => (xs.count i.val : Ext4)) α := by
  classical
  unfold rational logupLogDerivative point
  change _ = ∑ j∈(support sends).attach,(xs.count j.val : Ext4)/(α-embed j.val)
  rw [Finset.sum_attach (support sends) (fun (x : BabyBear) => (xs.count x : Ext4)/(α-embed x))]
  rw [Finset.sum_list_map_count xs (fun x => (α-embed x)⁻¹)]
  simp only [nsmul_eq_mul,div_eq_mul_inv]
  apply Finset.sum_subset
  · intro x hx
    exact hxs x (List.mem_toFinset.mp hx)
  · intro x hx hn
    have hc : xs.count x=0 := List.count_eq_zero.mpr (fun h => hn (List.mem_toFinset.mpr h))
    simp [hc]

theorem sound : Sound := by
  intro sends m α hrat
  by_cases he : NativeNibbleBus.ExactField sends m
  · exact Or.inl he
  · right
    by_cases hp : Pole sends α
    · exact Or.inl hp
    · right
      refine ⟨he,?_⟩
      apply (logup_rational_eq_iff_defect_eval_eq_zero (point sends)
        (expected sends) (claimed sends m) α (by simpa [Pole] using hp)).mp
      unfold claimed expected
      rw [←rational_histogram (NativeNibbleBus.receives m) sends α (receive_mem sends m),
        ←rational_histogram sends sends α (fun x hx => Finset.mem_union_left _ (List.mem_toFinset.mpr hx))]
      exact hrat.symm

theorem bad_probability (sends : List BabyBear) (m : Nat → Nat) :
    uniformProb Ext4 (Bad sends m) ≤
      ((support sends).card : ℝ)/Fintype.card Ext4 +
      (((support sends).card-1 : Nat) : ℝ)/Fintype.card Ext4 := by
  by_cases he : NativeNibbleBus.ExactField sends m
  · have hb : ∀ α,Bad sends m α → Pole sends α := by intro α h; exact h.resolve_right (by simp [he])
    refine le_trans (uniformProb_mono hb) ?_
    have hp := logup_denominator_zero_prob_le (point sends)
    have hc : Fintype.card (Index sends)=(support sends).card := Fintype.card_coe _
    rw [hc] at hp
    exact le_trans hp (le_add_of_nonneg_right (by positivity))
  · have hn : claimed sends m≠expected sends := fun h => he ((exact_iff sends m).mpr h)
    refine le_trans (uniformProb_mono (q := fun α => Pole sends α ∨ (Defect sends m).eval α=0) (fun α h => ?_)) ?_
    · exact h.imp_right And.right
    · simpa only [Fintype.card_coe] using
        logup_wrong_or_pole_prob_le (point sends) (point_injective sends) hn

/-- Actual Horner compression of a singleton tuple is independent of beta. -/
def compress (β : Ext4) (xs : List BabyBear) : Ext4 :=
  xs.foldl (fun acc x => embed x+acc*β) 0
def TupleCollision (β : Ext4) : Prop :=
  ∃ x y : BabyBear,x≠y ∧ compress β [x]=compress β [y]

theorem no_tuple_collision (β : Ext4) : ¬TupleCollision β := by
  rintro ⟨x,y,hxy,h⟩
  apply hxy
  apply embed.injective
  simpa [compress] using h

theorem fresh_pair_probability (sends : List BabyBear) (m : Nat → Nat) :
    uniformProb (Ext4×Ext4) (fun coins => TupleCollision coins.1 ∨ Bad sends m coins.2) ≤
      ((support sends).card : ℝ)/(2013265921 : ℝ)^4 +
      (((support sends).card-1 : Nat) : ℝ)/(2013265921 : ℝ)^4 := by
  apply uniformProb_prod_le (by positivity)
  intro β
  have h := bad_probability sends m
  have hc : Fintype.card Ext4=2013265921^4 := ext4_card
  rw [hc] at h
  simpa only [no_tuple_collision, false_or,Nat.cast_pow,Nat.cast_ofNat] using h

theorem support_card_bound (sends : List BabyBear) :
    (support sends).card≤sends.length+16 := by
  have ht : tableKeys.card≤16 := by
    exact le_trans Finset.card_image_le (by simp)
  exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add sends.toFinset_card_le ht)

theorem fresh_pair_length_bound (sends : List BabyBear) (m : Nat → Nat) :
    uniformProb (Ext4×Ext4) (fun coins => TupleCollision coins.1 ∨ Bad sends m coins.2) ≤
      (2*(sends.length : ℝ)+31)/(2013265921 : ℝ)^4 := by
  have h := fresh_pair_probability sends m
  have hcard := support_card_bound sends
  have hpred : (support sends).card-1≤sends.length+15 := by omega
  have h' : ((support sends).card : ℝ)/(2013265921 : ℝ)^4 +
      (((support sends).card-1 : Nat) : ℝ)/(2013265921 : ℝ)^4 ≤
      ((sends.length+16 : Nat) : ℝ)/(2013265921 : ℝ)^4 +
      ((sends.length+15 : Nat) : ℝ)/(2013265921 : ℝ)^4 := by
    gcongr
  refine le_trans h (le_trans h' ?_)
  push_cast
  ring_nf
  exact le_rfl

/-- A concrete wrong histogram supplies a nonzero defect polynomial. -/
theorem wrong_histogram : ¬NativeNibbleBus.ExactField [(16 : BabyBear)] (fun _ => 0) := by
  intro h
  have hh := h 16
  norm_num [NativeNibbleBus.receives,List.range_succ] at hh

theorem wrong_defect_nonzero : Defect [(16 : BabyBear)] (fun _ => 0)≠0 := by
  apply logupDefect_ne_zero_of_ne (point _) (point_injective _)
  exact fun h => wrong_histogram ((exact_iff _ _).mpr h)

/-- The complete nonzero bus witness from the previous packet remains a valid
committed multiplicity choice before either lookup coin is selected. -/
theorem nonzeroPremise : ∃ sends m,NativeNibbleBus.ExactField sends m ∧
    NativeNibbleBus.NoSendWrap sends ∧ ∃ x∈sends,x≠0 :=
  NativeNibbleBus.fieldPremiseInhabited

end
end Minidregg.Compiler.ByteLogUpDefect

/-- info: 'Minidregg.Compiler.ByteLogUpDefect.point_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.point_injective
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.receive_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.receive_mem
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.exact_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.exact_iff
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.rational_histogram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.rational_histogram
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.sound
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.bad_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.bad_probability
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.no_tuple_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.no_tuple_collision
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.fresh_pair_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.fresh_pair_probability
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.support_card_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.support_card_bound
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.fresh_pair_length_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.fresh_pair_length_bound
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.wrong_histogram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.wrong_histogram
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.wrong_defect_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.wrong_defect_nonzero
/-- info: 'Minidregg.Compiler.ByteLogUpDefect.nonzeroPremise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.ByteLogUpDefect.nonzeroPremise
