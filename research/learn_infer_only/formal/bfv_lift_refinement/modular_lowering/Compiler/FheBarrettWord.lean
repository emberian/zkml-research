/- Exact two-word Barrett quotient decomposition used by zq/mod.rs:674-682.
The proof separates the universal algebra from explicit no-wrap premises for
the literal u128 additions. This handwritten integer model is not Rust semantics. -/
import Compiler.FheShoupWord

namespace Minidregg.Compiler.FheBarrettWord
open Minidregg.Compiler.FheShoupWord
set_option autoImplicit false

def middle (B a c : ℤ) : ℤ :=
  (a%B)*(c/B)+(a/B)*(c%B)+((a%B)*(c%B))/B
def splitQuotient (B a c : ℤ) : ℤ := middle B a c/B+(a/B)*(c/B)

/-- The split high-word arithmetic computes floor(a*c/B²) exactly. -/
theorem split_quotient_exact (B a c : ℤ) (hB : 0<B) :
    splitQuotient B a c=a*c/(B^2) := by
  have ha := Int.mul_ediv_add_emod a B
  have hc := Int.mul_ediv_add_emod c B
  have hlo := Int.mul_ediv_add_emod ((a%B)*(c%B)) B
  have hm := Int.mul_ediv_add_emod (middle B a c) B
  let rem := B*(middle B a c%B)+((a%B)*(c%B))%B
  have h0 := Int.emod_nonneg (middle B a c) (ne_of_gt hB)
  have h1 := Int.emod_lt_of_pos (middle B a c) hB
  have h2 := Int.emod_nonneg ((a%B)*(c%B)) (ne_of_gt hB)
  have h3 := Int.emod_lt_of_pos ((a%B)*(c%B)) hB
  have he : a*c=B^2*splitQuotient B a c+rem := by
    have hproduct : a*c=(B*(a/B)+a%B)*(B*(c/B)+c%B) := by rw [ha,hc]
    dsimp [rem,splitQuotient,middle] at *
    nlinarith [congrArg (fun x : ℤ => B*x) hlo,congrArg (fun x : ℤ => B*x) hm]
  exact Minidregg.Compiler.FheSourceCertificate.qr_forced _ _ _ _
    (by positivity) (by dsimp [rem]; positivity) (by dsimp [rem];nlinarith) he

/-- Canonical one-word pieces imply the source middle sum stays below u128 when
the reciprocal's low+high pieces fit one word. This is checked for the target constants. -/
theorem middle_range (B a c : ℤ) (hB : 0<B) (ha0 : 0≤a) (ha : a<B^2)
    (hc0 : 0≤c) (_hc : c<B^2) (hparts : c%B+c/B<B) :
    0≤middle B a c ∧ middle B a c<B^2 := by
  have a0 := Int.emod_nonneg a (ne_of_gt hB)
  have a1 := Int.emod_lt_of_pos a hB
  have c0 := Int.emod_nonneg c (ne_of_gt hB)
  have c1 := Int.emod_lt_of_pos c hB
  have ah0 := Int.ediv_nonneg ha0 hB.le
  have ch0 := Int.ediv_nonneg hc0 hB.le
  have haqr := Int.mul_ediv_add_emod a B
  have ah1 : a/B<B := by nlinarith
  have lo0 : 0≤((a%B)*(c%B))/B := Int.ediv_nonneg (mul_nonneg a0 c0) hB.le
  have loqr := Int.mul_ediv_add_emod ((a%B)*(c%B)) B
  have lorem := Int.emod_nonneg ((a%B)*(c%B)) (ne_of_gt hB)
  have lobound := mul_le_mul_of_nonneg_right a1.le c0
  have lo1 : ((a%B)*(c%B))/B≤c%B := by nlinarith
  have hleft := mul_le_mul_of_nonneg_right (show a%B≤B-1 by omega) ch0
  have hright := mul_le_mul_of_nonneg_right (show a/B≤B-1 by omega) c0
  have hparts' := mul_le_mul_of_nonneg_left (show c%B+c/B≤B-1 by omega) hB.le
  dsimp [middle]
  constructor
  · positivity
  · nlinarith

/-- Literal u128 middle products/addition, quotient addition and residual/cast. -/
def wordLazyBarrett (B p a : ℤ) : ℤ :=
  let c := B^2/p
  let lo := c%B
  let hi := c/B
  let aLo := a%B
  let aHi := a/B
  let ll := ((aLo*lo)%(B^2))/B
  let hl := (aHi*lo)%(B^2)
  let lh := (aLo*hi)%(B^2)
  let q := ((((lh+hl+ll)%(B^2))/B)+(aHi*hi)%(B^2))%(B^2)
  ((a-(q*p)%(B^2))%(B^2))%B

/-- Reference lazy Barrett is the already proved Shoup formula at the double word base. -/
theorem barrett_reference (B p a : ℤ) (hB : 0<B) (hp : 1<p)
    (ha0 : 0≤a) (ha : a<B^2) :
    0≤a-(a*(B^2/p)/(B^2))*p ∧ a-(a*(B^2/p)/(B^2))*p<2*p ∧
    (a-(a*(B^2/p)/(B^2))*p)%p=a%p := by
  simpa [remainder,quotient,shoup] using
    shoupRefinement (B^2) p a 1 (by positivity) (by omega) ha0 ha (by omega) hp

/-- A product of two one-word values cannot overflow a double word. -/
theorem word_product_bound (B a b : ℤ) (hB : 0<B)
    (ha0 : 0≤a) (ha : a<B) (hb0 : 0≤b) (hb : b<B) :
    0≤a*b ∧ a*b<B^2 := by
  have h1 := mul_le_mul_of_nonneg_left hb.le ha0
  have h2 := mul_lt_mul_of_pos_right ha hB
  exact ⟨mul_nonneg ha0 hb0,by nlinarith⟩

/-- Literal Barrett word arithmetic equals its exact lazy integer residual.
The low+high reciprocal bound discharges the source's three-term u128 addition. -/
theorem wordLazyBarrett_correct (B p a : ℤ) (hB : 0<B) (hp : 1<p) (hpB : 2*p<B)
    (ha0 : 0≤a) (ha : a<B^2)
    (hparts : (B^2/p)%B+(B^2/p)/B<B) :
    wordLazyBarrett B p a=a-(a*(B^2/p)/(B^2))*p := by
  let c := B^2/p
  have c0 : 0≤c := Int.ediv_nonneg (by positivity) (by omega)
  have cB : c<B^2 := by
    have hr := Int.emod_nonneg (B^2) (by omega : p≠0)
    have hq := Int.mul_ediv_add_emod (B^2) p
    dsimp [c] at *
    have hpow : 0<B^2 := by positivity
    nlinarith
  have al0 := Int.emod_nonneg a (ne_of_gt hB)
  have al1 := Int.emod_lt_of_pos a hB
  have cl0 := Int.emod_nonneg c (ne_of_gt hB)
  have cl1 := Int.emod_lt_of_pos c hB
  have ah0 := Int.ediv_nonneg ha0 hB.le
  have ch0 := Int.ediv_nonneg c0 hB.le
  have aqr := Int.mul_ediv_add_emod a B
  have cqr := Int.mul_ediv_add_emod c B
  have ah1 : a/B<B := by nlinarith
  have ch1 : c/B<B := by nlinarith
  have ll := word_product_bound B _ _ hB al0 al1 cl0 cl1
  have hl := word_product_bound B _ _ hB ah0 ah1 cl0 cl1
  have lh := word_product_bound B _ _ hB al0 al1 ch0 ch1
  have hh := word_product_bound B _ _ hB ah0 ah1 ch0 ch1
  have mid := middle_range B a c hB ha0 ha c0 cB hparts
  have qe := split_quotient_exact B a c hB
  have rr := barrett_reference B p a hB hp ha0 ha
  have q0 : 0≤a*c/(B^2) := Int.ediv_nonneg (mul_nonneg ha0 c0) (by positivity)
  have qp0 : 0≤(a*c/(B^2))*p := mul_nonneg q0 (by omega)
  have qp1 : (a*c/(B^2))*p<B^2 := by
    have hrr := rr.1
    change 0≤a-(a*c/(B^2))*p at hrr
    omega
  have q1 : a*c/(B^2)<B^2 := by
    have h := mul_le_mul_of_nonneg_left (show 1≤p by omega) q0
    nlinarith
  have rB : a-(a*c/(B^2))*p<B := lt_trans rr.2.1 hpB
  have rBB : a-(a*c/(B^2))*p<B^2 := by
    have h1 : 1≤B := by omega
    nlinarith
  dsimp only [wordLazyBarrett]
  rw [Int.emod_eq_of_lt ll.1 ll.2,Int.emod_eq_of_lt hl.1 hl.2,
    Int.emod_eq_of_lt lh.1 lh.2,Int.emod_eq_of_lt hh.1 hh.2]
  change ((a-(((middle B a c)%(B^2)/B+(a/B)*(c/B))%(B^2)*p)%(B^2))%(B^2))%B = _
  rw [Int.emod_eq_of_lt mid.1 mid.2]
  change ((a-((splitQuotient B a c)%(B^2)*p)%(B^2))%(B^2))%B = _
  rw [qe,Int.emod_eq_of_lt q0 q1,Int.emod_eq_of_lt qp0 qp1,
    Int.emod_eq_of_lt rr.1 rBB,Int.emod_eq_of_lt rr.1 rB]

/-- Conditional subtraction models reduce1's selected result; the unselected
wrapping subtraction may wrap, but its value is not returned. -/
def wordReduceOne (B p x : ℤ) : ℤ := if x<p then x else (x-p)%B

/-- One correction canonicalizes a lazy representative without changing its residue. -/
theorem wordReduceOne_correct (B p x : ℤ) (_hp : 0<p) (hpB : p<B)
    (hx0 : 0≤x) (hx : x<2*p) : wordReduceOne B p x=x%p := by
  unfold wordReduceOne
  split_ifs with h
  · exact (Int.emod_eq_of_lt hx0 h).symm
  · have hd0 : 0≤x-p := by omega
    have hd1 : x-p<p := by omega
    rw [Int.emod_eq_of_lt hd0 (lt_trans hd1 hpB)]
    calc
      x-p = (x-p)%p := (Int.emod_eq_of_lt hd0 hd1).symm
      _ = x%p := by simp

def wordReduce (B p x : ℤ) : ℤ := wordReduceOne B p (wordLazyBarrett B p x)

/-- The pinned Barrett plus one-subtraction source formula is exact canonical reduction. -/
theorem wordReduce_correct (B p a : ℤ) (hB : 0<B) (hp : 1<p) (hpB : 2*p<B)
    (ha0 : 0≤a) (ha : a<B^2)
    (hparts : (B^2/p)%B+(B^2/p)/B<B) : wordReduce B p a=a%p := by
  have hr := barrett_reference B p a hB hp ha0 ha
  unfold wordReduce
  rw [wordLazyBarrett_correct B p a hB hp hpB ha0 ha hparts,
    wordReduceOne_correct B p _ (by omega) (by omega) hr.1 hr.2.1]
  exact hr.2.2

/-- The source's mask/xor conditional selector returns precisely its selected word. -/
theorem mask_selection (onTrue onFalse : BitVec 64) (condition : Bool) :
    ((onTrue ^^^ onFalse) &&& (if condition then (-1 : BitVec 64) else 0)) ^^^ onFalse =
      (if condition then onTrue else onFalse) := by
  cases condition with
  | false => simp
  | true =>
    change ((onTrue ^^^ onFalse) &&& (-1 : BitVec 64)) ^^^ onFalse=onTrue
    have hmask : (-1 : BitVec 64)=BitVec.allOnes 64 := by decide
    rw [hmask,BitVec.and_allOnes,BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero]

/-- A full-double-word input can produce a noncanonical lazy residual, then reduce exactly. -/
theorem barrett_premises_inhabited :
    ((256 : ℤ)^2/31)%256+((256 : ℤ)^2/31)/256<256 ∧
    wordLazyBarrett 256 31 65535=32 ∧ wordReduce 256 31 65535=1 := by decide

/-- A single correction is insufficient if its strict lazy-input range is omitted. -/
theorem reduce_one_range_falsifier : wordReduceOne 256 31 62 ≠ 62%31 := by decide

end Minidregg.Compiler.FheBarrettWord

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheBarrettWord.split_quotient_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheBarrettWord.split_quotient_exact

/-- info: 'Minidregg.Compiler.FheBarrettWord.middle_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheBarrettWord.middle_range

/-- info: 'Minidregg.Compiler.FheBarrettWord.barrett_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheBarrettWord.barrett_reference

/-- info: 'Minidregg.Compiler.FheBarrettWord.word_product_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheBarrettWord.word_product_bound

/-- info: 'Minidregg.Compiler.FheBarrettWord.wordLazyBarrett_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheBarrettWord.wordLazyBarrett_correct

/-- info: 'Minidregg.Compiler.FheBarrettWord.wordReduceOne_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheBarrettWord.wordReduceOne_correct

/-- info: 'Minidregg.Compiler.FheBarrettWord.wordReduce_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheBarrettWord.wordReduce_correct

/-- info: 'Minidregg.Compiler.FheBarrettWord.mask_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheBarrettWord.mask_selection

/-- info: 'Minidregg.Compiler.FheBarrettWord.barrett_premises_inhabited' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheBarrettWord.barrett_premises_inhabited

/-- info: 'Minidregg.Compiler.FheBarrettWord.reduce_one_range_falsifier' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheBarrettWord.reduce_one_range_falsifier
