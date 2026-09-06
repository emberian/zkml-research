/- Statement first: the pinned lazy Shoup instruction formula is a correct lazy
residue for an ARBITRARY u64 first operand, a canonical second operand, and its
exact Shoup reciprocal. Products/subtraction fit u128 and the result fits u64.
This is a handwritten integer model of source word operations, not Rust semantics.
The a<wordBase condition is intentionally weaker than a<p: RnsScaler feeds
extended-base residues directly to a smaller target modulus. -/
import Compiler.FheTargetProjectionVerifier

namespace Minidregg.Compiler.FheShoupWord
set_option autoImplicit false

def shoup (B p b : ℤ) : ℤ := B*b/p
def quotient (B p a b : ℤ) : ℤ := a*shoup B p b/B
def remainder (B p a b : ℤ) : ℤ := a*b-quotient B p a b*p

def ShoupRefinement : Prop := ∀ B p a b : ℤ,
  0<B → 0<p → 0≤a → a<B → 0≤b → b<p →
  0≤remainder B p a b ∧ remainder B p a b<2*p ∧
  remainder B p a b%p=a*b%p

/-- Two Euclidean remainders give the exact error of the approximate quotient. -/
theorem error_identity (B p a b : ℤ) :
    B*remainder B p a b = a*((B*b)%p)+p*((a*shoup B p b)%B) := by
  have h1 := congrArg (fun x : ℤ => a*x) (Int.mul_ediv_add_emod (B*b) p)
  have h2 := congrArg (fun x : ℤ => p*x) (Int.mul_ediv_add_emod (a*shoup B p b) B)
  dsimp [remainder,quotient,shoup] at *
  nlinarith

/-- Shoup reciprocal truncation fits one word whenever b is canonical. -/
theorem shoup_range (B p b : ℤ) (hB : 0<B) (hp : 0<p) (hb0 : 0≤b) (hb : b<p) :
    0≤shoup B p b ∧ shoup B p b<B := by
  have hn : 0≤B*b := mul_nonneg hB.le hb0
  have he := Int.mul_ediv_add_emod (B*b) p
  have hr := Int.emod_nonneg (B*b) (ne_of_gt hp)
  have hh := mul_lt_mul_of_pos_left hb hB
  dsimp [shoup]
  exact ⟨Int.ediv_nonneg hn hp.le,by nlinarith⟩

/-- Canonical b and one-word a imply a nonnegative residual strictly below 2p. -/
theorem shoupRefinement : ShoupRefinement := by
  intro B p a b hB hp ha0 ha hb0 hb
  have e0 := Int.emod_nonneg (B*b) (ne_of_gt hp)
  have e1 := Int.emod_lt_of_pos (B*b) hp
  have s0 := Int.emod_nonneg (a*shoup B p b) (ne_of_gt hB)
  have s1 := Int.emod_lt_of_pos (a*shoup B p b) hB
  have h := error_identity B p a b
  have hlow := add_nonneg (mul_nonneg ha0 e0) (mul_nonneg hp.le s0)
  have he : a*((B*b)%p)<B*p :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left e1.le ha0) (mul_lt_mul_of_pos_right ha hp)
  have hs : p*((a*shoup B p b)%B)<B*p := by
    nlinarith [mul_lt_mul_of_pos_left s1 hp]
  refine ⟨by nlinarith,by nlinarith,?_⟩
  simp [remainder,Int.sub_emod]

/-- Every u128 multiplication/subtraction in lazy Shoup has an exact integer lift.
The second conjunct is the explicit no-underflow fact for the source subtraction. -/
theorem product_bounds (B p a b : ℤ) (hB : 0<B) (hp : 0<p) (hpB : p<B)
    (ha0 : 0≤a) (ha : a<B) (hb0 : 0≤b) (hb : b<p) :
    (0≤a*b ∧ a*b<B^2) ∧
    (0≤quotient B p a b*p ∧ quotient B p a b*p≤a*b) ∧
    (0≤a*shoup B p b ∧ a*shoup B p b<B^2) ∧
    (0≤B*b ∧ B*b<B^2) := by
  have sr := shoup_range B p b hB hp hb0 hb
  have rr := shoupRefinement B p a b hB hp ha0 ha hb0 hb
  have q0 : 0≤quotient B p a b := Int.ediv_nonneg (mul_nonneg ha0 sr.1) hB.le
  have ab := mul_le_mul_of_nonneg_left (lt_trans hb hpB).le ha0
  have asb := mul_le_mul_of_nonneg_left sr.2.le ha0
  have aB := mul_lt_mul_of_pos_right ha hB
  have Bb := mul_lt_mul_of_pos_left (lt_trans hb hpB) hB
  dsimp [remainder] at rr
  exact ⟨⟨mul_nonneg ha0 hb0,by nlinarith⟩,
    ⟨mul_nonneg q0 hp.le,by nlinarith⟩,
    ⟨mul_nonneg ha0 sr.1,by nlinarith⟩,
    ⟨mul_nonneg hB.le hb0,by nlinarith⟩⟩

/-- Literal source shape: u128 product/shift, u128 subtraction, and u64 result cast.
All casts/wrapping are modeled explicitly; the theorem below discharges them. -/
def wordLazyShoup (B p a b : ℤ) : ℤ :=
  let bs := (((B*b)%(B^2))/p)%B
  let q := ((a*bs)%(B^2))/B
  (((a*b)%(B^2)-(q*p)%(B^2))%(B^2))%B

/-- The literal word model equals the exact lazy residual under actual source bounds. -/
theorem wordLazyShoup_correct (B p a b : ℤ) (hB : 0<B) (hp : 0<p) (hpB : 2*p<B)
    (ha0 : 0≤a) (ha : a<B) (hb0 : 0≤b) (hb : b<p) :
    wordLazyShoup B p a b=remainder B p a b := by
  have hpB' : p<B := by omega
  have bounds := product_bounds B p a b hB hp hpB' ha0 ha hb0 hb
  have sr := shoup_range B p b hB hp hb0 hb
  have rr := shoupRefinement B p a b hB hp ha0 ha hb0 hb
  have rB : remainder B p a b<B := lt_trans rr.2.1 hpB
  have rBB : remainder B p a b<B^2 := by
    have h1 : 1≤B := by omega
    nlinarith
  have qpB : quotient B p a b*p<B^2 := lt_of_le_of_lt bounds.2.1.2 bounds.1.2
  simp only [wordLazyShoup,Int.emod_eq_of_lt bounds.2.2.2.1 bounds.2.2.2.2]
  change (((a*b)%(B^2)-(((a*(shoup B p b%B))%(B^2))/B*p)%(B^2))%(B^2))%B = _
  rw [Int.emod_eq_of_lt sr.1 sr.2,Int.emod_eq_of_lt bounds.2.2.1.1 bounds.2.2.1.2,
    Int.emod_eq_of_lt bounds.1.1 bounds.1.2]
  change ((a*b-(quotient B p a b*p)%(B^2))%(B^2))%B = _
  rw [Int.emod_eq_of_lt bounds.2.1.1 qpB]
  change (remainder B p a b%(B^2))%B = _
  rw [Int.emod_eq_of_lt rr.1 rBB,Int.emod_eq_of_lt rr.1 rB]

/-- The API's actual modulus bound is stronger than the required 2p<2^64. -/
theorem source_u64_bounds (p : ℤ) (hp0 : 2≤p) (hp : p<2^62) :
    0<p ∧ 2*p<(2^64 : ℤ) := by omega

/-- A valid first operand can exceed p; imposing a<p would miss RnsScaler's use. -/
theorem wide_first_operand_inhabited :
    (31 : ℤ)<34 ∧ wordLazyShoup 256 31 34 11=33 ∧
    33%31=34*11%31 := by decide

/-- Omitting the canonical-second-operand premise can truncate the reciprocal. -/
theorem noncanonical_second_falsifier :
    wordLazyShoup 256 31 8 32%31 ≠ 8*32%31 := by decide

end Minidregg.Compiler.FheShoupWord

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheShoupWord.error_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheShoupWord.error_identity

/-- info: 'Minidregg.Compiler.FheShoupWord.shoup_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheShoupWord.shoup_range

/-- info: 'Minidregg.Compiler.FheShoupWord.shoupRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheShoupWord.shoupRefinement

/-- info: 'Minidregg.Compiler.FheShoupWord.product_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheShoupWord.product_bounds

/-- info: 'Minidregg.Compiler.FheShoupWord.wordLazyShoup_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheShoupWord.wordLazyShoup_correct

/-- info: 'Minidregg.Compiler.FheShoupWord.source_u64_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheShoupWord.source_u64_bounds

/-- info: 'Minidregg.Compiler.FheShoupWord.wide_first_operand_inhabited' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheShoupWord.wide_first_operand_inhabited

/-- info: 'Minidregg.Compiler.FheShoupWord.noncanonical_second_falsifier' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheShoupWord.noncanonical_second_falsifier
