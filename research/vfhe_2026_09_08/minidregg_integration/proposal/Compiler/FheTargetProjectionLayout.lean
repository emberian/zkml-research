/- Generated nonnegative target projection matrix: Y=qi*quotienti+limbi,
limbi+slacki=qi-1. The source certificate supplies the shared Y through explicit
boundary equality checks. Every group has nineteen radix64 digits. -/
import Compiler.FheTargetProjection
namespace Minidregg.Compiler.FheTargetProjection
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def leftConstant (row : Fin 6) : ℕ := match row.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0
def leftMatrix (row : Fin 6) (col : Fin 10) : ℕ := match row.val,col.val with
  | 0,0 => 1
  | 1,1 => 1
  | 1,3 => 1
  | 2,0 => 1
  | 3,4 => 1
  | 3,6 => 1
  | 4,0 => 1
  | 5,7 => 1
  | 5,9 => 1
  | _,_ => 0

def rightConstant (row : Fin 6) : ℕ := match row.val with
  | 0 => 0
  | 1 => 68719403008
  | 2 => 0
  | 3 => 68719230976
  | 4 => 0
  | 5 => 137438822400
  | _ => 0
def rightMatrix (row : Fin 6) (col : Fin 10) : ℕ := match row.val,col.val with
  | 0,1 => 1
  | 0,2 => 68719403009
  | 2,4 => 1
  | 2,5 => 68719230977
  | 4,7 => 1
  | 4,8 => 137438822401
  | _,_ => 0

def dot (a : Fin 10 → ℕ) (x : Fin 10 → ℕ) : ℕ := ∑ i,a i*x i
def Balanced (x : Fin 10 → ℕ) : Prop := ∀ j,
  leftConstant j+dot (leftMatrix j) x=rightConstant j+dot (rightMatrix j) x
def readLimbs (x : Fin 10 → ℕ) : Fin 3 → ℕ := ![x 1,x 4,x 7]
def readQuotients (x : Fin 10 → ℕ) : Fin 3 → ℕ := ![x 2,x 5,x 8]
def readSlacks (x : Fin 10 → ℕ) : Fin 3 → ℕ := ![x 3,x 6,x 9]

/-- Fixed constants and digit coefficients fit the actual accumulator width. -/
theorem matrix_capacities :
    (∀ row col,leftMatrix row col<2^38 ∧ rightMatrix row col<2^38) ∧
    (∀ row,leftConstant row<64^26 ∧ rightConstant row<64^26) := by decide

/-- The six internally constrained rows supply QR and canonicality. -/
theorem balanced_projection (x : Fin 10 → ℕ) (h : Balanced x) :
    Projection (x 0) (readLimbs x) (readQuotients x) (readSlacks x) := by
  have h0 := h 0
  norm_num [dot,Fin.sum_univ_succ,leftConstant,rightConstant,leftMatrix,rightMatrix] at h0
  change x 0=x 1+68719403009*x 2 at h0
  have h1 := h 1
  norm_num [dot,Fin.sum_univ_succ,leftConstant,rightConstant,leftMatrix,rightMatrix] at h1
  change x 1+x 3=68719403008 at h1
  have h2 := h 2
  norm_num [dot,Fin.sum_univ_succ,leftConstant,rightConstant,leftMatrix,rightMatrix] at h2
  change x 0=x 4+68719230977*x 5 at h2
  have h3 := h 3
  norm_num [dot,Fin.sum_univ_succ,leftConstant,rightConstant,leftMatrix,rightMatrix] at h3
  change x 4+x 6=68719230976 at h3
  have h4 := h 4
  norm_num [dot,Fin.sum_univ_succ,leftConstant,rightConstant,leftMatrix,rightMatrix] at h4
  change x 0=x 7+137438822401*x 8 at h4
  have h5 := h 5
  norm_num [dot,Fin.sum_univ_succ,leftConstant,rightConstant,leftMatrix,rightMatrix] at h5
  change x 7+x 9=137438822400 at h5
  intro i
  fin_cases i
  · change x 0=68719403009*x 2+x 1 ∧ x 1+x 3=68719403008
    omega
  · change x 0=68719230977*x 5+x 4 ∧ x 4+x 6=68719230976
    omega
  · change x 0=137438822401*x 8+x 7 ∧ x 7+x 9=137438822400
    omega

/-- Matrix soundness forces the actual canonical target residues. -/
theorem balanced_limbs (x : Fin 10 → ℕ) (h : Balanced x) :
    ∀ i, readLimbs x i=x 0%targetPrime i :=
  projectionSound _ _ _ _ (balanced_projection x h)
end Minidregg.Compiler.FheTargetProjection

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheTargetProjection.matrix_capacities' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.matrix_capacities

/-- info: 'Minidregg.Compiler.FheTargetProjection.balanced_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.balanced_projection

/-- info: 'Minidregg.Compiler.FheTargetProjection.balanced_limbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.balanced_limbs
