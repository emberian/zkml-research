/- Both poles and the actual packed commitment carrier for the AIR/PCS bridge. -/
import Compiler.Ir2AirPcsOod
import Compiler.Ir2QuotientRecomposition
import Selvage.Ir2PcsPackedWitnesses

namespace Minidregg.Compiler.Ir2AirPcsOod.Witnesses
open Polynomial Minidregg.Selvage BabyBearExt4 Ir2Fri Ir2FriSchedule Packed Pcs AirPolynomialOod
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev W := Pcs.PackedWitnesses.plan

def firstTerm : Pcs.Term := ⟨0,⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩⟩
def equation : Expr := add' (cst 1) (mul' (cst (-1)) (vr (some firstTerm)))
def eqPlan : EquationPlan where
  physical _ _ := 0
  scale _ := 0
  expression _ := equation

def badConstraint : Fin 1 → Ext4[X] := fun _ => 1

/-- With exact zero committed columns, this source constraint is 1; the false
one-valued claimed opening nevertheless makes the displayed equation zero. -/
theorem claimed_equation_accepts (x : AirCoins) : AirAccepted eqPlan (fun _ => W) x := by
  simp [AirAccepted,eqPlan,equation,eval_add',eval_mul',eval_cst,eval_vr,opened,Pcs.PackedWitnesses.plan]

theorem exact_residual (γ : Ext4) :
    equationPoly (eqPlan.physical γ) eqPlan.scale (eqPlan.expression γ)=
      AirPolynomialOod.residual badConstraint X (fun _ => 0) γ := by
  simp [equationPoly,eqPlan,equation,lift,AirPolynomialOod.read,readAlg,fold_mk,cst,mul',add',vr,columnPolys,
    AirPolynomialOod.residual,badConstraint,batch]

theorem bad_row : (X:Ext4[X]).eval 0=0 ∧ ∃ j,(badConstraint j).eval 0 ≠ 0 := by
  exact ⟨by simp,⟨0,by simp [badConstraint]⟩⟩

theorem residual_degree (γ : Ext4) : (AirPolynomialOod.residual badConstraint X (fun _ => 0) γ).natDegree ≤ 0 := by
  simp [AirPolynomialOod.residual,batch,badConstraint]

/-- All premises fire together on the actual23-matrix/5-root carrier, with
fresh challenges retained in the full composed theorem. The hash remains the
existing deliberately noncryptographic witness. -/
theorem actual_packed_head_fires :
    uniformProb AllCoins (fun x => AirAccepted eqPlan (fun _ => W) x.1 ∧
      Accepted Packed.Witnesses.hash W (fun _ => Packed.Witnesses.openings 38) x.2) ≤
      ((0:ℕ):ℝ)/Fintype.card Ext4+((0:ℕ):ℝ)/Fintype.card Ext4+pcsError+
      uniformProb AllCoins (BoundaryFailure Packed.Witnesses.hash (fun _ => W)
        (fun _ => Packed.Witnesses.openings 38) (fun _ => Packed.Witnesses.checkpointLog)) := by
  apply air_pcs_soundness Packed.Witnesses.hash 0 0 badConstraint X (fun _ => 0) 0 eqPlan
    (fun _ => W) (fun _ => Packed.Witnesses.openings 38) (fun _ => Packed.Witnesses.checkpointLog)
    bad_row.1 bad_row.2 residual_degree exact_residual
  · intro x t
    simp [W,Pcs.PackedWitnesses.plan,eqPlan]
  · intro γ k
    simp [eqPlan]
  · intro x k i
    exact Pcs.PackedWitnesses.originals_exact k i
  · intro x
    exact Pcs.PackedWitnesses.checkpoints_logged x.2

/-- Correct quotient of a nonconstant valid source makes the residual zero,
and the source's nonzero row value is accepted. -/
theorem positive_quotient :
    ((X:Ext4[X])-1).eval 1=0 ∧
    ∀ γ,AirPolynomialOod.residual (fun _ : Fin 1 => (X:Ext4[X])-1) (X-1) (fun _ => 1) γ=0 := by
  constructor
  · simp
  · intro γ
    simp [AirPolynomialOod.residual,batch]

/-- Dropping the pre-zeta quotient restriction destroys the OOD argument:
a malicious quotient chosen as 1/zeta satisfies every nonzero OOD query while
the constraint remains nonzero at the base row 0. -/
theorem adaptive_quotient_falsifier :
    (1:Ext4[X]).eval 0 ≠ 0 ∧ ∀ ζ : Ext4,ζ ≠ 0 →
      ((1:Ext4[X])-X*C (ζ⁻¹)).eval ζ=0 := by
  constructor
  · simp
  · intro ζ hζ
    simp [hζ]

/-- A false opening really is necessary for the accepting claimed equation. -/
theorem false_opening_tooth :
    eval (opened W.claims 0) equation=0 ∧
      (equationPoly (fun _ => 0) (fun _ => 0) equation).eval 0 ≠ 0 := by
  constructor
  · exact claimed_equation_accepts (0,0)
  · simp [equationPoly,equation,lift,AirPolynomialOod.read,readAlg,fold_mk,cst,mul',add',vr,columnPolys]

end
end Minidregg.Compiler.Ir2AirPcsOod.Witnesses

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.Witnesses.claimed_equation_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.Witnesses.claimed_equation_accepts

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.Witnesses.exact_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.Witnesses.exact_residual

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.Witnesses.bad_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.Witnesses.bad_row

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.Witnesses.residual_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.Witnesses.residual_degree

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.Witnesses.actual_packed_head_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.Witnesses.actual_packed_head_fires

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.Witnesses.positive_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.Witnesses.positive_quotient

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.Witnesses.adaptive_quotient_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.Witnesses.adaptive_quotient_falsifier

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.Witnesses.false_opening_tooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.Witnesses.false_opening_tooth

