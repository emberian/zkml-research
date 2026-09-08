/- One compiler composition for every coefficient of the actual six-to-three
BFV downscaler. The source's two exact rounding quotients and the target's three
canonical remainders share variables in one source system, before serialization. -/
import Compiler.FheSourceCertificateEmit
import Compiler.FheTargetProjectionEmit
import Compiler.FheTargetProjectionWitness
import Compiler.PredCompile
import Compiler.AirSimplify

namespace Minidregg.Compiler.BfvRescaleRow
open Minidregg.Compiler
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.AirSimplify
open Minidregg.Theory
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

def nVars : Nat := 37665
def zeroWire : Fin nVars := ⟨88,by decide⟩
def publicInput (i : Fin 6) (d : Fin 11) : Fin nVars := ⟨1+11*i.val+d.val,by dsimp [nVars]; omega⟩
def publicOutput (i : Fin 3) (d : Fin 7) : Fin nVars := ⟨67+7*i.val+d.val,by dsimp [nVars]; omega⟩

/-- Public inputs replace the six source residue groups. Their unused high
digits, and the top three digits of the shared Y, are pinned through zeroWire. -/
def sourceIx (i : Fin 30294) : Fin nVars :=
  if h : i.val < 132 then
    if hd : i.val%22 < 11 then
      ⟨1+11*(i.val/22)+i.val%22,by dsimp [nVars]; omega⟩
    else zeroWire
  else if 415 ≤ i.val ∧ i.val < 418 then zeroWire
  else ⟨89+i.val,by dsimp [nVars]; omega⟩

/-- Target group zero is the same Y as the source. Three target remainder
groups are the public output words; all their unused high digits are zero. -/
def targetIx (i : Fin 7282) : Fin nVars :=
  if hy : i.val < 19 then sourceIx ⟨396+i.val,by omega⟩
  else if ho : i.val/19 = 1 ∨ i.val/19 = 4 ∨ i.val/19 = 7 then
    if hd : i.val%19 < 7 then
      ⟨67+7*((i.val/19-1)/3)+i.val%19,by dsimp [nVars]; omega⟩
    else zeroWire
  else ⟨30383+i.val,by dsimp [nVars]; omega⟩

def sourceView (asg : Fin nVars → BabyBear) (j : Nat) : BabyBear :=
  if h : j < 30294 then asg (sourceIx ⟨j,h⟩) else 0

def targetView (asg : Fin nVars → BabyBear) (j : Nat) : BabyBear :=
  if h : j < 7282 then asg (targetIx ⟨j,h⟩) else 0

def residues (asg : Fin nVars → BabyBear) (i : Fin 6) : Int :=
  (∑ d : Fin 11,64^d.val*(asg (publicInput i d)).val : Nat)
def output (asg : Fin nVars → BabyBear) (i : Fin 3) : Nat :=
  ∑ d : Fin 7,64^d.val*(asg (publicOutput i d)).val

def system : ConstraintSystem BabyBear (Fin nVars) :=
  [vr zeroWire] ++ renameS sourceIx FheSourceCertificate.sourceSystem ++ renameS targetIx FheTargetProjection.sourceSystem

/-- No gate-equation or rounding premise is supplied by the caller. The
combined generated relation forces every actual target residue of the exact
fixed-point downscaler, including its already-proved nearest+1 behavior. -/
def RowSound : Prop := ∀ asg : Fin nVars → BabyBear, systemAccepts asg system →
  ∀ i, (output asg i : Int) = FheRnsScale.deployedOutput (residues asg) % (FheTargetProjection.targetPrime i : Int)

theorem source_balanced (asg : Fin nVars → BabyBear)
    (h : systemAccepts (asg ∘ sourceIx) FheSourceCertificate.sourceSystem) : FheSourceCertificate.Balanced (FheSourceCertificate.decoded (sourceView asg)) := by
  obtain ⟨v,hv,hd⟩ := (emit_accepts_iff_fin 30294 0 (asg ∘ sourceIx) FheSourceCertificate.sourceSystem).mpr h
  have hb := FheSourceCertificate.sourceDescriptor_balanced v hd
  have he : FheSourceCertificate.decoded v = FheSourceCertificate.decoded (sourceView asg) := by
    funext g
    apply Finset.sum_congr rfl
    intro d _
    rw [hv (FheSourceCertificate.scalarWire (FheSourceCertificate.groupDigit (g,d)))]
    simp [sourceView]
  simpa only [he] using hb

theorem target_balanced (asg : Fin nVars → BabyBear)
    (h : systemAccepts (asg ∘ targetIx) FheTargetProjection.sourceSystem) : FheTargetProjection.Balanced (FheTargetProjection.decoded (targetView asg)) := by
  obtain ⟨v,hv,hd⟩ := (emit_accepts_iff_fin 7282 0 (asg ∘ targetIx) FheTargetProjection.sourceSystem).mpr h
  have hb := FheTargetProjection.sourceDescriptor_balanced v hd
  have he : FheTargetProjection.decoded v = FheTargetProjection.decoded (targetView asg) := by
    funext g
    apply Finset.sum_congr rfl
    intro d _
    rw [hv (FheTargetProjection.scalarWire (FheTargetProjection.groupDigit (g,d)))]
    simp [targetView]
  simpa only [he] using hb

theorem source_public (asg : Fin nVars → BabyBear) (hz : asg zeroWire = 0) :
    FheSourceCertificate.readResidues (FheSourceCertificate.decoded (sourceView asg)) = residues asg := by
  funext i
  fin_cases i <;>
    norm_num [FheSourceCertificate.readResidues,FheSourceCertificate.decoded,FheSourceCertificate.scalarWire,FheSourceCertificate.groupDigit,sourceView,sourceIx,
      residues,publicInput,Fin.sum_univ_succ,finProdFinEquiv,hz]

theorem shared_output (asg : Fin nVars → BabyBear) (hz : asg zeroWire = 0) :
    FheSourceCertificate.decoded (sourceView asg) 18 = FheTargetProjection.decoded (targetView asg) 0 := by
  norm_num [FheSourceCertificate.decoded,FheTargetProjection.decoded,FheSourceCertificate.scalarWire,FheTargetProjection.scalarWire,FheSourceCertificate.groupDigit,FheTargetProjection.groupDigit,
    sourceView,targetView,sourceIx,targetIx,Fin.sum_univ_succ,finProdFinEquiv,hz]

theorem target_public (asg : Fin nVars → BabyBear) (hz : asg zeroWire = 0) :
    FheTargetProjection.readLimbs (FheTargetProjection.decoded (targetView asg)) = output asg := by
  funext i
  fin_cases i <;>
    norm_num [FheTargetProjection.readLimbs,FheTargetProjection.decoded,FheTargetProjection.scalarWire,FheTargetProjection.groupDigit,targetView,targetIx,
      output,publicOutput,Fin.sum_univ_succ,finProdFinEquiv,hz]

theorem rowSound : RowSound := by
  intro asg hs
  obtain ⟨⟨hz,hs⟩,ht⟩ := (show (systemAccepts asg [vr zeroWire] ∧
      systemAccepts asg (renameS sourceIx FheSourceCertificate.sourceSystem)) ∧
      systemAccepts asg (renameS targetIx FheTargetProjection.sourceSystem) from by
      simpa only [system,systemAccepts_append] using hs)
  have hz' : asg zeroWire = 0 := by simpa [systemAccepts_cons,systemAccepts_nil,accepts,eval_vr] using hz
  have hs' := source_balanced asg ((systemAccepts_renameS asg sourceIx FheSourceCertificate.sourceSystem).mp hs)
  have ht' := target_balanced asg ((systemAccepts_renameS asg targetIx FheTargetProjection.sourceSystem).mp ht)
  have hy := FheSourceCertificate.balanced_output_forced _ hs'
  rw [source_public asg hz',shared_output asg hz'] at hy
  have h := FheTargetProjection.projection_source _ _ _ _ _ hy (FheTargetProjection.balanced_projection _ ht')
  rw [target_public asg hz'] at h
  exact h

/-- info: 'Minidregg.Compiler.BfvRescaleRow.source_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_balanced
/-- info: 'Minidregg.Compiler.BfvRescaleRow.target_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_balanced
/-- info: 'Minidregg.Compiler.BfvRescaleRow.source_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_public
/-- info: 'Minidregg.Compiler.BfvRescaleRow.shared_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shared_output
/-- info: 'Minidregg.Compiler.BfvRescaleRow.target_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_public
/-- info: 'Minidregg.Compiler.BfvRescaleRow.rowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowSound

end Minidregg.Compiler.BfvRescaleRow
