#!/usr/bin/env python3
"""Generate the fixed three-prime projection layout using the existing compiler."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent;FORMAL=ROOT.parents[2]/'formal/bfv_lift_refinement/target_projection'
ps=[68719403009,68719230977,137438822401];rows=[]
for i,p in enumerate(ps):
 l=[0]*10;r=[0]*10;l[0]=1;r[1+3*i]=1;r[2+3*i]=p
 rows.append(dict(left_constant=0,right_constant=0,left=l,right=r))
 l=[0]*10;r=[0]*10;l[1+3*i]=l[3+3*i]=1
 rows.append(dict(left_constant=0,right_constant=p-1,left=l,right=r))
s='''/- Generated nonnegative target projection matrix: Y=qi*quotienti+limbi,
limbi+slacki=qi-1. The source certificate supplies the shared Y through explicit
boundary equality checks. Every group has nineteen radix64 digits. -/
import Compiler.FheTargetProjection
namespace Minidregg.Compiler.FheTargetProjection
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
'''
for side in ['left','right']:
 s+=f'\ndef {side}Constant (row : Fin 6) : ℕ := match row.val with\n'
 for j,row in enumerate(rows):s+=f'  | {j} => {row[side+"_constant"]}\n'
 s+='  | _ => 0\n'
 s+=f'def {side}Matrix (row : Fin 6) (col : Fin 10) : ℕ := match row.val,col.val with\n'
 for j,row in enumerate(rows):
  for k,v in enumerate(row[side]):
   if v:s+=f'  | {j},{k} => {v}\n'
 s+='  | _,_ => 0\n'
s+='''
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
'''
for j,row in enumerate(rows):
 s+=f'  have h{j} := h {j}\n'
 s+=f'  norm_num [dot,Fin.sum_univ_succ,leftConstant,rightConstant,leftMatrix,rightMatrix] at h{j}\n'
 i=j//2;p=ps[i]
 if j%2==0:s+=f'  change x 0=x {1+3*i}+{p}*x {2+3*i} at h{j}\n'
 else:s+=f'  change x {1+3*i}+x {3+3*i}={p-1} at h{j}\n'
s+='''  intro i
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
'''
(FORMAL/'Compiler/FheTargetProjectionLayout.lean').write_text(s)
old=(FORMAL.parent/'source_certificate/Compiler/FheSourceCertificateEmit.lean').read_text().split('\n-- AXIOM PINS')[0]
s=old[:old.index('/-- Main emitted-descriptor refinement.')]
s=s.replace('FheSourceCertificate','FheTargetProjection').replace('21 groups of22 radix64 digits, twelve','10 groups of19 radix64 digits, six').replace('57 columns and15-bit carries','26 columns and14-bit carries')
# Ordered, explicit whole-number substitution avoids partial index corruption.
import re
mapping={462:190,30294:7282,21:10,22:19,12:6,3234:1330,2255:992,57:26,15:14,399:182,928:405,58:27,210:38}
s=re.sub(r'\b(?:'+ '|'.join(map(str,mapping)) +r')\b',lambda m:str(mapping[int(m.group())]),s)
s=s.replace('≤ 64^10','≤ 64^18').replace('matrix_capacities.2 row','matrix_capacities.2 row')
start=s.index('def EmittedSourceSound');end=s.index('/-- The emitted wire layout',start)
s=s[:start]+'''def EmittedTargetSound (d : ConstraintDescriptor BabyBear) : Prop :=
  ∀ v : ℕ → BabyBear,descriptorHolds d v →
    ∀ i,readLimbs (decoded v) i=decoded v 0%targetPrime i

'''+s[end:]
s+='''/-- Every target is fixed by the descriptor's own QR and range constraints. -/
theorem targetDescriptor_sound : EmittedTargetSound sourceDescriptor := by
  intro v hd
  exact balanced_limbs (decoded v) (sourceDescriptor_balanced v hd)

end Minidregg.Compiler.FheTargetProjection
'''
(FORMAL/'Compiler/FheTargetProjectionEmit.lean').write_text(s)
(ROOT/'layout.json').write_text(json.dumps(dict(target_primes=ps,rows=rows,groups=10,digits_per_group=19,columns=26,carry_bits=14,variables=7282),indent=2)+'\n')

# Preserve exact checked axiom pins when reproducing already frozen modules.
pinfile=FORMAL/'axiom-pins.json'
if pinfile.exists():
 pins=json.loads(pinfile.read_text())
 for name in ['FheTargetProjectionLayout','FheTargetProjectionEmit']:
  p=FORMAL/'Compiler'/f'{name}.lean';text=p.read_text().rstrip()+'\n'
  text+='\n-- AXIOM PINS: actual checked print output.\n'
  for declaration in re.findall(r'^theorem (\w+)',text,re.M):
   text+='\n/-- info: '+pins[declaration]+' -/\n#guard_msgs in\n#print axioms Minidregg.Compiler.FheTargetProjection.'+declaration+'\n'
  p.write_text(text)
