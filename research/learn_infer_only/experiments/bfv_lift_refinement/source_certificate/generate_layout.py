#!/usr/bin/env python3
"""Generate the pinned positive/negative balance matrix; no new AIR implementation."""
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from fhe_scaler_model import ScalerModel
from math import prod
ROOT=Path(__file__).resolve().parents[3]/'formal/bfv_lift_refinement/source_certificate'
base=[68719403009,68719230977,137438822401];ext=base+[4611686018427322369,4611686018427289601,4611686018427215873];Q=prod(base);s=ScalerModel(ext,base,1032193,Q)
BG=1<<126;BF=1<<127;WO=1<<65;UO=1<<120
rows=[]
def row(label,lc,rc,L,R):
 ll=[L.get(i,0) for i in range(21)];rr=[R.get(i,0) for i in range(21)];rows.append(dict(label=label,left_constant=lc,right_constant=rc,left=ll,right=rr))
for i,p in enumerate(ext):row(f'canonical input residue {i}',0,p-1,{i:1,6+i:1},{})
row('exact Garner index QR',BG,0,{i:2*c for i,c in enumerate(s.tgarner)},{12:2*BG,13:1})
row('Garner remainder range',0,2*BG-1,{13:1,14:1},{})
row('exact signed fixed correction QR',BF+2*BF*WO,0,{i:2*max(c,0) for i,c in enumerate(s.tomega)},{**{i:2*max(-c,0) for i,c in enumerate(s.tomega)},15:2*BF,16:1})
row('fixed correction remainder range',0,2*BF-1,{16:1,17:1},{})
row('canonical whole-Q output QR',Q*UO,WO,{**dict(enumerate(s.omega)),15:1},{12:s.gamma,18:1,20:Q})
row('output range',0,Q-1,{18:1,19:1},{})
assert len(rows)==12
assert all(c<2**210 for r in rows for c in r['left']+r['right'])
assert all(max(r['left_constant'],r['right_constant'])<64**57 for r in rows)
def vec(xs):return '!['+', '.join(map(str,xs))+']'
text='''/- Generated pinned linear balance matrix. Every row becomes TWO EXISTING weighted
accumulators with shared result limbs. Uniform 22-digit groups are a conservative
baseline, not an optimized layout or a mandatory lower bound. -/
import Compiler.FheSourceCertificate

namespace Minidregg.Compiler.FheSourceCertificate
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
\n'''
text+=f'def wOffset : ℕ := {WO}\ndef uOffset : ℕ := {UO}\n'
for key,name in [('left_constant','leftConstant'),('right_constant','rightConstant')]:
 text+=f'def {name} (row : Fin 12) : ℕ := match row.val with\n'
 for i,r in enumerate(rows):text+=f'  | {i} => {r[key]}\n'
 text+='  | _ => 0\n'
for key,name in [('left','leftMatrix'),('right','rightMatrix')]:
 text+=f'def {name} (row : Fin 12) (col : Fin 21) : ℕ := match row.val,col.val with\n'
 for i,r in enumerate(rows):
  for j,c in enumerate(r[key]):
   if c:text+=f'  | {i},{j} => {c}\n'
 text+='  | _,_ => 0\n'
text+='''
def dot (a : Fin 21 → ℕ) (x : Fin 21 → ℕ) : ℕ := ∑ i, a i*x i

def Balanced (x : Fin 21 → ℕ) : Prop := ∀ j,
  leftConstant j+dot (leftMatrix j) x = rightConstant j+dot (rightMatrix j) x

def readResidues (x : Fin 21 → ℕ) (i : Fin 6) : ℤ := match i.val with
  | 0 => x 0 | 1 => x 1 | 2 => x 2 | 3 => x 3 | 4 => x 4 | _ => x 5
def readCertificate (x : Fin 21 → ℕ) : Certificate where
  v := x 12
  w := (x 15 : ℤ)-wOffset
  garnerRemainder := x 13
  correctionRemainder := x 16
  outputQuotient := (x 20 : ℤ)-uOffset

/-- Finite coefficient/capacity facts, proved about the generated pinned matrix. -/
theorem matrix_capacities :
    (∀ row col, leftMatrix row col < 2^210 ∧ rightMatrix row col < 2^210) ∧
    (∀ row, leftConstant row < 64^57 ∧ rightConstant row < 64^57) := by decide

/-- The generated nonnegative balances imply the exact signed source certificate. -/
theorem balanced_source_accepts (x : Fin 21 → ℕ) (h : Balanced x) :
    accepts (readResidues x) (x 18) (readCertificate x) := by
  have rows (i : Fin 12) := h i
'''
def expr(c,coeff):
 tail='0'
 for i,a in reversed(list(enumerate(coeff))):tail=f'({a}*x {i}+{tail})'
 return f'{c}+{tail}'
for j,r in enumerate(rows):
 text+=f'  have h{j} := rows {j}\n'
 text+=f'  simp only [dot,Fin.sum_univ_succ] at h{j}\n'
 text+=f'  change {expr(r["left_constant"],r["left"])} = {expr(r["right_constant"],r["right"])} at h{j}\n'
 text+=f'  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h{j}\n'
text+='''  have hr : ∀ i : Fin 6, 0 ≤ readResidues x i ∧ readResidues x i < FheRnsScale.deployedBase i := by
    intro i
    fin_cases i <;> norm_num [readResidues,FheRnsScale.deployedBase,Fin.succ] <;> omega
  refine ⟨hr,Int.natCast_nonneg (x 13),?_,Int.natCast_nonneg (x 16),?_,Int.natCast_nonneg (x 18),?_,?_,?_,?_⟩
  · dsimp [readCertificate]
    exact_mod_cast (show x 13 < 2*(2^126) by omega)
  · dsimp [readCertificate]
    exact_mod_cast (show x 16 < 2*(2^127) by omega)
  · norm_num [FheRnsScale.deployedQ]
    omega
  · have hi := congrArg (fun n : ℕ => (n : ℤ)) h6
    norm_num [Nat.cast_add,Nat.cast_mul] at hi
    norm_num [readResidues,readCertificate,FheRnsScale.deployedThetaG,Fin.sum_univ_succ,Fin.succ]
    linear_combination hi
  · have hi := congrArg (fun n : ℕ => (n : ℤ)) h8
    norm_num [Nat.cast_add,Nat.cast_mul] at hi
    norm_num [readResidues,readCertificate,FheRnsScale.deployedThetaF,Fin.sum_univ_succ,Fin.succ,wOffset]
    linear_combination hi
  · have hi := congrArg (fun n : ℕ => (n : ℤ)) h10
    norm_num [Nat.cast_add,Nat.cast_mul] at hi
    norm_num [readResidues,readCertificate,FheRnsScale.integerPart,
      FheRnsScale.deployedOmega,FheRnsScale.deployedGamma,FheRnsScale.deployedQ,
      Fin.sum_univ_succ,Fin.succ,wOffset,uOffset]
    linear_combination hi

/-- Matrix acceptance fixes one output, even where the source is nearest+1. -/
theorem balanced_output_forced (x : Fin 21 → ℕ) (h : Balanced x) :
    (x 18 : ℤ) = FheRnsScale.deployedOutput (readResidues x) % FheRnsScale.deployedQ :=
  sourceCertificateSound _ _ _ (balanced_source_accepts x h)

end Minidregg.Compiler.FheSourceCertificate
'''
pinfile=ROOT/'axiom-pins.json'
if pinfile.exists():
 import re
 pins=json.loads(pinfile.read_text())
 names=re.findall(r'^theorem (\w+)',text,re.M)
 text+='\n-- AXIOM PINS: actual checked print output.\n'
 for name in names:text+='\n/-- info: '+pins[name]+' -/\n#guard_msgs in\n#print axioms Minidregg.Compiler.FheSourceCertificate.'+name+'\n'
(ROOT/'Compiler/FheSourceCertificateLayout.lean').write_text(text)
out=Path(__file__).resolve().parent
(out/'layout.json').write_text(json.dumps(dict(label='DERIVED compiler balance specification generated from pinned source constants',groups=21,digits_per_group=22,radix=64,scalar_digits=462,rows=rows,columns=57,carry_bits=15,variables=30294,w_offset=str(WO),u_offset=str(UO)),indent=2)+'\n')
