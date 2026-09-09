/- Whole-domain query-row scope and public-prefix coverage.
This is a deterministic source/gate theorem; Rust refinement, PCS and probability are not claimed. -/
import Compiler.BfvQueryRow
import Compiler.Ir2WholeRow

namespace Minidregg.Compiler.BfvQueryRow.WholeRows
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open Minidregg.Compiler.Ir2WholeRow
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-- The exact existing query-row theorem conclusion, for both deployed BFV primes. -/
def Arithmetic (asg : Fin nVars → BabyBear) : Prop :=
  ∀ l, (∀ g : Fin 4,value asg l (g.castLE (by decide)) < primes l) ∧
    value asg l 3=((value asg l 0*value asg l 1)%primes l+primes l-
      (value asg l 0*value asg l 2)%primes l)%primes l

/-- Statement-first whole-domain scope contract on the actual emitted query relation. -/
def AllRowsSound : Prop := ∀ (Row : Type) (isLast : Row → Bool) (trace : Row → Fin nVars → BabyBear),
  (∀ r,scopeHolds false (isLast r) (trace r) emittedSystem) → ∀ r,Arithmetic (trace r)

theorem all_rows_sound : AllRowsSound := by
  intro Row isLast trace h r
  exact emittedSystem_sound (trace r) (Ir2WholeRow.all_rows isLast trace emittedSystem h r)

/-- Public row ID plus the eight radix64 words occupy exactly the existing prefix57. -/
abbrev PublicTuple := Fin 57 → BabyBear

def publicPrefix (asg : Fin nVars → BabyBear) : PublicTuple := fun i => asg (i.castLE (by decide))

def publicValue (p : PublicTuple) (l : Fin 2) (g : Fin 4) : Nat :=
  Bignum.denoteNat 64 (List.ofFn fun i : Fin 7 =>
    (p ⟨1+14*g.val+7*l.val+i.val,by omega⟩).val)

def PublicArithmetic (p : PublicTuple) : Prop :=
  ∀ l,(∀ g,publicValue p l g < primes l) ∧
    publicValue p l 3=((publicValue p l 0*publicValue p l 1)%primes l+primes l-
      (publicValue p l 0*publicValue p l 2)%primes l)%primes l

/-- The public tuple's word reader is literally the existing query source's reader. -/
theorem public_value_eq (asg : Fin nVars → BabyBear) (l : Fin 2) (g : Fin 4) :
    publicValue (publicPrefix asg) l g = value asg l (g.castLE (by decide)) := by
  simp [publicValue,publicPrefix,value,AirBignum.limbVals,group,g.isLt]

/-- The actual query relation constrains only these public values in its modular conclusion. -/
theorem public_prefix_sound (asg : Fin nVars → BabyBear) (h : systemAccepts asg emittedSystem) :
    PublicArithmetic (publicPrefix asg) := by
  intro l
  simpa only [public_value_eq] using emittedSystem_sound asg h l

/-- A matching public tuple inherits the actual modular result from any covered trace row. -/
theorem public_sound_of_covered {Row : Type} (isLast : Row → Bool)
    (trace : Row → Fin nVars → BabyBear)
    (h : ∀ r,scopeHolds false (isLast r) (trace r) emittedSystem)
    (p : PublicTuple) (hp : ∃ r,publicPrefix (trace r)=p) : PublicArithmetic p := by
  obtain ⟨r,rfl⟩ := hp
  exact public_prefix_sound (trace r) (Ir2WholeRow.all_rows isLast trace emittedSystem h r)

/-- Exact public multiset coverage suffices; the public list need not have trace order. -/
theorem public_sound_of_perm {Row : Type} (isLast : Row → Bool)
    (trace : Row → Fin nVars → BabyBear)
    (h : ∀ r,scopeHolds false (isLast r) (trace r) emittedSystem)
    (rows : List Row) (publicRows : List PublicTuple)
    (hp : publicRows.Perm (rows.map (fun r => publicPrefix (trace r)))) :
    ∀ p ∈ publicRows,PublicArithmetic p := by
  intro p hmem
  have hm : p ∈ rows.map (fun r => publicPrefix (trace r)) := hp.mem_iff.mp hmem
  obtain ⟨r,_,hr⟩ := List.mem_map.mp hm
  exact public_sound_of_covered isLast trace h p ⟨r,hr⟩

/-- A real public-output mutation: A,PP,PM are zero, while output limb0 has low digit one. -/
def badTerminal (i : Fin nVars) : BabyBear := if i.val=43 then 1 else 0

/-- Actual public query values at the corrupted row, independent of private witness columns. -/
theorem bad_terminal_values :
    value badTerminal 0 0=0 ∧ value badTerminal 0 1=0 ∧
      value badTerminal 0 2=0 ∧ value badTerminal 0 3=1 := by
  norm_num [value,AirBignum.limbVals,group,badTerminal,List.ofFn_succ,Bignum.denoteNat]
  decide +kernel

/-- The existing emitted source theorem itself refuses this terminal output mutation. -/
theorem bad_terminal_refused : ¬systemAccepts badTerminal emittedSystem := by
  intro h
  have he := (emittedSystem_sound badTerminal h 0).2
  have hv := bad_terminal_values
  rw [hv.1,hv.2.1,hv.2.2.1,hv.2.2.2] at he
  norm_num at he

/-- The exact old gate accepts that refusing source row at the terminal selector;
the new whole-domain gate refuses it. -/
theorem actual_terminal_falsifier :
    scopeHolds true true badTerminal emittedSystem ∧
      ¬scopeHolds false true badTerminal emittedSystem :=
  Ir2WholeRow.terminal_falsifier badTerminal emittedSystem bad_terminal_refused

/-- The terminal-falsifier premises are inhabited by the actual query layout. -/
theorem terminal_premises_inhabited : ∃ asg : Fin nVars → BabyBear,
    asg ⟨43,by decide⟩=1 ∧ ¬systemAccepts asg emittedSystem ∧ scopeHolds true true asg emittedSystem ∧
      ¬scopeHolds false true asg emittedSystem :=
  ⟨badTerminal,by simp [badTerminal],bad_terminal_refused,actual_terminal_falsifier⟩

/-- Positive scope inhabitation on two rows, including a last row, with a nonzero local value. -/
theorem whole_scope_inhabited :
    ∃ (trace : Fin 2 → Fin 1 → BabyBear) (sys : ConstraintSystem BabyBear (Fin 1)),
      (∀ r,scopeHolds false (r=1) (trace r) sys) ∧
      (∀ r,systemAccepts (trace r) sys) ∧ trace 1 0=1 := by
  let sys : ConstraintSystem BabyBear (Fin 1) := [add' (vr 0) (cst (-1))]
  have h : ∀ r : Fin 2,scopeHolds false (r=1) (fun _ : Fin 1 => (1:BabyBear)) sys := by
    intro r
    simp [scopeHolds,sys,systemAccepts_cons,systemAccepts_nil,accepts,eval_add',eval_vr,eval_cst]
  exact ⟨fun _ _ => 1,sys,h,Ir2WholeRow.all_rows (fun r => r=1) (fun _ _ => 1) sys h,rfl⟩

end Minidregg.Compiler.BfvQueryRow.WholeRows

/-- info: 'Minidregg.Compiler.BfvQueryRow.WholeRows.all_rows_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.WholeRows.all_rows_sound

/-- info: 'Minidregg.Compiler.BfvQueryRow.WholeRows.public_value_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.WholeRows.public_value_eq

/-- info: 'Minidregg.Compiler.BfvQueryRow.WholeRows.public_prefix_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.WholeRows.public_prefix_sound

/-- info: 'Minidregg.Compiler.BfvQueryRow.WholeRows.public_sound_of_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.WholeRows.public_sound_of_covered

/-- info: 'Minidregg.Compiler.BfvQueryRow.WholeRows.public_sound_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.WholeRows.public_sound_of_perm

/-- info: 'Minidregg.Compiler.BfvQueryRow.WholeRows.bad_terminal_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.WholeRows.bad_terminal_values

/-- info: 'Minidregg.Compiler.BfvQueryRow.WholeRows.bad_terminal_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.WholeRows.bad_terminal_refused

/-- info: 'Minidregg.Compiler.BfvQueryRow.WholeRows.actual_terminal_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.WholeRows.actual_terminal_falsifier

/-- info: 'Minidregg.Compiler.BfvQueryRow.WholeRows.terminal_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.WholeRows.terminal_premises_inhabited

/-- info: 'Minidregg.Compiler.BfvQueryRow.WholeRows.whole_scope_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.WholeRows.whole_scope_inhabited
