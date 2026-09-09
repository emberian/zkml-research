/- Actual emitted query system enters the generic polynomial/OOD bridge.
Three appended lookup polynomial bodies are parameters, fixed before gamma;
the native lookup protocol is not silently assumed proved. -/
import Compiler.BfvQueryWholeRows
import Compiler.AirPolynomialOod

namespace Minidregg.Compiler.BfvQueryRow.PolynomialOod
open Minidregg.Compiler Minidregg.Compiler.AirPolynomialOod
open Minidregg.Selvage Minidregg.Selvage.BabyBearExt4 Polynomial WholeRows
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def embed : Minidregg.Compiler.BabyBear →+* Ext4 :=
  (algebraMap BabyBearExt4.BabyBear Ext4).comp (RingHom.id BabyBearExt4.BabyBear)

def nativeList (columns : Fin nVars → Ext4[X]) (lookup : Fin 3 → Ext4[X]) : List Ext4[X] :=
  emittedSystem.map (lift (embed) columns) ++ List.ofFn lookup

/-- Coefficient zero is the last asserted constraint. This is the native
left-fold challenge order A := gamma*A+C, with the three LogUp bodies appended. -/
def constraints (columns : Fin nVars → Ext4[X]) (lookup : Fin 3 → Ext4[X]) :
    Fin (emittedSystem.length+2+1) → Ext4[X] :=
  fun j => (nativeList columns lookup).reverse[j.val]'(by
    simpa [nativeList,List.length_reverse,List.length_map] using j.isLt)

theorem coefficient_list (columns : Fin nVars → Ext4[X]) (lookup : Fin 3 → Ext4[X]) :
    List.ofFn (constraints columns lookup)=(nativeList columns lookup).reverse := by
  apply List.ext_getElem
  · simp [nativeList,Nat.add_assoc]
  · intro i hi hi'
    simp only [List.getElem_ofFn]
    rfl

/-- The actual main/lookup list reaches the exact native fold-left recurrence. -/
theorem native_batch_order (columns : Fin nVars → Ext4[X]) (lookup : Fin 3 → Ext4[X]) (γ : Ext4) :
    batch (constraints columns lookup) γ=
      (nativeList columns lookup).foldl (fun acc c => C γ*acc+c) 0 := by
  rw [batch_horner,coefficient_list,List.reverse_reverse]

/-- A false actual modular query row supplies a nonzero coefficient in the
native ordered AIR list, regardless of the appended lookup bodies. -/
theorem arithmetic_error_coefficient (columns : Fin nVars → Ext4[X])
    (lookup : Fin 3 → Ext4[X]) (r : Ext4) (asg : Fin nVars → BabyBear)
    (hrow : ∀ i,(columns i).eval r=embed (asg i))
    (hbad : ¬Arithmetic asg) :
    ∃ j,(constraints columns lookup j).eval r ≠ 0 := by
  have hs : ¬systemAccepts asg emittedSystem := fun h => hbad (emittedSystem_sound asg h)
  change ¬(∀ t ∈ emittedSystem,eval asg t=0) at hs
  push Not at hs
  obtain ⟨t,ht,hne⟩ := hs
  let p := lift (embed) columns t
  have hm : p ∈ (nativeList columns lookup).reverse := by
    apply List.mem_reverse.mpr
    exact List.mem_append_left _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hm
  have hjlt : j.val<emittedSystem.length+2+1 := by
    simpa [nativeList,List.length_reverse,List.length_map] using j.isLt
  refine ⟨⟨j.val,hjlt⟩,?_⟩
  have he : constraints columns lookup ⟨j.val,hjlt⟩=p := hj
  rw [he]
  change (lift (embed) columns t).eval r ≠ 0
  rw [lift_source _ _ _ _ hrow]
  exact (map_ne_zero (embed)).mpr hne

/-- Actual emitted false arithmetic reduces to fresh gamma/zeta error. The
uncomputed length in the theorem is the source list's length, never a prose count. -/
theorem arithmetic_ood_sound (D : ℕ) (columns : Fin nVars → Ext4[X])
    (lookup : Fin 3 → Ext4[X]) (vanishing : Ext4[X]) (quotient : Ext4 → Ext4[X])
    (r : Ext4) (asg : Fin nVars → BabyBear)
    (hrow : ∀ i,(columns i).eval r=embed (asg i))
    (hbad : ¬Arithmetic asg) (hr : vanishing.eval r=0)
    (hdeg : ∀ γ,(residual (constraints columns lookup) vanishing quotient γ).natDegree ≤ D) :
    uniformProb (Ext4×Ext4) (fun x =>
      (residual (constraints columns lookup) vanishing quotient x.1).eval x.2=0) ≤
      ((emittedSystem.length+2:ℕ):ℝ)/Fintype.card Ext4+(D:ℝ)/Fintype.card Ext4 :=
  ood_soundness _ D (constraints columns lookup) vanishing quotient r hr
    (arithmetic_error_coefficient columns lookup r asg hrow hbad) hdeg

/-- The actual terminal output mutation reaches a nonzero AIR batching
coefficient with constant column polynomials; none of the premises is merely named. -/
theorem terminal_coefficient_inhabited :
    ∃ (columns : Fin nVars → Ext4[X]) (j : Fin (emittedSystem.length+2+1)),
      (∀ i,(columns i).eval 0=embed (badTerminal i)) ∧
      (constraints columns (fun _ => 0) j).eval 0 ≠ 0 := by
  let columns := fun i => C (embed (badTerminal i))
  have hrow : ∀ i,(columns i).eval 0=embed (badTerminal i) := by intro i; simp [columns]
  have hbad : ¬Arithmetic badTerminal := by
    intro h
    have he := (h 0).2
    obtain ⟨h0,h1,h2,h3⟩ := bad_terminal_values
    rw [h0,h1,h2,h3] at he
    norm_num at he
  obtain ⟨j,hj⟩ := arithmetic_error_coefficient columns (fun _ => 0) 0 badTerminal hrow hbad
  exact ⟨columns,j,hrow,hj⟩

end
end Minidregg.Compiler.BfvQueryRow.PolynomialOod

/-- info: 'Minidregg.Compiler.BfvQueryRow.PolynomialOod.coefficient_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.PolynomialOod.coefficient_list

/-- info: 'Minidregg.Compiler.BfvQueryRow.PolynomialOod.native_batch_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.PolynomialOod.native_batch_order

/-- info: 'Minidregg.Compiler.BfvQueryRow.PolynomialOod.arithmetic_error_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.PolynomialOod.arithmetic_error_coefficient

/-- info: 'Minidregg.Compiler.BfvQueryRow.PolynomialOod.arithmetic_ood_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.PolynomialOod.arithmetic_ood_sound

/-- info: 'Minidregg.Compiler.BfvQueryRow.PolynomialOod.terminal_coefficient_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvQueryRow.PolynomialOod.terminal_coefficient_inhabited

