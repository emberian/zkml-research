/-
# Selvage.AdditiveFriTower -- characteristic-two additive FRI domains

The multiplicative `FoldingTower` in `Selvage.Proximity` cannot be instantiated
in characteristic two: its fibres are `{x,-x}` and its structure contains the
field axiom `2 != 0`.  This file therefore records the additive tower directly.

For an affine domain `offset + span(beta_0,...,beta_(ell-1))`, round `r`
has applied the first `r` subspace-vanishing maps for the *reversed* basis.
Consequently it folds the current last generator, exactly like the executable
additive FRI, while retaining the low binary coordinate bits.  The central
lemmas below prove that

* the round maps are the iterated characteristic-two quotients;
* low/high representatives differ by the current additive pivot; and
* applying the quotient map to a low representative is definitionally the
  corresponding representative at the next round.

No multiplicative squaring/negation structure is used or assumed.
-/
import Selvage.AdditiveProximity
import Selvage.HalfThresholdFriCoherent

namespace Minidregg.Selvage

open Minidregg.Theory

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

/-! ## Reversed LCH chain and its iterated quotient map -/

/-- Reverse the first `ell` entries of a basis.  Only indices `< ell` are
used by the tower.  Thus round zero folds `beta (ell-1)`, matching the runtime
layout in which the two halves differ in the last (highest) basis bit. -/
def additiveReverseBasis (ell : ℕ) (beta : ℕ → F) (i : ℕ) : F :=
  beta (ell - 1 - i)

/-- The quotient map after `r` additive folds. -/
noncomputable def additiveTowerMap (ell : ℕ) (beta : ℕ → F)
    (r : ℕ) : F →ₗ[ZMod 2] F :=
  subspaceVanishingHom (additiveReverseBasis ell beta) r

/-- The additive kernel generator used by round `r`. -/
noncomputable def additiveTowerPivot (ell : ℕ) (beta : ℕ → F)
    (r : ℕ) : F :=
  additiveTowerMap ell beta r (additiveReverseBasis ell beta r)

@[simp] theorem additiveTowerMap_zero (ell : ℕ) (beta : ℕ → F) (x : F) :
    additiveTowerMap ell beta 0 x = x := by
  simp [additiveTowerMap, subspaceVanishingHom]

theorem additiveTowerMap_succ (ell : ℕ) (beta : ℕ → F)
    (r : ℕ) (x : F) :
    additiveTowerMap ell beta (r + 1) x =
      foldMap (additiveTowerPivot ell beta r) (additiveTowerMap ell beta r x) := by
  change (subspaceVanishing (additiveReverseBasis ell beta) (r + 1)).eval x =
    foldMap
      ((subspaceVanishing (additiveReverseBasis ell beta) r).eval
        (additiveReverseBasis ell beta r))
      ((subspaceVanishing (additiveReverseBasis ell beta) r).eval x)
  rw [subspaceVanishing_succ_eq_fold_comp]
  simp [Polynomial.eval_comp]

/-! ## Affine representatives at every level -/

/-- The unquotiented affine point using the first `k` (low-order) basis
coordinates. -/
def additiveTowerRawPoint (beta : ℕ → F) (offset : F) (k : ℕ)
    (c : Fin k → ZMod 2) : F :=
  offset + domainPoint beta k c

/-- A level-`r`, dimension-`k` affine representative after applying the first
`r` additive quotient maps. -/
noncomputable def additiveTowerPoint (ell : ℕ) (beta : ℕ → F)
    (offset : F) (r k : ℕ) (c : Fin k → ZMod 2) : F :=
  additiveTowerMap ell beta r (additiveTowerRawPoint beta offset k c)

omit [CharP F 2] in
@[simp] theorem additiveTowerRawPoint_snoc_zero
    (beta : ℕ → F) (offset : F) (k : ℕ) (c : Fin k → ZMod 2) :
    additiveTowerRawPoint beta offset (k + 1) (Fin.snoc c 0) =
      additiveTowerRawPoint beta offset k c := by
  simp [additiveTowerRawPoint, domainPoint, Fin.sum_univ_castSucc]

omit [CharP F 2] in
@[simp] theorem additiveTowerRawPoint_snoc_one
    (beta : ℕ → F) (offset : F) (k : ℕ) (c : Fin k → ZMod 2) :
    additiveTowerRawPoint beta offset (k + 1) (Fin.snoc c 1) =
      additiveTowerRawPoint beta offset k c + beta k := by
  simp [additiveTowerRawPoint, domainPoint, Fin.sum_univ_castSucc,
    add_assoc]

/-- **Quotient-domain coherence.**  Folding the low representative at round
`r` gives exactly the same coordinate at round `r+1`. -/
theorem additiveTower_foldMap_reindex
    (ell : ℕ) (beta : ℕ → F) (offset : F) (r k : ℕ)
    (c : Fin k → ZMod 2) :
    foldMap (additiveTowerPivot ell beta r)
        (additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc c 0)) =
      additiveTowerPoint ell beta offset (r + 1) k c := by
  unfold additiveTowerPoint
  rw [← additiveTowerMap_succ]
  simp

/-- In a genuine height-`ell` tower, the current high representative is the
low representative translated by the current additive pivot. -/
theorem additiveTower_high_eq_low_add_pivot
    (ell : ℕ) (beta : ℕ → F) (offset : F) (r k : ℕ)
    (hrk : r + k + 1 = ell) (c : Fin k → ZMod 2) :
    additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc c 1) =
      additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc c 0) +
        additiveTowerPivot ell beta r := by
  rw [additiveTowerPoint, additiveTowerPoint,
    additiveTowerRawPoint_snoc_one, additiveTowerRawPoint_snoc_zero,
    map_add]
  congr 1
  unfold additiveTowerPivot additiveReverseBasis
  congr 2
  omega

/-- The additive FRI fold reads exactly the low/high representatives of a
level and produces a word on the next quotient domain. -/
noncomputable def additiveTowerFold
    (ell : ℕ) (beta : ℕ → F) (offset : F) (r k : ℕ)
    (lam : F) (word : F → F) (c : Fin k → ZMod 2) : F :=
  friFold (additiveTowerPivot ell beta r) lam word
    (additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc c 0))

/-- Changing from the low to the high representative does not change the
folded value. -/
theorem additiveTowerFold_high
    (ell : ℕ) (beta : ℕ → F) (offset : F) (r k : ℕ)
    (hrk : r + k + 1 = ell) (lam : F) (word : F → F)
    (c : Fin k → ZMod 2) :
    friFold (additiveTowerPivot ell beta r) lam word
        (additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc c 1)) =
      additiveTowerFold ell beta offset r k lam word c := by
  rw [additiveTower_high_eq_low_add_pivot ell beta offset r k hrk]
  exact friFold_coset_invariant _ _ _ _

/-! ## Finite quotient domains -/

/-- The set of all level-`r`, dimension-`k` affine representatives. -/
noncomputable def additiveTowerDomain
    (ell : ℕ) (beta : ℕ → F) (offset : F) (r k : ℕ) : Finset F := by
  classical
  exact Finset.univ.image (additiveTowerPoint ell beta offset r k)

/-- The canonical low representative of every round-`r` additive fibre. -/
noncomputable def additiveTowerTransversal
    (ell : ℕ) (beta : ℕ → F) (offset : F) (r k : ℕ) : Finset F := by
  classical
  exact Finset.univ.image fun c : Fin k → ZMod 2 =>
    additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc c 0)

/-- Applying the additive quotient map to the canonical transversal produces
exactly the next affine domain. -/
theorem additiveTower_domain_image
    [DecidableEq F]
    (ell : ℕ) (beta : ℕ → F) (offset : F) (r k : ℕ) :
    (additiveTowerTransversal ell beta offset r k).image
        (foldMap (additiveTowerPivot ell beta r)) =
      additiveTowerDomain ell beta offset (r + 1) k := by
  classical
  ext y
  simp [additiveTowerTransversal, additiveTowerDomain,
    additiveTower_foldMap_reindex]

/-! ## Distinctness of every quotient level -/

/-- An independent height-`ell` input basis remains injective after `r`
quotients on any `k` low coordinates with `r+k <= ell`.  Algebraically, the
kernel of the reversed `W_r` map is the span of the `r` high coordinates, and
linear independence makes that span disjoint from the retained low span. -/
theorem additiveTowerPoint_injective
    (ell : ℕ) (beta : ℕ → F) (offset : F)
    (hbeta : LinearIndependent (ZMod 2) (fun j : Fin ell => beta j))
    (r k : ℕ) (hrk : r + k ≤ ell) :
    Function.Injective (additiveTowerPoint ell beta offset r k) := by
  classical
  have hr : r ≤ ell := le_trans (Nat.le_add_right r k) hrk
  have hk : k ≤ ell := le_trans (Nat.le_add_left k r) (by simpa [add_comm] using hrk)
  let revIndex : Fin r → Fin ell := fun i =>
    ⟨ell - 1 - (i : ℕ), by have := i.isLt; omega⟩
  have hrevIndex : Function.Injective revIndex := by
    intro i j hij
    apply Fin.ext
    have hijv := congrArg Fin.val hij
    dsimp [revIndex] at hijv
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hrev : LinearIndependent (ZMod 2)
      (fun i : Fin r => additiveReverseBasis ell beta i) := by
    have hcomp := hbeta.comp revIndex hrevIndex
    simpa [Function.comp_def, revIndex, additiveReverseBasis] using hcomp
  let lowIndex : Fin k → Fin ell := Fin.castLE hk
  have hlowIndependent : LinearIndependent (ZMod 2)
      (fun i : Fin k => beta i) := by
    have hcomp := hbeta.comp lowIndex (Fin.castLE_injective hk)
    simpa [Function.comp_def, lowIndex] using hcomp
  intro c d hcd
  let z : F := domainPoint beta k c - domainPoint beta k d
  have hzmap : additiveTowerMap ell beta r z = 0 := by
    have hsub : additiveTowerMap ell beta r
        (additiveTowerRawPoint beta offset k c -
          additiveTowerRawPoint beta offset k d) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hcd
    simpa [z, additiveTowerRawPoint] using hsub
  have hzkernel : z ∈ additiveDomain (additiveReverseBasis ell beta) r := by
    apply (subspaceVanishing_eval_eq_zero_iff hrev z).mp
    simpa [additiveTowerMap] using hzmap
  let v : Fin ell → F := fun j => beta j
  let low : Set (Fin ell) := {j | (j : ℕ) < k}
  let high : Set (Fin ell) := {j | ell - r ≤ (j : ℕ)}
  have hsets : Disjoint low high := by
    rw [Set.disjoint_left]
    intro j hjlow hjhigh
    simp only [low, Set.mem_setOf_eq] at hjlow
    simp only [high, Set.mem_setOf_eq] at hjhigh
    omega
  have hzlow : z ∈ Submodule.span (ZMod 2) (v '' low) := by
    change domainPoint beta k c - domainPoint beta k d ∈ _
    simp only [domainPoint, ← Finset.sum_sub_distrib, ← sub_smul]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨lowIndex j, ?_, ?_⟩
    · simp [low, lowIndex]
    · rfl
  have hzhigh : z ∈ Submodule.span (ZMod 2) (v '' high) := by
    obtain ⟨a, ha⟩ :=
      (mem_additiveDomain_iff (additiveReverseBasis ell beta) r z).mp hzkernel
    rw [← ha]
    unfold domainPoint
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨revIndex i, ?_, ?_⟩
    · simp only [high, Set.mem_setOf_eq, revIndex]
      have hi := i.isLt
      omega
    · simp [v, revIndex, additiveReverseBasis]
  have hz : z = 0 :=
    Submodule.disjoint_def.mp (hbeta.disjoint_span_image hsets) z hzlow hzhigh
  apply domainPoint_injective hlowIndependent
  rw [← sub_eq_zero]
  exact hz

/-- Every valid additive tower level is an RS-domain embedding. -/
noncomputable def additiveTowerEmbedding
    (ell : ℕ) (beta : ℕ → F) (offset : F)
    (hbeta : LinearIndependent (ZMod 2) (fun j : Fin ell => beta j))
    (r k : ℕ) (hrk : r + k ≤ ell) : (Fin k → ZMod 2) ↪ F :=
  ⟨additiveTowerPoint ell beta offset r k,
    additiveTowerPoint_injective ell beta offset hbeta r k hrk⟩

/-- Every genuine round pivot is nonzero, so the additive interpolation
division used by `friFold` is valid. -/
theorem additiveTowerPivot_ne_zero
    (ell : ℕ) (beta : ℕ → F) (offset : F)
    (hbeta : LinearIndependent (ZMod 2) (fun j : Fin ell => beta j))
    (r k : ℕ) (hrk : r + k + 1 = ell) :
    additiveTowerPivot ell beta r ≠ 0 := by
  intro hpivot
  let c : Fin k → ZMod 2 := 0
  have hinj := additiveTowerPoint_injective ell beta offset hbeta r (k + 1)
    (by omega)
  have hpoints :
      additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc c 1) =
        additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc c 0) := by
    rw [additiveTower_high_eq_low_add_pivot ell beta offset r k hrk, hpivot,
      add_zero]
  have hindices := hinj hpoints
  have hlast := congrFun hindices (Fin.last k)
  norm_num at hlast

/-- The low representatives are a genuine transversal: translating one by
the current pivot never lands on another low representative. -/
theorem additiveTower_transversal
    (ell : ℕ) (beta : ℕ → F) (offset : F)
    (hbeta : LinearIndependent (ZMod 2) (fun j : Fin ell => beta j))
    (r k : ℕ) (hrk : r + k + 1 = ell) :
    ∀ x ∈ additiveTowerTransversal ell beta offset r k,
      x + additiveTowerPivot ell beta r ∉
        additiveTowerTransversal ell beta offset r k := by
  classical
  intro x hx
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx
  intro hxhigh
  obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hxhigh
  have hinj := additiveTowerPoint_injective ell beta offset hbeta r (k + 1)
    (by omega)
  have hpoints :
      additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc c 1) =
        additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc d 0) := by
    rw [additiveTower_high_eq_low_add_pivot ell beta offset r k hrk]
    exact hd.symm
  have hindices := hinj hpoints
  have hlast := congrFun hindices (Fin.last k)
  norm_num at hlast

/-- The full current domain is exactly the disjoint low/high pair domain used
by the one-round additive proximity theorem. -/
theorem additiveTower_domain_eq_pairDomain
    [DecidableEq F]
    (ell : ℕ) (beta : ℕ → F) (offset : F)
    (r k : ℕ) (hrk : r + k + 1 = ell) :
    additiveTowerDomain ell beta offset r (k + 1) =
      pairDomain (additiveTowerTransversal ell beta offset r k)
        (additiveTowerPivot ell beta r) := by
  classical
  ext x
  simp only [additiveTowerDomain, additiveTowerTransversal, pairDomain, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨a, rfl⟩
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide)
        (a (Fin.last k)) with hbit | hbit
    · left
      have ha : Fin.snoc (Fin.init a) 0 = a := by
        simpa [hbit] using Fin.snoc_init_self a
      exact ⟨Fin.init a, congrArg
        (additiveTowerPoint ell beta offset r (k + 1)) ha⟩
    · right
      have ha : Fin.snoc (Fin.init a) 1 = a := by
        simpa [hbit] using Fin.snoc_init_self a
      refine ⟨additiveTowerPoint ell beta offset r (k + 1)
          (Fin.snoc (Fin.init a) 0), ⟨Fin.init a, rfl⟩, ?_⟩
      calc
        additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc (Fin.init a) 0) +
            additiveTowerPivot ell beta r =
          additiveTowerPoint ell beta offset r (k + 1) (Fin.snoc (Fin.init a) 1) :=
            (additiveTower_high_eq_low_add_pivot ell beta offset r k hrk _).symm
        _ = additiveTowerPoint ell beta offset r (k + 1) a :=
          congrArg (additiveTowerPoint ell beta offset r (k + 1)) ha
  · rintro (hlow | hhigh)
    · obtain ⟨c, hc⟩ := hlow
      exact ⟨Fin.snoc c 0, hc⟩
    · obtain ⟨y, ⟨c, rfl⟩, rfl⟩ := hhigh
      refine ⟨Fin.snoc c 1, ?_⟩
      exact additiveTower_high_eq_low_add_pivot ell beta offset r k hrk c

/-! ## Runtime-shaped coherent paths -/

/-- Additive binary coordinates at level `n`.  Their cardinality is the
runtime word length `2^(ell-n)`. -/
abbrev AdditiveFriLevels (ell n : ℕ) : Type := Fin (ell - n) → ZMod 2

/-- Little-endian binary coordinates are exactly the runtime's integer
indices.  `finFunctionFinEquiv` uses weights `2^i`, so removing the current
last coordinate preserves the low integer bits. -/
def additiveFriLevelEquivPowerTwo (ell n : ℕ) :
    AdditiveFriLevels ell n ≃ PowerTwoFriLevels ell n :=
  (Equiv.piCongrRight fun _ => (ZMod.finEquiv 2).toEquiv.symm).trans
    finFunctionFinEquiv

/-- Transport the existing modulo-based coherent round sampler to additive
bit-vector coordinates. -/
def additiveCoherentRound {ell m qCount : ℕ} (hmell : m ≤ ell)
    (j : Fin m) (seed : Fin qCount → PowerTwoFriLevels ell 1) :
    Fin qCount → AdditiveFriLevels ell ((j : ℕ) + 1) :=
  fun a => (additiveFriLevelEquivPowerTwo ell ((j : ℕ) + 1)).symm
    (powerTwoCoherentRound hmell j seed a)

/-- The batchwise coordinate equivalence used to transport uniformity. -/
def additiveBatchEquivPowerTwo (ell n qCount : ℕ) :
    (Fin qCount → AdditiveFriLevels ell n) ≃
      (Fin qCount → PowerTwoFriLevels ell n) :=
  Equiv.piCongrRight fun _ => additiveFriLevelEquivPowerTwo ell n

/-- **Coherent additive paths have exact uniform marginals at every round.**
This is the sampling/coherence fact needed by the `(1-tau)^q` argument; no
independence between rounds is claimed. -/
theorem additiveCoherentRound_uniform {ell m qCount : ℕ}
    (hmell : m ≤ ell) (j : Fin m)
    (p : (Fin qCount → AdditiveFriLevels ell ((j : ℕ) + 1)) → Prop) :
    uniformProb (Fin qCount → PowerTwoFriLevels ell 1)
        (fun seed => p (additiveCoherentRound hmell j seed)) =
      uniformProb
        (Fin qCount → AdditiveFriLevels ell ((j : ℕ) + 1)) p := by
  let e := additiveBatchEquivPowerTwo ell ((j : ℕ) + 1) qCount
  let pPower : (Fin qCount → PowerTwoFriLevels ell ((j : ℕ) + 1)) → Prop :=
    fun q => p (e.symm q)
  calc
    uniformProb (Fin qCount → PowerTwoFriLevels ell 1)
        (fun seed => p (additiveCoherentRound hmell j seed)) =
      uniformProb (Fin qCount → PowerTwoFriLevels ell ((j : ℕ) + 1))
        pPower := by
          simpa [additiveCoherentRound, pPower, e,
            additiveBatchEquivPowerTwo] using
            powerTwoCoherentRound_uniform hmell j pPower
    _ = uniformProb
        (Fin qCount → AdditiveFriLevels ell ((j : ℕ) + 1)) p := by
      symm
      simpa [pPower, e] using
        uniformProb_equiv e pPower

/-! ## The exact remaining boundary

The next theorem is an additive counterpart of
`friAdaptive_coherent_sampled_sound`: its round-consistency predicate must use
`additiveTowerFold`/the low-high representatives above, and its transition
hypotheses are supplied by `additiveFold_distance_UD`.  The existing adaptive
acceptance predicate is specialized to multiplicative `FoldingData` (including
the impossible characteristic-two field `two_ne`), so there is no honest type
to instantiate here without first extracting that generic transcript layer.
-/

/-- info: 'Minidregg.Selvage.additiveTowerMap_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveTowerMap_succ
/-- info: 'Minidregg.Selvage.additiveTower_foldMap_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveTower_foldMap_reindex
/-- info: 'Minidregg.Selvage.additiveTower_high_eq_low_add_pivot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveTower_high_eq_low_add_pivot
/-- info: 'Minidregg.Selvage.additiveTower_domain_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveTower_domain_image
/-- info: 'Minidregg.Selvage.additiveTowerPoint_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveTowerPoint_injective
/-- info: 'Minidregg.Selvage.additiveTowerPivot_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveTowerPivot_ne_zero
/-- info: 'Minidregg.Selvage.additiveTower_transversal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveTower_transversal
/-- info: 'Minidregg.Selvage.additiveTower_domain_eq_pairDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveTower_domain_eq_pairDomain
/-- info: 'Minidregg.Selvage.additiveCoherentRound_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveCoherentRound_uniform

end Minidregg.Selvage
