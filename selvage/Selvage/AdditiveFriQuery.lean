/-
# Selvage.AdditiveFriQuery -- adaptive sampled additive FRI

This is the characteristic-two counterpart of `HalfThresholdFriQuery`.  Its
round equation is the literal low/high additive interpolation used by
`additiveTowerFold`; it does not mention multiplicative `FoldingData`.
-/
import Selvage.AdditiveFriTower

namespace Minidregg.Selvage

open Minidregg.Theory

variable {F : Type} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

/-! ## Reindexing finite RS domains -/

omit [Field F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem hammingDist_equiv {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq F]
    (e : I ≃ K) (f g : I → F) :
    hammingDist f g =
      hammingDist (fun k => f (e.symm k)) (fun k => g (e.symm k)) := by
  classical
  unfold hammingDist
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa using (Finset.mem_filter.mp hi).2
  · intro i _ i' _ hii'
    exact e.injective hii'
  · intro k hk
    refine ⟨e.symm k, ?_, by simp⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hk).2⟩

omit [Field F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem relDist_equiv {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq F]
    (e : I ≃ K) (f g : I → F) :
    relDist f g = relDist (fun k => f (e.symm k)) (fun k => g (e.symm k)) := by
  rw [relDist, relDist, ← hammingDist_equiv e]
  rw [Fintype.card_congr e]

omit [CharP F 2] [Algebra (ZMod 2) F] in
/-- Closeness to an RS code is invariant under a domain-coordinate
equivalence that preserves the embedded evaluation point. -/
theorem close_reindex_iff {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq F]
    (e : I ≃ K) (domI : I ↪ F) (domK : K ↪ F)
    (hdom : ∀ i, domK (e i) = domI i)
    (d : ℕ) (delta : ℝ) (word : I → F) :
    close delta (reedSolomonCode domI d) word ↔
      close delta (reedSolomonCode domK d) (fun k => word (e.symm k)) := by
  constructor
  · rintro ⟨u, hu, hdist⟩
    obtain ⟨p, hp, hpu⟩ := mem_reedSolomonCode_iff.mp hu
    refine ⟨fun k => u (e.symm k), mem_reedSolomonCode_iff.mpr
      ⟨p, hp, fun k => ?_⟩, ?_⟩
    · rw [hpu, ← hdom (e.symm k)]
      simp
    · simpa [relDist_equiv e word u] using hdist
  · rintro ⟨u, hu, hdist⟩
    obtain ⟨p, hp, hpu⟩ := mem_reedSolomonCode_iff.mp hu
    refine ⟨fun i => u (e i), mem_reedSolomonCode_iff.mpr
      ⟨p, hp, fun i => ?_⟩, ?_⟩
    · rw [hpu, hdom]
    · have hd := relDist_equiv e word (fun i => u (e i))
      rw [hd]
      simpa using hdist

/-! ## Concrete additive tower data -/

/-- A finite additive FRI tower, with the input basis independent over GF(2). -/
structure AdditiveFriTower (F : Type*) [Field F] [CharP F 2]
    [Algebra (ZMod 2) F] (ell m : ℕ) where
  beta : ℕ → F
  offset : F
  independent : LinearIndependent (ZMod 2) (fun j : Fin ell => beta j)
  rounds_le : m ≤ ell

namespace AdditiveFriTower

variable {ell m : ℕ} (T : AdditiveFriTower F ell m)

/-- The additive evaluation embedding at every level.  Levels beyond `ell`
are singleton types and are included only so commitment families can retain
their conventional `Nat` index. -/
noncomputable def dom (n : ℕ) : AdditiveFriLevels ell n ↪ F := by
  classical
  by_cases hn : n ≤ ell
  · exact additiveTowerEmbedding ell T.beta T.offset T.independent n (ell - n)
      (by omega)
  · exact ⟨additiveTowerPoint ell T.beta T.offset n (ell - n),
      fun a b _ => by
        funext i
        have hi := i.isLt
        omega⟩

theorem level_succ_dim (T : AdditiveFriTower F ell m) (j : ℕ) (hj : j < m) :
    ell - j = (ell - (j + 1)) + 1 := by
  have := T.rounds_le
  omega

/-- Insert the low (`bit=0`) or high (`bit=1`) last coordinate of a fibre. -/
def liftBit (T : AdditiveFriTower F ell m)
    (j : ℕ) (hj : j < m) (bit : ZMod 2)
    (c : AdditiveFriLevels ell (j + 1)) : AdditiveFriLevels ell j :=
  fun i => (Fin.snoc c bit : Fin ((ell - (j + 1)) + 1) → ZMod 2)
    (Fin.cast (T.level_succ_dim j hj) i)

/-- The literal executable additive fold on indexed words. -/
noncomputable def fold (j : ℕ) (hj : j < m)
    (word : AdditiveFriLevels ell j → F) (alpha : F) :
    AdditiveFriLevels ell (j + 1) → F :=
  fun c =>
    let low := T.liftBit j hj 0 c
    let high := T.liftBit j hj 1 c
    let x := T.dom j low
    let pivot := additiveTowerPivot ell T.beta j
    word low + (x + alpha) * ((word low + word high) / pivot)

/-- The indexed low/high point is the corresponding canonical representative
from `AdditiveFriTower`. -/
theorem dom_liftBit (j : ℕ) (hj : j < m) (bit : ZMod 2)
    (c : AdditiveFriLevels ell (j + 1)) :
    T.dom j (T.liftBit j hj bit c) =
      additiveTowerPoint ell T.beta T.offset j ((ell - (j + 1)) + 1)
        (Fin.snoc c bit) := by
  classical
  have hjell : j ≤ ell := le_trans (Nat.le_of_lt hj) T.rounds_le
  rw [dom, dif_pos hjell]
  apply congrArg (additiveTowerMap ell T.beta j)
  unfold additiveTowerRawPoint
  congr 1
  unfold domainPoint
  apply Fintype.sum_equiv (finCongr (T.level_succ_dim j hj))
  intro i
  simp [liftBit]

/-- The two indexed source positions differ by the round pivot. -/
theorem dom_high_eq_low_add_pivot (j : ℕ) (hj : j < m)
    (c : AdditiveFriLevels ell (j + 1)) :
    T.dom j (T.liftBit j hj 1 c) =
      T.dom j (T.liftBit j hj 0 c) + additiveTowerPivot ell T.beta j := by
  rw [T.dom_liftBit, T.dom_liftBit]
  apply additiveTower_high_eq_low_add_pivot
  have := T.rounds_le
  omega

/-- The next-level point is the additive quotient of its low representative. -/
theorem dom_next_eq_foldMap_low (j : ℕ) (hj : j < m)
    (c : AdditiveFriLevels ell (j + 1)) :
    T.dom (j + 1) c = foldMap (additiveTowerPivot ell T.beta j)
      (T.dom j (T.liftBit j hj 0 c)) := by
  have hs : j + 1 ≤ ell := le_trans (Nat.succ_le_iff.mpr hj) T.rounds_le
  rw [dom, dif_pos hs, T.dom_liftBit]
  exact (additiveTower_foldMap_reindex ell T.beta T.offset j
    (ell - (j + 1)) c).symm

theorem liftBit_injective (j : ℕ) (hj : j < m) (bit : ZMod 2) :
    Function.Injective (T.liftBit j hj bit) := by
  intro c d hcd
  funext i
  let ii : Fin (ell - j) := Fin.cast (T.level_succ_dim j hj).symm i.castSucc
  have h := congrFun hcd ii
  simpa [liftBit, ii] using h

/-- Low representatives as an embedding into the field. -/
noncomputable def lowEmbedding (j : ℕ) (hj : j < m) :
    AdditiveFriLevels ell (j + 1) ↪ F :=
  ⟨fun c => T.dom j (T.liftBit j hj 0 c),
    T.dom j |>.injective.comp (T.liftBit_injective j hj 0)⟩

/-- The finite low-representative transversal. -/
noncomputable def transversal [DecidableEq F] (j : ℕ) (hj : j < m) : Finset F :=
  Finset.univ.image (T.lowEmbedding j hj)

theorem transversal_card [DecidableEq F] (j : ℕ) (hj : j < m) :
    (T.transversal j hj).card = 2 ^ (ell - (j + 1)) := by
  classical
  rw [transversal, Finset.card_image_of_injective _ (T.lowEmbedding j hj).injective,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- Additive level coordinates are equivalent to the transversal subtype. -/
noncomputable def transversalEquiv [DecidableEq F] (j : ℕ) (hj : j < m) :
    AdditiveFriLevels ell (j + 1) ≃ T.transversal j hj := by
  classical
  let f : AdditiveFriLevels ell (j + 1) → T.transversal j hj := fun c =>
    ⟨T.lowEmbedding j hj c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro c d h
    exact (T.lowEmbedding j hj).injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp x.property
    refine ⟨c, Subtype.ext ?_⟩
    exact hc

/-- The low set is a genuine additive transversal. -/
theorem transversal_property [DecidableEq F] (j : ℕ) (hj : j < m) :
    ∀ r ∈ T.transversal j hj,
      r + additiveTowerPivot ell T.beta j ∉ T.transversal j hj := by
  intro r hr
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
  intro hmem
  obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hmem
  have hpoints : T.dom j (T.liftBit j hj 1 c) =
      T.dom j (T.liftBit j hj 0 d) := by
    rw [T.dom_high_eq_low_add_pivot]
    exact hd.symm
  have hindices := (T.dom j).injective hpoints
  let last : Fin (ell - j) :=
    Fin.cast (T.level_succ_dim j hj).symm (Fin.last (ell - (j + 1)))
  have hlast := congrFun hindices last
  norm_num [liftBit, last] at hlast

/-- All current level points are exactly the two translates of the low
transversal. -/
theorem levelDomain_eq_pairDomain [DecidableEq F] (j : ℕ) (hj : j < m) :
    Finset.univ.image (T.dom j) =
      pairDomain (T.transversal j hj) (additiveTowerPivot ell T.beta j) := by
  ext x
  simp only [pairDomain, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_union, transversal]
  constructor
  · rintro ⟨a, rfl⟩
    let aa : Fin ((ell - (j + 1)) + 1) → ZMod 2 :=
      fun i => a (Fin.cast (T.level_succ_dim j hj).symm i)
    let c := Fin.init aa
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide)
        (aa (Fin.last _)) with hbit | hbit
    · left
      refine ⟨c, ?_⟩
      apply congrArg (T.dom j)
      funext i
      have haa := Fin.snoc_init_self aa
      have hv := congrFun haa (Fin.cast (T.level_succ_dim j hj) i)
      simpa [c, aa, hbit, liftBit] using hv
    · right
      refine ⟨T.dom j (T.liftBit j hj 0 c), ⟨c, rfl⟩, ?_⟩
      rw [← T.dom_high_eq_low_add_pivot j hj c]
      apply congrArg (T.dom j)
      funext i
      have haa := Fin.snoc_init_self aa
      have hv := congrFun haa (Fin.cast (T.level_succ_dim j hj) i)
      simpa [c, aa, hbit, liftBit] using hv
  · rintro (hlow | hhigh)
    · obtain ⟨c, hc⟩ := hlow
      exact ⟨T.liftBit j hj 0 c, hc⟩
    · obtain ⟨y, ⟨c, rfl⟩, rfl⟩ := hhigh
      exact ⟨T.liftBit j hj 1 c, (T.dom_high_eq_low_add_pivot j hj c)⟩

/-- Finite set of all embedded points at a level. -/
noncomputable def levelDomain [DecidableEq F] (n : ℕ) : Finset F :=
  Finset.univ.image (T.dom n)

/-- Coordinates are equivalent to the subtype of their level-domain set. -/
noncomputable def levelEquiv [DecidableEq F] (n : ℕ) :
    AdditiveFriLevels ell n ≃ T.levelDomain n := by
  classical
  let f : AdditiveFriLevels ell n → T.levelDomain n := fun c =>
    ⟨T.dom n c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro c d h
    exact (T.dom n).injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp x.property
    exact ⟨c, Subtype.ext hc⟩

@[simp] theorem levelEquiv_apply_val [DecidableEq F] (n : ℕ)
    (c : AdditiveFriLevels ell n) :
    ((T.levelEquiv n c : T.levelDomain n) : F) = T.dom n c := rfl

/-- Extend an indexed word arbitrarily off its finite evaluation domain. -/
noncomputable def extendWord [DecidableEq F] (n : ℕ)
    (word : AdditiveFriLevels ell n → F) : F → F :=
  fun x => if hx : x ∈ T.levelDomain n then
    word ((T.levelEquiv n).symm ⟨x, hx⟩) else 0

@[simp] theorem extendWord_dom [DecidableEq F] (n : ℕ)
    (word : AdditiveFriLevels ell n → F) (c : AdditiveFriLevels ell n) :
    T.extendWord n word (T.dom n c) = word c := by
  classical
  unfold extendWord
  have hx : T.dom n c ∈ T.levelDomain n := by
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
  rw [dif_pos hx]
  congr 1
  apply (T.levelEquiv n).injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem extendWord_levelEquiv [DecidableEq F] (n : ℕ)
    (word : AdditiveFriLevels ell n → F) (x : T.levelDomain n) :
    T.extendWord n word x = word ((T.levelEquiv n).symm x) := by
  let c := (T.levelEquiv n).symm x
  have hx : T.levelEquiv n c = x := (T.levelEquiv n).apply_symm_apply x
  calc
    T.extendWord n word x = T.extendWord n word (T.dom n c) := by
      rw [← T.levelEquiv_apply_val n c, hx]
    _ = word c := T.extendWord_dom n word c
    _ = word ((T.levelEquiv n).symm x) := rfl

/-- On a low representative, the field-indexed `friFold` of the extension is
literally the indexed additive fold. -/
theorem friFold_extendWord_low [DecidableEq F]
    (j : ℕ) (hj : j < m) (word : AdditiveFriLevels ell j → F)
    (alpha : F) (c : AdditiveFriLevels ell (j + 1)) :
    friFold (additiveTowerPivot ell T.beta j) alpha (T.extendWord j word)
        (T.dom j (T.liftBit j hj 0 c)) =
      T.fold j hj word alpha c := by
  rw [friFold, fold, T.extendWord_dom]
  rw [← T.dom_high_eq_low_add_pivot j hj c, T.extendWord_dom]

end AdditiveFriTower

/-! ## Additive round transitions -/

/-- Radius-scheduled distance preservation for one literal additive round. -/
def AdditiveFoldDistanceTransition {ell m : ℕ}
    [DecidableEq F]
    (T : AdditiveFriTower F ell m) (j : ℕ) (hj : j < m)
    (dbig dsmall : ℕ) (deltaIn deltaOut : ℝ) (b : ℕ) : Prop :=
  ∀ word : AdditiveFriLevels ell j → F,
    ¬ close deltaIn (reedSolomonCode (T.dom j) dbig) word →
    ∃ bad : Finset F, bad.card ≤ b ∧ ∀ alpha, alpha ∉ bad →
      ¬ close deltaOut (reedSolomonCode (T.dom (j + 1)) dsmall)
        (T.fold j hj word alpha)

/-- **The landed one-round additive proximity theorem supplies every tower
transition on its proved macroscopic UD band.** -/
theorem additiveFoldDistanceTransition_UD
    [Fintype F] [DecidableEq F]
    {ell m : ℕ} (T : AdditiveFriTower F ell m)
    (j : ℕ) (hj : j < m) (d : ℕ) (hd : 0 < d)
    (delta : ℝ) (hdelta0 : 0 < delta)
    (hdeltaB : delta < 1 -
      (2 + (d : ℝ) / ((T.transversal j hj).card : ℝ)) / 3) :
    AdditiveFoldDistanceTransition T j hj (2 * d) d delta delta
      (T.transversal j hj).card := by
  classical
  let R := T.transversal j hj
  let pivot := additiveTowerPivot ell T.beta j
  have hRn : R.Nonempty := by
    refine ⟨T.dom j (T.liftBit j hj 0 0), ?_⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hR : ∀ r ∈ R, r + pivot ∉ R := by
    simpa [R, pivot] using T.transversal_property j hj
  have hpivot : pivot ≠ 0 := by
    apply additiveTowerPivot_ne_zero ell T.beta T.offset T.independent j
      (ell - (j + 1))
    have := T.rounds_le
    omega
  intro word hfar
  let ext := T.extendWord j word
  have hDnonempty : (T.levelDomain j).Nonempty := by
    exact ⟨T.dom j 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  have hfarField : ¬ closeToDeg (pairDomain R pivot) (2 * d) delta ext := by
    intro hclose
    have hcloseD : close delta
        (reedSolomonCode (finsetDomain (T.levelDomain j)) (2 * d))
        (wordOn (T.levelDomain j) ext) :=
      (closeToDeg_iff_close (T.levelDomain j) hDnonempty
        (by omega) delta ext).mp (by
          have heq : T.levelDomain j = pairDomain R pivot := by
            simpa [AdditiveFriTower.levelDomain, R, pivot] using
              T.levelDomain_eq_pairDomain j hj
          rw [heq]
          exact hclose)
    have hreindexed : wordOn (T.levelDomain j) ext =
        fun x => word ((T.levelEquiv j).symm x) := by
      funext x
      exact T.extendWord_levelEquiv j word x
    rw [hreindexed] at hcloseD
    exact hfar ((close_reindex_iff (T.levelEquiv j) (T.dom j)
      (finsetDomain (T.levelDomain j)) (fun _ => rfl)
      (2 * d) delta word).mpr hcloseD)
  obtain ⟨bad, hbadCard, hbad⟩ := additiveFold_distance_UD
    hRn hpivot hR hd hdelta0 (by simpa [R] using hdeltaB) hfarField
  refine ⟨bad, hbadCard, fun alpha halpha hclose => ?_⟩
  apply hbad alpha halpha
  apply (foldedCloseToDeg_iff_close R hRn pivot hR hd delta
    (friFold pivot alpha ext)).mpr
  let e := T.transversalEquiv j hj
  have hdom : ∀ c, additiveImageDomain R pivot hR (e c) = T.dom (j + 1) c := by
    intro c
    change foldMap pivot (T.dom j (T.liftBit j hj 0 c)) = T.dom (j + 1) c
    exact (T.dom_next_eq_foldMap_low j hj c).symm
  have hcloseR := (close_reindex_iff e (T.dom (j + 1))
    (additiveImageDomain R pivot hR) hdom d delta
    (T.fold j hj word alpha)).mp hclose
  convert hcloseR using 1
  funext x
  obtain ⟨c, rfl⟩ := e.surjective x
  simp only [wordOn, Equiv.symm_apply_apply]
  have heval : ((e c : R) : F) = T.dom j (T.liftBit j hj 0 c) := by
    rfl
  rw [heval]
  change friFold pivot alpha ext (T.dom j (T.liftBit j hj 0 c)) =
    T.fold j hj word alpha c
  exact T.friFold_extendWord_low j hj word alpha c

/-! ## Opened additive fibres -/

/-- One authenticated additive low/high/next fibre. -/
def OpenedAdditiveFriQuery
    {ell m j : ℕ} {RootBig RootSmall OpBig OpSmall : Type*}
    (T : AdditiveFriTower F ell m) (hj : j < m)
    (Sbig : BindingCommitment RootBig F (AdditiveFriLevels ell j) OpBig)
    (Ssmall : BindingCommitment RootSmall F (AdditiveFriLevels ell (j + 1)) OpSmall)
    (rt : RootBig) (rt' : RootSmall) (alpha : F)
    (k : AdditiveFriLevels ell (j + 1))
    (o : FriQueryOpening F OpBig OpSmall) : Prop :=
  Sbig.verifyOpen rt (T.liftBit j hj 0 k) o.left o.leftPath ∧
  Sbig.verifyOpen rt (T.liftBit j hj 1 k) o.right o.rightPath ∧
  Ssmall.verifyOpen rt' k o.next o.nextPath ∧
  o.next = o.left + (T.dom j (T.liftBit j hj 0 k) + alpha) *
    ((o.left + o.right) / additiveTowerPivot ell T.beta j)

/-- Binding pins an accepted opened fibre to the literal additive fold. -/
theorem openedAdditiveFriQuery_pins
    {ell m j : ℕ} {RootBig RootSmall OpBig OpSmall : Type*}
    (T : AdditiveFriTower F ell m) (hj : j < m)
    (Sbig : BindingCommitment RootBig F (AdditiveFriLevels ell j) OpBig)
    (Ssmall : BindingCommitment RootSmall F (AdditiveFriLevels ell (j + 1)) OpSmall)
    {word : AdditiveFriLevels ell j → F}
    {word' : AdditiveFriLevels ell (j + 1) → F}
    {rt : RootBig} {rt' : RootSmall}
    (hrt : rt = Sbig.commit word) (hrt' : rt' = Ssmall.commit word')
    {alpha : F} {k : AdditiveFriLevels ell (j + 1)}
    {o : FriQueryOpening F OpBig OpSmall}
    (hopen : OpenedAdditiveFriQuery T hj Sbig Ssmall rt rt' alpha k o) :
    word' k = T.fold j hj word alpha k := by
  rcases hopen with ⟨hleft, hright, hnext, heq⟩
  have hl : o.left = word (T.liftBit j hj 0 k) :=
    Sbig.binding rt _ _ _ o.leftPath (Sbig.openAt word _)
      hleft (Sbig.toOpeningScheme.verifyOpen_of_commit_eq hrt _)
  have hr : o.right = word (T.liftBit j hj 1 k) :=
    Sbig.binding rt _ _ _ o.rightPath (Sbig.openAt word _)
      hright (Sbig.toOpeningScheme.verifyOpen_of_commit_eq hrt _)
  have hn : o.next = word' k :=
    Ssmall.binding rt' _ _ _ o.nextPath (Ssmall.openAt word' _)
      hnext (Ssmall.toOpeningScheme.verifyOpen_of_commit_eq hrt' _)
  rw [← hn, heq, hl, hr]
  rfl

/-- Acceptance of one batch of authenticated additive fibre equations. -/
def AdditiveFriRoundQueriesAccept
    {ell m j qCount : ℕ} {RootBig RootSmall OpBig OpSmall : Type*}
    (T : AdditiveFriTower F ell m) (hj : j < m)
    (Sbig : BindingCommitment RootBig F (AdditiveFriLevels ell j) OpBig)
    (Ssmall : BindingCommitment RootSmall F (AdditiveFriLevels ell (j + 1)) OpSmall)
    (rt : RootBig) (rt' : RootSmall) (alpha : F)
    (q : Fin qCount → AdditiveFriLevels ell (j + 1)) : Prop :=
  ∃ opening : ∀ _a : Fin qCount, FriQueryOpening F OpBig OpSmall,
    ∀ a, OpenedAdditiveFriQuery T hj Sbig Ssmall rt rt' alpha (q a) (opening a)

/-- Fixed-round additive query miss bound. -/
theorem additiveFriRound_query_miss_uniform
    [DecidableEq F]
    {ell m j qCount : ℕ} {RootBig RootSmall OpBig OpSmall : Type*}
    (T : AdditiveFriTower F ell m) (hj : j < m)
    (Sbig : BindingCommitment RootBig F (AdditiveFriLevels ell j) OpBig)
    (Ssmall : BindingCommitment RootSmall F (AdditiveFriLevels ell (j + 1)) OpSmall)
    {word : AdditiveFriLevels ell j → F}
    {word' : AdditiveFriLevels ell (j + 1) → F}
    {rt : RootBig} {rt' : RootSmall}
    (hrt : rt = Sbig.commit word) (hrt' : rt' = Ssmall.commit word')
    (alpha : F) {tau : ℝ}
    (hfar : tau ≤ relDist word' (T.fold j hj word alpha)) :
    uniformProb (Fin qCount → AdditiveFriLevels ell (j + 1))
      (AdditiveFriRoundQueriesAccept T hj Sbig Ssmall rt rt' alpha) ≤
        (1 - tau) ^ qCount := by
  classical
  let agree : Finset (Fin qCount → AdditiveFriLevels ell (j + 1)) :=
    Finset.univ.filter fun q => ∀ a, word' (q a) = T.fold j hj word alpha (q a)
  have hsub : (@Finset.univ (Fin qCount → AdditiveFriLevels ell (j + 1)) _).filter
      (AdditiveFriRoundQueriesAccept T hj Sbig Ssmall rt rt' alpha) ⊆ agree := by
    intro q hq
    obtain ⟨opening, hopen⟩ := (Finset.mem_filter.mp hq).2
    change q ∈ Finset.univ.filter fun q =>
      ∀ a, word' (q a) = T.fold j hj word alpha (q a)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ q, fun a =>
      openedAdditiveFriQuery_pins T hj Sbig Ssmall hrt hrt' (hopen a)⟩
  have hcard : (((@Finset.univ
      (Fin qCount → AdditiveFriLevels ell (j + 1)) _).filter
        (AdditiveFriRoundQueriesAccept T hj Sbig Ssmall rt rt' alpha)).card : ℝ)
      ≤ (agree.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hcount : (((@Finset.univ
      (Fin qCount → AdditiveFriLevels ell (j + 1)) _).filter
        (AdditiveFriRoundQueriesAccept T hj Sbig Ssmall rt rt' alpha)).card : ℝ)
      ≤ (1 - tau) ^ qCount *
        (Fintype.card (AdditiveFriLevels ell (j + 1)) : ℝ) ^ qCount := by
    refine le_trans hcard ?_
    simpa [agree] using column_sampling_bridge qCount hfar
  unfold uniformProb
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hden : (0 : ℝ) <
      (Fintype.card (AdditiveFriLevels ell (j + 1)) : ℝ) ^ qCount := by
    positivity
  rw [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [div_le_iff₀ hden]
  simpa using hcount

/-! ## Prefix-adaptive committed words -/

section Adaptive

variable {ell m : ℕ} {Root Op : ℕ → Type*}
variable [DecidableEq F]
variable (T : AdditiveFriTower F ell m)
variable (S : ∀ n, BindingCommitment (Root n) F (AdditiveFriLevels ell n) (Op n))

/-- Exact opened consistency for one adaptive additive round. -/
def AdditiveFriAdaptiveRoundQueriesAccept
    (st : FriAdaptiveTranscript S) (r : Fin m → F) (j : Fin m)
    {qCount : ℕ} (q : Fin qCount → AdditiveFriLevels ell (j + 1)) : Prop :=
  ∃ opening : ∀ _a : Fin qCount, FriQueryOpening F (Op j) (Op (j + 1)),
    ∀ a, OpenedAdditiveFriQuery T j.isLt (S j) (S (j + 1))
      (st.rootAt r j (Nat.le_of_lt j.isLt))
      (st.rootAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (r j) (q a) (opening a)

omit [DecidableEq F] in
/-- Binding pins every accepted adaptive query to the literal additive fold. -/
theorem additiveFriAdaptiveRoundQueries_pins
    (st : FriAdaptiveTranscript S) (r : Fin m → F) (j : Fin m)
    {qCount : ℕ} {q : Fin qCount → AdditiveFriLevels ell (j + 1)}
    (hopen : AdditiveFriAdaptiveRoundQueriesAccept T S st r j q) :
    ∀ a, st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt) (q a) =
      T.fold j j.isLt (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j) (q a) := by
  obtain ⟨opening, hopen⟩ := hopen
  intro a
  exact openedAdditiveFriQuery_pins T j.isLt (S j) (S (j + 1))
    (st.rootAt_eq_commit r j (Nat.le_of_lt j.isLt))
    (st.rootAt_eq_commit r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
    (hopen a)

/-- Runtime-shaped acceptance: every coherent path equation passes and the
final committed word is in the advertised final RS code. -/
def AdditiveFriAdaptiveCoherentAccepts
    (deg : ℕ → ℕ) (st : FriAdaptiveTranscript S)
    (qCount : ℕ) (r : Fin m → F)
    (seed : Fin qCount → PowerTwoFriLevels ell 1) : Prop :=
  (∀ j, AdditiveFriAdaptiveRoundQueriesAccept T S st r j
    (additiveCoherentRound T.rounds_le j seed)) ∧
  st.wordAt r m le_rfl ∈ reedSolomonCode (T.dom m) (deg m)

/-! ## Radius-scheduled earliest deviation -/

/-- Additive adaptive first-crossing cover. -/
theorem additiveFriAdaptive_earliestDeviation_cover
    (deg : ℕ → ℕ) (st : FriAdaptiveTranscript S)
    (radius : ℕ → ℝ) (foldRadius : Fin m → ℝ) (tau : ℝ) {b : ℕ}
    (hfinal : 0 ≤ radius m)
    (hgap : ∀ j : Fin m, radius (j + 1) + tau ≤ foldRadius j)
    (hfold : ∀ j : Fin m,
      AdditiveFoldDistanceTransition T j j.isLt (deg j) (deg (j + 1))
        (radius j) (foldRadius j) b)
    (hfar0 : ¬ close (radius 0) (reedSolomonCode (T.dom 0) (deg 0))
      (st.word 0 (fun i => i.elim0))) :
    ∃ bad : (Fin m → F) → Fin m → Finset F,
      (∀ (j : Fin m) (r r' : Fin m → F),
        (∀ i : Fin m, (i : ℕ) < (j : ℕ) → r i = r' i) →
          bad r j = bad r' j) ∧
      (∀ r j, (bad r j).card ≤ b) ∧
      ∀ r : Fin m → F,
        st.wordAt r m le_rfl ∈ reedSolomonCode (T.dom m) (deg m) →
          (∃ j, r j ∈ bad r j) ∨
          ∃ j : Fin m, tau ≤ relDist
            (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
            (T.fold j j.isLt
              (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j)) := by
  classical
  have hbadAt : ∀ (j : ℕ) (hj : j < m)
      (word : AdditiveFriLevels ell j → F),
      ∃ bad : Finset F, bad.card ≤ b ∧
        (¬ close (radius j) (reedSolomonCode (T.dom j) (deg j)) word →
          ∀ alpha, alpha ∉ bad →
            ¬ close (foldRadius ⟨j, hj⟩)
              (reedSolomonCode (T.dom (j + 1)) (deg (j + 1)))
              (T.fold j hj word alpha)) := by
    intro j hj word
    by_cases hw : ¬ close (radius j) (reedSolomonCode (T.dom j) (deg j)) word
    · obtain ⟨bad, hcard, hspec⟩ := hfold ⟨j, hj⟩ word hw
      exact ⟨bad, hcard, fun _ => hspec⟩
    · exact ⟨∅, Nat.zero_le b, fun hw' => absurd (not_not.mp hw) hw'⟩
  choose badAt hbadCard hbadSpec using hbadAt
  let bad : (Fin m → F) → Fin m → Finset F := fun r j =>
    badAt j j.isLt (st.wordAt r j (Nat.le_of_lt j.isLt))
  refine ⟨bad, ?_, ?_, ?_⟩
  · intro j r r' hagree
    unfold bad
    congr 1
    exact st.wordAt_congr hagree
  · intro r j
    exact hbadCard j j.isLt _
  · intro r hmem
    by_contra hcover
    push Not at hcover
    obtain ⟨hnoBad, hnoDev⟩ := hcover
    have hfarAll : ∀ (n : ℕ) (hn : n ≤ m),
        ¬ close (radius n) (reedSolomonCode (T.dom n) (deg n))
          (st.wordAt r n hn) := by
      intro n
      induction n with
      | zero =>
          intro hn
          have hp : friPrefix r 0 hn = (fun i => i.elim0) := Subsingleton.elim _ _
          rw [FriAdaptiveTranscript.wordAt, hp]
          exact hfar0
      | succ j ih =>
          intro hn
          have hj : j < m := hn
          let src := st.wordAt r j (Nat.le_of_succ_le hn)
          let folded := T.fold j hj src (r ⟨j, hj⟩)
          let next := st.wordAt r (j + 1) hn
          have hsrc : ¬ close (radius j)
              (reedSolomonCode (T.dom j) (deg j)) src :=
            ih (Nat.le_of_succ_le hn)
          have halpha : r ⟨j, hj⟩ ∉ badAt j hj src := hnoBad ⟨j, hj⟩
          have hfoldFar : ¬ close (foldRadius ⟨j, hj⟩)
              (reedSolomonCode (T.dom (j + 1)) (deg (j + 1))) folded :=
            hbadSpec j hj src hsrc _ halpha
          have hdist : relDist next folded < tau := by
            simpa [next, folded, src] using hnoDev ⟨j, hj⟩
          intro hnextClose
          obtain ⟨c, hc, hnextc⟩ := hnextClose
          apply hfoldFar
          refine ⟨c, hc, ?_⟩
          letI : Nonempty (AdditiveFriLevels ell (j + 1)) := ⟨0⟩
          have htri := relDist_triangle folded next c
          have hcomm : relDist folded next = relDist next folded := relDist_comm _ _
          exact (calc
            relDist folded c ≤ relDist folded next + relDist next c := htri
            _ = relDist next folded + relDist next c := by rw [hcomm]
            _ < tau + radius (j + 1) := add_lt_add_of_lt_of_le hdist hnextc
            _ = radius (j + 1) + tau := by ring
            _ ≤ foldRadius ⟨j, hj⟩ := hgap ⟨j, hj⟩).le
    exact hfarAll m le_rfl (close_of_mem hmem hfinal)

end Adaptive

/-! ## Coherent-path sampled soundness -/

section CoherentSoundness

variable {ell m : ℕ} {Root Op : ℕ → Type*}
variable [Fintype F] [DecidableEq F]
variable (T : AdditiveFriTower F ell m)
variable (S : ∀ n, BindingCommitment (Root n) F (AdditiveFriLevels ell n) (Op n))

omit [Fintype F] in
/-- A fixed transcript with one far additive transition passes all coherent
query paths with probability at most `(1-tau)^qCount`. -/
theorem additiveFriAdaptive_coherent_query_miss
    (st : FriAdaptiveTranscript S) (r : Fin m → F) (qCount : ℕ) {tau : ℝ}
    (hfar : ∃ j : Fin m, tau ≤ relDist
      (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (T.fold j j.isLt
        (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j))) :
    uniformProb (Fin qCount → PowerTwoFriLevels ell 1)
      (fun seed => ∀ j, AdditiveFriAdaptiveRoundQueriesAccept T S st r j
        (additiveCoherentRound T.rounds_le j seed)) ≤
      (1 - tau) ^ qCount := by
  obtain ⟨j, hfarj⟩ := hfar
  refine le_trans (uniformProb_mono fun seed hseed => hseed j) ?_
  refine le_trans (additiveCoherentRound_uniform T.rounds_le j
    (AdditiveFriAdaptiveRoundQueriesAccept T S st r j)).le ?_
  change uniformProb (Fin qCount → AdditiveFriLevels ell (j + 1))
    (AdditiveFriRoundQueriesAccept T j.isLt (S j) (S (j + 1))
      (st.rootAt r j (Nat.le_of_lt j.isLt))
      (st.rootAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt)) (r j)) ≤
      (1 - tau) ^ qCount
  exact additiveFriRound_query_miss_uniform T j.isLt (S j) (S (j + 1))
    (st.rootAt_eq_commit r j (Nat.le_of_lt j.isLt))
    (st.rootAt_eq_commit r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
    (r j) hfarj

/-- **Adaptive coherent sampled additive-FRI soundness.**  The challenge and
query terms compose as

`m*b/|F| + (1-tau)^qCount`.

The theorem is ideal-binding and interactive.  Merkle collision resistance
and Fiat--Shamir/XOF analysis are separate cryptographic assumptions. -/
theorem additiveFriAdaptive_coherent_sampled_sound
    (deg : ℕ → ℕ) (st : FriAdaptiveTranscript S)
    (radius : ℕ → ℝ) (foldRadius : Fin m → ℝ)
    (qCount : ℕ) {tau : ℝ} {b : ℕ}
    (htau : tau ≤ 1)
    (hfinal : 0 ≤ radius m)
    (hgap : ∀ j : Fin m, radius (j + 1) + tau ≤ foldRadius j)
    (hfold : ∀ j : Fin m,
      AdditiveFoldDistanceTransition T j j.isLt (deg j) (deg (j + 1))
        (radius j) (foldRadius j) b)
    (hfar0 : ¬ close (radius 0) (reedSolomonCode (T.dom 0) (deg 0))
      (st.word 0 (fun i => i.elim0))) :
    uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => AdditiveFriAdaptiveCoherentAccepts T S deg st qCount x.1 x.2) ≤
      (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) +
        (1 - tau) ^ qCount := by
  classical
  obtain ⟨bad, hmeas, hcard, hcover⟩ :=
    additiveFriAdaptive_earliestDeviation_cover T S deg st radius foldRadius tau
      hfinal hgap hfold hfar0
  let badHit : (Fin m → F) → Prop := fun r => ∃ j, r j ∈ bad r j
  let eps : ℝ := (1 - tau) ^ qCount
  have heps : 0 ≤ eps := pow_nonneg (sub_nonneg.mpr htau) _
  have hsplit : uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => AdditiveFriAdaptiveCoherentAccepts T S deg st qCount x.1 x.2) ≤
      uniformProb ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
        (fun x => badHit x.1) +
      uniformProb ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
        (fun x => ¬ badHit x.1 ∧
          AdditiveFriAdaptiveCoherentAccepts T S deg st qCount x.1 x.2) := by
    refine le_trans (uniformProb_mono fun x hx => ?_) (uniformProb_or_le _ _)
    by_cases hb : badHit x.1
    · exact Or.inl hb
    · exact Or.inr ⟨hb, hx⟩
  have hbadPr : uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => badHit x.1) ≤
      (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
    let e := Equiv.prodComm (Fin m → F)
      (Fin qCount → PowerTwoFriLevels ell 1)
    calc
      uniformProb ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
          (fun x => badHit x.1) =
        uniformProb ((Fin qCount → PowerTwoFriLevels ell 1) × (Fin m → F))
          (fun x => badHit x.2) := by
            simpa [e] using uniformProb_equiv e (fun x => badHit x.2)
      _ ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
        apply uniformProb_prod_le
        · positivity
        · intro seed
          exact friAdaptive_badChallenge_pr_le bad hmeas hcard
  have hqueryPr : uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => ¬ badHit x.1 ∧
        AdditiveFriAdaptiveCoherentAccepts T S deg st qCount x.1 x.2) ≤ eps := by
    apply uniformProb_prod_le heps
    intro r
    by_cases hb : badHit r
    · rw [uniformProb_false]
      · exact heps
      · intro seed hseed
        exact hseed.1 hb
    · by_cases hmem : st.wordAt r m le_rfl ∈
          reedSolomonCode (T.dom m) (deg m)
      · have hdev : ∃ j : Fin m, tau ≤ relDist
            (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
            (T.fold j j.isLt
              (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j)) := by
          rcases hcover r hmem with hbad | hdev
          · exact False.elim (hb hbad)
          · exact hdev
        refine le_trans (uniformProb_mono fun seed hseed => hseed.2.1) ?_
        exact additiveFriAdaptive_coherent_query_miss T S st r qCount hdev
      · rw [uniformProb_false]
        · exact heps
        · intro seed hseed
          exact hmem hseed.2.2
  exact le_trans hsplit (add_le_add hbadPr hqueryPr)

/-- **Runtime headline on the proved additive UD regime.**  A decreasing
radius schedule pays the exact adaptive challenge term plus the coherent
query miss term.  Each round transition is instantiated from
`additiveFold_distance_UD`; the common challenge bound is the initial pair
count `2^(ell-1)`.

This is why a radius schedule is essential: the literal fold preserves the
round-`j` radius, while allowing a `tau`-far recommitment requires
`radius (j+1) + tau <= radius j`. -/
theorem additiveFriAdaptive_coherent_sampled_sound_UD
    (deg : ℕ → ℕ) (st : FriAdaptiveTranscript S)
    (radius : ℕ → ℝ) (qCount : ℕ) {tau : ℝ}
    (htau : tau ≤ 1)
    (hfinal : 0 ≤ radius m)
    (hshrink : ∀ j : Fin m, radius (j + 1) + tau ≤ radius j)
    (hdeg : ∀ j : Fin m, deg j = 2 * deg (j + 1))
    (hdegpos : ∀ j : Fin m, 0 < deg (j + 1))
    (hradius : ∀ j : Fin m, 0 < radius j)
    (hband : ∀ j : Fin m, radius j < 1 -
      (2 + (deg (j + 1) : ℝ) /
        ((T.transversal j j.isLt).card : ℝ)) / 3)
    (hfar0 : ¬ close (radius 0) (reedSolomonCode (T.dom 0) (deg 0))
      (st.word 0 (fun i => i.elim0))) :
    uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => AdditiveFriAdaptiveCoherentAccepts T S deg st qCount x.1 x.2) ≤
      (m : ℝ) * (2 ^ (ell - 1) : ℕ) / (Fintype.card F : ℝ) +
        (1 - tau) ^ qCount := by
  apply additiveFriAdaptive_coherent_sampled_sound T S deg st radius
    (fun j => radius j) qCount htau hfinal hshrink (b := 2 ^ (ell - 1)) ?_ hfar0
  intro j
  have htransition := additiveFoldDistanceTransition_UD T j j.isLt
    (deg (j + 1)) (hdegpos j) (radius j) (hradius j) (hband j)
  intro word hfar
  have hfar' : ¬ close (radius j)
      (reedSolomonCode (T.dom j) (2 * deg (j + 1))) word := by
    simpa [hdeg j] using hfar
  obtain ⟨bad, hcard, hspec⟩ := htransition word hfar'
  refine ⟨bad, ?_, hspec⟩
  refine le_trans hcard ?_
  rw [T.transversal_card j j.isLt]
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  have hmpos : 0 < m := Nat.zero_lt_of_lt j.isLt
  have hjell : (j : ℕ) + 1 ≤ ell :=
    le_trans (Nat.succ_le_iff.mpr j.isLt) T.rounds_le
  omega

end CoherentSoundness

/-- info: 'Minidregg.Selvage.openedAdditiveFriQuery_pins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms openedAdditiveFriQuery_pins
/-- info: 'Minidregg.Selvage.additiveFriRound_query_miss_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveFriRound_query_miss_uniform
/-- info: 'Minidregg.Selvage.additiveFriAdaptive_earliestDeviation_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveFriAdaptive_earliestDeviation_cover
/-- info: 'Minidregg.Selvage.additiveFriAdaptive_coherent_query_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveFriAdaptive_coherent_query_miss
/-- info: 'Minidregg.Selvage.additiveFriAdaptive_coherent_sampled_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveFriAdaptive_coherent_sampled_sound
/-- info: 'Minidregg.Selvage.additiveFoldDistanceTransition_UD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveFoldDistanceTransition_UD
/-- info: 'Minidregg.Selvage.additiveFriAdaptive_coherent_sampled_sound_UD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveFriAdaptive_coherent_sampled_sound_UD

end Minidregg.Selvage
