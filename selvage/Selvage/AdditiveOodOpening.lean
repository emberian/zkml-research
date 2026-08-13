/-
# Selvage.AdditiveOodOpening -- additive OOD quotient and evaluation channel

For an affine additive evaluation domain `a + W_k`, an out-of-domain opening
claim `y = p(z)` is reduced to the degree-`< d-1` quotient

  `Q(X) = (p(X) - y) / (X - z)`.

This file proves the reduction exactly: the quotient has the advertised
degree, reconstructs `p` as `y + (X-z)Q`, and its pointwise evaluations are
the runtime evaluation channel on every additive-domain coordinate.  The
converse retirement theorem proves that ANY degree-`< d-1` polynomial passing
that channel on a size-at-least-`d` additive domain forces `y = p(z)`.

The commitment layer then authenticates the two opened symbols and proves the
fixed-batch false-opening bound by binding plus exact column sampling,
conditional only on exact Reed--Solomon membership of the quotient word.  A
sampled additive-FRI proof of that membership is still separate: Selvage's current
coherent global theorem consumes the multiplicative `FoldingTower`, whereas
`AdditiveProximity` currently exposes additive distance preservation one round
at a time.  No CR/Merkle or Fiat--Shamir claim is hidden here.
-/
import Selvage.AdditiveProximity
import Selvage.HalfThresholdFriCoherent
import Selvage.OutOfDomain

namespace Minidregg.Selvage

open Polynomial
open Minidregg.Theory

variable {F : Type*} [Field F]

/-! ## Affine additive-domain representation -/

/-- Coordinate `c` of the affine additive domain `offset + W_k`. -/
def affineAdditivePoint [Algebra (ZMod 2) F]
    (offset : F) (beta : ℕ → F) (k : ℕ) (c : Fin k → ZMod 2) : F :=
  offset + domainPoint beta k c

/-- Independent additive generators make affine-domain coordinates distinct. -/
theorem affineAdditivePoint_injective [Algebra (ZMod 2) F]
    {offset : F} {beta : ℕ → F} {k : ℕ}
    (hbeta : LinearIndependent (ZMod 2) fun j : Fin k => beta j) :
    Function.Injective (affineAdditivePoint offset beta k) := by
  intro c c' h
  apply domainPoint_injective hbeta
  exact add_left_cancel h

/-- The affine additive domain as the embedding expected by Selvage's
Reed--Solomon and distance APIs. -/
def affineAdditiveDomain [Algebra (ZMod 2) F]
    (offset : F) (beta : ℕ → F) (k : ℕ)
    (hbeta : LinearIndependent (ZMod 2) fun j : Fin k => beta j) :
    (Fin k → ZMod 2) ↪ F :=
  ⟨affineAdditivePoint offset beta k, affineAdditivePoint_injective hbeta⟩

/-! ## The exact OOD quotient -/

/-- Synthetic-division quotient attached to the claimed opening `(z,y)`. -/
noncomputable def additiveOodQuotient (p : F[X]) (z y : F) : F[X] :=
  (p - C y) /ₘ (X - C z)

/-- If `y = p(z)`, synthetic division reconstructs the numerator exactly. -/
theorem additiveOodQuotient_mul (p : F[X]) (z y : F)
    (hy : p.eval z = y) :
    (X - C z) * additiveOodQuotient p z y = p - C y := by
  apply (mul_divByMonic_eq_iff_isRoot).2
  simp [Polynomial.IsRoot, hy]

/-- Polynomial reconstruction form of the evaluation channel. -/
theorem additiveOodQuotient_reconstruct (p : F[X]) (z y : F)
    (hy : p.eval z = y) :
    C y + (X - C z) * additiveOodQuotient p z y = p := by
  rw [additiveOodQuotient_mul p z y hy]
  abel

/-- Dividing a degree-`< d` polynomial by `X-z` gives degree `< d-1`.
The `1 < d` guard is the natural nondegenerate PCS window and handles the
zero quotient in `natDegree` convention. -/
theorem additiveOodQuotient_natDegree_lt {p : F[X]} {z y : F} {d : ℕ}
    (hd : 1 < d) (hp : p.natDegree < d) :
    (additiveOodQuotient p z y).natDegree < d - 1 := by
  rw [additiveOodQuotient, natDegree_divByMonic _ (monic_X_sub_C z),
    natDegree_X_sub_C]
  have hnum : (p - C y).natDegree < d := by
    calc
      (p - C y).natDegree ≤ max p.natDegree (C y).natDegree :=
        natDegree_sub_le _ _
      _ ≤ max p.natDegree 0 :=
        max_le_max le_rfl (natDegree_C y).le
      _ = p.natDegree := max_eq_left (Nat.zero_le _)
      _ < d := hp
  omega

/-- The same degree drop in Selvage's `degree < d` Reed--Solomon convention. -/
theorem additiveOodQuotient_degree_lt {p : F[X]} {z y : F} {d : ℕ}
    (hd : 1 < d) (hp : p.natDegree < d) :
    (additiveOodQuotient p z y).degree < ((d - 1 : ℕ) : WithBot ℕ) := by
  exact lt_of_le_of_lt degree_le_natDegree (by
    exact_mod_cast additiveOodQuotient_natDegree_lt hd hp)

/-- Pointwise reconstruction at every field element. -/
theorem additiveOodQuotient_eval (p : F[X]) (z y : F)
    (hy : p.eval z = y) (x : F) :
    p.eval x = y + (x - z) * (additiveOodQuotient p z y).eval x := by
  have h := congrArg (Polynomial.eval x)
    (additiveOodQuotient_reconstruct p z y hy)
  simpa [eval_add, eval_mul, eval_sub] using h.symm

/-- Outside the affine additive domain the denominator is nonzero, so the
runtime quotient channel is literally `(p(x)-y)/(x-z)`. -/
theorem additiveOodQuotient_eval_div [Algebra (ZMod 2) F]
    (offset : F) (beta : ℕ → F) (k : ℕ)
    (p : F[X]) (z y : F) (hy : p.eval z = y)
    (hz : z ∉ Set.range (affineAdditivePoint offset beta k))
    (c : Fin k → ZMod 2) :
    (additiveOodQuotient p z y).eval (affineAdditivePoint offset beta k c) =
      (p.eval (affineAdditivePoint offset beta k c) - y) /
        (affineAdditivePoint offset beta k c - z) := by
  let x := affineAdditivePoint offset beta k c
  have hxz : x ≠ z := by
    intro h
    exact hz ⟨c, h⟩
  have hchan := additiveOodQuotient_eval p z y hy x
  rw [eq_div_iff (sub_ne_zero.mpr hxz)]
  calc
    (additiveOodQuotient p z y).eval x * (x - z) =
        (x - z) * (additiveOodQuotient p z y).eval x := mul_comm _ _
    _ = p.eval x - y := by rw [hchan]; ring

/-- **Additive evaluation-channel theorem.**  The honest quotient is
degree-`< d-1` and its evaluations on `a+W_k` are exactly the OOD quotient
channel read by the prover/verifier. -/
theorem additiveOodQuotient_channel [Algebra (ZMod 2) F]
    (offset : F) (beta : ℕ → F) (k d : ℕ)
    (p : F[X]) (z y : F) (hd : 1 < d) (hp : p.natDegree < d)
    (hy : p.eval z = y)
    (hz : z ∉ Set.range (affineAdditivePoint offset beta k)) :
    (additiveOodQuotient p z y).natDegree < d - 1 ∧
      ∀ c : Fin k → ZMod 2,
        (additiveOodQuotient p z y).eval
            (affineAdditivePoint offset beta k c) =
          (p.eval (affineAdditivePoint offset beta k c) - y) /
            (affineAdditivePoint offset beta k c - z) := by
  exact ⟨additiveOodQuotient_natDegree_lt hd hp,
    additiveOodQuotient_eval_div offset beta k p z y hy hz⟩

/-! ## Converse: retire the evaluation channel -/

/-- The polynomial represented by an alleged quotient channel. -/
noncomputable def additiveOodReconstruction (q : F[X]) (z y : F) : F[X] :=
  C y + (X - C z) * q

@[simp] theorem additiveOodReconstruction_eval (q : F[X]) (z y x : F) :
    (additiveOodReconstruction q z y).eval x = y + (x - z) * q.eval x := by
  simp [additiveOodReconstruction, eval_add, eval_mul, eval_sub]

/-- The reconstructed polynomial remains degree-`< d` when `q` is
degree-`< d-1`. -/
theorem additiveOodReconstruction_natDegree_lt {q : F[X]} {z y : F} {d : ℕ}
    (hd : 1 < d) (hq : q.natDegree < d - 1) :
    (additiveOodReconstruction q z y).natDegree < d := by
  have hlin : (X - C z).natDegree ≤ 1 := by
    rw [natDegree_X_sub_C]
  have hmul : ((X - C z) * q).natDegree < d := by
    calc
      ((X - C z) * q).natDegree ≤ (X - C z).natDegree + q.natDegree :=
        natDegree_mul_le
      _ ≤ 1 + q.natDegree := Nat.add_le_add_right hlin _
      _ < d := by omega
  calc
    (additiveOodReconstruction q z y).natDegree ≤
        max (C y).natDegree (((X - C z) * q).natDegree) :=
      natDegree_add_le _ _
    _ ≤ max 0 (((X - C z) * q).natDegree) :=
      max_le_max (natDegree_C y).le le_rfl
    _ = ((X - C z) * q).natDegree := max_eq_right (Nat.zero_le _)
    _ < d := hmul

/-- **Evaluation-channel retirement.**  Let `p` have degree `< d`, let an
alleged quotient `q` have degree `< d-1`, and suppose the channel equation
holds at every point of a size-`2^k` affine additive domain with `d ≤ 2^k`.
Then the claimed OOD value is forced: `y = p(z)`.

The proof is interpolation, not a protocol assumption: the degree-`< d`
residual vanishes at `2^k ≥ d` distinct affine-domain points, hence is the
zero polynomial; evaluating it at `z` retires the channel. -/
theorem additiveOodEvaluationChannel_retires [Algebra (ZMod 2) F]
    {offset : F} {beta : ℕ → F} {k d : ℕ}
    (hbeta : LinearIndependent (ZMod 2) fun j : Fin k => beta j)
    (hd : 1 < d) (hdk : d ≤ 2 ^ k)
    {p q : F[X]} {z y : F}
    (hp : p.natDegree < d) (hq : q.natDegree < d - 1)
    (hchannel : ∀ c : Fin k → ZMod 2,
      p.eval (affineAdditivePoint offset beta k c) =
        y + (affineAdditivePoint offset beta k c - z) *
          q.eval (affineAdditivePoint offset beta k c)) :
    p.eval z = y := by
  let residual := p - additiveOodReconstruction q z y
  have hresdeg : residual.natDegree < d := by
    calc
      residual.natDegree ≤
          max p.natDegree (additiveOodReconstruction q z y).natDegree :=
        natDegree_sub_le _ _
      _ < d := max_lt hp (additiveOodReconstruction_natDegree_lt hd hq)
  have hcard : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hzero : residual = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero residual
      (f := affineAdditivePoint offset beta k)
      (affineAdditivePoint_injective hbeta)
    · intro c
      simp only [residual, eval_sub, additiveOodReconstruction_eval,
        hchannel c, sub_self]
    · rw [hcard]
      exact lt_of_lt_of_le hresdeg hdk
  have hzres := congrArg (Polynomial.eval z) hzero
  apply sub_eq_zero.mp
  simpa [residual, additiveOodReconstruction_eval] using hzres

/-! ## Reed--Solomon and committed sampled-channel bridge -/

section ReedSolomonBridge

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq F]

omit [Nonempty ι] in
/-- Exact low degree of the alleged quotient plus the pointwise channel imply
both low degree of the reconstructed main word and the claimed OOD value.
This is the whole-word seam that a future sampled additive-FRI transcript must
supply for the quotient root. -/
theorem mem_reedSolomonCode_and_oodEval_of_additiveOodChannel
    (dom : ι ↪ F) {d : ℕ} (hd : 1 < d) (hdcard : d ≤ Fintype.card ι)
    {mainWord quotientWord : ι → F} {z y : F}
    (hquotient : quotientWord ∈ reedSolomonCode dom (d - 1))
    (hchannel : ∀ i,
      mainWord i = y + (dom i - z) * quotientWord i) :
    mainWord ∈ reedSolomonCode dom d ∧ oodEval dom d mainWord z = y := by
  obtain ⟨q, hqdeg, hqword⟩ := mem_reedSolomonCode_iff.mp hquotient
  have hqnat : q.natDegree < d - 1 :=
    (natDegree_lt_iff_degree_lt (by omega)).mpr hqdeg
  have hreconNat : (additiveOodReconstruction q z y).natDegree < d :=
    additiveOodReconstruction_natDegree_lt hd hqnat
  have hreconDeg : (additiveOodReconstruction q z y).degree <
      (d : WithBot ℕ) :=
    (natDegree_lt_iff_degree_lt (by omega)).mp hreconNat
  have hmain : ∀ i,
      mainWord i = (additiveOodReconstruction q z y).eval (dom i) := by
    intro i
    rw [additiveOodReconstruction_eval, ← hqword i]
    exact hchannel i
  have hmem : mainWord ∈ reedSolomonCode dom d :=
    mem_reedSolomonCode_iff.mpr ⟨_, hreconDeg, hmain⟩
  refine ⟨hmem, ?_⟩
  rw [oodEval_eq_of_witness dom hdcard hreconDeg hmain z]
  simp

end ReedSolomonBridge

/-- Values and authentication paths opened for one OOD quotient-channel
check at a common domain coordinate. -/
structure AdditiveOodQueryOpening (F OpMain OpQuotient : Type*) where
  main : F
  quotient : F
  mainPath : OpMain
  quotientPath : OpQuotient

section CommittedQueries

variable {ι RootMain RootQuotient OpMain OpQuotient : Type*}
variable [Fintype ι] [Nonempty ι] [DecidableEq F]

/-- One authenticated, division-free OOD quotient equation. -/
def OpenedAdditiveOodQuery
    (Smain : BindingCommitment RootMain F ι OpMain)
    (Squotient : BindingCommitment RootQuotient F ι OpQuotient)
    (dom : ι ↪ F) (rtMain : RootMain) (rtQuotient : RootQuotient)
    (z y : F) (i : ι)
    (o : AdditiveOodQueryOpening F OpMain OpQuotient) : Prop :=
  Smain.verifyOpen rtMain i o.main o.mainPath ∧
  Squotient.verifyOpen rtQuotient i o.quotient o.quotientPath ∧
  o.main = y + (dom i - z) * o.quotient

omit [Fintype ι] [Nonempty ι] [DecidableEq F] in
/-- Binding pins an adversarial accepted opening to the two committed words. -/
theorem openedAdditiveOodQuery_pins
    (Smain : BindingCommitment RootMain F ι OpMain)
    (Squotient : BindingCommitment RootQuotient F ι OpQuotient)
    (dom : ι ↪ F)
    {mainWord quotientWord : ι → F}
    {rtMain : RootMain} {rtQuotient : RootQuotient}
    (hrtMain : rtMain = Smain.commit mainWord)
    (hrtQuotient : rtQuotient = Squotient.commit quotientWord)
    {z y : F} {i : ι} {o : AdditiveOodQueryOpening F OpMain OpQuotient}
    (hopen : OpenedAdditiveOodQuery Smain Squotient dom
      rtMain rtQuotient z y i o) :
    mainWord i = y + (dom i - z) * quotientWord i := by
  rcases hopen with ⟨hmain, hquotient, hrelation⟩
  have hmainHonest :=
    Smain.toOpeningScheme.verifyOpen_of_commit_eq hrtMain i
  have hquotientHonest :=
    Squotient.toOpeningScheme.verifyOpen_of_commit_eq hrtQuotient i
  have hm : o.main = mainWord i :=
    Smain.binding rtMain i o.main (mainWord i) o.mainPath
      (Smain.openAt mainWord i) hmain hmainHonest
  have hq : o.quotient = quotientWord i :=
    Squotient.binding rtQuotient i o.quotient (quotientWord i)
      o.quotientPath (Squotient.openAt quotientWord i)
      hquotient hquotientHonest
  simpa [hm, hq] using hrelation

/-- Acceptance of independently sampled authenticated channel coordinates,
with opening values and paths existential/adversarial. -/
def AdditiveOodQueriesAccept
    (Smain : BindingCommitment RootMain F ι OpMain)
    (Squotient : BindingCommitment RootQuotient F ι OpQuotient)
    (dom : ι ↪ F) (rtMain : RootMain) (rtQuotient : RootQuotient)
    (z y : F) {qCount : ℕ} (schedule : Fin qCount → ι) : Prop :=
  ∃ opening : ∀ _a : Fin qCount,
      AdditiveOodQueryOpening F OpMain OpQuotient,
    ∀ a, OpenedAdditiveOodQuery Smain Squotient dom rtMain rtQuotient
      z y (schedule a) (opening a)

/-- Finite event of accepted OOD-channel query schedules. -/
noncomputable def additiveOodQueryAcceptSet
    (Smain : BindingCommitment RootMain F ι OpMain)
    (Squotient : BindingCommitment RootQuotient F ι OpQuotient)
    (dom : ι ↪ F) (rtMain : RootMain) (rtQuotient : RootQuotient)
    (z y : F) (qCount : ℕ) : Finset (Fin qCount → ι) :=
  @Finset.filter (Fin qCount → ι)
    (AdditiveOodQueriesAccept Smain Squotient dom rtMain rtQuotient z y)
    (Classical.decPred _) Finset.univ

/-- Binding plus column sampling: if the committed words violate the OOD
channel on a `tau` fraction, all authenticated checks pass with probability
at most `(1-tau)^qCount`. -/
theorem additiveOod_query_miss_pr
    (Smain : BindingCommitment RootMain F ι OpMain)
    (Squotient : BindingCommitment RootQuotient F ι OpQuotient)
    (dom : ι ↪ F)
    {mainWord quotientWord : ι → F}
    {rtMain : RootMain} {rtQuotient : RootQuotient}
    (hrtMain : rtMain = Smain.commit mainWord)
    (hrtQuotient : rtQuotient = Squotient.commit quotientWord)
    (z y : F) (qCount : ℕ) {tau : ℝ}
    (hfar : tau ≤ relDist mainWord
      (fun i => y + (dom i - z) * quotientWord i)) :
    ((additiveOodQueryAcceptSet Smain Squotient dom rtMain rtQuotient
          z y qCount).card : ℝ) /
        (Fintype.card ι : ℝ) ^ qCount ≤ (1 - tau) ^ qCount := by
  classical
  set reconstructed : ι → F :=
    fun i => y + (dom i - z) * quotientWord i
  set agree : Finset (Fin qCount → ι) := Finset.univ.filter fun schedule =>
    ∀ a, mainWord (schedule a) = reconstructed (schedule a) with hagree
  have hsub : additiveOodQueryAcceptSet Smain Squotient dom rtMain
      rtQuotient z y qCount ⊆ agree := by
    intro schedule hschedule
    obtain ⟨opening, hopen⟩ := (Finset.mem_filter.mp hschedule).2
    rw [hagree, Finset.mem_filter]
    refine ⟨Finset.mem_univ schedule, fun a => ?_⟩
    exact openedAdditiveOodQuery_pins Smain Squotient dom hrtMain
      hrtQuotient (hopen a)
  have hcard :
      ((additiveOodQueryAcceptSet Smain Squotient dom rtMain rtQuotient
        z y qCount).card : ℝ) ≤ (agree.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hcount : (agree.card : ℝ) ≤
      (1 - tau) ^ qCount * (Fintype.card ι : ℝ) ^ qCount := by
    rw [hagree]
    exact column_sampling_bridge qCount hfar
  have hden : (0 : ℝ) < (Fintype.card ι : ℝ) ^ qCount := by positivity
  rw [div_le_iff₀ hden]
  exact le_trans hcard hcount

/-- **Committed false-opening soundness with an exact quotient LDT.**  If the
committed quotient is exactly degree `< d-1` while `y` is false for the main
word's canonical degree-`< d` OOD evaluation, authenticated sampling accepts
with probability at most `(1-1/|domain|)^qCount`.

Replacing `hquotient` by a sampled additive-FRI verdict is the remaining
additive tower/transcript composition; current coherent FRI is multiplicative
and cannot discharge it in characteristic two. -/
theorem additiveOod_false_claim_query_miss_pr
    (Smain : BindingCommitment RootMain F ι OpMain)
    (Squotient : BindingCommitment RootQuotient F ι OpQuotient)
    (dom : ι ↪ F) {d : ℕ} (hd : 1 < d)
    (hdcard : d ≤ Fintype.card ι)
    {mainWord quotientWord : ι → F}
    {rtMain : RootMain} {rtQuotient : RootQuotient}
    (hrtMain : rtMain = Smain.commit mainWord)
    (hrtQuotient : rtQuotient = Squotient.commit quotientWord)
    (z y : F) (qCount : ℕ)
    (hquotient : quotientWord ∈ reedSolomonCode dom (d - 1))
    (hfalse : oodEval dom d mainWord z ≠ y) :
    ((additiveOodQueryAcceptSet Smain Squotient dom rtMain rtQuotient
          z y qCount).card : ℝ) /
        (Fintype.card ι : ℝ) ^ qCount ≤
      (1 - 1 / (Fintype.card ι : ℝ)) ^ qCount := by
  let reconstructed : ι → F :=
    fun i => y + (dom i - z) * quotientWord i
  have hne : mainWord ≠ reconstructed := by
    intro heq
    have hchannel : ∀ i,
        mainWord i = y + (dom i - z) * quotientWord i := by
      intro i
      exact congrFun heq i
    exact hfalse
      (mem_reedSolomonCode_and_oodEval_of_additiveOodChannel dom hd hdcard
        hquotient hchannel).2
  exact additiveOod_query_miss_pr Smain Squotient dom hrtMain hrtQuotient
    z y qCount (one_div_card_le_relDist hne)

end CommittedQueries

/-- info: 'Minidregg.Selvage.additiveOodQuotient_channel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveOodQuotient_channel
/-- info: 'Minidregg.Selvage.additiveOodEvaluationChannel_retires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveOodEvaluationChannel_retires
/-- info: 'Minidregg.Selvage.additiveOod_false_claim_query_miss_pr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveOod_false_claim_query_miss_pr

end Minidregg.Selvage
