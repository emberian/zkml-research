/-
# Selvage.BaseFoldRbr — the quadratic BaseFold leg enters the RBR kernel

`BaseFoldBraid` constructs the honest degree-two product sumcheck for
`table(b) * chi_b(z)`.  `SumcheckRbr` turns any well-formed adaptive sumcheck
family into an actual WARP `Reduction`/`KStateFn`/`RbrKnowledgeSoundness`
object.  This file joins them.

The resulting reduction has source relation

`claimedValue = mle table z`

and exact per-round knowledge error `2 / |F|`.  Its knowledge state contains
the completed Boolean-sum checks and the equality between the adversarial
claim chain and BaseFold's honest product chain.  The identity extractor is
appropriate for this scalar-preservation component.

This is one load-bearing leg of the final BaseFold reduction, not the whole
opening protocol.  The RS/proximity leg still has to be product-composed with
this state, and the committed intermediate words still require the existing
FRI opening/query layer (`HalfThresholdFriTranscript`) before BCS/FS.  Those
costs are not absorbed into the `2 / |F|` field below.
-/
import Selvage.BaseFoldBraid
import Selvage.SumcheckRbr
import Selvage.FiatShamir

namespace Minidregg.Selvage

open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- BaseFold's scalar sumcheck leg as a native WARP reduction. -/
@[reducible] noncomputable def basefoldSumcheckReduction (hm : 0 < m)
    (table : (Fin m → Bool) → F) (z : Fin m → F) : Reduction :=
  sumcheckReduction m 2 hm (mle table z) (basefoldHonest table z)

omit [Fintype F] [DecidableEq F] in
/-- A finite RBR transcript prefix, restricted to `Fin m`, induces the same
zero-padded schedule expected by the landed BaseFold sumcheck theorems. -/
def basefoldPrefixChallenges (rs : List (Polynomial F × F)) : Fin m → F :=
  fun j => scSchedule rs j

omit [Fintype F] [DecidableEq F] in
theorem scSchedule_eq_chalOf_prefix (rs : List (Polynomial F × F))
    (h : rs.length < m) :
    ∀ j, j < rs.length →
      scSchedule rs j =
        chalOf (basefoldPrefixChallenges (m := m) rs) j := by
  intro j hj
  rw [chalOf, dif_pos (lt_trans hj h)]
  rfl

omit [Fintype F] [DecidableEq F] in
/-- The landed BaseFold family satisfies the list-prefix degree obligation of
the generic RBR construction. -/
theorem basefoldRbr_honest_degree (table : (Fin m → Bool) → F)
    (z : Fin m → F) (rs : List (Polynomial F × F)) (h : rs.length < m) :
    (scHonestAt (basefoldHonest table z) rs).degree <
      ((2 + 1 : ℕ) : WithBot ℕ) :=
  basefoldHonest_degree table z (scSchedule rs) rs.length h

omit [Fintype F] [DecidableEq F] in
/-- The landed BaseFold Boolean-sum theorem, transported from its padded
`Fin m` challenge tuple to RBR's finite transcript prefix. -/
theorem basefoldRbr_honest_check (table : (Fin m → Bool) → F)
    (z : Fin m → F) (rs : List (Polynomial F × F)) (h : rs.length < m) :
    (scHonestAt (basefoldHonest table z) rs).eval 0 +
        (scHonestAt (basefoldHonest table z) rs).eval 1 =
      scTruthAfter (mle table z) (basefoldHonest table z) rs := by
  let r : Fin m → F := basefoldPrefixChallenges (m := m) rs
  have hpre : ∀ j, j < rs.length → scSchedule rs j = chalOf r j :=
    scSchedule_eq_chalOf_prefix rs h
  rw [scHonestAt_eq_of_prefix (basefoldHonest_prefixMeasurable table z) rs
      (chalOf r) hpre,
    scTruthAfter_eq_of_prefix (basefoldHonest_prefixMeasurable table z) rs
      (chalOf r) hpre]
  exact basefoldHonest_boolean_sum table z r rs.length h

/-- ⭐ The native Def-4.2 instance for BaseFold's degree-two sumcheck leg. -/
noncomputable def basefoldSumcheckRbr (hm : 0 < m)
    (table : (Fin m → Bool) → F) (z : Fin m → F) :
    RbrKnowledgeSoundness (basefoldSumcheckReduction hm table z) :=
  sumcheckRbrKnowledgeSound m 2 hm (mle table z) (basefoldHonest table z)
    (basefoldHonest_prefixMeasurable table z)
    (basefoldRbr_honest_degree table z)
    (basefoldRbr_honest_check table z)

omit [DecidableEq F] in
/-- The source relation is exactly the public BaseFold evaluation claim. -/
theorem basefoldSumcheck_source_iff (hm : 0 < m)
    (table : (Fin m → Bool) → F) (z : Fin m → F) (H : F)
    (y : Fin (basefoldSumcheckReduction hm table z).n →
      (basefoldSumcheckReduction hm table z).A) :
    (basefoldSumcheckReduction hm table z).R () H y () ↔ H = mle table z :=
  Iff.rfl

/-- The BaseFold RBR leg pays exactly two field roots per round. -/
@[simp] theorem basefoldSumcheckRbr_err (hm : 0 < m)
    (table : (Fin m → Bool) → F) (z : Fin m → F)
    (i : Fin m) (st : Stmt (basefoldSumcheckReduction hm table z)) (δ : ℝ) :
    (basefoldSumcheckRbr hm table z).err i st δ =
      (2 : ℝ) / Fintype.card F := rfl

/-! ## The compiled leg

The point of building a NATIVE `RbrKnowledgeSoundness` object rather than a
standalone probability bound is that Selvage's Fiat–Shamir keystone consumes
exactly that object, unconditionally (`fsKeystone_proved`, discharged from
[OB-2a] in `Selvage/Depth.lean`).  Without the theorem below the instance is an
island: `basefoldSumcheckRbr` had no consumer, while the operational bound of
`Selvage/BaseFoldIor.lean` reached the ledger by a different route. -/

/-- ⭐ **BaseFold's sumcheck leg, Fiat–Shamir compiled.**  Straightline, loss-free,
with the grinding factor named: a `t`-query ROM adversary that outputs a WRONG
claimed total and has its FS-compiled transcript accepted succeeds with
probability at most `(t + m) · 2/|F|`.

⚠ Read the content exactly.  This reduction's witness type is `Unit`
(`sumcheckReduction`'s `W`), so `FsStraightlineKnowledgeSoundness` here is
straightline *soundness* with a trivial extractor, not extraction of the
committed table: `R` is `claimedValue = mle table z`, a statement predicate.
Extracting the committed multilinear is the commitment layer's job
(`MleEvalClaim`, Merkle binding, `[COMMIT-CR]`), not this leg's. -/
theorem basefoldSumcheck_fs_sound (hm : 0 < m)
    (table : (Fin m → Bool) → F) (z : Fin m → F) :
    FsStraightlineKnowledgeSoundness (basefoldSumcheckReduction hm table z)
      Set.univ
      (fun _s t _δ => ((t : ℝ) + (m : ℝ)) * (2 / Fintype.card F)) :=
  fsKeystone_proved.sound _ (basefoldSumcheckRbr hm table z) Set.univ
    (fun _ => (2 : ℝ) / Fintype.card F)
    (fun _ _ => by positivity)
    (fun i st _ δ _ => le_of_eq (basefoldSumcheckRbr_err hm table z i st δ))

namespace BaseFoldRbrExample

open BaseFoldExample ProximityExample

/-- The native object exists on the landed one-round F5 BaseFold example. -/
noncomputable def rbrF5 :
    RbrKnowledgeSoundness (basefoldSumcheckReduction (by decide) table ![3]) :=
  basefoldSumcheckRbr (by decide) table ![3]

/-- The exact public evaluation claim as a native statement. -/
noncomputable def stF5 :
    Stmt (basefoldSumcheckReduction (by decide) table ![3]) :=
  ⟨(), mle table ![3], fun _ => ()⟩

/-- **Premise inhabitation:** the native knowledge state is true on the exact
F5 claim at the empty transcript and a nonzero relaxation radius. -/
theorem rbrF5_state_alive :
    rbrF5.kstate.state (1 / 2) stF5 Transcript.empty () = true := by
  refine (rbrF5.kstate.empty_iff (1 / 2) ?_ stF5 ()).mpr ?_
  · change (1 / 2 : ℝ) ∈ Set.Ioo 0 1
    norm_num
  · refine ⟨stF5.y, rfl, ?_⟩
    rw [fracHamming_self]
    norm_num

/-- Its round price computes to `2/5`; this is a live finite-field instance,
not an uninstantiated interface. -/
theorem rbrF5_err (i : Fin 1)
    (st : Stmt (basefoldSumcheckReduction (by decide) table ![3])) (δ : ℝ) :
    rbrF5.err i st δ = 2 / 5 := by
  rw [rbrF5, basefoldSumcheckRbr_err, ZMod.card]
  norm_num

/-- The compiled leg on the landed F5 instance: a `t`-query Fiat–Shamir
adversary claiming a wrong total is accepted with probability at most
`(t + 1) · 2/5`.  A live finite-field number, not an uninstantiated
interface. -/
theorem fs_sound_f5 :
    FsStraightlineKnowledgeSoundness
      (basefoldSumcheckReduction (by decide) table ![3]) Set.univ
      (fun _s t _δ => ((t : ℝ) + 1) * (2 / 5)) := by
  have h := basefoldSumcheck_fs_sound (m := 1) (by decide) table ![3]
  have hfun : (fun (_s t : ℕ) (_δ : ℝ) =>
        ((t : ℝ) + ((1 : ℕ) : ℝ)) * (2 / (Fintype.card (ZMod 5) : ℝ)))
      = fun (_s t : ℕ) (_δ : ℝ) => ((t : ℝ) + 1) * (2 / 5) := by
    funext s t δ
    rw [ZMod.card]
    norm_num
  rwa [hfun] at h

end BaseFoldRbrExample

/-- info: 'Minidregg.Selvage.basefoldSumcheckRbr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldSumcheckRbr
/-- info: 'Minidregg.Selvage.basefoldSumcheck_fs_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldSumcheck_fs_sound
/-- info: 'Minidregg.Selvage.BaseFoldRbrExample.fs_sound_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BaseFoldRbrExample.fs_sound_f5

end Minidregg.Selvage
