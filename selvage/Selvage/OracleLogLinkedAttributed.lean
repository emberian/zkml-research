/-
# Selvage.OracleLogLinkedAttributed — root-word attribution in the verifier

`OracleLogLinkedSubUd` proves that the current linked verifier accepts roots
which are position-consistent at the sampled columns but have no whole-word
preimage under `commit`.  Def.-4.1 `full_iff` then prevents a knowledge state
from silently imposing whole-word attribution on every live transcript.

This module makes the smallest semantic repair:

* `RootAttribution S` is a partial validity/read interface.  Honest commitment
  roots are valid; a valid root reads to a word which commits back to it.
  Invalid bit strings remain possible values of `Root` and are rejected.
* `accReductionBcsShiftedLinkedAttributed` is the existing linked reduction
  with one additional verifier guard: every prover-message root is valid.
* accepting transcripts expose a whole word behind every root, every verified
  sampled column of that word, and every existing `LinkOpened` check.

The old junk-root transcript is rejected, while the existing honest shifted
run passes unchanged.  A hiding-window audit below finds a second, independent
completeness defect: when `t < d`, the inherited column erasure deliberately
returns zero even though the transcript is accepted.  The repaired reduction
therefore takes its output word from the attributed final root.  After this
repair, the remaining sub-UD premise is the probabilistic
sampling-to-large-agreement bridge for the exposed consecutive root words.
-/
import Selvage.OracleLogLinkedSubUd

namespace Minidregg.Selvage

/-! ## A partial, sound root-word reader -/

section Attribution

variable {Root F ι Op : Type}

/-- A validity predicate and sound partial reader for commitment roots.
Unlike requiring `commit` to be surjective, this permits arbitrary invalid
root bit strings while identifying exactly the ones the verifier may accept. -/
structure RootAttribution (S : BindingCommitment Root F ι Op) where
  /-- Roots admitted by the enhanced verifier. -/
  Valid : Root → Prop
  /-- Every honestly committed word produces a valid root. -/
  valid_commit : ∀ w : ι → F, Valid (S.commit w)
  /-- Read the unique whole word behind a valid root. -/
  read : ∀ rt : Root, Valid rt → ι → F
  /-- Reading is sound: the root is exactly the commitment to that word. -/
  read_spec : ∀ (rt : Root) (h : Valid rt), rt = S.commit (read rt h)

/-- The canonical, noncomputable attribution interface: validity means being
in the range of `commit`.  Binding makes its chosen preimage unique. -/
noncomputable def rangeRootAttribution
    (S : BindingCommitment Root F ι Op) : RootAttribution S where
  Valid := RootInCommitRange S
  valid_commit := fun w => ⟨w, rfl⟩
  read := fun _ h => h.choose
  read_spec := fun _ h => h.choose_spec

theorem rangeRootAttribution_valid_iff
    (S : BindingCommitment Root F ι Op) (rt : Root) :
    (rangeRootAttribution S).Valid rt ↔ RootInCommitRange S rt :=
  Iff.rfl

/-- A valid root has exactly one attributed word. -/
theorem RootAttribution.read_eq_of_commit
    (S : BindingCommitment Root F ι Op) (A : RootAttribution S)
    {rt : Root} (hvalid : A.Valid rt) {w : ι → F}
    (hrt : rt = S.commit w) : A.read rt hvalid = w :=
  S.commit_injective ((A.read_spec rt hvalid).symm.trans hrt)

end Attribution

/-! ## The attribution-grown linked verifier -/

section AttributedReduction

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F))
  (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op)
  (A : RootAttribution S)
  (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m)
  (wv : Fin ch.length → Fin m → F)

open Classical in
/-- The existing linked reduction with one additional, load-bearing check:
every recommitted fold root must be readable by the attribution interface. -/
@[reducible] noncomputable def accReductionBcsShiftedLinkedAttributed : Reduction :=
  { linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv with
    verify := fun idx x y πs ρs =>
      if ∀ c, A.Valid (πs c).root then
        (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv).verify
          idx x y πs ρs
      else none }

open Classical in
/-- The total word named by a root, with an arbitrary zero value off the valid
root language.  The verifier below calls this only after its validity guard.
For a concrete commitment this interface is implemented by carrying a final
root-word opening (or an equivalent commitment decoder) in the proof. -/
noncomputable def attributedRootWord (rt : Root') : Fin m → F :=
  if h : A.Valid rt then A.read rt h else 0

omit [Fintype F] [DecidableEq F] in
/-- Attribution recovers an honestly committed word exactly. -/
@[simp] theorem attributedRootWord_commit (w : Fin m → F) :
    attributedRootWord (S := S) (A := A) (S.commit w) = w := by
  classical
  unfold attributedRootWord
  rw [dif_pos (A.valid_commit w)]
  exact A.read_eq_of_commit S (A.valid_commit w) rfl

open Classical in
/-- Completeness repair for the hiding window: retain every check of the
attributed linked verifier, but output the word named by the final attributed
root instead of attempting degree-`d` erasure from only `t` columns. -/
@[reducible] noncomputable def accReductionBcsShiftedLinkedAttributedWord :
    Reduction :=
  { linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv with
    verify := fun idx x y πs ρs =>
      if ∀ c, A.Valid (πs c).root then
        match (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q
          wv).verify idx x y πs ρs with
        | some out => some (out.1,
            attributedRootWord (S := S) (A := A)
              (πs (Fin.last ch.length)).root)
        | none => none
      else none }

/-- Enhanced acceptance implies acceptance by the exact linked verifier and
exposes validity of every message root. -/
theorem attributed_verify_strengthens
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (πs : Fin (ch.length + 1) → BcsMsg Root' F Op t)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : (accReductionBcsShiftedLinkedAttributed C foldRoot ch hm hch δs
      hδpos hδone S A dom d q wv).verify () A₀ f₀ πs ρs = some out) :
    (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv).verify
        () A₀ f₀ πs ρs = some out ∧
      ∀ c, A.Valid (πs c).root := by
  classical
  by_cases hv : ∀ c, A.Valid (πs c).root
  · exact ⟨by simpa [accReductionBcsShiftedLinkedAttributed, hv] using hacc, hv⟩
  · simp [accReductionBcsShiftedLinkedAttributed, hv] at hacc

/-- Any acceptance by the guard-only verifier is accepted by the repaired
verifier with the same aggregate and the final root's attributed word. -/
theorem attributedWord_verify_of_attributed_accept
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (πs : Fin (ch.length + 1) → BcsMsg Root' F Op t)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : (accReductionBcsShiftedLinkedAttributed C foldRoot ch hm hch δs
      hδpos hδone S A dom d q wv).verify () A₀ f₀ πs ρs = some out) :
    (accReductionBcsShiftedLinkedAttributedWord C foldRoot ch hm hch δs
      hδpos hδone S A dom d q wv).verify () A₀ f₀ πs ρs =
      some (out.1, attributedRootWord (S := S) (A := A)
        (πs (Fin.last ch.length)).root) := by
  classical
  obtain ⟨hlinked, hvalid⟩ := attributed_verify_strengthens C foldRoot ch hm
    hch δs hδpos hδone S A dom d q wv A₀ f₀ πs ρs hacc
  change (if ∀ c, A.Valid (πs c).root then
      match (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q
        wv).verify () A₀ f₀ πs ρs with
      | some out => some
          (out.1, attributedRootWord (S := S) (A := A)
            (πs (Fin.last ch.length)).root)
      | none => none
    else none) = _
  rw [if_pos hvalid, hlinked]

/-- Enhanced acceptance exposes the actual whole fold words, their sampled
columns, and the existing link openings.  This is the deterministic data the
sub-UD transport consumes. -/
theorem attributed_verify_accept_data
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (πs : Fin (ch.length + 1) → BcsMsg Root' F Op t)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : (accReductionBcsShiftedLinkedAttributed C foldRoot ch hm hch δs
      hδpos hδone S A dom d q wv).verify () A₀ f₀ πs ρs = some out) :
    ∃ folds : Fin (ch.length + 1) → Fin m → F,
      (∀ c, (πs c).root = S.commit (folds c)) ∧
      (∀ c, ColsOpen S q (πs c)) ∧
      (∀ c j, (πs c).cols j = folds c (q j)) ∧
      ∀ i : Fin ch.length,
        LinkOpened S q (S.commit (wv i)) (πs i.castSucc) (πs i.succ)
          (ρs i.castSucc) := by
  classical
  obtain ⟨hlinked, hvalid⟩ := attributed_verify_strengthens C foldRoot ch hm
    hch δs hδpos hδone S A dom d q wv A₀ f₀ πs ρs hacc
  have hstrength := linked_verify_strengthens C foldRoot ch hm hch δs hδpos
    hδone S dom d q wv A₀ f₀ πs ρs hlinked
  have hopen : ∀ c, ColsOpen S q (πs c) := by
    have hunlinked := hstrength.1
    by_cases hc : (∀ c, ColsOpen S q (πs c)) ∧
        ∀ j, (πs 0).cols j = f₀ (q j)
    · exact hc.1
    · change (if (∀ c, ColsOpen S q (πs c)) ∧
          ∀ j, (πs 0).cols j = f₀ (q j)
        then _ else none) = some out at hunlinked
      rw [if_neg hc] at hunlinked
      simp at hunlinked
  let folds : Fin (ch.length + 1) → Fin m → F :=
    fun c => A.read (πs c).root (hvalid c)
  refine ⟨folds, fun c => A.read_spec _ _, hopen, ?_, hstrength.2⟩
  intro c j
  exact binding_columns S (A.read_spec _ _) (hopen c) j

/-- Acceptance already gives the deterministic half of the sampling bridge:
the two attributed consecutive root words have normalized difference equal to
the designated link word on every sampled coordinate.  What remains is only
the probabilistic amplification from this sampled agreement to the large
agreement set required by `subUdMessageIncrement_pinned`. -/
theorem attributed_acceptance_increment_agreesOn_queries
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (πs : Fin (ch.length + 1) → BcsMsg Root' F Op t)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : (accReductionBcsShiftedLinkedAttributed C foldRoot ch hm hch δs
      hδpos hδone S A dom d q wv).verify () A₀ f₀ πs ρs = some out)
    (i : Fin ch.length) (hρ : ρs i.castSucc ≠ 0) :
    ∃ folds : Fin (ch.length + 1) → Fin m → F,
      (∀ c, (πs c).root = S.commit (folds c)) ∧
      AgreesOn (Finset.univ.image q)
        ((ρs i.castSucc)⁻¹ • (folds i.succ - folds i.castSucc)) (wv i) := by
  obtain ⟨folds, hroot, hopen, -, hlinks⟩ := attributed_verify_accept_data
    C foldRoot ch hm hch δs hδpos hδone S A dom d q wv A₀ f₀ πs ρs hacc
  refine ⟨folds, hroot, ?_⟩
  exact attributedIncrement_agreesOn_queries S q
    (hroot i.castSucc) (hroot i.succ) (hopen i.castSucc) (hopen i.succ)
    hρ (hlinks i)

/-- Honest shifted roots and columns pass the enhanced verifier at *every*
`d,t`, including `t < d`.  Outside the erasure regime the exact output remains
the verifier's `bcsWord` synthesis; this theorem intentionally does not claim
that synthesis is the honest full fold or that it satisfies the target
relation. -/
theorem attributed_verify_honest_raw
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (ms : Fin ch.length → Fin m → F)
    (ρs : Fin (ch.length + 1) → F) :
    (accReductionBcsShiftedLinkedAttributed C foldRoot ch hm hch δs hδpos
        hδone S A dom d q ms).verify () A₀ f₀
        (fun c => shiftedMsg S q
          (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (c : ℕ)) ρs
      = some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          bcsWord dom d q (shiftedMsg S q
            (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms
            ch.length)) := by
  classical
  let γs : ℕ → F := padSched fun i : Fin ch.length => ρs i.castSucc
  let πs : Fin (ch.length + 1) → BcsMsg Root' F Op t :=
    fun c => shiftedMsg S q γs f₀ ms (c : ℕ)
  have hshift :
      (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q).verify
        () A₀ f₀ πs ρs =
        some (aggregate foldRoot γs A₀ ch,
          bcsWord dom d q (πs (Fin.last ch.length))) := by
    change (if (∀ c, ColsOpen S q (πs c)) ∧
      (∀ j, (πs 0).cols j = f₀ (q j)) then _ else none) = _
    rw [if_pos]
    refine ⟨fun c => shiftedMsg_opens S q γs f₀ ms (c : ℕ), ?_⟩
    intro j
    show partialFold γs f₀ ms 0 (q j) = f₀ (q j)
    rw [partialFold_zero]
  have hlinked := linked_verify_of_shifted C foldRoot ch hm hch δs hδpos
    hδone S dom d q ms A₀ f₀ πs ρs hshift
    (fun i => by
      have hi := linkOpened_honest S q γs f₀ ms i
      have hγ : γs (i : ℕ) = ρs i.castSucc := by
        dsimp [γs]
        rw [padSched_lt _ i.isLt]
      rw [← hγ]
      simpa [πs] using hi)
  change (if ∀ c, A.Valid (πs c).root then
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q ms).verify
        () A₀ f₀ πs ρs else none) = _
  have hv : ∀ c, A.Valid (πs c).root := by
    intro c
    exact A.valid_commit _
  rw [if_pos hv]
  simpa [γs, πs] using hlinked

/-- With the final-root word output, honest shifted transcripts are complete
at every query/degree ratio.  In particular this theorem has no `d ≤ t`
premise: the final word comes from attribution, not column erasure. -/
theorem attributedWord_verify_honest
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (ms : Fin ch.length → Fin m → F)
    (ρs : Fin (ch.length + 1) → F) :
    (accReductionBcsShiftedLinkedAttributedWord C foldRoot ch hm hch δs hδpos
        hδone S A dom d q ms).verify () A₀ f₀
        (fun c => shiftedMsg S q
          (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (c : ℕ)) ρs
      = some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          flatFold (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms) := by
  classical
  have hraw := attributed_verify_honest_raw C foldRoot ch hm hch δs hδpos
    hδone S A dom d q A₀ f₀ ms ρs
  have hout := attributedWord_verify_of_attributed_accept C foldRoot ch hm hch
    δs hδpos hδone S A dom d q ms A₀ f₀
    (fun c => shiftedMsg S q
      (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (c : ℕ)) ρs hraw
  simpa [shiftedMsg, Fin.val_last, partialFold_last] using hout

omit [Fintype F] [DecidableEq F] in
/-- Outside the erasure regime `bcsWord` does not recover a partial fold; by
definition it fails closed to the zero word. -/
theorem bcsWord_eq_zero_of_lt (hlt : t < d) (π : BcsMsg Root' F Op t) :
    bcsWord dom d q π = 0 := by
  unfold bcsWord recoverFromColumns
  rw [dif_neg (Nat.not_le_of_gt hlt)]

/-- In the erasure regime the raw honest output is the true full fold.  This
is the stronger completeness theorem previously used by the F₅ `t=d` tooth. -/
theorem attributed_verify_honest (hdt : d ≤ t)
    (hq : Function.Injective (dom ∘ q)) (A₀ : AccClaim Root F (Fin m) r)
    {f₀ : Fin m → F} {ms : Fin ch.length → Fin m → F}
    (hf₀ : f₀ ∈ reedSolomonCode dom d)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (ρs : Fin (ch.length + 1) → F) :
    (accReductionBcsShiftedLinkedAttributed C foldRoot ch hm hch δs hδpos
        hδone S A dom d q ms).verify () A₀ f₀
        (fun c => shiftedMsg S q
          (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (c : ℕ)) ρs
      = some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          flatFold (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms) := by
  classical
  rw [show (accReductionBcsShiftedLinkedAttributed C foldRoot ch hm hch δs
      hδpos hδone S A dom d q ms).verify () A₀ f₀
      (fun c => shiftedMsg S q
        (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (c : ℕ)) ρs =
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q ms).verify
        () A₀ f₀
        (fun c => shiftedMsg S q
          (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (c : ℕ)) ρs from
    if_pos (fun c => A.valid_commit _)]
  exact linked_verify_honest C foldRoot ch hm hch δs hδpos hδone S dom d q
    hdt hq A₀ hf₀ hms ρs

end AttributedReduction

/-! ## Teeth and premise firing -/

namespace OracleLogLinkedAttributedExample

open OracleLogLinkedSubUdCounterexample

/-- The enhanced verifier rejects the exact junk transcript which the old
linked verifier accepted. -/
theorem old_junk_transcript_rejected :
    (accReductionBcsShiftedLinkedAttributed
      (⊤ : Submodule F₅ Word₁) zeroFoldRoot zeroChain
      OracleLogLinkedSubUdCounterexample.one_pos zeroChain_pos
      (1 / 2) half_pos half_le_one junkCommitment
      (rangeRootAttribution junkCommitment) dom₁ 1 q₁ zeroDesignations).verify
        junkStmt.idx junkStmt.x junkStmt.y junkMsgs junkChallenges = none := by
  classical
  change (if ∀ c, RootInCommitRange junkCommitment (junkMsgs c).root then _
    else none) = none
  rw [if_neg]
  intro hall
  exact junkRoot_not_in_range (hall 0)

open RSExample LCExample AccExample ZkHidingExample ZkExtractionExample
  CommitExample AccRbrBcsExample AccRbrBcsShiftedExample AccSoundRbrExample
  AccRbrInstanceExample OracleLogProgramExample OracleLogLinkedExample in
/-- The existing honest F₅ linked execution still passes with range
attribution, so the new guard has both satisfiability and teeth. -/
theorem honest_roots_pass_F5 (ρs : Fin 3 → ZMod 5) :
    (accReductionBcsShiftedLinkedAttributed
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ (rangeRootAttribution S₅) dom₅ 2 qPair msEx).verify () genesis xWord
      (fun c => shiftedMsg S₅ qPair
        (padSched fun i : Fin 2 => ρs i.castSucc) xWord msEx (c : ℕ)) ρs =
      some (aggregate linRoot (padSched fun i : Fin 2 => ρs i.castSucc)
          genesis goodChain,
        flatFold (padSched fun i : Fin 2 => ρs i.castSucc) xWord msEx) := by
  exact attributed_verify_honest
    (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
    (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ (rangeRootAttribution S₅) dom₅ 2 qPair
    (by norm_num) qPair_inj genesis xWord_mem msEx_mem ρs

open RSExample LCExample AccExample ZkHidingExample ZkArgumentExample
  ZkExtractionExample CommitExample AccRbrBcsShiftedExample
  AccExtractChainExample

/-- The concrete three Reduction challenges: the first two are the honest
fold schedule `(1,1)` and the final coordinate is inert. -/
def hidingChallengesF5 : Fin 3 → ZMod 5 := ![1, 1, 0]

def hidingScheduleF5 : ℕ → ZMod 5 :=
  padSched fun i : Fin 2 => hidingChallengesF5 i.castSucc

noncomputable def hidingMsgsF5 :
    Fin 3 → BcsMsg (Fin 4 → ZMod 5) (ZMod 5) Unit 1 :=
  fun c => shiftedMsg S₅ qz hidingScheduleF5 xWord msEx (c : ℕ)

/-- **Audit result, positive but weaker than completeness:** at the actual
constrained-mask hiding point `t=1<d=2`, the enhanced verifier DOES accept
the honest roots, columns, and link equations.  Its synthesized output word,
however, is zero because erasure recovery is outside its regime. -/
theorem honest_hiding_transcript_accepted_F5 :
    (accReductionBcsShiftedLinkedAttributed
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ (rangeRootAttribution S₅) dom₅ 2 qz msEx).verify () genesis xWord
      hidingMsgsF5 hidingChallengesF5 =
      some (aggregate linRoot hidingScheduleF5 genesis goodChain, 0) := by
  have hraw := attributed_verify_honest_raw
    (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
    (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ (rangeRootAttribution S₅) dom₅ 2 qz genesis xWord msEx
    hidingChallengesF5
  have hz : bcsWord dom₅ 2 qz
      (shiftedMsg S₅ qz
        (padSched fun i : Fin 2 => hidingChallengesF5 i.castSucc)
        xWord msEx goodChain.length) = 0 :=
    bcsWord_eq_zero_of_lt dom₅ 2 qz (by norm_num) _
  simpa only [hidingMsgsF5, hidingScheduleF5, hz] using hraw

/-- The zero synthesis is not an honest target witness for the `(1,1)`
aggregate.  The aggregate target is nonzero while every functional evaluates
to zero on the zero word. -/
theorem zero_not_hiding_target_F5 :
    ¬ AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      (aggregate linRoot hidingScheduleF5 genesis goodChain) 0 := by
  intro hsat
  have ht := hsat.2 (0 : Fin 1)
  norm_num [aggregate, hidingScheduleF5, hidingChallengesF5, padSched,
    goodChain, link₀, link₁, foldClaims, claim₀, claim₁, genesis,
    AccClaim.weights, AccClaim.targets] at ht
  exact (by decide : (0 : ZMod 5) ≠ 3) ht

/-- The failure persists at the reduction's actual proximity radius: below
one coordinate (`1/4` on length four), every word within `1/16` of zero is
zero, which the preceding theorem refutes.  Thus syntactic acceptance at the
hiding point is NOT Def.-4.1/target-relation completeness. -/
theorem honest_hiding_output_not_relaxed_F5 :
    ¬ RelaxedMem
      (accReductionBcsShiftedLinkedAttributed
        (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
        (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
        S₅ (rangeRootAttribution S₅) dom₅ 2 qz msEx).R'
      (1 / 16 : ℝ) ()
      (aggregate linRoot hidingScheduleF5 genesis goodChain) 0
      (fun _ => 0) := by
  rintro ⟨ystar, hsat, hdist⟩
  change AccClaim.Satisfies
    (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
    (aggregate linRoot hidingScheduleF5 genesis goodChain) ystar at hsat
  change fracHamming (0 : Fin 4 → ZMod 5) ystar ≤ (1 / 16 : ℝ) at hdist
  rw [fracHamming_eq_relDist] at hdist
  by_cases hy : ystar = 0
  · subst ystar
    exact zero_not_hiding_target_F5 hsat
  · have hfloor := one_div_card_le_relDist (F := ZMod 5) (Ne.symm hy)
    norm_num [Fintype.card_fin] at hfloor
    have hbad : (1 / 4 : ℝ) ≤ 1 / 16 := le_trans hfloor hdist
    norm_num at hbad

/-- The final-root word repair restores honest verifier completeness at the
actual hiding point `t=1<d=2`; no degree-erasure premise is used. -/
theorem honest_hiding_word_verifies_F5 :
    (accReductionBcsShiftedLinkedAttributedWord
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ (rangeRootAttribution S₅) dom₅ 2 qz msEx).verify () genesis xWord
      hidingMsgsF5 hidingChallengesF5 =
      some (aggregate linRoot hidingScheduleF5 genesis goodChain,
        flatFold hidingScheduleF5 xWord msEx) := by
  simpa only [hidingMsgsF5, hidingScheduleF5] using
    (attributedWord_verify_honest
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ (rangeRootAttribution S₅) dom₅ 2 qz genesis xWord msEx
      hidingChallengesF5)

/-- The repaired output is not merely the honest fold syntactically: it is a
genuine witness of the reduction target relation at the hiding point. -/
theorem honest_hiding_word_satisfies_F5 :
    AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      (aggregate linRoot hidingScheduleF5 genesis goodChain)
      (flatFold hidingScheduleF5 xWord msEx) :=
  ⟨Submodule.mem_top,
    (masked_completeness_F5 hidingScheduleF5).2⟩

end OracleLogLinkedAttributedExample

/-- info: 'Minidregg.Selvage.RootAttribution.read_eq_of_commit' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RootAttribution.read_eq_of_commit
/-- info: 'Minidregg.Selvage.attributedRootWord_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attributedRootWord_commit
/-- info: 'Minidregg.Selvage.attributed_verify_strengthens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attributed_verify_strengthens
/-- info: 'Minidregg.Selvage.attributedWord_verify_of_attributed_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attributedWord_verify_of_attributed_accept
/-- info: 'Minidregg.Selvage.attributed_verify_accept_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attributed_verify_accept_data
/-- info: 'Minidregg.Selvage.attributed_acceptance_increment_agreesOn_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attributed_acceptance_increment_agreesOn_queries
/-- info: 'Minidregg.Selvage.attributed_verify_honest_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attributed_verify_honest_raw
/-- info: 'Minidregg.Selvage.attributedWord_verify_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attributedWord_verify_honest
/-- info: 'Minidregg.Selvage.attributed_verify_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attributed_verify_honest
/-- info: 'Minidregg.Selvage.OracleLogLinkedAttributedExample.old_junk_transcript_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedAttributedExample.old_junk_transcript_rejected
/-- info: 'Minidregg.Selvage.OracleLogLinkedAttributedExample.honest_roots_pass_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedAttributedExample.honest_roots_pass_F5
/-- info: 'Minidregg.Selvage.OracleLogLinkedAttributedExample.honest_hiding_transcript_accepted_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedAttributedExample.honest_hiding_transcript_accepted_F5
/-- info: 'Minidregg.Selvage.OracleLogLinkedAttributedExample.zero_not_hiding_target_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedAttributedExample.zero_not_hiding_target_F5
/-- info: 'Minidregg.Selvage.OracleLogLinkedAttributedExample.honest_hiding_output_not_relaxed_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedAttributedExample.honest_hiding_output_not_relaxed_F5
/-- info: 'Minidregg.Selvage.OracleLogLinkedAttributedExample.honest_hiding_word_verifies_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedAttributedExample.honest_hiding_word_verifies_F5
/-- info: 'Minidregg.Selvage.OracleLogLinkedAttributedExample.honest_hiding_word_satisfies_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedAttributedExample.honest_hiding_word_satisfies_F5

end Minidregg.Selvage
