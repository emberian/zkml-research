/-
# Selvage.OracleLogLinkedSubUd — the first exact sub-UD/state-design join

`OracleLogLinkedAssembly` closes the linked log theorem in the erasure
regime: its log reader reconstructs a word from `t` opened columns and hence
assumes `d ≤ t`.  Constrained-mask hiding needs the opposite window.  This
module isolates the first honest join toward that window.

There are two findings.

1. A `BindingCommitment` supplies position binding, but a `BcsMsg` carries
   only a root and finitely many openings.  `ColsOpen` does not imply that an
   adversarial root lies in the range of `commit`.  Consequently a Def.-4.1
   state for the current linked verifier cannot silently demand a whole word
   behind every live root: a concrete accepted transcript below uses a
   position-binding junk root outside the commitment range.  The attempted
   state-design strengthening is machine-refuted.
2. Once root attribution and the sampling-to-closeness fact are explicit,
   `subUdRecover` pins the challenge-normalized root increment exactly, with
   no `d ≤ t` or query-injectivity hypothesis.  `LinkOpened` supplies the
   observed-coordinate equality; the only remaining probabilistic premise is
   that the attributed increment has a large enough agreement set.

Thus the old residual is not a missing algebra lemma.  The current verifier
must grow a root-preimage/word-attribution check (or the commitment interface
must carry a sound root decoder), and the sampling bridge must price the
closeness event.  After those two premises, the sub-UD transport is closed.
-/
import Selvage.OracleLogLinkedAssembly
import Selvage.SubUdSeam

namespace Minidregg.Selvage

/-! ## Why the closed erasure target is not yet constrained-mask ZK -/

/-- The `d ≤ t` premise used by `OracleLogLinkedAssembly`'s exact column
reader is formally disjoint from constrained-mask hiding (for a nonzero code
dimension).  This is the reason a word-resolution replacement is required,
not an optimization of the existing proof. -/
theorem linkedErasureRegime_excludes_constrainedMaskHiding
    {F : Type} [Field F] {m d t : ℕ} (dom : Fin m ↪ F)
    (hd : 0 < d) (hdt : d ≤ t) (q : Fin t → Fin m)
    (hq : Function.Injective (dom ∘ q)) (pt : Fin m) (gamma : F) :
    ¬ MaskedOpeningHiding (constrainedMaskSpace dom d pt) q gamma :=
  not_constrainedMask_hiding_of_recoverable dom hd hdt hq pt gamma

/-! ## Root attribution, stated rather than inferred -/

section RootAttribution

variable {Root' Op F ι : Type*}

/-- A root has a whole-word preimage under the commitment map.  Position
binding gives uniqueness of such a word, not existence. -/
def RootInCommitRange (S : BindingCommitment Root' F ι Op) (rt : Root') : Prop :=
  ∃ w : ι → F, rt = S.commit w

/-- Classical partial root reader.  It is deliberately partial: arbitrary
roots need not be commitments. -/
noncomputable def committedWord?
    (S : BindingCommitment Root' F ι Op) (rt : Root') : Option (ι → F) := by
  classical
  exact if h : RootInCommitRange S rt then some h.choose else none

/-- The partial reader succeeds exactly on honest commitment roots, and the
word it returns is forced by binding. -/
theorem committedWord?_eq_some_iff
    (S : BindingCommitment Root' F ι Op) (rt : Root') (w : ι → F) :
    committedWord? S rt = some w ↔ rt = S.commit w := by
  classical
  constructor
  · intro hread
    by_cases h : RootInCommitRange S rt
    · have hw : h.choose = w := Option.some.inj (by
        simpa [committedWord?, h] using hread)
      simpa [hw] using h.choose_spec
    · simp [committedWord?, h] at hread
  · intro hrt
    have hrange : RootInCommitRange S rt := ⟨w, hrt⟩
    have hw : hrange.choose = w :=
      S.commit_injective (hrange.choose_spec.symm.trans hrt)
    simp [committedWord?, hrange, hw]

@[simp] theorem committedWord?_commit
    (S : BindingCommitment Root' F ι Op) (w : ι → F) :
    committedWord? S (S.commit w) = some w :=
  (committedWord?_eq_some_iff S _ _).2 rfl

end RootAttribution

/-! ## The exact word-resolution increment transport -/

section SubUdTransport

variable {Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m t : ℕ}

/-- Read the two whole words attributed to consecutive roots and form their
challenge-normalized increment. -/
noncomputable def attributedIncrement?
    (S : BindingCommitment Root' F (Fin m) Op) (ρ : F)
    (uπ uπ' : BcsMsg Root' F Op t) : Option (Fin m → F) := do
  let u ← committedWord? S uπ.root
  let u' ← committedWord? S uπ'.root
  pure (ρ⁻¹ • (u' - u))

/-- The sub-UD message increment.  Missing root attribution fails closed to
zero, exactly as the log reader fails closed on an unqueried challenge. -/
noncomputable def subUdMessageIncrement
    (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F)
    (d : ℕ) (decodeRadius : ℝ) (ρ : F)
    (uπ uπ' : BcsMsg Root' F Op t) : Fin m → F :=
  (attributedIncrement? S ρ uπ uπ').map
      (subUdRecover dom d decodeRadius) |>.getD 0

omit [Fintype F] [DecidableEq F] in
/-- On attributed roots the reader exposes exactly the normalized whole-word
increment. -/
theorem attributedIncrement?_eq_some
    (S : BindingCommitment Root' F (Fin m) Op) (ρ : F)
    {u u' : Fin m → F} {uπ uπ' : BcsMsg Root' F Op t}
    (hu : uπ.root = S.commit u) (hu' : uπ'.root = S.commit u') :
    attributedIncrement? S ρ uπ uπ' = some (ρ⁻¹ • (u' - u)) := by
  unfold attributedIncrement?
  rw [(committedWord?_eq_some_iff S _ _).2 hu,
    (committedWord?_eq_some_iff S _ _).2 hu']
  rfl

omit [Fintype F] [DecidableEq F] in
theorem subUdMessageIncrement_eq
    (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F)
    (d : ℕ) (decodeRadius : ℝ) (ρ : F)
    {u u' : Fin m → F} {uπ uπ' : BcsMsg Root' F Op t}
    (hu : uπ.root = S.commit u) (hu' : uπ'.root = S.commit u') :
    subUdMessageIncrement S dom d decodeRadius ρ uπ uπ' =
      subUdRecover dom d decodeRadius (ρ⁻¹ • (u' - u)) := by
  unfold subUdMessageIncrement
  rw [attributedIncrement?_eq_some S ρ hu hu']
  rfl

omit [Fintype F] [DecidableEq F] in
/-- `LinkOpened` plus root attribution identifies the normalized increment at
every queried coordinate.  No interpolation count appears. -/
theorem attributedIncrement_eq_at_query
    (S : BindingCommitment Root' F (Fin m) Op) (q : Fin t → Fin m)
    {w u u' : Fin m → F} {uπ uπ' : BcsMsg Root' F Op t}
    (hu : uπ.root = S.commit u) (hu' : uπ'.root = S.commit u')
    (hopen : ColsOpen S q uπ) (hopen' : ColsOpen S q uπ')
    {ρ : F} (hρ : ρ ≠ 0)
    (hlink : LinkOpened S q (S.commit w) uπ uπ' ρ) (j : Fin t) :
    (ρ⁻¹ • (u' - u)) (q j) = w (q j) := by
  obtain ⟨lc, lo, hlcOpen, hcols⟩ := hlink
  have hπ : uπ.cols j = u (q j) := binding_columns S hu hopen j
  have hπ' : uπ'.cols j = u' (q j) := binding_columns S hu' hopen' j
  have hlc : lc j = w (q j) := binding_columns S rfl hlcOpen j
  have hstep : u' (q j) = u (q j) + ρ * w (q j) := by
    rw [← hπ', hcols j, hπ, hlc]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hstep, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hρ, one_mul]

omit [Fintype F] [DecidableEq F] in
/-- The pointwise observation bundled as the exact agreement set exposed by
the verifier's sampled queries.  Sampling amplification must turn acceptance
of this set into a large global agreement set; no stronger deterministic
conclusion follows from `LinkOpened`. -/
theorem attributedIncrement_agreesOn_queries
    (S : BindingCommitment Root' F (Fin m) Op) (q : Fin t → Fin m)
    {w u u' : Fin m → F} {uπ uπ' : BcsMsg Root' F Op t}
    (hu : uπ.root = S.commit u) (hu' : uπ'.root = S.commit u')
    (hopen : ColsOpen S q uπ) (hopen' : ColsOpen S q uπ')
    {ρ : F} (hρ : ρ ≠ 0)
    (hlink : LinkOpened S q (S.commit w) uπ uπ' ρ) :
    AgreesOn (Finset.univ.image q) (ρ⁻¹ • (u' - u)) w := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact attributedIncrement_eq_at_query S q hu hu' hopen hopen' hρ hlink j

omit [Fintype F] in
/-- The exact sub-UD pin.  A large agreement set for the attributed root
increment forces the selected codeword to be the designated link word.
Unlike the erasure pin, this theorem has no `d ≤ t` and no injective query
schedule. -/
theorem subUdMessageIncrement_pinned [Nonempty (Fin m)]
    (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F)
    {d : ℕ} {decodeRadius : ℝ}
    (hUD : decodeRadius <
      (1 - ((d : ℝ) - 1) / (Fintype.card (Fin m) : ℝ)) / 2)
    {ρ : F} {w u u' : Fin m → F} {uπ uπ' : BcsMsg Root' F Op t}
    (hu : uπ.root = S.commit u) (hu' : uπ'.root = S.commit u')
    (hw : w ∈ reedSolomonCode dom d) {A : Finset (Fin m)}
    (hcard : (1 - decodeRadius) * (Fintype.card (Fin m) : ℝ) ≤ (A.card : ℝ))
    (hagrees : AgreesOn A (ρ⁻¹ • (u' - u)) w) :
    subUdMessageIncrement S dom d decodeRadius ρ uπ uπ' = w := by
  rw [subUdMessageIncrement_eq S dom d decodeRadius ρ hu hu']
  exact subUdRecover_sound dom hUD hw hcard hagrees

/-! ### The log-level root reader -/

variable {Root : Type} {r : ℕ}

variable (C : Submodule F (Fin m → F))
  (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m) (wv : Fin ch.length → Fin m → F)

/-- The sub-UD replacement for the erasure-based exact extractor: challenges
come from the same oracle log, but increments come from attributed roots and
are decoded at word resolution. -/
noncomputable def linkedSubUdLogExtractor (decodeRadius : ℝ) (s : ℕ) :
    StraightlineOracleExtractor
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s :=
  fun o L i =>
    match L.answerOf (o.query i.castSucc) with
    | none => 0
    | some ρ => subUdMessageIncrement S dom d decodeRadius ρ
        (o.πs i.castSucc) (o.πs i.succ)

theorem linkedSubUdLogExtractor_eq_zero_of_unqueried (decodeRadius : ℝ)
    {s : ℕ}
    (o : SrOutput
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (L : OracleLog
      (SrMove (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s) F)
    (i : Fin ch.length) (hnone : L.answerOf (o.query i.castSucc) = none) :
    linkedSubUdLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q wv
      decodeRadius s o L i = 0 := by
  unfold linkedSubUdLogExtractor
  rw [hnone]

/-- The log-level exact pin, with the two missing deployment premises visible:
the consecutive roots are attributed to words, and their normalized
increment has a sufficiently large agreement set with the designated word. -/
theorem linkedSubUdLogExtractor_pinned [Nonempty (Fin m)]
    {decodeRadius : ℝ}
    (hUD : decodeRadius <
      (1 - ((d : ℝ) - 1) / (Fintype.card (Fin m) : ℝ)) / 2)
    {s : ℕ}
    (o : SrOutput
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (L : OracleLog
      (SrMove (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s) F)
    (i : Fin ch.length) {ρ : F}
    (hans : L.answerOf (o.query i.castSucc) = some ρ)
    {u u' : Fin m → F}
    (hu : (o.πs i.castSucc).root = S.commit u)
    (hu' : (o.πs i.succ).root = S.commit u')
    (hw : wv i ∈ reedSolomonCode dom d) {A : Finset (Fin m)}
    (hcard : (1 - decodeRadius) * (Fintype.card (Fin m) : ℝ) ≤ (A.card : ℝ))
    (hagrees : AgreesOn A (ρ⁻¹ • (u' - u)) (wv i)) :
    linkedSubUdLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q wv
      decodeRadius s o L i = wv i := by
  unfold linkedSubUdLogExtractor
  rw [hans]
  exact subUdMessageIncrement_pinned S dom hUD hu hu' hw hcard hagrees

end SubUdTransport

/-! ## The tempting Def.-4.2 state join, stated exactly -/

section StateTarget

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F))
  (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m) (wv : Fin ch.length → Fin m → F)

/-- The most direct attempted Def.-4.2 join: keep the current linked
reduction, but demand that every live knowledge state attributes every
completed message root to a whole commitment preimage.  This is precisely
what a word-resolution backward extractor would need to read its folds.

The concrete theorem below proves this target false for the current verifier:
Def.-4.1's `full_iff` makes an accepting target-satisfying transcript live,
even when its partially opened message roots are outside `commit`'s range. -/
def LinkedRootAttributedRbrTarget : Prop :=
  ∃ rbr : RbrKnowledgeSoundness
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv),
    ∀ δ ∈ Set.Ioo (0 : ℝ) δs,
      ∀ (st : Stmt
          (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv))
        (tr : Transcript (BcsMsg Root' F Op t) F)
        (w : Fin ch.length → Fin m → F),
        rbr.kstate.state δ st tr w = true →
          ∀ e ∈ tr.rounds, RootInCommitRange S e.1.root

end StateTarget

/-! ## Machine refutation: live current-verifier roots need not be attributed -/

namespace OracleLogLinkedSubUdCounterexample

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F₅ := ZMod 5
abbrev Word₁ := Fin 1 → F₅
abbrev JunkRoot := Option Word₁

/-- A position-binding commitment with one extra root `none`.  That root
opens consistently to zero but is not in the range of `commit`. -/
def junkCommitment : BindingCommitment JunkRoot F₅ (Fin 1) Unit where
  commit := some
  openAt := fun _ _ => ()
  verifyOpen := fun rt i v _ => match rt with
    | some w => v = w i
    | none => v = 0
  verifyOpen_commit := by
    intro w i
    rfl
  binding := by
    intro rt i v v' _ _ hv hv'
    cases rt <;> simp_all

def q₁ : Fin 1 → Fin 1 := fun i => i

def junkMsg : BcsMsg JunkRoot F₅ Unit 1 :=
  ⟨none, fun _ => 0, fun _ => ()⟩

theorem junkMsg_colsOpen : ColsOpen junkCommitment q₁ junkMsg := by
  intro j
  rfl

theorem junkRoot_not_in_range : ¬ RootInCommitRange junkCommitment none := by
  intro h
  obtain ⟨w, hw⟩ := h
  simp [junkCommitment] at hw

/-- The hidden implication needed by a root-reading state is false even for
a genuinely position-binding commitment. -/
theorem colsOpen_not_root_attributed :
    ColsOpen junkCommitment q₁ junkMsg ∧
      ¬ RootInCommitRange junkCommitment junkMsg.root :=
  ⟨junkMsg_colsOpen, junkRoot_not_in_range⟩

/-! ### The stronger refuter: an accepting linked transcript -/

/-- One zero-functional constraint.  Every word satisfies it over `⊤`. -/
def zeroClaim : AccClaim Unit F₅ (Fin 1) 1 :=
  ⟨(), fun _ => (0, 0)⟩

def zeroLink : Link Unit F₅ (Fin 1) 1 := ⟨(), (), zeroClaim⟩
def zeroChain : Chain Unit F₅ (Fin 1) 1 := [zeroLink]

def zeroFoldRoot : Unit → F₅ → Unit → Unit := fun _ _ _ => ()

def dom₁ : Fin 1 ↪ F₅ := ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

def zeroDesignations : Fin zeroChain.length → Word₁ := fun _ => 0

theorem one_pos : 0 < (1 : ℕ) := by norm_num
theorem zeroChain_pos : 0 < zeroChain.length := by decide
theorem half_pos : (0 : ℝ) < 1 / 2 := by norm_num
theorem half_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num

@[reducible] noncomputable def junkLinkedReduction : Reduction :=
  linkedReduction (⊤ : Submodule F₅ Word₁) zeroFoldRoot zeroChain one_pos
    zeroChain_pos (1 / 2) half_pos half_le_one junkCommitment dom₁ 1 q₁
    zeroDesignations

def junkStmt : Stmt junkLinkedReduction := ⟨(), zeroClaim, 0⟩

def junkMsgs : Fin (zeroChain.length + 1) → BcsMsg JunkRoot F₅ Unit 1 :=
  fun _ => junkMsg

def junkChallenges : Fin (zeroChain.length + 1) → F₅ := fun _ => 0

theorem zeroClaim_satisfies (f : Word₁) :
    AccClaim.Satisfies (⊤ : Submodule F₅ Word₁) zeroClaim f := by
  refine ⟨Submodule.mem_top, ?_⟩
  intro i
  simp [zeroClaim, AccClaim.weights, AccClaim.targets]

theorem junk_linkOpened (i : Fin zeroChain.length) :
    LinkOpened junkCommitment q₁
      (junkCommitment.commit (zeroDesignations i))
      (junkMsgs i.castSucc) (junkMsgs i.succ) (junkChallenges i.castSucc) := by
  refine ⟨fun _ => 0, fun _ => (), ?_, ?_⟩
  · intro j
    rfl
  · intro j
    rfl

/-- The current linked verifier accepts a full transcript all of whose
message roots are the unattributed junk root. -/
theorem junk_linked_accepts :
    junkLinkedReduction.verify junkStmt.idx junkStmt.x junkStmt.y
        junkMsgs junkChallenges =
      some (aggregate zeroFoldRoot
          (padSched fun i : Fin zeroChain.length => junkChallenges i.castSucc)
          zeroClaim zeroChain,
        bcsWord dom₁ 1 q₁ (junkMsgs (Fin.last zeroChain.length))) := by
  classical
  change (if (forall i, ColsOpen junkCommitment q₁ (junkMsgs i)) ∧
      (forall j, (junkMsgs 0).cols j = junkStmt.y (q₁ j)) ∧
      forall i : Fin zeroChain.length,
        LinkOpened junkCommitment q₁
          (junkCommitment.commit (zeroDesignations i))
          (junkMsgs i.castSucc) (junkMsgs i.succ) (junkChallenges i.castSucc)
    then _ else none) = _
  rw [if_pos (by
    refine ⟨fun _ => junkMsg_colsOpen, ?_, junk_linkOpened⟩
    intro j
    rfl)]
  rfl

theorem junk_target_relaxed :
    RelaxedMem junkLinkedReduction.R' (1 / 4 : ℝ) junkStmt.idx
      (aggregate zeroFoldRoot
        (padSched fun i : Fin zeroChain.length => junkChallenges i.castSucc)
        zeroClaim zeroChain)
      (bcsWord dom₁ 1 q₁ (junkMsgs (Fin.last zeroChain.length)))
      (fun _ => 0) := by
  let y := bcsWord dom₁ 1 q₁ (junkMsgs (Fin.last zeroChain.length))
  refine ⟨y, ?_, ?_⟩
  · change AccClaim.Satisfies (⊤ : Submodule F₅ Word₁)
      (aggregate zeroFoldRoot
        (padSched fun i : Fin zeroChain.length => junkChallenges i.castSucc)
        zeroClaim zeroChain) y
    apply AccClaim.satisfies_of_channel_eq
      (aggregate_channel_of_zero zeroFoldRoot (fun _ => rfl) zeroClaim zeroChain)
    exact zeroClaim_satisfies y
  · rw [fracHamming_self]
    norm_num

/-- **Machine refutation of the tempting state join.**  No Def.-4.2 object
for the current linked reduction can make root attribution an invariant of
all live states: `full_iff` forces the accepted transcript above live, while
its first message root has no commitment preimage.  The verifier/interface
must grow; this premise cannot be hidden in the knowledge state. -/
theorem linkedRootAttributedRbrTarget_false :
    ¬ LinkedRootAttributedRbrTarget
      (⊤ : Submodule F₅ Word₁) zeroFoldRoot zeroChain one_pos zeroChain_pos
      (1 / 2) half_pos half_le_one junkCommitment dom₁ 1 q₁
      zeroDesignations := by
  rintro ⟨rbr, hattr⟩
  have hδ : (1 / 4 : ℝ) ∈ Set.Ioo 0 (1 / 2) := by norm_num
  have halive : rbr.kstate.state (1 / 4 : ℝ) junkStmt
      (Transcript.ofFull junkMsgs junkChallenges) (fun _ => 0) = true := by
    apply (rbr.kstate.full_iff (1 / 4 : ℝ) hδ junkStmt junkMsgs
      junkChallenges (fun _ => 0)).2
    exact ⟨_, _, junk_linked_accepts, junk_target_relaxed⟩
  have hroots := hattr (1 / 4 : ℝ) hδ junkStmt
    (Transcript.ofFull junkMsgs junkChallenges) (fun _ => 0) halive
  have hmem : (junkMsg, (0 : F₅)) ∈
      (Transcript.ofFull junkMsgs junkChallenges).rounds := by
    rw [Transcript.ofFull]
    rw [List.mem_ofFn]
    exact ⟨0, rfl⟩
  exact junkRoot_not_in_range (hroots (junkMsg, 0) hmem)

end OracleLogLinkedSubUdCounterexample

/-! ## Positive tooth: the transport fires inside the hiding window -/

namespace OracleLogLinkedSubUdExample

open RSExample AccExample LCExample ZkHidingExample ZkArgumentExample
  ZkExtractionExample CommitExample AccRbrBcsShiftedExample
  AccExtractChainExample

/-- At `t = 1 < d = 2`, where constrained-mask hiding actually holds, the
root-word sub-UD increment recovers the existing masked link word exactly.
This is the parameter point the erasure-based linked extractor cannot enter. -/
theorem subUd_root_transport_hiding_F5 :
    MaskedOpeningHiding (constrainedMaskSpace dom₅ 2 pt2) qz (1 : ZMod 5) ∧
      subUdMessageIncrement S₅ dom₅ 2 (1 / 4 : ℝ) (γbase 0)
        (shiftedMsg S₅ qz γbase xWord msEx 0)
        (shiftedMsg S₅ qz γbase xWord msEx 1) = msEx 0 := by
  refine ⟨window_F5.1, ?_⟩
  rw [subUdMessageIncrement_eq S₅ dom₅ 2 (1 / 4 : ℝ) (γbase 0)
    (u := partialFold γbase xWord msEx 0)
    (u' := partialFold γbase xWord msEx 1) rfl rfl]
  change subUdRecover dom₅ 2 (1 / 4 : ℝ)
    ((γbase 0)⁻¹ •
      (partialFold γbase xWord msEx 1 - partialFold γbase xWord msEx 0)) = msEx 0
  have hinc : (γbase 0)⁻¹ •
      (partialFold γbase xWord msEx 1 - partialFold γbase xWord msEx 0) =
        msEx 0 := by
    simpa using seam_increment γbase xWord msEx (0 : Fin 2) (by decide)
  rw [hinc]
  exact subUdRecover_codeword dom₅ (by norm_num)
    (by norm_num [Fintype.card_fin]) (msEx_mem 0)

end OracleLogLinkedSubUdExample

/-- info: 'Minidregg.Selvage.committedWord?_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms committedWord?_eq_some_iff
/-- info: 'Minidregg.Selvage.linkedErasureRegime_excludes_constrainedMaskHiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkedErasureRegime_excludes_constrainedMaskHiding
/-- info: 'Minidregg.Selvage.attributedIncrement_eq_at_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attributedIncrement_eq_at_query
/-- info: 'Minidregg.Selvage.attributedIncrement_agreesOn_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attributedIncrement_agreesOn_queries
/-- info: 'Minidregg.Selvage.subUdMessageIncrement_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms subUdMessageIncrement_pinned
/-- info: 'Minidregg.Selvage.linkedSubUdLogExtractor_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkedSubUdLogExtractor_pinned
/-- info: 'Minidregg.Selvage.OracleLogLinkedSubUdCounterexample.colsOpen_not_root_attributed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedSubUdCounterexample.colsOpen_not_root_attributed
/-- info: 'Minidregg.Selvage.OracleLogLinkedSubUdCounterexample.linkedRootAttributedRbrTarget_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedSubUdCounterexample.linkedRootAttributedRbrTarget_false
/-- info: 'Minidregg.Selvage.OracleLogLinkedSubUdExample.subUd_root_transport_hiding_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedSubUdExample.subUd_root_transport_hiding_F5

end Minidregg.Selvage
