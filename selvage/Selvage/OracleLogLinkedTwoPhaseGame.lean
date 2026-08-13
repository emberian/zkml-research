/-
# Two-phase root/query/response game for linked sub-UD

This module compiles the roots-before-queries interface into `Reduction` and
the landed OracleLog/Fiat--Shamir machinery.  An extra response round is
load-bearing: the challenge after the final frozen root supplies the query
schedule, then the prover sends all columns/paths, then an inert challenge
closes the uniform alternating transcript.
-/
import Selvage.OracleLogLinkedTwoPhase

namespace Minidregg.Selvage

/-! ## A query sampler and the staged message alphabet -/

structure TwoPhaseQuerySampler (m t : ℕ) where
  Query : Type
  queryFintype : Fintype Query
  queryNonempty : Nonempty Query
  schedule : Query → Fin t → Fin m

instance (Q : TwoPhaseQuerySampler m t) : Fintype Q.Query := Q.queryFintype
instance (Q : TwoPhaseQuerySampler m t) : Nonempty Q.Query := Q.queryNonempty

/-- One uniform message type serves both stages.  Root rounds use `root` and
`preimage`; the single response round uses `cols` and `ops`.  `isResponse`
is checked, so no response is accepted before the query challenge. -/
structure TwoPhaseGameMsg {Root F Op : Type} {m : ℕ}
    (S : BindingCommitment Root F (Fin m) Op) (V : RootPreimageScheme S)
    (rootCount t : ℕ) (Query : Type) where
  isResponse : Bool
  root : Root
  preimage : V.Opening
  /-- The response echoes the already-sampled query.  This is redundant for
  verification, but load-bearing for a log-only extractor on the fresh-query
  horn: the accepted transcript itself still names the schedule even when the
  ROM query was absent from the bounded log. -/
  claimedQuery : Query
  cols : Fin rootCount → Fin t → F
  ops : Fin rootCount → Fin t → Op

section Slots

variable {n : ℕ}

/-- Root `c` is prover message slot `c` in the `n+2`-round transcript. -/
def twoPhaseRootSlot (c : Fin (n + 1)) : Fin (n + 2) := c.castSucc

/-- Fold challenge `i` follows root `i`. -/
def twoPhaseFoldSlot (i : Fin n) : Fin (n + 2) := i.castSucc.castSucc

/-- The query schedule follows the final root, at challenge slot `n`. -/
def twoPhaseQuerySlot : Fin (n + 2) := (Fin.last n).castSucc

/-- The response occupies the last prover-message slot; its following
challenge is inert padding required by `Reduction`'s alternation. -/
def twoPhaseResponseSlot : Fin (n + 2) := Fin.last (n + 1)

theorem twoPhase_foldSlot_lt_querySlot (i : Fin n) :
    twoPhaseFoldSlot i < twoPhaseQuerySlot := by
  simp [twoPhaseFoldSlot, twoPhaseQuerySlot]

theorem twoPhase_querySlot_lt_responseSlot :
    (twoPhaseQuerySlot : Fin (n + 2)) < twoPhaseResponseSlot := by
  simp [twoPhaseQuerySlot, twoPhaseResponseSlot]

/-- The FS/ROM keys are domain-separated by distinct transcript-prefix
lengths: the schedule query cannot alias any algebra-challenge query. -/
theorem twoPhase_query_domainSeparated {r : Reduction} {s : ℕ}
    (o : SrOutput r s) (hk : r.k = n + 2) (i : Fin n) :
    o.query (Fin.cast hk.symm twoPhaseQuerySlot) ≠
      o.query (Fin.cast hk.symm (twoPhaseFoldSlot i)) := by
  intro heq
  have hi := o.query_injective heq
  have hv := congrArg Fin.val hi
  simp [twoPhaseQuerySlot, twoPhaseFoldSlot] at hv
  omega

end Slots

/-! ## Compilation to `Reduction` -/

section Reduction

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F))
  (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op)
  (V : RootPreimageScheme S)
  (dom : Fin m ↪ F) (d : ℕ)
  (Q : TwoPhaseQuerySampler m t)
  (wv : Fin ch.length → Fin m → F)

abbrev TwoPhaseChal := F × Q.Query
abbrev TwoPhaseMsg :=
  TwoPhaseGameMsg S V (ch.length + 1) t Q.Query

/-- The algebra challenge vector read by the linked verifier.  The first
`ch.length` challenges are the field components of the root rounds; the last
coordinate is inert zero. -/
def twoPhaseAlgebraChallenges
    (ρs : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q) :
    Fin (ch.length + 1) → F :=
  fun c => padSched
    (fun i : Fin ch.length => (ρs (twoPhaseFoldSlot i)).1) (c : ℕ)

/-- The query schedule is exactly the query component sampled after the final
root message. -/
def twoPhaseSampledSchedule
    (ρs : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q) : Fin t → Fin m :=
  Q.schedule (ρs twoPhaseQuerySlot).2

/-- Build the ordinary preimage messages from frozen root slots and the one
post-query response slot. -/
def twoPhaseAssembledMessages
    (πs : Fin (ch.length + 2) →
      TwoPhaseMsg (ch := ch) (S := S) (V := V) (t := t) (Q := Q)) :
    Fin (ch.length + 1) →
      PreimageBcsMsg S V t :=
  fun c =>
    { base :=
        { root := (πs (twoPhaseRootSlot c)).root
          cols := (πs twoPhaseResponseSlot).cols c
          ops := (πs twoPhaseResponseSlot).ops c }
      preimage := (πs (twoPhaseRootSlot c)).preimage }

/-- The phase tag discipline enforced by the verifier. -/
def TwoPhaseShape
    (πs : Fin (ch.length + 2) →
      TwoPhaseMsg (ch := ch) (S := S) (V := V) (t := t) (Q := Q)) : Prop :=
  (∀ c : Fin (ch.length + 1),
      (πs (twoPhaseRootSlot c)).isResponse = false) ∧
    (πs twoPhaseResponseSlot).isResponse = true

/-- The post-query response is bound to the designated domain-separated
challenge, rather than being free to claim a different schedule. -/
def TwoPhaseQueryBound
    (πs : Fin (ch.length + 2) →
      TwoPhaseMsg (ch := ch) (S := S) (V := V) (t := t) (Q := Q))
    (ρs : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q) : Prop :=
  (πs twoPhaseResponseSlot).claimedQuery = (ρs twoPhaseQuerySlot).2

open Classical in
/-- The compiled two-phase reduction.  Its source/target relations are the
linked accumulator relations.  Only transcript staging and the challenge
alphabet change. -/
noncomputable def accReductionBcsShiftedLinkedTwoPhase : Reduction := by
  let q₀ : Fin t → Fin m := Q.schedule (Classical.arbitrary Q.Query)
  let base := preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone
    S V dom d q₀ wv
  exact
    { base with
      k := ch.length + 2
      k_pos := by omega
      PMsg := TwoPhaseMsg (ch := ch) (S := S) (V := V) (t := t) (Q := Q)
      Chal := TwoPhaseChal (F := F) Q
      pmsgNonempty := ⟨
        { isResponse := false
          root := S.commit 0
          preimage := V.prove 0
          claimedQuery := Classical.arbitrary Q.Query
          cols := fun _ _ => 0
          ops := fun _ _ => S.openAt 0 ⟨0, hm⟩ }⟩
      chalFintype := inferInstance
      chalNonempty := inferInstance
      verify := fun idx A₀ f₀ πs ρs =>
        if TwoPhaseShape (ch := ch) (S := S) (V := V) (Q := Q) πs ∧
            TwoPhaseQueryBound (ch := ch) (S := S) (V := V) (Q := Q) πs ρs
        then
          (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V
            dom d (twoPhaseSampledSchedule ch Q ρs) wv).verify idx A₀ f₀
              (twoPhaseAssembledMessages (ch := ch) (S := S) (V := V)
                (Q := Q) πs)
              (twoPhaseAlgebraChallenges ch Q ρs)
        else none }

noncomputable abbrev twoPhaseReduction : Reduction :=
  accReductionBcsShiftedLinkedTwoPhase (C := C) (foldRoot := foldRoot)
    (ch := ch) (hm := hm) (hch := hch) (δs := δs) (hδpos := hδpos)
    (hδone := hδone) (S := S) (V := V) (dom := dom) (d := d) (Q := Q)
    (wv := wv)

/-- Successful compiled verification exposes phase correctness and acceptance
by the already-proved explicit-preimage verifier at the post-root schedule. -/
theorem twoPhase_verify_strengthens
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (πs : Fin (ch.length + 2) →
      TwoPhaseMsg (ch := ch) (S := S) (V := V) (t := t) (Q := Q))
    (ρs : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : (twoPhaseReduction (C := C) (foldRoot := foldRoot) (ch := ch)
      (hm := hm) (hch := hch) (δs := δs) (hδpos := hδpos)
      (hδone := hδone) (S := S) (V := V) (dom := dom) (d := d)
      (Q := Q) (wv := wv)).verify () A₀ f₀ πs ρs = some out) :
    TwoPhaseShape (ch := ch) (S := S) (V := V) (Q := Q) πs ∧
    TwoPhaseQueryBound (ch := ch) (S := S) (V := V) (Q := Q) πs ρs ∧
    (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V dom d
      (twoPhaseSampledSchedule ch Q ρs) wv).verify () A₀ f₀
        (twoPhaseAssembledMessages (ch := ch) (S := S) (V := V) (Q := Q) πs)
        (twoPhaseAlgebraChallenges ch Q ρs) = some out := by
  classical
  by_cases hs : TwoPhaseShape (ch := ch) (S := S) (V := V) (Q := Q) πs ∧
      TwoPhaseQueryBound (ch := ch) (S := S) (V := V) (Q := Q) πs ρs
  · exact ⟨hs.1, hs.2,
      by simpa [accReductionBcsShiftedLinkedTwoPhase, hs] using hacc⟩
  · simp [accReductionBcsShiftedLinkedTwoPhase, hs] at hacc

end Reduction

/-! ## OracleLog extractor at the staged reduction -/

section LogExtractor

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F))
  (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op)
  (V : RootPreimageScheme S)
  (dom : Fin m ↪ F) (d : ℕ)
  (Q : TwoPhaseQuerySampler m t)
  (wv : Fin ch.length → Fin m → F)

/-- The staged log extractor reads only algebra challenges.  Query-schedule
randomness is consumed by verification/sampling, not as a fold scalar. -/
noncomputable def twoPhaseSubUdLogExtractor (decodeRadius : ℝ) (s : ℕ) :
    StraightlineOracleExtractor
      (twoPhaseReduction (C := C) (foldRoot := foldRoot) (ch := ch) (hm := hm)
        (hch := hch) (δs := δs) (hδpos := hδpos) (hδone := hδone)
        (S := S) (V := V) (dom := dom) (d := d) (Q := Q) (wv := wv)) s :=
  fun o L i =>
    match L.answerOf (o.query (twoPhaseFoldSlot i)) with
    | none => 0
    | some ρ => subUdRecover dom d decodeRadius
        (ρ.1⁻¹ •
          (V.word (o.πs (twoPhaseRootSlot i.succ)).preimage -
            V.word (o.πs (twoPhaseRootSlot i.castSucc)).preimage))

/-- FS acceptance at the staged reduction exposes all data checked by the
ordinary preimage verifier. -/
theorem twoPhase_fiatShamir_accept_data {s : ℕ}
    (o : SrOutput
      (twoPhaseReduction (C := C) (foldRoot := foldRoot) (ch := ch) (hm := hm)
        (hch := hch) (δs := δs) (hδpos := hδpos) (hδone := hδone)
        (S := S) (V := V) (dom := dom) (d := d) (Q := Q) (wv := wv)) s)
    (ρs : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : fiatShamir
      (twoPhaseReduction (C := C) (foldRoot := foldRoot) (ch := ch) (hm := hm)
        (hch := hch) (δs := δs) (hδpos := hδpos) (hδone := hδone)
        (S := S) (V := V) (dom := dom) (d := d) (Q := Q) (wv := wv)) s
      (fsOracle o ρs) o = some out) :
    TwoPhaseShape (ch := ch) (S := S) (V := V) (Q := Q) o.πs ∧
    TwoPhaseQueryBound (ch := ch) (S := S) (V := V) (Q := Q) o.πs ρs ∧
    out = (aggregate foldRoot
        (padSched fun i : Fin ch.length =>
          (twoPhaseAlgebraChallenges ch Q ρs) i.castSucc) o.stmt.x ch,
      V.word (o.πs (twoPhaseRootSlot (Fin.last ch.length))).preimage) ∧
    (∀ c : Fin (ch.length + 1),
      (o.πs (twoPhaseRootSlot c)).root =
        S.commit (V.word (o.πs (twoPhaseRootSlot c)).preimage)) ∧
    (∀ c, ColsOpen S (twoPhaseSampledSchedule ch Q ρs)
      (twoPhaseAssembledMessages (ch := ch) (S := S) (V := V) (Q := Q)
        o.πs c).base) ∧
    ∀ i : Fin ch.length,
      LinkOpened S (twoPhaseSampledSchedule ch Q ρs) (S.commit (wv i))
        (twoPhaseAssembledMessages (ch := ch) (S := S) (V := V) (Q := Q)
          o.πs i.castSucc).base
        (twoPhaseAssembledMessages (ch := ch) (S := S) (V := V) (Q := Q)
          o.πs i.succ).base
        ((twoPhaseAlgebraChallenges ch Q ρs) i.castSucc) := by
  rw [fiatShamir_fsOracle] at hacc
  obtain ⟨hshape, hbound, hbase⟩ := twoPhase_verify_strengthens C foldRoot ch hm hch δs
    hδpos hδone S V dom d Q wv o.stmt.x o.stmt.y o.πs ρs hacc
  have hdata := preimage_verify_accept_data C foldRoot ch hm hch δs hδpos hδone
    S V dom d (twoPhaseSampledSchedule ch Q ρs) wv o.stmt.x o.stmt.y
    (twoPhaseAssembledMessages (ch := ch) (S := S) (V := V) (Q := Q) o.πs)
    (twoPhaseAlgebraChallenges ch Q ρs) hbase
  exact ⟨hshape, hbound, hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2⟩

/-- A logged nonzero algebra challenge plus a good post-root sample pins the
staged OracleLog extractor exactly. -/
theorem twoPhaseGame_hitLogExtractor_pinned [Nonempty (Fin m)]
    {decodeRadius : ℝ}
    (hUD : decodeRadius <
      (1 - ((d : ℝ) - 1) / (Fintype.card (Fin m) : ℝ)) / 2)
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    {s tq : ℕ}
    (P : SrProver
      (twoPhaseReduction (C := C) (foldRoot := foldRoot) (ch := ch) (hm := hm)
        (hch := hch) (δs := δs) (hδpos := hδpos) (hδone := hδone)
        (S := S) (V := V) (dom := dom) (d := d) (Q := Q) (wv := wv)) s)
    (coins : Fin tq → TwoPhaseChal (F := F) Q)
    (fallback : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)
    (i : Fin ch.length) {ρ : TwoPhaseChal (F := F) Q}
    (hans : OracleLog.answerOf (srTrace P coins)
      ((srOut P coins).query (twoPhaseFoldSlot i)) = some ρ)
    (hρ : ρ.1 ≠ 0)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : fiatShamir
      (twoPhaseReduction (C := C) (foldRoot := foldRoot) (ch := ch) (hm := hm)
        (hch := hch) (δs := δs) (hδpos := hδpos) (hδone := hδone)
        (S := S) (V := V) (dom := dom) (d := d) (Q := Q) (wv := wv)) s
      (fsOracle (srOut P coins) (srFinalChal P coins fallback))
      (srOut P coins) = some out)
    (hsample : QueryAgreementAmplifies
      (twoPhaseSampledSchedule ch Q (srFinalChal P coins fallback)) decodeRadius
      (ρ.1⁻¹ •
        (V.word ((srOut P coins).πs (twoPhaseRootSlot i.succ)).preimage -
          V.word ((srOut P coins).πs
            (twoPhaseRootSlot i.castSucc)).preimage)) (wv i)) :
    twoPhaseSubUdLogExtractor (C := C) (foldRoot := foldRoot) (ch := ch)
      (hm := hm) (hch := hch) (δs := δs) (hδpos := hδpos)
      (hδone := hδone) (S := S) (V := V) (dom := dom) (d := d) (Q := Q)
      (wv := wv) decodeRadius s (srOut P coins) (srTrace P coins) i = wv i := by
  let ρs := srFinalChal P coins fallback
  have hchal : ρs (twoPhaseFoldSlot i) = ρ := by
    dsimp [ρs]
    rw [srFinalChal_eq_answerOf, hans]
    rfl
  have hdata := twoPhase_fiatShamir_accept_data C foldRoot ch hm hch δs hδpos
    hδone S V dom d Q wv (srOut P coins) ρs hacc
  have halg : (twoPhaseAlgebraChallenges ch Q ρs) i.castSucc = ρ.1 := by
    unfold twoPhaseAlgebraChallenges
    change padSched (fun j : Fin ch.length => (ρs (twoPhaseFoldSlot j)).1)
      (i : ℕ) = ρ.1
    rw [padSched_lt _ i.isLt]
    exact congrArg Prod.fst hchal
  have hquery : AgreesOn
      (Finset.univ.image (twoPhaseSampledSchedule ch Q ρs))
      (ρ.1⁻¹ •
        (V.word ((srOut P coins).πs (twoPhaseRootSlot i.succ)).preimage -
          V.word ((srOut P coins).πs
            (twoPhaseRootSlot i.castSucc)).preimage)) (wv i) := by
    exact attributedIncrement_agreesOn_queries S
      (twoPhaseSampledSchedule ch Q ρs)
      (hdata.2.2.2.1 i.castSucc) (hdata.2.2.2.1 i.succ)
      (hdata.2.2.2.2.1 i.castSucc) (hdata.2.2.2.2.1 i.succ) hρ (by
        simpa [halg, twoPhaseAssembledMessages] using hdata.2.2.2.2.2 i)
  obtain ⟨A, hcard, hagrees⟩ := hsample hquery
  unfold twoPhaseSubUdLogExtractor
  rw [hans]
  exact subUdRecover_sound dom hUD (hwv i) hcard hagrees

end LogExtractor

/-! ## Exact combined-error interface -/

section ErrorComposition

variable {Omega : Type} [Fintype Omega]

/-- The five disjointly-priced causes retained by the staged game.  `cr` and
`zk` are explicit computational premises; transparent direct preimages do not
discharge either one. -/
def TwoPhaseCombinedBad (fresh hitZero sampling cr zk : Omega → Prop)
    (coins : Omega) : Prop :=
  fresh coins ∨ hitZero coins ∨ sampling coins ∨ cr coins ∨ zk coins

/-- Sharp additive composition of fresh-link, hit/zero, schedule sampling,
commitment/preimage soundness, and ZK simulation errors. -/
theorem twoPhaseCombinedBad_le
    (fresh hitZero sampling cr zk : Omega → Prop)
    {εfresh εhitZero εsampling εcr εzk : ℝ}
    (hfresh : uniformProb Omega fresh ≤ εfresh)
    (hhit : uniformProb Omega hitZero ≤ εhitZero)
    (hsampling : uniformProb Omega sampling ≤ εsampling)
    (hcr : uniformProb Omega cr ≤ εcr)
    (hzk : uniformProb Omega zk ≤ εzk) :
    uniformProb Omega (TwoPhaseCombinedBad fresh hitZero sampling cr zk) ≤
      εfresh + εhitZero + εsampling + εcr + εzk := by
  have h₁ := uniformProb_or_le fresh (fun c =>
    hitZero c ∨ sampling c ∨ cr c ∨ zk c)
  have h₂ := uniformProb_or_le hitZero (fun c => sampling c ∨ cr c ∨ zk c)
  have h₃ := uniformProb_or_le sampling (fun c => cr c ∨ zk c)
  have h₄ := uniformProb_or_le cr zk
  unfold TwoPhaseCombinedBad
  linarith

/-- Smallest exact shared-ROM game interface.  The event cover is the only
game-specific obligation; the five bounds remain independently replaceable
by the landed fresh/hit horns, full-domain or allowed-coordinate sampling,
commitment soundness, and ZK simulation theorems. -/
structure TwoPhaseFsErrorInterface (soundFailure : Omega → Prop)
    (εfresh εhitZero εsampling εcr εzk : ℝ) where
  fresh : Omega → Prop
  hitZero : Omega → Prop
  sampling : Omega → Prop
  cr : Omega → Prop
  zk : Omega → Prop
  cover : ∀ c, soundFailure c →
    TwoPhaseCombinedBad fresh hitZero sampling cr zk c
  fresh_le : uniformProb Omega fresh ≤ εfresh
  hitZero_le : uniformProb Omega hitZero ≤ εhitZero
  sampling_le : uniformProb Omega sampling ≤ εsampling
  cr_le : uniformProb Omega cr ≤ εcr
  zk_le : uniformProb Omega zk ≤ εzk

theorem TwoPhaseFsErrorInterface.sound_le
    {soundFailure : Omega → Prop}
    {εfresh εhitZero εsampling εcr εzk : ℝ}
    (I : TwoPhaseFsErrorInterface soundFailure
      εfresh εhitZero εsampling εcr εzk) :
    uniformProb Omega soundFailure ≤
      εfresh + εhitZero + εsampling + εcr + εzk :=
  le_trans (uniformProb_mono I.cover)
    (twoPhaseCombinedBad_le I.fresh I.hitZero I.sampling I.cr I.zk
      I.fresh_le I.hitZero_le I.sampling_le I.cr_le I.zk_le)

/-- Full-domain IID headline.  The first two premises are precisely the
landed fresh-link and logged-hit/zero horns at the staged game.  Sampling is
multiplied by `tq + 1`: at most `tq` logged frozen-root candidates plus the
single fresh fallback schedule. -/
theorem twoPhaseCombined_fullDomain_rate
    {F : Type} [Fintype F]
    (fresh hitZero sampling cr zk : Omega → Prop)
    (n tq t : ℕ) (radius : ℝ) (εcr εzk : ℝ)
    (hfresh : uniformProb Omega fresh ≤
      (n : ℝ) / (Fintype.card F : ℝ))
    (hhitZero : uniformProb Omega hitZero ≤
      (tq : ℝ) / (Fintype.card F : ℝ))
    (hsampling : uniformProb Omega sampling ≤
      ((tq : ℝ) + 1) * (n : ℝ) * (1 - radius) ^ t)
    (hcr : uniformProb Omega cr ≤ εcr)
    (hzk : uniformProb Omega zk ≤ εzk) :
    uniformProb Omega (TwoPhaseCombinedBad fresh hitZero sampling cr zk) ≤
      (n : ℝ) / (Fintype.card F : ℝ) +
      (tq : ℝ) / (Fintype.card F : ℝ) +
      ((tq : ℝ) + 1) * (n : ℝ) * (1 - radius) ^ t + εcr + εzk :=
  twoPhaseCombinedBad_le fresh hitZero sampling cr zk
    hfresh hhitZero hsampling hcr hzk

/-- Allowed-coordinate headline.  `allowedMiss` is the per-frozen-vector
sum of the linkwise falling-factorial prices supplied by
`AllowedWithoutReplacementFallingPremise`; the same `tq+1` grinding factor
applies, and no full-domain IID term appears. -/
theorem twoPhaseCombined_allowed_rate
    {F : Type} [Fintype F]
    (fresh hitZero sampling cr zk : Omega → Prop)
    (n tq : ℕ) (allowedMiss εcr εzk : ℝ)
    (hfresh : uniformProb Omega fresh ≤
      (n : ℝ) / (Fintype.card F : ℝ))
    (hhitZero : uniformProb Omega hitZero ≤
      (tq : ℝ) / (Fintype.card F : ℝ))
    (hsampling : uniformProb Omega sampling ≤
      ((tq : ℝ) + 1) * allowedMiss)
    (hcr : uniformProb Omega cr ≤ εcr)
    (hzk : uniformProb Omega zk ≤ εzk) :
    uniformProb Omega (TwoPhaseCombinedBad fresh hitZero sampling cr zk) ≤
      (n : ℝ) / (Fintype.card F : ℝ) +
      (tq : ℝ) / (Fintype.card F : ℝ) +
      ((tq : ℝ) + 1) * allowedMiss + εcr + εzk :=
  twoPhaseCombinedBad_le fresh hitZero sampling cr zk
    hfresh hhitZero hsampling hcr hzk

end ErrorComposition

/-! ## Allowed-coordinate sampling assembly -/

section AllowedAssembly

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [DecidableEq F]

open Classical in
/-- Union bound across frozen links for the constrained-mask schedule.  The
per-link premise is the exact allowed-injection falling-factorial statement,
never the full-domain IID theorem. -/
theorem allowedFrozenLinks_samplingFailure_uniform
    {Root Op : Type} [Field F]
    {n t : ℕ} (S : BindingCommitment Root F ι Op)
    (V : RootPreimageScheme S)
    (frozen : FrozenPreimagePhase S V (k := n + 1))
    (ρs : Fin (n + 1) → F) (wv : Fin n → ι → F)
    (allowed : Finset ι) (radius : ℝ) (agreeCap : Fin n → ℕ)
    (hprem : ∀ i : Fin n, AllowedWithoutReplacementFallingPremise
      allowed t radius
      ((ρs i.castSucc)⁻¹ •
        (V.word (frozen.preimage i.succ) -
          V.word (frozen.preimage i.castSucc))) (wv i) (agreeCap i)) :
    uniformProb (AllowedInjectiveSchedule allowed t) (fun q => ∃ i : Fin n,
      ¬ QueryAgreementAmplifies (allowedSchedule q) radius
        ((ρs i.castSucc)⁻¹ •
          (V.word (frozen.preimage i.succ) -
            V.word (frozen.preimage i.castSucc))) (wv i)) ≤
      ∑ i : Fin n, fallingFactorialMiss (agreeCap i) allowed.card t := by
  refine le_trans (uniformProb_exists_le (fun i q =>
    ¬ QueryAgreementAmplifies (allowedSchedule q) radius
      ((ρs i.castSucc)⁻¹ •
        (V.word (frozen.preimage i.succ) -
          V.word (frozen.preimage i.castSucc))) (wv i))) ?_
  exact Finset.sum_le_sum fun i _ => (hprem i).failure_bound

end AllowedAssembly

/-- info: 'Minidregg.Selvage.twoPhase_query_domainSeparated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhase_query_domainSeparated
/-- info: 'Minidregg.Selvage.twoPhase_verify_strengthens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhase_verify_strengthens
/-- info: 'Minidregg.Selvage.twoPhase_fiatShamir_accept_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhase_fiatShamir_accept_data
/-- info: 'Minidregg.Selvage.twoPhaseGame_hitLogExtractor_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhaseGame_hitLogExtractor_pinned
/-- info: 'Minidregg.Selvage.twoPhaseCombinedBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhaseCombinedBad_le
/-- info: 'Minidregg.Selvage.TwoPhaseFsErrorInterface.sound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TwoPhaseFsErrorInterface.sound_le
/-- info: 'Minidregg.Selvage.twoPhaseCombined_fullDomain_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhaseCombined_fullDomain_rate
/-- info: 'Minidregg.Selvage.twoPhaseCombined_allowed_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhaseCombined_allowed_rate
/-- info: 'Minidregg.Selvage.allowedFrozenLinks_samplingFailure_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allowedFrozenLinks_samplingFailure_uniform

end Minidregg.Selvage
