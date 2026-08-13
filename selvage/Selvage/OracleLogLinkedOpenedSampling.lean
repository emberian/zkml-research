/-
# Explicit root preimages and the sampled sub-UD OracleLog seam

This module removes the noncomputable root decoder from the deployed message
interface.  Every fold-root message carries a checked preimage opening, and
the verifier returns the word in the final opening.  The remaining column
sampling step is separated at its exact boundary: fixed committed words must
be sampled independently after commitment.  Its failure probability is the
landed `(1 - radius)^t` bound; the deterministic OracleLog-to-sub-UD transport
is closed below without `d ≤ t`.
-/
import Selvage.OracleLogLinkedAttributed
import Selvage.JohnsonRegime

namespace Minidregg.Selvage

/-! ## Executable root-preimage openings -/

section PreimageScheme

variable {Root F ι Op : Type}

/-- A deployed root-preimage interface.  `Opening` is explicit proof data;
`word` extracts its claimed whole word, while `check` is the executable
verification step.  Soundness is precisely the commitment/CR premise needed
below. -/
structure RootPreimageScheme (S : BindingCommitment Root F ι Op) where
  Opening : Type
  word : Opening → ι → F
  prove : (ι → F) → Opening
  word_prove : ∀ w, word (prove w) = w
  check : Root → Opening → Bool
  check_prove : ∀ w, check (S.commit w) (prove w) = true
  check_sound : ∀ rt pf, check rt pf = true → rt = S.commit (word pf)

/-- A message carries the ordinary root/column openings and an explicit
whole-root preimage opening. -/
structure PreimageBcsMsg (S : BindingCommitment Root F ι Op)
    (V : RootPreimageScheme S) (t : ℕ) where
  base : BcsMsg Root F Op t
  preimage : V.Opening

/-- Equality checking gives the canonical transparent preimage scheme.  A
Merkle deployment may replace this by any proof format satisfying the same
two laws. -/
def directRootPreimageScheme [DecidableEq Root]
    (S : BindingCommitment Root F ι Op) : RootPreimageScheme S where
  Opening := ι → F
  word := id
  prove := id
  word_prove := fun _ => rfl
  check := fun rt w => decide (rt = S.commit w)
  check_prove := by simp
  check_sound := by
    intro rt w h
    simpa using of_decide_eq_true h

end PreimageScheme

/-! ## The explicit-preimage linked reduction -/

section PreimageReduction

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F))
  (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op)
  (V : RootPreimageScheme S)
  (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m)
  (wv : Fin ch.length → Fin m → F)

/-- Honest shifted messages with explicit root-preimage openings. -/
noncomputable def preimageShiftedMsg (γs : ℕ → F) (f₀ : Fin m → F)
    (ms : Fin ch.length → Fin m → F) (c : ℕ) :
    PreimageBcsMsg S V t where
  base := shiftedMsg S q γs f₀ ms c
  preimage := V.prove (partialFold γs f₀ ms c)

open Classical in
/-- The linked verifier with an explicit checked preimage at every live root.
The final output is read directly from the final proof object, never from a
classical root decoder and never by erasure from the sampled columns. -/
@[reducible] noncomputable def accReductionBcsShiftedLinkedPreimage : Reduction :=
  { linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv with
    PMsg := PreimageBcsMsg S V t
    pmsgNonempty := ⟨⟨⟨S.commit 0, fun _ => 0,
      fun j => S.openAt 0 (q j)⟩, V.prove 0⟩⟩
    verify := fun _ A₀ f₀ πs ρs =>
      if (∀ c, V.check (πs c).base.root (πs c).preimage = true) ∧
          (∀ c, ColsOpen S q (πs c).base) ∧
          (∀ j, (πs 0).base.cols j = f₀ (q j)) ∧
          ∀ i : Fin ch.length,
            LinkOpened S q (S.commit (wv i)) (πs i.castSucc).base
              (πs i.succ).base (ρs i.castSucc) then
        some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          V.word (πs (Fin.last ch.length)).preimage)
      else none }

/-- Acceptance exposes every checked whole word, all sampled openings, every
link equation, and the exact final-word output. -/
theorem preimage_verify_accept_data
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (πs : Fin (ch.length + 1) → PreimageBcsMsg S V t)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : (accReductionBcsShiftedLinkedPreimage C foldRoot ch hm hch δs
      hδpos hδone S V dom d q wv).verify () A₀ f₀ πs ρs = some out) :
    out = (aggregate foldRoot
        (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
      V.word (πs (Fin.last ch.length)).preimage) ∧
    (∀ c, (πs c).base.root = S.commit (V.word (πs c).preimage)) ∧
    (∀ c, ColsOpen S q (πs c).base) ∧
    ∀ i : Fin ch.length,
      LinkOpened S q (S.commit (wv i)) (πs i.castSucc).base
        (πs i.succ).base (ρs i.castSucc) := by
  classical
  let hc := (∀ c, V.check (πs c).base.root (πs c).preimage = true) ∧
    (∀ c, ColsOpen S q (πs c).base) ∧
    (∀ j, (πs 0).base.cols j = f₀ (q j)) ∧
    ∀ i : Fin ch.length,
      LinkOpened S q (S.commit (wv i)) (πs i.castSucc).base
        (πs i.succ).base (ρs i.castSucc)
  have hcond : hc := by
    by_contra hn
    change (if hc then _ else none) = some out at hacc
    rw [if_neg hn] at hacc
    simp at hacc
  change (if hc then _ else none) = some out at hacc
  rw [if_pos hcond] at hacc
  refine ⟨(Option.some.inj hacc).symm,
    fun c => V.check_sound _ _ (hcond.1 c), hcond.2.1,
    hcond.2.2.2⟩

/-- Verifier acceptance yields the exact sampled-coordinate agreement for an
explicit pair of consecutive root words. -/
theorem preimage_acceptance_increment_agreesOn_queries
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (πs : Fin (ch.length + 1) → PreimageBcsMsg S V t)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : (accReductionBcsShiftedLinkedPreimage C foldRoot ch hm hch δs
      hδpos hδone S V dom d q wv).verify () A₀ f₀ πs ρs = some out)
    (i : Fin ch.length) (hρ : ρs i.castSucc ≠ 0) :
    AgreesOn (Finset.univ.image q)
      ((ρs i.castSucc)⁻¹ •
        (V.word (πs i.succ).preimage - V.word (πs i.castSucc).preimage))
      (wv i) := by
  obtain ⟨-, hroots, hopens, hlinks⟩ := preimage_verify_accept_data C foldRoot
    ch hm hch δs hδpos hδone S V dom d q wv A₀ f₀ πs ρs hacc
  exact attributedIncrement_agreesOn_queries S q
    (hroots i.castSucc) (hroots i.succ) (hopens i.castSucc) (hopens i.succ)
    hρ (hlinks i)

/-- Completeness at every `d,t`: explicit preimages make neither decoding nor
query-count assumptions necessary for an honest transcript. -/
theorem preimage_verify_honest
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (ms : Fin ch.length → Fin m → F)
    (ρs : Fin (ch.length + 1) → F) :
    (accReductionBcsShiftedLinkedPreimage C foldRoot ch hm hch δs hδpos
      hδone S V dom d q ms).verify () A₀ f₀
      (fun c => preimageShiftedMsg (ch := ch) (S := S) (V := V) (q := q)
        (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (c : ℕ)) ρs =
      some (aggregate foldRoot
          (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
        flatFold (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms) := by
  classical
  change (if
      ((∀ c : Fin (ch.length + 1), V.check
          (preimageShiftedMsg (ch := ch) (S := S) (V := V) (q := q)
            (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms
            (c : ℕ)).base.root
          (preimageShiftedMsg (ch := ch) (S := S) (V := V) (q := q)
            (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms
            (c : ℕ)).preimage = true) ∧
        (∀ c : Fin (ch.length + 1), ColsOpen S q
          (preimageShiftedMsg (ch := ch) (S := S) (V := V) (q := q)
            (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms
            (c : ℕ)).base) ∧
        (∀ j, (preimageShiftedMsg (ch := ch) (S := S) (V := V) (q := q)
          (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms 0).base.cols j
            = f₀ (q j)) ∧
        ∀ i : Fin ch.length,
          LinkOpened S q (S.commit (ms i))
            (preimageShiftedMsg (ch := ch) (S := S) (V := V) (q := q)
              (padSched fun k : Fin ch.length => ρs k.castSucc) f₀ ms
              (i : ℕ)).base
            (preimageShiftedMsg (ch := ch) (S := S) (V := V) (q := q)
              (padSched fun k : Fin ch.length => ρs k.castSucc) f₀ ms
              (i.succ : ℕ)).base (ρs i.castSucc)) then
      some (aggregate foldRoot
          (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
        V.word (preimageShiftedMsg (ch := ch) (S := S) (V := V) (q := q)
          (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms
          (Fin.last ch.length : ℕ)).preimage)
    else none) = _
  rw [if_pos]
  · simp only [preimageShiftedMsg, Fin.val_last]
    rw [partialFold_last, V.word_prove]
  · refine ⟨fun c => V.check_prove _, fun c => shiftedMsg_opens S q _ f₀ ms _,
      ?_, ?_⟩
    · intro j
      show partialFold _ f₀ ms 0 (q j) = f₀ (q j)
      rw [partialFold_zero]
    · intro i
      simpa [preimageShiftedMsg] using
        (linkOpened_honest S q
          (padSched fun k : Fin ch.length => ρs k.castSucc) f₀ ms i)

end PreimageReduction

/-! ## Exact sampling boundary -/

section Sampling

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [DecidableEq F]

/-- The global agreement needed by sub-unique decoding. -/
def LargeAgreement (radius : ℝ) (g w : ι → F) : Prop :=
  ∃ A : Finset ι,
    (1 - radius) * (Fintype.card ι : ℝ) ≤ (A.card : ℝ) ∧
    AgreesOn A g w

/-- The precise deterministic premise supplied by a good sampled schedule. -/
def QueryAgreementAmplifies {t : ℕ} (q : Fin t → ι) (radius : ℝ)
    (g w : ι → F) : Prop :=
  AgreesOn (Finset.univ.image q) g w → LargeAgreement radius g w

omit [DecidableEq ι] in
/-- Closeness supplies the canonical large agreement set. -/
theorem largeAgreement_of_relDist_le [Nonempty ι] {radius : ℝ}
    {g w : ι → F} (hclose : relDist g w ≤ radius) :
    LargeAgreement radius g w := by
  classical
  refine ⟨Finset.univ.filter fun x => g x = w x,
    card_agreeFilter_ge_of_relDist_le hclose, ?_⟩
  intro x hx
  exact (Finset.mem_filter.mp hx).2

open Classical in
/-- **Exact randomness premise and bound.**  For words fixed before the query
schedule is sampled, the fraction of independent uniform schedules on which
sampled agreement fails to amplify is at most `(1-radius)^t`.  This theorem
does not apply if either word is chosen after seeing `q`; a deployed transcript
must therefore sample `q` after binding the two roots (and use commitment
binding/CR to keep those roots fixed). -/
theorem queryAgreementAmplification_failure_pr [Nonempty ι]
    (t : ℕ) (radius : ℝ) (hradius1 : radius ≤ 1)
    (g w : ι → F) :
    ((Finset.univ.filter fun q : Fin t → ι =>
        ¬ QueryAgreementAmplifies q radius g w).card : ℝ) /
        (Fintype.card ι : ℝ) ^ t ≤ (1 - radius) ^ t := by
  classical
  by_cases hlarge : LargeAgreement radius g w
  · have hempty : (Finset.univ.filter fun q : Fin t → ι =>
        ¬ QueryAgreementAmplifies q radius g w) = ∅ := by
      ext q
      simp [QueryAgreementAmplifies, hlarge]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    exact pow_nonneg (sub_nonneg.mpr hradius1) _
  · have hfar : radius ≤ relDist g w := by
      by_contra hn
      exact hlarge (largeAgreement_of_relDist_le (le_of_lt (lt_of_not_ge hn)))
    have hbridge := column_sampling_bridge_pr (F := F) t hfar
    have heq : (Finset.univ.filter fun q : Fin t → ι =>
        ¬ QueryAgreementAmplifies q radius g w) =
        Finset.univ.filter fun q : Fin t → ι =>
          ∀ j, g (q j) = w (q j) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [QueryAgreementAmplifies, hlarge, AgreesOn]
    rw [heq]
    exact hbridge

end Sampling

/-! ## OracleLog extraction with explicit words -/

section PreimageOracleLog

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F))
  (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op)
  (V : RootPreimageScheme S)
  (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m)
  (wv : Fin ch.length → Fin m → F)

noncomputable abbrev preimageLinkedReduction : Reduction :=
  accReductionBcsShiftedLinkedPreimage C foldRoot ch hm hch δs hδpos hδone
    S V dom d q wv

/-- The aligned statement set for the explicit-preimage reduction. -/
def preimageLinkedStatementSet :
    Set (Stmt (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone
      S V dom d q wv)) :=
  {st | AccClaim.Satisfies C st.x st.y ∧
    ∀ i, LinkAligned C st.x ch i (wv i)}

/-- The real word-resolution OracleLog extractor.  It reads challenges from
the query log and applies sub-UD recovery directly to explicit preimages; no
root decoder and no column erasure occurs. -/
noncomputable def preimageLinkedSubUdLogExtractor (decodeRadius : ℝ) (s : ℕ) :
    StraightlineOracleExtractor
      (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V dom d q
        wv) s :=
  fun o L i =>
    match L.answerOf (o.query i.castSucc) with
    | none => 0
    | some ρ => subUdRecover dom d decodeRadius
        (ρ⁻¹ • (V.word (o.πs i.succ).preimage -
          V.word (o.πs i.castSucc).preimage))

/-- FS acceptance exposes the same checked preimages and sampled-coordinate
equations as interactive acceptance. -/
theorem preimage_fiatShamir_accept_data {s : ℕ}
    (o : SrOutput
      (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V dom d q
        wv) s)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : fiatShamir
      (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V dom d q
        wv) s (fsOracle o ρs) o = some out) :
    out = (aggregate foldRoot
        (padSched fun i : Fin ch.length => ρs i.castSucc) o.stmt.x ch,
      V.word (o.πs (Fin.last ch.length)).preimage) ∧
    (∀ c, (o.πs c).base.root = S.commit (V.word (o.πs c).preimage)) ∧
    (∀ c, ColsOpen S q (o.πs c).base) ∧
    ∀ i : Fin ch.length,
      LinkOpened S q (S.commit (wv i)) (o.πs i.castSucc).base
        (o.πs i.succ).base (ρs i.castSucc) := by
  rw [fiatShamir_fsOracle] at hacc
  exact preimage_verify_accept_data C foldRoot ch hm hch δs hδpos hδone S V
    dom d q wv o.stmt.x o.stmt.y o.πs ρs hacc

/-- **The deterministic soundness seam, closed.**  A logged nonzero challenge,
FS acceptance, and the good sampling implication force the explicit-word
sub-UD extractor to the designated link word.  There is no `d ≤ t` premise. -/
theorem preimage_hitLogExtractor_pinned [Nonempty (Fin m)]
    {decodeRadius : ℝ}
    (hUD : decodeRadius <
      (1 - ((d : ℝ) - 1) / (Fintype.card (Fin m) : ℝ)) / 2)
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    {s tq : ℕ}
    (P : SrProver
      (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V dom d q
        wv) s)
    (coins : Fin tq → F) (fallback : Fin (ch.length + 1) → F)
    (i : Fin ch.length) {ρ : F}
    (hans : OracleLog.answerOf (srTrace P coins)
      ((srOut P coins).query i.castSucc) = some ρ)
    (hρ : ρ ≠ 0)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : fiatShamir
      (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V dom d q
        wv) s
      (fsOracle (srOut P coins) (srFinalChal P coins fallback))
      (srOut P coins) = some out)
    (hsample : QueryAgreementAmplifies q decodeRadius
      (ρ⁻¹ • (V.word ((srOut P coins).πs i.succ).preimage -
        V.word ((srOut P coins).πs i.castSucc).preimage)) (wv i)) :
    preimageLinkedSubUdLogExtractor C foldRoot ch hm hch δs hδpos hδone S V
      dom d q wv decodeRadius s (srOut P coins) (srTrace P coins) i = wv i := by
  have hchal : srFinalChal P coins fallback i.castSucc = ρ := by
    rw [srFinalChal_eq_answerOf, hans]
    rfl
  have hdata := preimage_fiatShamir_accept_data C foldRoot ch hm hch δs hδpos
    hδone S V dom d q wv (srOut P coins) (srFinalChal P coins fallback) hacc
  have hquery : AgreesOn (Finset.univ.image q)
      (ρ⁻¹ • (V.word ((srOut P coins).πs i.succ).preimage -
        V.word ((srOut P coins).πs i.castSucc).preimage)) (wv i) := by
    exact attributedIncrement_agreesOn_queries S q
      (hdata.2.1 i.castSucc) (hdata.2.1 i.succ)
      (hdata.2.2.1 i.castSucc) (hdata.2.2.1 i.succ) hρ (by
        simpa [hchal] using hdata.2.2.2 i)
  obtain ⟨A, hcard, hagrees⟩ := hsample hquery
  unfold preimageLinkedSubUdLogExtractor
  rw [hans]
  exact subUdRecover_sound dom hUD (hwv i) hcard hagrees

/-- If every designated prefix was logged at a nonzero answer and every fixed
root pair received a good post-commitment query schedule, the OracleLog
extractor is a genuine source witness.  This is the deterministic RBR
soundness conclusion; fresh-log horns, zero challenges, and sampling failures
are exactly the three events a probabilistic assembly must price. -/
theorem preimage_oracleLog_source_relaxed [Nonempty (Fin m)]
    {decodeRadius : ℝ}
    (hUD : decodeRadius <
      (1 - ((d : ℝ) - 1) / (Fintype.card (Fin m) : ℝ)) / 2)
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    {s tq : ℕ}
    (P : SrProver
      (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V dom d q
        wv) s)
    (coins : Fin tq → F) (fallback : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : fiatShamir
      (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V dom d q
        wv) s
      (fsOracle (srOut P coins) (srFinalChal P coins fallback))
      (srOut P coins) = some out)
    (hst : (srOut P coins).stmt ∈
      preimageLinkedStatementSet C foldRoot ch hm hch δs hδpos hδone S V dom d q
        wv)
    (hhit : ∀ i : Fin ch.length, ∃ ρ : F,
      OracleLog.answerOf (srTrace P coins)
          ((srOut P coins).query i.castSucc) = some ρ ∧
      ρ ≠ 0 ∧
      QueryAgreementAmplifies q decodeRadius
        (ρ⁻¹ • (V.word ((srOut P coins).πs i.succ).preimage -
          V.word ((srOut P coins).πs i.castSucc).preimage)) (wv i))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    RelaxedMem
      (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V dom d q
        wv).R δ (srOut P coins).stmt.idx (srOut P coins).stmt.x
      (srOut P coins).stmt.y
      (preimageLinkedSubUdLogExtractor C foldRoot ch hm hch δs hδpos hδone S V
        dom d q wv decodeRadius s (srOut P coins) (srTrace P coins)) := by
  have hextract : preimageLinkedSubUdLogExtractor C foldRoot ch hm hch δs
      hδpos hδone S V dom d q wv decodeRadius s (srOut P coins)
      (srTrace P coins) = wv := by
    funext i
    obtain ⟨ρ, hans, hρ, hsample⟩ := hhit i
    exact preimage_hitLogExtractor_pinned C foldRoot ch hm hch δs hδpos hδone
      S V dom d q wv hUD hwv P coins fallback i hans hρ hacc hsample
  rw [hextract]
  refine ⟨(srOut P coins).stmt.y, ?_, ?_⟩
  · exact ⟨hst.1, hst.2⟩
  · rw [fracHamming_self]
    exact hδ

end PreimageOracleLog

/-- info: 'Minidregg.Selvage.RootPreimageScheme.check_sound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms RootPreimageScheme.check_sound
/-- info: 'Minidregg.Selvage.preimage_verify_accept_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preimage_verify_accept_data
/-- info: 'Minidregg.Selvage.preimage_verify_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preimage_verify_honest
/-- info: 'Minidregg.Selvage.queryAgreementAmplification_failure_pr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms queryAgreementAmplification_failure_pr
/-- info: 'Minidregg.Selvage.preimage_hitLogExtractor_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preimage_hitLogExtractor_pinned
/-- info: 'Minidregg.Selvage.preimage_oracleLog_source_relaxed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preimage_oracleLog_source_relaxed

end Minidregg.Selvage
