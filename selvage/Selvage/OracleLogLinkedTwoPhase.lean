/-
# Roots-before-queries transcript for linked sub-UD extraction

The frozen phase below contains every root and checked preimage proof but no
query-dependent column data.  A query schedule is sampled only after that
value exists; the response phase is then indexed by both the frozen phase and
the schedule.  This is the ordering required by the fixed-word sampling
theorem.
-/
import Selvage.OracleLogLinkedOpenedSampling

namespace Minidregg.Selvage

/-! ## Two-phase transcript types -/

section Transcript

variable {Root F ι Op : Type} {k t : ℕ}
  (S : BindingCommitment Root F ι Op) (V : RootPreimageScheme S)

/-- Phase one: all commitment roots and their abstract preimage proofs are
frozen before any column-query schedule exists. -/
structure FrozenPreimagePhase where
  root : Fin k → Root
  preimage : Fin k → V.Opening

/-- Phase three: columns and paths are supplied only after `q` has been
sampled.  The `frozen` parameter records the transcript dependency/order. -/
structure ColumnResponsePhase (frozen : FrozenPreimagePhase S V (k := k))
    (q : Fin t → ι) where
  cols : Fin k → Fin t → F
  ops : Fin k → Fin t → Op

/-- Assemble the two phases into the explicit-preimage alphabet consumed by
the linked reduction. -/
def assemblePreimageMessages (frozen : FrozenPreimagePhase S V (k := k))
    (q : Fin t → ι)
    (response : ColumnResponsePhase S V (k := k) frozen q) :
    Fin k → PreimageBcsMsg S V t :=
  fun c =>
    { base := ⟨frozen.root c, response.cols c, response.ops c⟩
      preimage := frozen.preimage c }

/-- Transparent direct preimages inhabit the frozen phase.  This is only a
satisfiability tooth; a ZK deployment uses a hiding proof-of-preimage scheme,
not this word-revealing instance. -/
def directFrozenPreimages [DecidableEq Root]
    (words : Fin k → ι → F) :
    FrozenPreimagePhase S (directRootPreimageScheme S) (k := k) where
  root := fun c => S.commit (words c)
  preimage := words

theorem directFrozenPreimages_check [DecidableEq Root]
    (words : Fin k → ι → F) (c : Fin k) :
    (directRootPreimageScheme S).check
      ((directFrozenPreimages S words).root c)
      ((directFrozenPreimages S words).preimage c) = true := by
  simp [directFrozenPreimages, directRootPreimageScheme]

end Transcript

/-! ## Accepted good-sampling transcripts feed sub-UD -/

section AcceptedTransport

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F))
  (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op)
  (V : RootPreimageScheme S)
  (dom : Fin m ↪ F) (d : ℕ)
  (wv : Fin ch.length → Fin m → F)

/-- Interactive acceptance plus a good post-root sampling schedule pins one
explicit normalized increment.  This is the two-phase form of the exact
premise consumed by `subUdRecover_sound`; it has no `d ≤ t`. -/
theorem twoPhase_acceptance_subUd_pinned [Nonempty (Fin m)]
    {decodeRadius : ℝ}
    (hUD : decodeRadius <
      (1 - ((d : ℝ) - 1) / (Fintype.card (Fin m) : ℝ)) / 2)
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    (frozen : FrozenPreimagePhase S V (k := ch.length + 1))
    (q : Fin t → Fin m)
    (response : ColumnResponsePhase S V (k := ch.length + 1) frozen q)
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone
      S V dom d q wv).verify () A₀ f₀
        (assemblePreimageMessages S V frozen q response) ρs = some out)
    (i : Fin ch.length) (hρ : ρs i.castSucc ≠ 0)
    (hsample : QueryAgreementAmplifies q decodeRadius
      ((ρs i.castSucc)⁻¹ •
        (V.word (frozen.preimage i.succ) -
          V.word (frozen.preimage i.castSucc))) (wv i)) :
    subUdRecover dom d decodeRadius
      ((ρs i.castSucc)⁻¹ •
        (V.word (frozen.preimage i.succ) -
          V.word (frozen.preimage i.castSucc))) = wv i := by
  have hquery := preimage_acceptance_increment_agreesOn_queries C foldRoot ch hm
    hch δs hδpos hδone S V dom d q wv A₀ f₀
    (assemblePreimageMessages S V frozen q response) ρs hacc i hρ
  obtain ⟨A, hcard, hagrees⟩ := hsample (by
    simpa [assemblePreimageMessages] using hquery)
  exact subUdRecover_sound dom hUD (hwv i) hcard hagrees

/-- The same phase ordering connected to the actual query log.  Equality of
the prover output's messages with the assembled two-phase transcript lets the
existing log extractor consume the good-sampling premise. -/
theorem twoPhase_hitLogExtractor_pinned [Nonempty (Fin m)]
    {decodeRadius : ℝ}
    (hUD : decodeRadius <
      (1 - ((d : ℝ) - 1) / (Fintype.card (Fin m) : ℝ)) / 2)
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    (frozen : FrozenPreimagePhase S V (k := ch.length + 1))
    (q : Fin t → Fin m)
    (response : ColumnResponsePhase S V (k := ch.length + 1) frozen q)
    {s tq : ℕ}
    (P : SrProver
      (preimageLinkedReduction C foldRoot ch hm hch δs hδpos hδone S V dom d q
        wv) s)
    (coins : Fin tq → F) (fallback : Fin (ch.length + 1) → F)
    (hπ : (srOut P coins).πs =
      assemblePreimageMessages S V frozen q response)
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
      (ρ⁻¹ • (V.word (frozen.preimage i.succ) -
        V.word (frozen.preimage i.castSucc))) (wv i)) :
    preimageLinkedSubUdLogExtractor C foldRoot ch hm hch δs hδpos hδone S V
      dom d q wv decodeRadius s (srOut P coins) (srTrace P coins) i = wv i := by
  apply preimage_hitLogExtractor_pinned C foldRoot ch hm hch δs hδpos hδone
    S V dom d q wv hUD hwv P coins fallback i hans hρ hacc
  simpa [hπ, assemblePreimageMessages] using hsample

end AcceptedTransport

/-! ## Fixed-root sampling loss across every link -/

section SamplingAssembly

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [DecidableEq F]

open Classical in
/-- `uniformProb` rendering of the fixed-word sampling theorem. -/
theorem queryAgreementAmplification_failure_uniform [Nonempty ι]
    (t : ℕ) (radius : ℝ) (hradius1 : radius ≤ 1) (g w : ι → F) :
    uniformProb (Fin t → ι)
      (fun q => ¬ QueryAgreementAmplifies q radius g w) ≤
      (1 - radius) ^ t := by
  classical
  rw [show uniformProb (Fin t → ι)
      (fun q => ¬ QueryAgreementAmplifies q radius g w) =
      ((Finset.univ.filter fun q : Fin t → ι =>
        ¬ QueryAgreementAmplifies q radius g w).card : ℝ) /
        (Fintype.card ι : ℝ) ^ t by
    unfold uniformProb
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fun,
      Fintype.card_fin]
    push_cast
    rfl]
  exact queryAgreementAmplification_failure_pr t radius hradius1 g w

open Classical in
/-- One shared post-commitment query schedule is union-bounded across all
frozen consecutive-root increments.  Independence between links is not used;
only the roots, preimages, and fold challenges must be fixed before `q`. -/
theorem frozenLinks_samplingFailure_uniform
    {Root Op : Type} [Field F] [Nonempty ι]
    {n t : ℕ} (S : BindingCommitment Root F ι Op)
    (V : RootPreimageScheme S)
    (frozen : FrozenPreimagePhase S V (k := n + 1))
    (ρs : Fin (n + 1) → F) (wv : Fin n → ι → F)
    (radius : ℝ) (hradius1 : radius ≤ 1) :
    uniformProb (Fin t → ι) (fun q => ∃ i : Fin n,
      ¬ QueryAgreementAmplifies q radius
        ((ρs i.castSucc)⁻¹ •
          (V.word (frozen.preimage i.succ) -
            V.word (frozen.preimage i.castSucc))) (wv i)) ≤
      (n : ℝ) * (1 - radius) ^ t := by
  refine le_trans (uniformProb_exists_le (fun i q =>
    ¬ QueryAgreementAmplifies q radius
      ((ρs i.castSucc)⁻¹ •
        (V.word (frozen.preimage i.succ) -
          V.word (frozen.preimage i.castSucc))) (wv i))) ?_
  calc
    ∑ i : Fin n, uniformProb (Fin t → ι) (fun q =>
        ¬ QueryAgreementAmplifies q radius
          ((ρs i.castSucc)⁻¹ •
            (V.word (frozen.preimage i.succ) -
              V.word (frozen.preimage i.castSucc))) (wv i))
      ≤ ∑ _i : Fin n, (1 - radius) ^ t := by
        exact Finset.sum_le_sum fun i _ =>
          queryAgreementAmplification_failure_uniform t radius hradius1 _ _
    _ = (n : ℝ) * (1 - radius) ^ t := by simp

/-! ### Constrained-mask schedules -/

/-- Ordered sampling without replacement from an allowed coordinate set. -/
abbrev AllowedInjectiveSchedule (allowed : Finset ι) (t : ℕ) :=
  Fin t ↪ {x : ι // x ∈ allowed}

/-- Convert an allowed injective schedule to the query map checked by the
verifier. -/
def allowedSchedule {allowed : Finset ι} {t : ℕ}
    (q : AllowedInjectiveSchedule allowed t) : Fin t → ι :=
  fun j => (q j).1

/-- The exact allowed-coordinate premise for constrained-mask deployment.
It deliberately uses uniform ordered injections, not full-domain IID draws.
`epsilon` should be instantiated by the hypergeometric/falling-factorial
ratio after accounting for blind constraint coordinates. -/
structure AllowedWithoutReplacementSamplingPremise
    (allowed : Finset ι) (t : ℕ) (radius epsilon : ℝ)
    (g w : ι → F) : Prop where
  enough_allowed : t ≤ allowed.card
  failure_bound :
    uniformProb (AllowedInjectiveSchedule allowed t) (fun q =>
      ¬ QueryAgreementAmplifies (allowedSchedule q) radius g w) ≤ epsilon

/-- The exact falling-factorial miss price associated with at most `agreeCap`
agreeing allowed coordinates among `allowedCount` coordinates. -/
noncomputable def fallingFactorialMiss
    (agreeCap allowedCount t : ℕ) : ℝ :=
  (agreeCap.descFactorial t : ℝ) /
    (allowedCount.descFactorial t : ℝ)

/-- Precise constrained-mask premise with blind-coordinate accounting.  When
global large agreement fails, at most `agreeCap` allowed coordinates may
agree; uniform ordered sampling without replacement is then priced by the
exact falling-factorial ratio `(agreeCap)ₜ / (|allowed|)ₜ`. -/
structure AllowedWithoutReplacementFallingPremise
    (allowed : Finset ι) (t : ℕ) (radius : ℝ)
    (g w : ι → F) (agreeCap : ℕ) : Prop where
  enough_allowed : t ≤ allowed.card
  agreement_cap : ¬ LargeAgreement radius g w →
    (allowed.filter fun x => g x = w x).card ≤ agreeCap
  failure_bound :
    uniformProb (AllowedInjectiveSchedule allowed t) (fun q =>
      ¬ QueryAgreementAmplifies (allowedSchedule q) radius g w) ≤
      fallingFactorialMiss agreeCap allowed.card t

end SamplingAssembly

/-- info: 'Minidregg.Selvage.twoPhase_acceptance_subUd_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhase_acceptance_subUd_pinned
/-- info: 'Minidregg.Selvage.twoPhase_hitLogExtractor_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhase_hitLogExtractor_pinned
/-- info: 'Minidregg.Selvage.queryAgreementAmplification_failure_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms queryAgreementAmplification_failure_uniform
/-- info: 'Minidregg.Selvage.frozenLinks_samplingFailure_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frozenLinks_samplingFailure_uniform

end Minidregg.Selvage
