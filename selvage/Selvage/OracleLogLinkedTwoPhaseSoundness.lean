/-
# Full OracleLog/FS soundness for the staged linked protocol

This module joins the staged source-failure cover, fresh algebra horn,
logged-zero horn, and the adaptive sampling theorem.  Commitment/preimage
soundness and zero knowledge remain explicit computational error events; the
transparent preimage tooth is never used to discharge them.
-/
import Selvage.OracleLogLinkedTwoPhaseHorns

namespace Minidregg.Selvage

section Soundness

open Classical

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

private noncomputable abbrev stagedR : Reduction :=
  twoPhaseReduction (C := C) (foldRoot := foldRoot) (ch := ch) (hm := hm)
    (hch := hch) (δs := δs) (hδpos := hδpos) (hδone := hδone)
    (S := S) (V := V) (dom := dom) (d := d) (Q := Q) (wv := wv)

/-! ## Source event and deterministic cover -/

/-- The deployed aligned statement set, now typed at the staged reduction. -/
def twoPhaseLinkedStatementSet :
    Set (Stmt (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv)) :=
  {st | AccClaim.Satisfies C st.x st.y ∧
    ∀ i, LinkAligned C st.x ch i (wv i)}

/-- Source relaxed-membership follows from base satisfaction and linkwise
alignment for the exact staged extractor. -/
theorem twoPhase_relaxedMem_of_links
    {st : Stmt (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv)}
    {w : Fin ch.length → Fin m → F}
    (hbase : AccClaim.Satisfies C st.x st.y)
    (hlinks : ∀ i, LinkAligned C st.x ch i (w i))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    RelaxedMem
      (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).R
      δ st.idx st.x st.y w := by
  refine ⟨st.y, ⟨hbase, hlinks⟩, ?_⟩
  rw [fracHamming_self]
  exact hδ

/-- Failure of the staged source relation over the aligned statement set
exposes an exact bad link. -/
theorem twoPhase_source_failure_has_bad_link
    {st : Stmt (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv)}
    (hst : st ∈ twoPhaseLinkedStatementSet C foldRoot ch hm hch δs hδpos
      hδone S V dom d Q wv)
    {w : Fin ch.length → Fin m → F} {δ : ℝ} (hδ : 0 ≤ δ)
    (hfail : ¬ RelaxedMem
      (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).R
      δ st.idx st.x st.y w) :
    ∃ i : Fin ch.length, ¬ LinkAligned C st.x ch i (w i) := by
  classical
  by_contra hnone
  push Not at hnone
  exact hfail (twoPhase_relaxedMem_of_links C foldRoot ch hm hch δs hδpos
    hδone S V dom d Q wv hst.1 hnone hδ)

/-- The exact staged OracleLog/FS soundness event before computational CR/ZK
hybrids are added. -/
def TwoPhaseLogSoundEvent {s tq : ℕ} (decodeRadius δ : ℝ)
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (ω : (Fin tq → TwoPhaseChal (F := F) Q) ×
      (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)) : Prop :=
  let o := srOut P ω.1
  let L := srTrace P ω.1
  let ρs := srFinalChal P ω.1 ω.2
  o.stmt ∈ twoPhaseLinkedStatementSet C foldRoot ch hm hch δs hδpos hδone S V
    dom d Q wv ∧
  ¬ RelaxedMem
    (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).R
    δ o.stmt.idx o.stmt.x o.stmt.y
      (twoPhaseSubUdLogExtractor C foldRoot ch hm hch δs hδpos hδone S V dom d
        Q wv decodeRadius s o L) ∧
  ∃ (x' : AccClaim Root F (Fin m) r) (y' : Fin m → F),
    fiatShamir
      (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s
      (fsOracle o ρs) o = some (x', y') ∧
    RelaxedMem
      (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).R'
      δ o.stmt.idx x' y' o.w'

/-- Fresh algebra badness at a particular link. -/
def TwoPhaseFreshAlgebraBad {s tq : ℕ} (decodeRadius δ : ℝ)
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (i : Fin ch.length)
    (ω : (Fin tq → TwoPhaseChal (F := F) Q) ×
      (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)) : Prop :=
  TwoPhaseLogSoundEvent C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv
      decodeRadius δ P ω ∧
    OracleLog.answerOf (srTrace P ω.1)
      ((srOut P ω.1).query (twoPhaseFoldSlot i)) = none ∧
    ¬ LinkAligned C (srOut P ω.1).stmt.x ch i
      (twoPhaseSubUdLogExtractor C foldRoot ch hm hch δs hδpos hδone S V dom d
        Q wv decodeRadius s (srOut P ω.1) (srTrace P ω.1) i)

/-- The staged extractor defaults to zero on an unqueried algebra prefix. -/
theorem twoPhaseSubUdLogExtractor_eq_zero_of_unqueried {s : ℕ}
    (o : SrOutput (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (L : OracleLog
      (SrMove (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
      (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).Chal)
    (decodeRadius : ℝ) (i : Fin ch.length)
    (h : L.answerOf (o.query (twoPhaseFoldSlot i)) = none) :
    twoPhaseSubUdLogExtractor C foldRoot ch hm hch δs hδpos hδone S V dom d Q
      wv decodeRadius s o L i = 0 := by
  unfold twoPhaseSubUdLogExtractor
  cases hopt : L.answerOf (o.query (twoPhaseFoldSlot i)) with
  | none => rfl
  | some ρ =>
      rw [hopt] at h
      contradiction

/-! ## Fresh algebra fibre -/

/-- Replace the full product challenge at algebra slot `i`. -/
def twoPhaseChallengeVectorAt
    (ρs : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)
    (i : Fin ch.length) (ρ : TwoPhaseChal (F := F) Q) :
    Fin (ch.length + 2) → TwoPhaseChal (F := F) Q :=
  Function.update ρs (twoPhaseFoldSlot i) ρ

omit [Fintype F] [DecidableEq F] in
/-- Updating the staged algebra slot updates exactly the corresponding scalar
in the aggregate schedule. -/
theorem twoPhaseAlgebra_update_schedule
    (ρs : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)
    (i : Fin ch.length) (ρ : TwoPhaseChal (F := F) Q) :
    padSched (fun k : Fin ch.length =>
      (twoPhaseAlgebraChallenges ch Q (twoPhaseChallengeVectorAt ch Q ρs i ρ))
        k.castSucc) =
    scheduleAt (padSched fun k : Fin ch.length =>
      (twoPhaseAlgebraChallenges ch Q ρs) k.castSucc) (i : ℕ) ρ.1 := by
  funext a
  by_cases hai : a = (i : ℕ)
  · subst a
    simp [scheduleAt, twoPhaseAlgebraChallenges, twoPhaseChallengeVectorAt,
      padSched_lt, i.isLt, Function.update_self]
  · rw [scheduleAt, Function.update_of_ne hai]
    by_cases ha : a < ch.length
    · let k : Fin ch.length := ⟨a, ha⟩
      have hki : k ≠ i := fun h => hai (congrArg Fin.val h)
      have hslot : twoPhaseFoldSlot k ≠ twoPhaseFoldSlot i := by
        intro h
        exact hki (Fin.ext (by
          have hv := congrArg Fin.val h
          simpa [twoPhaseFoldSlot] using hv))
      rw [padSched_lt _ ha, padSched_lt _ ha]
      unfold twoPhaseAlgebraChallenges
      change padSched _ a = padSched _ a
      rw [padSched_lt _ k.isLt, padSched_lt _ k.isLt]
      exact congrArg Prod.fst (Function.update_of_ne hslot _ _)
    · rw [padSched_of_le _ (Nat.le_of_not_gt ha),
        padSched_of_le _ (Nat.le_of_not_gt ha)]

/-- Acceptance at a staged output has at most one accepting field scalar per
fixed ignored query component when zero is not aligned. -/
theorem twoPhaseFreshOutputFibre_le
    {dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    {δ : ℝ} (hδC : δ < dC / 2) {s : ℕ}
    (o : SrOutput (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (ρs : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)
    (i : Fin ch.length)
    (hbad : ¬ LinkAligned C o.stmt.x ch i (0 : Fin m → F)) :
    uniformProb (TwoPhaseChal (F := F) Q) (fun ρ =>
      ∃ (x' : AccClaim Root F (Fin m) r) (y' : Fin m → F),
        fiatShamir
          (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s
          (fsOracle o (twoPhaseChallengeVectorAt ch Q ρs i ρ)) o =
            some (x', y') ∧
        RelaxedMem
          (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).R'
          δ o.stmt.idx x' y' o.w') ≤ 1 / (Fintype.card F : ℝ) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨j, hj⟩ := exists_nonzero_target_of_zero_not_linkAligned C ch i hbad
  let Bad : TwoPhaseChal (F := F) Q → Prop := fun ρ =>
    ∃ (x' : AccClaim Root F (Fin m) r) (y' : Fin m → F),
      fiatShamir
        (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s
        (fsOracle o (twoPhaseChallengeVectorAt ch Q ρs i ρ)) o = some (x', y') ∧
      RelaxedMem
        (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).R'
        δ o.stmt.idx x' y' o.w'
  have heq := uniformProb_equiv (Equiv.prodComm F Q.Query)
    (fun z : Q.Query × F => Bad (z.2, z.1))
  rw [show (fun ρ : TwoPhaseChal (F := F) Q => Bad ρ) =
      fun ρ => (fun z : Q.Query × F => Bad (z.2, z.1))
        (Equiv.prodComm F Q.Query ρ) from rfl, heq]
  refine uniformProb_prod_le (by positivity) fun qpart => ?_
  refine uniformProb_le_inv_card_of_subsingleton_public F
    (p := fun ρ => Bad (ρ, qpart)) fun ρ₁ ρ₂ h₁ h₂ => ?_
  obtain ⟨x₁, y₁, hacc₁, hrel₁⟩ := h₁
  obtain ⟨x₂, y₂, hacc₂, hrel₂⟩ := h₂
  have hd₁ := twoPhase_fiatShamir_accept_data C foldRoot ch hm hch δs hδpos
    hδone S V dom d Q wv o (twoPhaseChallengeVectorAt ch Q ρs i (ρ₁, qpart))
    hacc₁
  have hd₂ := twoPhase_fiatShamir_accept_data C foldRoot ch hm hch δs hδpos
    hδone S V dom d Q wv o (twoPhaseChallengeVectorAt ch Q ρs i (ρ₂, qpart))
    hacc₂
  have hx₁ : x₁ = aggregate foldRoot
      (padSched fun k : Fin ch.length =>
        (twoPhaseAlgebraChallenges ch Q
          (twoPhaseChallengeVectorAt ch Q ρs i (ρ₁, qpart))) k.castSucc)
      o.stmt.x ch := by simpa using congrArg Prod.fst hd₁.2.2.1
  have hy₁ : y₁ =
      V.word (o.πs (twoPhaseRootSlot (Fin.last ch.length))).preimage := by
    simpa using congrArg Prod.snd hd₁.2.2.1
  have hx₂ : x₂ = aggregate foldRoot
      (padSched fun k : Fin ch.length =>
        (twoPhaseAlgebraChallenges ch Q
          (twoPhaseChallengeVectorAt ch Q ρs i (ρ₂, qpart))) k.castSucc)
      o.stmt.x ch := by simpa using congrArg Prod.fst hd₂.2.2.1
  have hy₂ : y₂ =
      V.word (o.πs (twoPhaseRootSlot (Fin.last ch.length))).preimage := by
    simpa using congrArg Prod.snd hd₂.2.2.1
  obtain ⟨z₁, hz₁, hclose₁⟩ := hrel₁
  obtain ⟨z₂, hz₂, hclose₂⟩ := hrel₂
  have hs₁ : AccClaim.Satisfies C
      (aggregate foldRoot
        (scheduleAt (padSched fun k : Fin ch.length =>
          (twoPhaseAlgebraChallenges ch Q ρs) k.castSucc) (i : ℕ) ρ₁)
        o.stmt.x ch) z₁ := by
    change AccClaim.Satisfies C x₁ z₁ at hz₁
    rw [hx₁, twoPhaseAlgebra_update_schedule] at hz₁
    exact hz₁
  have hs₂ : AccClaim.Satisfies C
      (aggregate foldRoot
        (scheduleAt (padSched fun k : Fin ch.length =>
          (twoPhaseAlgebraChallenges ch Q ρs) k.castSucc) (i : ℕ) ρ₂)
        o.stmt.x ch) z₂ := by
    change AccClaim.Satisfies C x₂ z₂ at hz₂
    rw [hx₂, twoPhaseAlgebra_update_schedule] at hz₂
    exact hz₂
  have hc₁ : relDist
      (V.word (o.πs (twoPhaseRootSlot (Fin.last ch.length))).preimage) z₁ ≤ δ := by
    rw [← hy₁]
    rw [← fracHamming_eq_relDist]
    exact hclose₁
  have hc₂ : relDist
      (V.word (o.πs (twoPhaseRootSlot (Fin.last ch.length))).preimage) z₂ ≤ δ := by
    rw [← hy₂]
    rw [← fracHamming_eq_relDist]
    exact hclose₂
  exact freshAggregateChallenge_injective foldRoot
    (padSched fun k : Fin ch.length =>
      (twoPhaseAlgebraChallenges ch Q ρs) k.castSucc) i
    (V.word (o.πs (twoPhaseRootSlot (Fin.last ch.length))).preimage)
    hdC hδC j hj ⟨z₁, hs₁, hc₁⟩ ⟨z₂, hs₂, hc₂⟩

/-- Splitting any unqueried fallback changes exactly that challenge
coordinate.  The generic reduction typing avoids relying on transparency of
the compiled two-phase reduction's `k` and `Chal` fields. -/
theorem twoPhase_srFinalChal_split_of_none {R₀ : Reduction} {s tq : ℕ}
    (P : SrProver R₀ s) (c : Fin tq → R₀.Chal) (a : Fin R₀.k)
    (rest : {j : Fin R₀.k // j ≠ a} → R₀.Chal) (ρ₀ ρ : R₀.Chal)
    (hnone : OracleLog.answerOf (srTrace P c) ((srOut P c).query a) = none) :
    srFinalChal P c ((splitCoord a).symm (rest, ρ)) =
      Function.update
        (srFinalChal P c ((splitCoord a).symm (rest, ρ₀)))
        a ρ := by
  funext b
  by_cases hba : b = a
  · subst b
    rw [srFinalChal_eq_answerOf, hnone]
    simp [Function.update_self]
  · rw [Function.update_of_ne hba]
    apply srFinalChal_congr
    rw [splitCoord_symm_apply_ne hba, splitCoord_symm_apply_ne hba]

/-- Fresh algebra horn, one link. -/
theorem twoPhaseFreshAlgebraLink_le
    {dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hδsC : δs ≤ dC / 2)
    {decodeRadius : ℝ} {s tq : ℕ} {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) δs)
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (i : Fin ch.length) :
    uniformProb
      ((Fin tq → TwoPhaseChal (F := F) Q) ×
        (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q))
      (TwoPhaseFreshAlgebraBad C foldRoot ch hm hch δs hδpos hδone S V dom d Q
        wv decodeRadius δ P i) ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  let a : Fin (ch.length + 2) := twoPhaseFoldSlot i
  have hsplit :
      uniformProb
        ((Fin tq → TwoPhaseChal (F := F) Q) ×
          (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q))
        (TwoPhaseFreshAlgebraBad C foldRoot ch hm hch δs hδpos hδone S V dom d
          Q wv decodeRadius δ P i) =
      uniformProb
        (((Fin tq → TwoPhaseChal (F := F) Q) ×
          ({j : Fin (ch.length + 2) // j ≠ a} → TwoPhaseChal (F := F) Q)) ×
          TwoPhaseChal (F := F) Q)
        (fun x => TwoPhaseFreshAlgebraBad C foldRoot ch hm hch δs hδpos hδone
          S V dom d Q wv decodeRadius δ P i
          (x.1.1, (splitCoord a).symm (x.1.2, x.2))) :=
    (uniformProb_equiv
      ((((Equiv.refl (Fin tq → TwoPhaseChal (F := F) Q)).prodCongr
        (splitCoord a)).trans (Equiv.prodAssoc _ _ _).symm).symm)
      (TwoPhaseFreshAlgebraBad C foldRoot ch hm hch δs hδpos hδone S V dom d Q
        wv decodeRadius δ P i)).symm
  rw [hsplit]
  refine uniformProb_prod_le (by positivity) fun rest => ?_
  let c : Fin tq → TwoPhaseChal (F := F) Q := rest.1
  let ρ₀ : TwoPhaseChal (F := F) Q := Classical.arbitrary _
  let d₀ := (splitCoord a).symm (rest.2, ρ₀)
  let o := srOut P c
  let ρs := srFinalChal P c d₀
  by_cases hbad : ¬ LinkAligned C o.stmt.x ch i (0 : Fin m → F)
  · refine le_trans (uniformProb_mono ?_)
      (twoPhaseFreshOutputFibre_le C foldRoot ch hm hch δs hδpos hδone S V dom
        d Q wv hdC (lt_of_lt_of_le hδ.2 hδsC) o ρs i hbad)
    intro ρ hev
    obtain ⟨-, -, x', y', hacc, hrel⟩ := hev.1
    have hnone : OracleLog.answerOf (srTrace P c)
        ((srOut P c).query a) = none := by
      simpa [a] using hev.2.1
    have hvec := twoPhase_srFinalChal_split_of_none P c a rest.2 ρ₀ ρ hnone
    refine ⟨x', y', ?_, hrel⟩
    dsimp [c, o, a] at hacc
    dsimp [c, a] at hvec
    have hacc' :
        fiatShamir
          (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s
          (fsOracle (srOut P rest.1)
            (Function.update
              (srFinalChal P rest.1
                ((splitCoord (twoPhaseFoldSlot i)).symm (rest.2, ρ₀)))
              (twoPhaseFoldSlot i) ρ))
          (srOut P rest.1) = some (x', y') := hvec ▸ hacc
    simpa [c, o, ρs, d₀, a, twoPhaseChallengeVectorAt] using hacc'
  · refine le_trans (le_of_eq (uniformProb_false fun ρ hev => ?_)) (by positivity)
    have hz := twoPhaseSubUdLogExtractor_eq_zero_of_unqueried C foldRoot ch hm
      hch δs hδpos hδone S V dom d Q wv o (srTrace P c) decodeRadius i hev.2.1
    have he := hev.2.2
    change ¬ LinkAligned C (srOut P c).stmt.x ch i
      (twoPhaseSubUdLogExtractor C foldRoot ch hm hch δs hδpos hδone S V dom d
        Q wv decodeRadius s (srOut P c) (srTrace P c) i) at he
    rw [hz] at he
    exact hbad he

/-! ## Logged-zero horn and full composition -/

omit [DecidableEq F] in
/-- A fixed game coin has zero field component with probability exactly the
field inverse, even though the challenge also carries a query schedule. -/
theorem twoPhase_gameCoinFstZero_le {tq : ℕ} {Γ : Type} [Fintype Γ]
    (j : Fin tq) :
    uniformProb ((Fin tq → TwoPhaseChal (F := F) Q) × Γ)
      (fun x => (x.1 j).1 = 0) ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  have hsplit := uniformProb_equiv
    (splitProd1 (β := TwoPhaseChal (F := F) Q) (γ := Γ) j)
    (fun y : (({i : Fin tq // i ≠ j} → TwoPhaseChal (F := F) Q) × Γ) ×
      TwoPhaseChal (F := F) Q => y.2.1 = 0)
  rw [show (fun x : (Fin tq → TwoPhaseChal (F := F) Q) × Γ =>
      (x.1 j).1 = 0) = fun x =>
        ((splitProd1 (β := TwoPhaseChal (F := F) Q) (γ := Γ) j x).2).1 = 0
      from rfl, hsplit]
  refine uniformProb_prod_le (by positivity) fun _ => ?_
  have hprod := uniformProb_equiv (Equiv.prodComm F Q.Query)
    (fun z : Q.Query × F => z.2 = 0)
  rw [show (fun z : TwoPhaseChal (F := F) Q => z.1 = 0) = fun z =>
      (Equiv.prodComm F Q.Query z).2 = 0 from rfl, hprod]
  refine uniformProb_prod_le (by positivity) fun _ => ?_
  exact le_of_eq (uniformProb_eq_single 0)

/-- Some logged game coin has zero field component. -/
def TwoPhaseHitZeroBad {tq : ℕ}
    (ω : (Fin tq → TwoPhaseChal (F := F) Q) ×
      (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)) : Prop :=
  ∃ j : Fin tq, (ω.1 j).1 = 0

omit [DecidableEq F] in
theorem twoPhaseHitZeroBad_le {tq : ℕ} :
    uniformProb
      ((Fin tq → TwoPhaseChal (F := F) Q) ×
        (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q))
      (TwoPhaseHitZeroBad (ch := ch) (Q := Q)) ≤
      (tq : ℝ) / (Fintype.card F : ℝ) := by
  refine le_trans (uniformProb_exists_le fun (j : Fin tq)
    (ω : (Fin tq → TwoPhaseChal (F := F) Q) ×
      (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)) =>
      (ω.1 j).1 = 0) ?_
  refine le_trans (Finset.sum_le_sum fun j _ =>
    twoPhase_gameCoinFstZero_le (Q := Q)
      (Γ := Fin (ch.length + 2) → TwoPhaseChal (F := F) Q) j) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [div_eq_mul_inv, one_mul]
  exact le_rfl

/-- Pointwise source-failure cover by fresh algebra, logged zero, or sampling
failure. -/
theorem twoPhaseLogSoundEvent_cover [Nonempty (Fin m)]
    {decodeRadius : ℝ}
    (hUD : decodeRadius <
      (1 - ((d : ℝ) - 1) / (Fintype.card (Fin m) : ℝ)) / 2)
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    {s tq : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s) :
    ∀ ω : (Fin tq → TwoPhaseChal (F := F) Q) ×
        (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q),
      TwoPhaseLogSoundEvent C foldRoot ch hm hch δs hδpos hδone S V dom d Q
        wv decodeRadius δ P ω →
      (∃ i : Fin ch.length,
        TwoPhaseFreshAlgebraBad C foldRoot ch hm hch δs hδpos hδone S V dom d Q
          wv decodeRadius δ P i ω) ∨
      TwoPhaseHitZeroBad (ch := ch) (Q := Q) ω ∨
      TwoPhaseSamplingBad C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv
        P decodeRadius ω := by
  intro ω hev
  have hev' := hev
  obtain ⟨hst, hfail, x', y', hacc, hrel⟩ := hev
  obtain ⟨i, hbad⟩ := twoPhase_source_failure_has_bad_link C foldRoot ch hm hch
    δs hδpos hδone S V dom d Q wv hst hδ hfail
  rcases logSlot_cover P (twoPhaseFoldSlot i) ω.1 with hfresh | ⟨j, hhit⟩
  · exact Or.inl ⟨i, hev', hfresh, hbad⟩
  · by_cases hsample : TwoPhaseSamplingBad C foldRoot ch hm hch δs hδpos hδone
        S V dom d Q wv P decodeRadius ω
    · exact Or.inr (Or.inr hsample)
    · by_cases hz : (ω.1 j).1 = 0
      · exact Or.inr (Or.inl ⟨j, hz⟩)
      · have hans := hitAt_answerOf P hhit
        have hgood : QueryAgreementAmplifies
            (twoPhaseSampledSchedule ch Q (srFinalChal P ω.1 ω.2)) decodeRadius
            (((ω.1 j).1)⁻¹ •
              (V.word ((srOut P ω.1).πs (twoPhaseRootSlot i.succ)).preimage -
                V.word ((srOut P ω.1).πs
                  (twoPhaseRootSlot i.castSucc)).preimage)) (wv i) := by
          have hi := not_exists.mp hsample i
          have hchal : srFinalChal P ω.1 ω.2 (twoPhaseFoldSlot i) = ω.1 j := by
            rw [srFinalChal_eq_answerOf, hans]
            rfl
          have halg :
              (twoPhaseAlgebraChallenges ch Q (srFinalChal P ω.1 ω.2))
                i.castSucc = (ω.1 j).1 := by
            unfold twoPhaseAlgebraChallenges
            change padSched _ (i : ℕ) = _
            rw [padSched_lt _ i.isLt]
            exact congrArg Prod.fst hchal
          simpa [halg] using hi
        have hpin := twoPhaseGame_hitLogExtractor_pinned C foldRoot ch hm hch δs
          hδpos hδone S V dom d Q wv hUD hwv P ω.1 ω.2 i hans hz hacc hgood
        rw [hpin] at hbad
        exact (hbad (hst.2 i)).elim

/-- Actual staged OracleLog/FS soundness with algebra, adaptive sampling, and
explicit computational CR/ZK losses. -/
theorem twoPhaseOracleLogFsSoundness_le [Nonempty (Fin m)]
    {decodeRadius dC δ εsample εcr εzk : ℝ}
    (hUD : decodeRadius <
      (1 - ((d : ℝ) - 1) / (Fintype.card (Fin m) : ℝ)) / 2)
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hδsC : δs ≤ dC / 2) (hδ : δ ∈ Set.Ioo (0 : ℝ) δs)
    (hεsample : 0 ≤ εsample)
    (hsample : TwoPhaseFixedScheduleBound (S := S) (ch := ch) (V := V)
      (Q := Q) (wv := wv) decodeRadius εsample)
    {s tq : ℕ}
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (cr zk : ((Fin tq → TwoPhaseChal (F := F) Q) ×
      (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)) → Prop)
    (hcr : uniformProb _ cr ≤ εcr) (hzk : uniformProb _ zk ≤ εzk) :
    uniformProb
      ((Fin tq → TwoPhaseChal (F := F) Q) ×
        (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q))
      (fun ω => TwoPhaseLogSoundEvent C foldRoot ch hm hch δs hδpos hδone S V
          dom d Q wv decodeRadius δ P ω ∨ cr ω ∨ zk ω) ≤
      (ch.length : ℝ) / (Fintype.card F : ℝ) +
      (tq : ℝ) / (Fintype.card F : ℝ) +
      ((tq : ℝ) + 1) * εsample + εcr + εzk := by
  let Ω := (Fin tq → TwoPhaseChal (F := F) Q) ×
    (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)
  let Fresh : Ω → Prop := fun ω => ∃ i : Fin ch.length,
    TwoPhaseFreshAlgebraBad C foldRoot ch hm hch δs hδpos hδone S V dom d Q
      wv decodeRadius δ P i ω
  let HitZero : Ω → Prop := TwoPhaseHitZeroBad (ch := ch) (Q := Q)
  let Sampling : Ω → Prop := TwoPhaseSamplingBad C foldRoot ch hm hch δs hδpos
    hδone S V dom d Q wv P decodeRadius
  refine le_trans (uniformProb_mono
    (q := TwoPhaseCombinedBad Fresh HitZero Sampling cr zk) ?_) ?_
  · intro ω hbad
    rcases hbad with hsnd | hcrzk
    · rcases twoPhaseLogSoundEvent_cover C foldRoot ch hm hch δs hδpos hδone S
        V dom d Q wv hUD hwv hδ.1.le P ω hsnd with hf | hz | hs
      · exact Or.inl hf
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr (Or.inl hs))
    · rcases hcrzk with hc | hz
      · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hz)))
  · apply twoPhaseCombinedBad_le Fresh HitZero Sampling cr zk
    · dsimp only [Fresh, Ω]
      refine le_trans (uniformProb_exists_le fun i =>
        TwoPhaseFreshAlgebraBad C foldRoot ch hm hch δs hδpos hδone S V dom d Q
          wv decodeRadius δ P i) ?_
      refine le_trans (Finset.sum_le_sum fun i _ =>
        twoPhaseFreshAlgebraLink_le C foldRoot ch hm hch δs hδpos hδone S V dom
          d Q wv hdC hδsC hδ P i) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [div_eq_mul_inv, one_mul]
      exact le_rfl
    · dsimp only [HitZero, Ω]
      exact twoPhaseHitZeroBad_le (F := F) (ch := ch) (Q := Q)
    · dsimp only [Sampling, Ω]
      exact twoPhaseSamplingBad_le C foldRoot ch hm hch δs hδpos hδone S V dom d
        Q wv decodeRadius εsample hεsample hsample P
    · exact hcr
    · exact hzk

/-- info: 'Minidregg.Selvage.twoPhaseFreshOutputFibre_le' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhaseFreshOutputFibre_le
/-- info: 'Minidregg.Selvage.twoPhaseFreshAlgebraLink_le' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhaseFreshAlgebraLink_le
/-- info: 'Minidregg.Selvage.twoPhase_gameCoinFstZero_le' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhase_gameCoinFstZero_le
/-- info: 'Minidregg.Selvage.twoPhaseLogSoundEvent_cover' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhaseLogSoundEvent_cover
/-- info: 'Minidregg.Selvage.twoPhaseOracleLogFsSoundness_le' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhaseOracleLogFsSoundness_le

end Soundness

end Minidregg.Selvage
