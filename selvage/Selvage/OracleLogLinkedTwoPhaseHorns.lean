/-
# Adaptive sampling horns for the staged linked game

The designated sampling challenge is itself a Fiat--Shamir query.  On a
logged hit its answer is a game coin, so the frozen prefix appears adaptive.
This module performs the lazy-ROM fibre argument: condition on the game past,
pin the final-root query to the move made at the hit slot, jointly resolve all
shorter algebra-prefix queries with `card_resolve_runFrom`, and push the fixed
root sampling theorem through that exactly-uniform map.
-/
import Selvage.OracleLogLinkedTwoPhaseGame

namespace Minidregg.Selvage

section SamplingHit

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

/-- Sampling failure at the designated post-root challenge.  It mentions no
transparent preimage implementation: words are obtained only through the
abstract opening interface. -/
def TwoPhaseSamplingBad {s tq : ℕ}
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (radius : ℝ)
    (ω : (Fin tq → TwoPhaseChal (F := F) Q) ×
      (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)) : Prop :=
  ∃ i : Fin ch.length,
    ¬ QueryAgreementAmplifies
      (twoPhaseSampledSchedule ch Q (srFinalChal P ω.1 ω.2)) radius
      (((twoPhaseAlgebraChallenges ch Q (srFinalChal P ω.1 ω.2))
          i.castSucc)⁻¹ •
        (V.word ((srOut P ω.1).πs (twoPhaseRootSlot i.succ)).preimage -
          V.word ((srOut P ω.1).πs
            (twoPhaseRootSlot i.castSucc)).preimage))
      (wv i)

/-- Sampling failure attributed to a specific game-log hit of the designated
post-root query. -/
def TwoPhaseQueryHitSamplingBad {s tq : ℕ}
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (j : Fin tq) (radius : ℝ)
    (ω : (Fin tq → TwoPhaseChal (F := F) Q) ×
      (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)) : Prop :=
  hitAt P (twoPhaseQuerySlot (n := ch.length)) j ω.1 ∧
    TwoPhaseSamplingBad C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv
      P radius ω

/-- Sampling failure on the fresh designated-query horn. -/
def TwoPhaseQueryFreshSamplingBad {s tq : ℕ}
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (radius : ℝ)
    (ω : (Fin tq → TwoPhaseChal (F := F) Q) ×
      (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)) : Prop :=
  OracleLog.answerOf (srTrace P ω.1)
      ((srOut P ω.1).query (twoPhaseQuerySlot (n := ch.length))) = none ∧
    TwoPhaseSamplingBad C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv
      P radius ω

/-- The exact sampler property consumed by the adaptive ROM argument.  It is
deliberately quantified over every fixed opening vector and algebra vector:
`TwoPhaseQuerySampler.schedule` alone may be constant, so it cannot imply an
IID or without-replacement rate. -/
def TwoPhaseFixedScheduleBound (radius ε : ℝ) : Prop :=
  ∀ (u : Fin (ch.length + 1) → V.Opening)
    (γ : Fin ch.length → F),
    uniformProb Q.Query (fun z => ∃ i : Fin ch.length,
      ¬ QueryAgreementAmplifies (Q.schedule z) radius
        ((γ i)⁻¹ • (V.word (u i.succ) - V.word (u i.castSucc))) (wv i)) ≤ ε

/-- Per-past-fibre adaptive-hit bound for the designated query slot.  The
queried final-root prefix freezes every root/preimage.  The shorter fold
challenges are either already fixed in the past log or are jointly uniform by
`card_resolve_runFrom`; `uniformProb_pushforward_le` then exposes the tested
query coin to `frozenLinks_samplingFailure_uniform`.

This is the missing query-hit kernel needed by the staged FS sampling port. -/
theorem twoPhase_queryHitSampling_fibre_le
    (radius εsample : ℝ) (hεsample : 0 ≤ εsample)
    (hsample : TwoPhaseFixedScheduleBound (S := S) (ch := ch) (V := V)
      (Q := Q) (wv := wv) radius εsample)
    {s tq : ℕ}
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (j : Fin tq) (p : Fin (j : ℕ) → TwoPhaseChal (F := F) Q)
    (Lp : List (SrMove
      (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s ×
      (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).Chal))
    (hLplen : Lp.length = (j : ℕ))
    (hTr : ∀ (ρ : TwoPhaseChal (F := F) Q)
      (cs : Fin (tq - (j : ℕ) - 1) → TwoPhaseChal (F := F) Q),
      srTrace P ((splitGame j).symm (p, ρ, cs)) =
        runFrom P (stepOnce P Lp ρ) (List.ofFn cs)) :
    uniformProb
      (TwoPhaseChal (F := F) Q ×
        (Fin (tq - (j : ℕ) - 1) → TwoPhaseChal (F := F) Q) ×
        (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q))
      (fun b => TwoPhaseQueryHitSamplingBad C foldRoot ch hm hch δs hδpos
        hδone S V dom d Q wv P j radius ((splitAtGame j).symm (p, b))) ≤
      εsample := by
  classical
  obtain ⟨ρ₀⟩ :=
    (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).chalNonempty
  set mv := P.move (Lp.map Prod.snd) with hmv
  have hTsplit : ∀ (ρ : TwoPhaseChal (F := F) Q)
      (cs : Fin (tq - (j : ℕ) - 1) → TwoPhaseChal (F := F) Q),
      ∃ M, srTrace P ((splitGame j).symm (p, ρ, cs)) =
        stepOnce P Lp ρ ++ M := by
    intro ρ cs
    obtain ⟨M, hM⟩ := runFrom_eq_append P (List.ofFn cs) (stepOnce P Lp ρ)
    exact ⟨M, by rw [hTr ρ cs, hM]⟩
  have hquery : ∀ (ρ : TwoPhaseChal (F := F) Q)
      (cs : Fin (tq - (j : ℕ) - 1) → TwoPhaseChal (F := F) Q),
      hitAt P (twoPhaseQuerySlot (n := ch.length)) j
          ((splitGame j).symm (p, ρ, cs)) →
      (srOut P ((splitGame j).symm (p, ρ, cs))).query
          (twoPhaseQuerySlot (n := ch.length)) = mv ∧
      (∀ e ∈ Lp, e.1 ≠ mv) := by
    intro ρ cs hhit
    have hhit' :
        (srTrace P ((splitGame j).symm (p, ρ, cs))).findIdx?
          (fun e => decide (e.1 =
            (srOut P ((splitGame j).symm (p, ρ, cs))).query
              (twoPhaseQuerySlot (n := ch.length)))) = some (j : ℕ) := hhit
    rw [List.findIdx?_eq_some_iff_getElem] at hhit'
    obtain ⟨hjlt, hpj, hmin⟩ := hhit'
    obtain ⟨M, hM⟩ := hTsplit ρ cs
    have hs := stepOnce_eq P Lp ρ
    rw [← hmv] at hs
    rw [hs] at hM
    simp only [List.append_assoc, List.singleton_append] at hM
    have hget1fst :
        ((srTrace P ((splitGame j).symm (p, ρ, cs)))[(j : ℕ)]'hjlt).1 = mv := by
      simp only [hM]
      simp [hLplen]
    have hTj1 := of_decide_eq_true hpj
    rw [hget1fst] at hTj1
    have hq :
        (srOut P ((splitGame j).symm (p, ρ, cs))).query
          (twoPhaseQuerySlot (n := ch.length)) = mv := hTj1.symm
    refine ⟨hq, ?_⟩
    intro e he heq
    obtain ⟨n, hn, hgetn⟩ := List.mem_iff_getElem.mp he
    have hmn := hmin n (by omega)
    have hTn :
        (srTrace P ((splitGame j).symm (p, ρ, cs)))[n]'(by omega) =
          Lp[n]'hn := by
      simp only [hM]
      exact List.getElem_append_left hn
    rw [hTn, hgetn] at hmn
    simp only [decide_eq_true_eq] at hmn
    exact hmn (heq.trans hq.symm)
  by_cases hgd : mv.pfx.length = ch.length + 1 ∧ ∀ e ∈ Lp, e.1 ≠ mv
  · obtain ⟨hlen, hclean⟩ := hgd
    set Qq : Fin (ch.length + 2) →
        SrMove (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s :=
      fun a => ⟨mv.stmt, mv.pfx.take ((a : ℕ) + 1)⟩ with hQq
    set Sf : Finset (Fin (ch.length + 2)) := Finset.univ.filter
      (fun a => (a : ℕ) < ch.length ∧ ∀ e ∈ Lp, e.1 ≠ Qq a) with hSf
    have hQlen : ∀ a : Fin (ch.length + 2), (a : ℕ) < ch.length →
        (Qq a).pfx.length = (a : ℕ) + 1 := by
      intro a ha
      show (mv.pfx.take ((a : ℕ) + 1)).length = (a : ℕ) + 1
      rw [List.length_take, hlen]
      omega
    have hdist : ∀ a ∈ Sf, ∀ a' ∈ Sf, a ≠ a' → Qq a ≠ Qq a' := by
      intro a ha a' ha' hne hc
      have h1 := hQlen a (Finset.mem_filter.mp ha).2.1
      have h2 := hQlen a' (Finset.mem_filter.mp ha').2.1
      rw [hc] at h1
      exact hne (Fin.ext (by omega))
    have hQmv : ∀ a : Fin (ch.length + 2), (a : ℕ) < ch.length →
        Qq a ≠ mv := by
      intro a ha hc
      have h1 := hQlen a ha
      rw [hc, hlen] at h1
      omega
    have hstep : ∀ ρ :
        (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).Chal,
        stepOnce P Lp ρ = Lp ++ [(mv, ρ)] := by
      intro ρ
      rw [stepOnce_eq, ← hmv, find?_eq_none_of_forall_ne hclean]
    have hfreshSf : ∀ (ρ :
        (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).Chal),
        ∀ a ∈ Sf,
        ∀ e ∈ stepOnce P Lp ρ, e.1 ≠ Qq a := by
      intro ρ a ha e he
      rw [hstep ρ] at he
      rcases List.mem_append.mp he with he | he
      · exact (Finset.mem_filter.mp ha).2.2 e he
      · have heq : e = (mv, ρ) := by simpa using he
        subst e
        exact fun hc => hQmv a (Finset.mem_filter.mp ha).2.1 hc.symm
    let frozen : FrozenPreimagePhase S V (k := ch.length + 1) :=
      { root := fun c =>
          (mv.pfx[(c : ℕ)]'(by omega)).1.root
        preimage := fun c =>
          (mv.pfx[(c : ℕ)]'(by omega)).1.preimage }
    let fixedAlg
        (v : {a : Fin (ch.length + 2) // a ∈ Sf} →
          TwoPhaseChal (F := F) Q) : Fin (ch.length + 1) → F :=
      fun c => padSched (fun i : Fin ch.length =>
        if hi : twoPhaseFoldSlot i ∈ Sf
        then (v ⟨twoPhaseFoldSlot i, hi⟩).1
        else (resolveIn Lp (Qq (twoPhaseFoldSlot i)) ρ₀).1) (c : ℕ)
    let resolved (ρ : TwoPhaseChal (F := F) Q)
        (w : (Fin (tq - (j : ℕ) - 1) → TwoPhaseChal (F := F) Q) ×
          (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q)) :
        {a : Fin (ch.length + 2) // a ∈ Sf} →
          TwoPhaseChal (F := F) Q :=
      fun a => resolveIn (runFrom P (stepOnce P Lp ρ) (List.ofFn w.1))
        (Qq a.1) (w.2 a.1)
    let FixedSamplingBad
        (v : {a : Fin (ch.length + 2) // a ∈ Sf} →
          TwoPhaseChal (F := F) Q)
        (ρ : TwoPhaseChal (F := F) Q) : Prop :=
      ∃ i : Fin ch.length,
        ¬ QueryAgreementAmplifies (Q.schedule ρ.2) radius
          (((fixedAlg v) i.castSucc)⁻¹ •
            (V.word (frozen.preimage i.succ) -
              V.word (frozen.preimage i.castSucc))) (wv i)
    refine le_trans (uniformProb_mono ?_)
      (uniformProb_pushforward_le hεsample resolved FixedSamplingBad ?_ ?_)
    · rintro ⟨ρ, cs, dd⟩ ⟨hhit, i, hbad⟩
      obtain ⟨hq, -⟩ := hquery ρ cs hhit
      obtain ⟨M, hM⟩ := hTsplit ρ cs
      rw [hstep ρ] at hM
      simp only [List.append_assoc, List.singleton_append] at hM
      have hfin :
          srFinalChal P ((splitGame j).symm (p, ρ, cs)) dd
              (twoPhaseQuerySlot (n := ch.length)) = ρ := by
        rw [srFinalChal_eq_resolveIn, hq, hM,
          resolveIn_append_of_ne hclean, resolveIn_cons_self]
      have hπ : ∀ c : Fin (ch.length + 1),
          (srOut P ((splitGame j).symm (p, ρ, cs))).πs
              (twoPhaseRootSlot c) = (mv.pfx[(c : ℕ)]'(by omega)).1 := by
        intro c
        have hg := SrOutput.query_pfx_getElem
          (srOut P ((splitGame j).symm (p, ρ, cs)))
          (twoPhaseQuerySlot (n := ch.length)) (n := (c : ℕ))
          (by simp [twoPhaseQuerySlot]; omega) (by
            change (c : ℕ) < ch.length + 2
            omega)
        simp only [hq] at hg
        simpa only using (congrArg Prod.fst hg).symm
      have hfold_mem : ∀ (i : Fin ch.length) (hi : twoPhaseFoldSlot i ∈ Sf),
          srFinalChal P ((splitGame j).symm (p, ρ, cs)) dd
              (twoPhaseFoldSlot i) =
            resolved ρ (cs, dd) ⟨twoPhaseFoldSlot i, hi⟩ := by
        intro i hi
        have hqn :
            (srOut P ((splitGame j).symm (p, ρ, cs))).query
                (twoPhaseFoldSlot i) = Qq (twoPhaseFoldSlot i) := by
          rw [SrOutput.query_le _
            (a := twoPhaseQuerySlot (n := ch.length)) (by
              simp [twoPhaseFoldSlot, twoPhaseQuerySlot]), hq]
        rw [srFinalChal_eq_resolveIn, hqn]
        rw [hTr ρ cs]
      have halg :
          (twoPhaseAlgebraChallenges ch Q
            (srFinalChal P ((splitGame j).symm (p, ρ, cs)) dd)) i.castSucc =
            (fixedAlg (resolved ρ (cs, dd))) i.castSucc := by
        simp only [twoPhaseAlgebraChallenges, fixedAlg]
        change padSched _ (i : ℕ) = padSched _ (i : ℕ)
        rw [padSched_lt _ i.isLt, padSched_lt _ i.isLt]
        by_cases hi : twoPhaseFoldSlot i ∈ Sf
        · simp only [hi, dif_pos]
          exact congrArg Prod.fst (hfold_mem i hi)
        · simp only [hi]
          have hex : ∃ e ∈ Lp, e.1 = Qq (twoPhaseFoldSlot i) := by
            by_contra hne
            refine hi ?_
            rw [hSf]
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
            · simp [twoPhaseFoldSlot]
            · intro e he heq
              exact hne ⟨e, he, heq⟩
          obtain ⟨e', hfind⟩ := find?_isSome_of_exists hex
          rw [srFinalChal_eq_resolveIn]
          have hqn :
              (srOut P ((splitGame j).symm (p, ρ, cs))).query
                  (twoPhaseFoldSlot i) = Qq (twoPhaseFoldSlot i) := by
            rw [SrOutput.query_le _
              (a := twoPhaseQuerySlot (n := ch.length)) (by
                simp [twoPhaseFoldSlot, twoPhaseQuerySlot]), hq]
          rw [hqn, hM, resolveIn_append_left hfind, resolveIn_found hfind]
          simp
      refine ⟨i, ?_⟩
      change ¬ QueryAgreementAmplifies
        (twoPhaseSampledSchedule ch Q
          (srFinalChal P ((splitGame j).symm (p, ρ, cs)) dd)) radius
        (((twoPhaseAlgebraChallenges ch Q
          (srFinalChal P ((splitGame j).symm (p, ρ, cs)) dd)) i.castSucc)⁻¹ •
          (V.word ((srOut P ((splitGame j).symm (p, ρ, cs))).πs
              (twoPhaseRootSlot i.succ)).preimage -
            V.word ((srOut P ((splitGame j).symm (p, ρ, cs))).πs
              (twoPhaseRootSlot i.castSucc)).preimage)) (wv i) at hbad
      unfold twoPhaseSampledSchedule at hbad
      rw [hfin, halg, hπ i.succ, hπ i.castSucc] at hbad
      simpa only [FixedSamplingBad, frozen] using hbad
    · intro ρ v
      have hiff : ∀ w :
          (Fin (tq - (j : ℕ) - 1) → TwoPhaseChal (F := F) Q) ×
            (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q),
          resolved ρ w = v ↔
            ∀ a ∈ Sf,
              resolveIn (runFrom P (stepOnce P Lp ρ) (List.ofFn w.1))
                (Qq a) (w.2 a) =
                  if ha : a ∈ Sf then v ⟨a, ha⟩ else ρ₀ := by
        intro w
        constructor
        · intro hw a ha
          rw [dif_pos ha]
          exact congrFun hw ⟨a, ha⟩
        · intro hw
          funext a
          have := hw a.1 a.2
          rw [dif_pos a.2] at this
          exact this
      have hcard : Nat.card {w :
          (Fin (tq - (j : ℕ) - 1) → TwoPhaseChal (F := F) Q) ×
            (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q) //
          resolved ρ w = v} =
          Fintype.card (TwoPhaseChal (F := F) Q) ^
            ((tq - (j : ℕ) - 1) + ((ch.length + 2) - Sf.card)) := by
        rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
        exact card_resolve_runFrom P Qq
          (fun a : Fin (ch.length + 2) =>
            if ha : a ∈ Sf then v ⟨a, ha⟩ else ρ₀)
          (tq - (j : ℕ) - 1) (stepOnce P Lp ρ) Sf (hfreshSf ρ) hdist
      have hkSf : Sf.card ≤ ch.length + 2 := by
        have := Finset.card_le_univ Sf
        simpa using this
      rw [hcard]
      simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_prod,
        Fintype.card_fin]
      push_cast
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    · intro v
      apply uniformProb_prod_le hεsample
      intro _ρF
      exact hsample (fun c => frozen.preimage c)
        (fun i => (fixedAlg v) i.castSucc)
  · refine le_trans (le_of_eq (uniformProb_false ?_)) hεsample
    rintro ⟨ρ, cs, dd⟩ ⟨hhit, -⟩
    obtain ⟨hq, hclean⟩ := hquery ρ cs hhit
    apply hgd
    refine ⟨?_, hclean⟩
    rw [← hq]
    simpa [twoPhaseQuerySlot] using
      SrOutput.query_pfx_length
        (srOut P ((splitGame j).symm (p, ρ, cs)))
        (twoPhaseQuerySlot (n := ch.length))

/-- The per-fibre result reassembled over the whole SR coin space.  Thus each
possible logged game slot contributes at most the fixed-schedule price once,
despite adaptive later resolution of the algebra-prefix queries. -/
theorem twoPhase_queryHitSampling_le
    (radius εsample : ℝ) (hεsample : 0 ≤ εsample)
    (hsample : TwoPhaseFixedScheduleBound (S := S) (ch := ch) (V := V)
      (Q := Q) (wv := wv) radius εsample)
    {s tq : ℕ}
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (j : Fin tq) :
    uniformProb
      ((Fin tq → TwoPhaseChal (F := F) Q) ×
        (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q))
      (TwoPhaseQueryHitSamplingBad C foldRoot ch hm hch δs hδpos hδone S V
        dom d Q wv P j radius) ≤ εsample := by
  classical
  have heq := uniformProb_equiv
    ((splitAtGame (C := TwoPhaseChal (F := F) Q)
      (D := Fin (ch.length + 2) → TwoPhaseChal (F := F) Q) j).symm)
    (TwoPhaseQueryHitSamplingBad C foldRoot ch hm hch δs hδpos hδone S V
      dom d Q wv P j radius)
  rw [← heq]
  refine uniformProb_prod_le hεsample ?_
  intro p
  refine twoPhase_queryHitSampling_fibre_le C foldRoot ch hm hch δs hδpos
    hδone S V dom d Q wv radius εsample hεsample hsample P j p
    (runFrom P [] (List.ofFn p)) ?_ ?_
  · rw [runFrom_length]
    simp
  · intro ρ cs
    rw [srTrace_eq_runFrom, ofFn_splitGame_symm, runFrom_append, runFrom_cons]

/-- Fresh designated-query sampling costs the fixed-schedule price once.  The
entire prover output is fixed by game coins, and splitting the designated
fallback coordinate leaves every earlier fold challenge unchanged. -/
theorem twoPhase_queryFreshSampling_le
    (radius εsample : ℝ) (hεsample : 0 ≤ εsample)
    (hsample : TwoPhaseFixedScheduleBound (S := S) (ch := ch) (V := V)
      (Q := Q) (wv := wv) radius εsample)
    {s tq : ℕ}
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s) :
    uniformProb
      ((Fin tq → TwoPhaseChal (F := F) Q) ×
        (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q))
      (TwoPhaseQueryFreshSamplingBad C foldRoot ch hm hch δs hδpos hδone S V
        dom d Q wv P radius) ≤ εsample := by
  classical
  let a : Fin (ch.length + 2) := twoPhaseQuerySlot (n := ch.length)
  have hsplit :
      uniformProb
        ((Fin tq → TwoPhaseChal (F := F) Q) ×
          (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q))
        (TwoPhaseQueryFreshSamplingBad C foldRoot ch hm hch δs hδpos hδone S V
          dom d Q wv P radius) =
      uniformProb
        (((Fin tq → TwoPhaseChal (F := F) Q) ×
          ({j : Fin (ch.length + 2) // j ≠ a} → TwoPhaseChal (F := F) Q)) ×
          TwoPhaseChal (F := F) Q)
        (fun x => TwoPhaseQueryFreshSamplingBad C foldRoot ch hm hch δs hδpos
          hδone S V dom d Q wv P radius
          (x.1.1, (splitCoord a).symm (x.1.2, x.2))) :=
    (uniformProb_equiv
      ((((Equiv.refl (Fin tq → TwoPhaseChal (F := F) Q)).prodCongr
        (splitCoord a)).trans (Equiv.prodAssoc _ _ _).symm).symm)
      (TwoPhaseQueryFreshSamplingBad C foldRoot ch hm hch δs hδpos hδone S V
        dom d Q wv P radius)).symm
  rw [hsplit]
  refine uniformProb_prod_le hεsample ?_
  intro rest
  let c : Fin tq → TwoPhaseChal (F := F) Q := rest.1
  obtain ⟨ρ₀⟩ :=
    (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv).chalNonempty
  let d₀ : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q :=
    (splitCoord a).symm (rest.2, ρ₀)
  by_cases hn : OracleLog.answerOf (srTrace P c)
      ((srOut P c).query a) = none
  · let u : Fin (ch.length + 1) → V.Opening :=
      fun k => ((srOut P c).πs (twoPhaseRootSlot k)).preimage
    let γ : Fin ch.length → F := fun i =>
      (twoPhaseAlgebraChallenges ch Q (srFinalChal P c d₀)) i.castSucc
    let FixedBad (ρ : TwoPhaseChal (F := F) Q) : Prop :=
      ∃ i : Fin ch.length,
        ¬ QueryAgreementAmplifies (Q.schedule ρ.2) radius
          ((γ i)⁻¹ • (V.word (u i.succ) - V.word (u i.castSucc))) (wv i)
    refine le_trans (uniformProb_mono (q := FixedBad) ?_) ?_
    · intro ρ hev
      obtain ⟨-, i, hbad⟩ := hev
      let dρ : Fin (ch.length + 2) → TwoPhaseChal (F := F) Q :=
        (splitCoord a).symm (rest.2, ρ)
      have hfin : srFinalChal P c dρ a = ρ := by
        rw [unqueried_chal_fresh P c dρ a hn]
        exact splitCoord_symm_apply_self a (rest.2, ρ)
      have halg :
          (twoPhaseAlgebraChallenges ch Q (srFinalChal P c dρ)) i.castSucc =
            γ i := by
        simp only [twoPhaseAlgebraChallenges, γ]
        change padSched _ (i : ℕ) = padSched _ (i : ℕ)
        rw [padSched_lt _ i.isLt, padSched_lt _ i.isLt]
        apply congrArg Prod.fst
        apply srFinalChal_congr
        have hne : twoPhaseFoldSlot i ≠ a := by
          exact ne_of_lt (twoPhase_foldSlot_lt_querySlot i)
        simp only [dρ, d₀]
        rw [splitCoord_symm_apply_ne hne, splitCoord_symm_apply_ne hne]
      refine ⟨i, ?_⟩
      change ¬ QueryAgreementAmplifies
        (twoPhaseSampledSchedule ch Q (srFinalChal P c dρ)) radius
        (((twoPhaseAlgebraChallenges ch Q (srFinalChal P c dρ))
          i.castSucc)⁻¹ •
          (V.word ((srOut P c).πs (twoPhaseRootSlot i.succ)).preimage -
            V.word ((srOut P c).πs
              (twoPhaseRootSlot i.castSucc)).preimage)) (wv i) at hbad
      unfold twoPhaseSampledSchedule at hbad
      rw [hfin, halg] at hbad
      simpa only [FixedBad, u, γ] using hbad
    · apply uniformProb_prod_le hεsample
      intro _ρF
      exact hsample u γ
  · refine le_trans (le_of_eq (uniformProb_false ?_)) hεsample
    rintro ρ ⟨hn', -⟩
    exact hn hn'

/-- Pointwise fresh/hit attribution for the staged sampling failure. -/
theorem twoPhaseSamplingBad_cover {s tq : ℕ}
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s)
    (radius : ℝ) :
    ∀ ω : (Fin tq → TwoPhaseChal (F := F) Q) ×
      (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q),
      TwoPhaseSamplingBad C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv
          P radius ω →
        TwoPhaseQueryFreshSamplingBad C foldRoot ch hm hch δs hδpos hδone S V
            dom d Q wv P radius ω ∨
          ∃ j : Fin tq, TwoPhaseQueryHitSamplingBad C foldRoot ch hm hch δs
            hδpos hδone S V dom d Q wv P j radius ω := by
  intro ω hbad
  rcases logSlot_cover P (twoPhaseQuerySlot (n := ch.length)) ω.1 with hn | hh
  · exact Or.inl ⟨hn, hbad⟩
  · obtain ⟨j, hj⟩ := hh
    exact Or.inr ⟨j, hj, hbad⟩

/-- Full staged sampling port: one fresh fallback schedule plus at most `tq`
logged candidates, with no independence assumption between the algebra
queries and the tested query. -/
theorem twoPhaseSamplingBad_le
    (radius εsample : ℝ) (hεsample : 0 ≤ εsample)
    (hsample : TwoPhaseFixedScheduleBound (S := S) (ch := ch) (V := V)
      (Q := Q) (wv := wv) radius εsample)
    {s tq : ℕ}
    (P : SrProver (stagedR C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv) s) :
    uniformProb
      ((Fin tq → TwoPhaseChal (F := F) Q) ×
        (Fin (ch.length + 2) → TwoPhaseChal (F := F) Q))
      (TwoPhaseSamplingBad C foldRoot ch hm hch δs hδpos hδone S V dom d Q wv
        P radius) ≤ ((tq : ℝ) + 1) * εsample := by
  refine le_trans (uniformProb_mono
    (twoPhaseSamplingBad_cover C foldRoot ch hm hch δs hδpos hδone S V dom d
      Q wv P radius)) ?_
  refine le_trans (uniformProb_or_le _ _) ?_
  refine le_trans (add_le_add
    (twoPhase_queryFreshSampling_le C foldRoot ch hm hch δs hδpos hδone S V
      dom d Q wv radius εsample hεsample hsample P)
    (uniformProb_exists_le fun j =>
      TwoPhaseQueryHitSamplingBad C foldRoot ch hm hch δs hδpos hδone S V dom
        d Q wv P j radius)) ?_
  refine le_trans (add_le_add le_rfl
    (Finset.sum_le_sum fun j _ =>
      twoPhase_queryHitSampling_le C foldRoot ch hm hch δs hδpos hδone S V dom
        d Q wv radius εsample hεsample hsample P j)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-! ## Concrete sampler inhabitants -/

/-- The literal full-domain IID sampler. -/
def fullDomainTwoPhaseQuerySampler (m t : ℕ) (hm : 0 < m) :
    TwoPhaseQuerySampler m t where
  Query := Fin t → Fin m
  queryFintype := inferInstance
  queryNonempty := ⟨fun _ => ⟨0, hm⟩⟩
  schedule := id

omit [Fintype F] in
/-- The fixed-schedule interface is inhabited at the familiar IID rate for
the literal full-domain sampler. -/
theorem fullDomainTwoPhase_fixedScheduleBound
    (radius : ℝ) (hradius1 : radius ≤ 1) :
    TwoPhaseFixedScheduleBound (S := S) (ch := ch) (V := V)
      (Q := fullDomainTwoPhaseQuerySampler m t hm) (wv := wv) radius
      ((ch.length : ℝ) * (1 - radius) ^ t) := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  intro u γ
  let frozen : FrozenPreimagePhase S V (k := ch.length + 1) :=
    { root := fun c => S.commit (V.word (u c))
      preimage := u }
  have hb := frozenLinks_samplingFailure_uniform (t := t) S V frozen
    (fun c => padSched γ (c : ℕ)) wv radius hradius1
  simpa [fullDomainTwoPhaseQuerySampler, frozen, padSched] using hb

/-- The literal allowed-coordinate, ordered-without-replacement sampler. -/
noncomputable def allowedTwoPhaseQuerySampler (allowed : Finset (Fin m))
    (hne : Nonempty (AllowedInjectiveSchedule allowed t)) :
    TwoPhaseQuerySampler m t where
  Query := AllowedInjectiveSchedule allowed t
  queryFintype := inferInstance
  queryNonempty := hne
  schedule := allowedSchedule

omit [Fintype F] in
/-- Constrained-mask inhabitant of the fixed-schedule interface.  The premise
is universally quantified over frozen openings and algebra challenges, which
is exactly what the adaptive hit proof needs; it is the falling-factorial
premise, not a silently substituted IID statement. -/
theorem allowedTwoPhase_fixedScheduleBound
    (allowed : Finset (Fin m))
    (hne : Nonempty (AllowedInjectiveSchedule allowed t))
    (radius : ℝ) (agreeCap : Fin ch.length → ℕ)
    (hprem : ∀ (u : Fin (ch.length + 1) → V.Opening)
      (γ : Fin ch.length → F) (i : Fin ch.length),
      AllowedWithoutReplacementFallingPremise allowed t radius
        ((γ i)⁻¹ • (V.word (u i.succ) - V.word (u i.castSucc)))
        (wv i) (agreeCap i)) :
    TwoPhaseFixedScheduleBound (S := S) (ch := ch) (V := V)
      (Q := allowedTwoPhaseQuerySampler (t := t) allowed hne) (wv := wv)
      radius (∑ i : Fin ch.length,
        fallingFactorialMiss (agreeCap i) allowed.card t) := by
  classical
  intro u γ
  let frozen : FrozenPreimagePhase S V (k := ch.length + 1) :=
    { root := fun c => S.commit (V.word (u c))
      preimage := u }
  have hb := allowedFrozenLinks_samplingFailure_uniform S V frozen
    (fun c => padSched γ (c : ℕ)) wv allowed radius agreeCap (fun i => by
      simpa [frozen, padSched] using hprem u γ i)
  simpa [allowedTwoPhaseQuerySampler, frozen, padSched] using hb

/-- info: 'Minidregg.Selvage.twoPhase_queryHitSampling_fibre_le' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhase_queryHitSampling_fibre_le
/-- info: 'Minidregg.Selvage.twoPhase_queryHitSampling_le' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhase_queryHitSampling_le
/-- info: 'Minidregg.Selvage.twoPhase_queryFreshSampling_le' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhase_queryFreshSampling_le
/-- info: 'Minidregg.Selvage.twoPhaseSamplingBad_cover' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhaseSamplingBad_cover
/-- info: 'Minidregg.Selvage.twoPhaseSamplingBad_le' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoPhaseSamplingBad_le
/-- info: 'Minidregg.Selvage.fullDomainTwoPhase_fixedScheduleBound' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fullDomainTwoPhase_fixedScheduleBound
/-- info: 'Minidregg.Selvage.allowedTwoPhase_fixedScheduleBound' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allowedTwoPhase_fixedScheduleBound

end SamplingHit

end Minidregg.Selvage
