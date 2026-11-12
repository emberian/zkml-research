/-
# Selvage.OracleLogLinkedAssembly — corrected deployed-ZK horn bounds

This module advances the exact-extractor target from
`Selvage.OracleLogLinkedTarget` without weakening it.  It proves:

* the linked verifier's accepting-output characterization;
* the fresh-horn `1/|F|` bound for a fixed linked output and all coins except
  one designated fresh challenge;
* the sound-event fresh/hit cover at the linked log extractor;
* the hit-horn `1/|F|` bound once per game slot, uniformly over the bad link;
* the complete `(t + k)` union bound and an `OracleLogReduction` whose
  extractor is definitionally the linked shifted-log reader.

Thus this module closes `DeployedZKAdaptiveSoundLinkedTarget`.  No alternate
extractor is introduced.
-/
import Selvage.OracleLogLinkedTarget

namespace Minidregg.Selvage

/-! ## Counting and schedule plumbing -/

/-- A predicate with at most one inhabitant has uniform probability at most
`1/|F|`. -/
theorem uniformProb_le_inv_card_of_subsingleton_public (F : Type) [Fintype F]
    {p : F → Prop} (h : ∀ a b, p a → p b → a = b) :
    uniformProb F p ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  unfold uniformProb
  have hcard : (Nat.card {c : F // p c} : ℝ) ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_le_one_iff.mpr fun a b =>
      Subtype.ext (h _ _ a.2 b.2)
  gcongr

/-- Replace the challenge that folds link `i`; the reduction has one extra
inert final challenge, hence the `castSucc`. -/
def challengeVectorAt {F : Type} {n : ℕ} (ρs : Fin (n + 1) → F)
    (i : Fin n) (ρ : F) : Fin (n + 1) → F :=
  Function.update ρs i.castSucc ρ

/-- Updating the reduction challenge vector at `i.castSucc` is exactly
updating the aggregate schedule at link `i`. -/
theorem padSched_challengeVectorAt {F : Type} [Field F] {n : ℕ}
    (ρs : Fin (n + 1) → F) (i : Fin n) (ρ : F) :
    padSched (fun k : Fin n => challengeVectorAt ρs i ρ k.castSucc) =
      scheduleAt (padSched fun k : Fin n => ρs k.castSucc) (i : ℕ) ρ := by
  funext a
  by_cases hai : a = (i : ℕ)
  · subst a
    simp [challengeVectorAt, scheduleAt, padSched_lt, i.isLt,
      Function.update_self]
  · rw [scheduleAt, Function.update_of_ne hai]
    by_cases ha : a < n
    · let k : Fin n := ⟨a, ha⟩
      have hki : k ≠ i := fun h => hai (congrArg Fin.val h)
      have hcast : k.castSucc ≠ i.castSucc := fun h => hki (Fin.castSucc_inj.mp h)
      rw [padSched_lt _ ha, padSched_lt _ ha, challengeVectorAt,
        Function.update_of_ne hcast]
    · have hge : n ≤ a := Nat.not_lt.mp ha
      rw [padSched_of_le _ hge, padSched_of_le _ hge]

/-! ## Linked verifier acceptance exposes exactly the data the horns need -/

section Linked

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F))
  (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m) (wv : Fin ch.length → Fin m → F)

/-- Linked FS acceptance fixes the output to the aggregate and synthesized
last word, and exposes every verifier-enforced link opening. -/
theorem linked_fiatShamir_accept_data {s : ℕ}
    (o : SrOutput
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (hacc : fiatShamir
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s
      (fsOracle o ρs) o = some out) :
    out =
        (aggregate foldRoot (padSched fun i : Fin ch.length => ρs i.castSucc)
          o.stmt.x ch,
        bcsWord dom d q (o.πs (Fin.last ch.length))) ∧
      ∀ i : Fin ch.length,
        LinkOpened S q (S.commit (wv i)) (o.πs i.castSucc) (o.πs i.succ)
          (ρs i.castSucc) := by
  classical
  rw [fiatShamir_fsOracle] at hacc
  by_cases hc : (∀ i, ColsOpen S q (o.πs i)) ∧
      (∀ j, (o.πs 0).cols j = o.stmt.y (q j)) ∧
      ∀ i : Fin ch.length,
        LinkOpened S q (S.commit (wv i)) (o.πs i.castSucc) (o.πs i.succ)
          (ρs i.castSucc)
  · change (if (∀ i, ColsOpen S q (o.πs i)) ∧
          (∀ j, (o.πs 0).cols j = o.stmt.y (q j)) ∧
          ∀ i : Fin ch.length,
            LinkOpened S q (S.commit (wv i)) (o.πs i.castSucc) (o.πs i.succ)
              (ρs i.castSucc)
        then some (aggregate foldRoot
          (padSched fun i : Fin ch.length => ρs i.castSucc) o.stmt.x ch,
          bcsWord dom d q (o.πs (Fin.last ch.length))) else none) = some out at hacc
    rw [if_pos hc] at hacc
    exact ⟨(Option.some.inj hacc).symm, hc.2.2⟩
  · change (if (∀ i, ColsOpen S q (o.πs i)) ∧
          (∀ j, (o.πs 0).cols j = o.stmt.y (q j)) ∧
          ∀ i : Fin ch.length,
            LinkOpened S q (S.commit (wv i)) (o.πs i.castSucc) (o.πs i.succ)
              (ρs i.castSucc)
        then some (aggregate foldRoot
          (padSched fun i : Fin ch.length => ρs i.castSucc) o.stmt.x ch,
          bcsWord dom d q (o.πs (Fin.last ch.length))) else none) = some out at hacc
    rw [if_neg hc] at hacc
    simp at hacc

/-- **The linked-specific fresh fibre bound.**  Fix the prover output and every
challenge except link `i`'s fresh challenge.  If the exact log extractor returns
zero and zero is not aligned at that link, linked acceptance with a δ-close
target witness occurs for at most one challenge. -/
theorem linkedFreshOutputFibre_le
    {dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    {δ : ℝ} (hδC : δ < dC / 2) {s : ℕ}
    (o : SrOutput
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (ρs : Fin (ch.length + 1) → F) (i : Fin ch.length)
    (hbad : ¬ LinkAligned C o.stmt.x ch i (0 : Fin m → F)) :
    uniformProb F (fun ρ =>
      ∃ (x' : AccClaim Root F (Fin m) r) (y' : Fin m → F),
        fiatShamir
            (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s
            (fsOracle o (challengeVectorAt ρs i ρ)) o = some (x', y') ∧
        RelaxedMem
          (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv).R'
          δ o.stmt.idx x' y' o.w')
      ≤ 1 / (Fintype.card F : ℝ) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨j, hj⟩ := exists_nonzero_target_of_zero_not_linkAligned C ch i hbad
  refine uniformProb_le_inv_card_of_subsingleton_public F fun ρ₁ ρ₂ h₁ h₂ => ?_
  obtain ⟨x₁, y₁, hacc₁, hrel₁⟩ := h₁
  obtain ⟨x₂, y₂, hacc₂, hrel₂⟩ := h₂
  have hd₁ := linked_fiatShamir_accept_data C foldRoot ch hm hch δs hδpos hδone
    S dom d q wv o (challengeVectorAt ρs i ρ₁) hacc₁
  have hd₂ := linked_fiatShamir_accept_data C foldRoot ch hm hch δs hδpos hδone
    S dom d q wv o (challengeVectorAt ρs i ρ₂) hacc₂
  have hx₁ : x₁ = aggregate foldRoot
      (padSched fun k : Fin ch.length => challengeVectorAt ρs i ρ₁ k.castSucc)
      o.stmt.x ch := by simpa using congrArg Prod.fst hd₁.1
  have hy₁ : y₁ = bcsWord dom d q (o.πs (Fin.last ch.length)) := by
    simpa using congrArg Prod.snd hd₁.1
  have hx₂ : x₂ = aggregate foldRoot
      (padSched fun k : Fin ch.length => challengeVectorAt ρs i ρ₂ k.castSucc)
      o.stmt.x ch := by simpa using congrArg Prod.fst hd₂.1
  have hy₂ : y₂ = bcsWord dom d q (o.πs (Fin.last ch.length)) := by
    simpa using congrArg Prod.snd hd₂.1
  obtain ⟨z₁, hz₁, hclose₁⟩ := hrel₁
  obtain ⟨z₂, hz₂, hclose₂⟩ := hrel₂
  rw [fracHamming_eq_relDist] at hclose₁ hclose₂
  have hs₁ : AccClaim.Satisfies C
      (aggregate foldRoot
        (scheduleAt (padSched fun k : Fin ch.length => ρs k.castSucc)
          (i : ℕ) ρ₁) o.stmt.x ch) z₁ := by
    change AccClaim.Satisfies C x₁ z₁ at hz₁
    rw [hx₁, padSched_challengeVectorAt] at hz₁
    exact hz₁
  have hs₂ : AccClaim.Satisfies C
      (aggregate foldRoot
        (scheduleAt (padSched fun k : Fin ch.length => ρs k.castSucc)
          (i : ℕ) ρ₂) o.stmt.x ch) z₂ := by
    change AccClaim.Satisfies C x₂ z₂ at hz₂
    rw [hx₂, padSched_challengeVectorAt] at hz₂
    exact hz₂
  have hc₁ : relDist (bcsWord dom d q (o.πs (Fin.last ch.length))) z₁ ≤ δ := by
    rw [← hy₁]
    exact hclose₁
  have hc₂ : relDist (bcsWord dom d q (o.πs (Fin.last ch.length))) z₂ ≤ δ := by
    rw [← hy₂]
    exact hclose₂
  exact freshAggregateChallenge_injective foldRoot
    (padSched fun k : Fin ch.length => ρs k.castSucc) i
    (bcsWord dom d q (o.πs (Fin.last ch.length))) hdC hδC j hj
    ⟨z₁, hs₁, hc₁⟩ ⟨z₂, hs₂, hc₂⟩

/-- On an unqueried designated prefix, splitting out its fallback coin changes
the full final-challenge vector at exactly that one coordinate. -/
theorem linked_srFinalChal_split_of_none {s tq : ℕ}
    (P : SrProver
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (c : Fin tq → F) (i : Fin ch.length)
    (rest : {j : Fin (ch.length + 1) // j ≠ i.castSucc} → F) (ρ : F)
    (hnone : OracleLog.answerOf (srTrace P c)
      ((srOut P c).query i.castSucc) = none) :
    srFinalChal P c ((splitCoord i.castSucc).symm (rest, ρ)) =
      challengeVectorAt
        (srFinalChal P c ((splitCoord i.castSucc).symm (rest, 0))) i ρ := by
  funext a
  by_cases hai : a = i.castSucc
  · subst a
    rw [srFinalChal_eq_answerOf, hnone]
    simp [challengeVectorAt, Function.update_self]
  · rw [challengeVectorAt, Function.update_of_ne hai]
    apply srFinalChal_congr
    rw [splitCoord_symm_apply_ne hai, splitCoord_symm_apply_ne hai]

/-! ## The linked sound event and its horn cover -/

/-- The exact `sound_log` event for the corrected linked log extractor. -/
def LinkedLogSoundEvent {s tq : ℕ} (δ : ℝ)
    (P : SrProver
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (coins : (Fin tq → F) × (Fin (ch.length + 1) → F)) : Prop :=
  let log := srTrace P coins.1
  let o := srOut P coins.1
  let ρs := srFinalChal P coins.1 coins.2
  o.stmt ∈ linkedStatementSet C foldRoot ch hm hch δs hδpos hδone S dom d q wv ∧
  ¬ RelaxedMem
    (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv).R
    δ o.stmt.idx o.stmt.x o.stmt.y
      (linkedShiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q wv
        s o log) ∧
  ∃ (x' : AccClaim Root F (Fin m) r) (y' : Fin m → F),
    fiatShamir
        (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s
        (fsOracle o ρs) o = some (x', y') ∧
    RelaxedMem
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv).R'
      δ o.stmt.idx x' y' o.w'

/-- Fresh badness at one source-link coordinate. -/
def LinkedFreshBad {s tq : ℕ} (δ : ℝ)
    (P : SrProver
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (i : Fin ch.length)
    (coins : (Fin tq → F) × (Fin (ch.length + 1) → F)) : Prop :=
  LinkedLogSoundEvent C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P coins ∧
  OracleLog.answerOf (srTrace P coins.1)
    ((srOut P coins.1).query i.castSucc) = none ∧
  ¬ LinkAligned C (srOut P coins.1).stmt.x ch i
    (linkedShiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q wv
      s (srOut P coins.1) (srTrace P coins.1) i)

/-- Hit badness at one game-query slot, existential over the bad source link so
the slot pays `1/|F|` only once. -/
def LinkedHitBad {s tq : ℕ} (δ : ℝ)
    (P : SrProver
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (j : Fin tq)
    (coins : (Fin tq → F) × (Fin (ch.length + 1) → F)) : Prop :=
  LinkedLogSoundEvent C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P coins ∧
  ∃ i : Fin ch.length,
    hitAt P i.castSucc j coins.1 ∧
    ¬ LinkAligned C (srOut P coins.1).stmt.x ch i
      (linkedShiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q wv
        s (srOut P coins.1) (srTrace P coins.1) i)

/-- Every corrected linked sound event lies in a fresh link horn or a hit game
slot horn. -/
theorem linkedLogSoundEvent_cover {s tq : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (P : SrProver
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s) :
    ∀ coins, LinkedLogSoundEvent C foldRoot ch hm hch δs hδpos hδone S dom d q wv
        δ P coins →
      (∃ i : Fin ch.length,
        LinkedFreshBad C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P i coins) ∨
      (∃ j : Fin tq,
        LinkedHitBad C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P j coins) := by
  intro coins hev
  have hev' := hev
  obtain ⟨hz, hfail, hacc⟩ := hev
  obtain ⟨i, hbad⟩ := linked_source_failure_has_bad_link C foldRoot ch hm hch δs
    hδpos hδone S dom d q wv hz hδ hfail
  rcases logSlot_cover P i.castSucc coins.1 with hfresh | ⟨j, hhit⟩
  · exact Or.inl ⟨i, hev', hfresh, hbad⟩
  · exact Or.inr ⟨j, hev', i, hhit, hbad⟩

/-- **Fresh horn, one link:** after splitting out the unqueried fallback coin,
the prover output, log, and last word are fixed.  The exact extractor is zero;
if zero misaligns, `linkedFreshOutputFibre_le` gives at most one accepting draw.
-/
theorem linkedFreshLink_le
    {dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hδsC : δs ≤ dC / 2)
    {s tq : ℕ} {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) δs)
    (P : SrProver
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (i : Fin ch.length) :
    uniformProb ((Fin tq → F) × (Fin (ch.length + 1) → F))
      (LinkedFreshBad C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P i)
      ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  let a : Fin (ch.length + 1) := i.castSucc
  have hsplit : uniformProb ((Fin tq → F) × (Fin (ch.length + 1) → F))
      (LinkedFreshBad C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P i) =
      uniformProb
        (((Fin tq → F) × ({j : Fin (ch.length + 1) // j ≠ a} → F)) × F)
        (fun x => LinkedFreshBad C foldRoot ch hm hch δs hδpos hδone S dom d q
          wv δ P i (x.1.1, (splitCoord a).symm (x.1.2, x.2))) :=
    (uniformProb_equiv
      ((((Equiv.refl (Fin tq → F)).prodCongr (splitCoord a)).trans
        (Equiv.prodAssoc _ _ _).symm).symm)
      (LinkedFreshBad C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P i)).symm
  rw [hsplit]
  refine uniformProb_prod_le (by positivity) fun rest => ?_
  let c : Fin tq → F := rest.1
  let d₀ : Fin (ch.length + 1) → F := (splitCoord a).symm (rest.2, 0)
  let o := srOut P c
  let ρs := srFinalChal P c d₀
  by_cases hbad : ¬ LinkAligned C o.stmt.x ch i (0 : Fin m → F)
  · refine le_trans (uniformProb_mono ?_)
      (linkedFreshOutputFibre_le C foldRoot ch hm hch δs hδpos hδone S dom d q
        wv hdC (lt_of_lt_of_le hδ.2 hδsC) o ρs i hbad)
    intro ρ hev
    obtain ⟨-, -, x', y', hacc, hrel⟩ := hev.1
    have hvec := linked_srFinalChal_split_of_none C foldRoot ch hm hch δs hδpos
      hδone S dom d q wv P c i rest.2 ρ hev.2.1
    refine ⟨x', y', ?_, hrel⟩
    rw [← hvec]
    exact hacc
  · refine le_trans (le_of_eq (uniformProb_false fun ρ hev => ?_)) (by positivity)
    have hz := linkedShiftedLogExtractor_eq_zero_of_unqueried C foldRoot ch hm
      hch δs hδpos hδone S dom d q wv (srOut P c) (srTrace P c) i hev.2.1
    have he := hev.2.2
    change ¬ LinkAligned C (srOut P c).stmt.x ch i
      (linkedShiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q
        wv s (srOut P c) (srTrace P c) i) at he
    rw [hz] at he
    exact hbad he

/-- **Hit horn, linked and uniform in the bad link:** a linked accepting run
supplies `LinkOpened`; on `hitAt`, the logged answer is the game coin `c_j`.
At nonzero `c_j`, binding and erasure recovery pin the exact log extractor to
`wv i`, while statement-set membership says that word is aligned.  Thus the
whole existential-over-links event is contained in `{c_j = 0}`. -/
theorem linkedHitSlot_le (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    {s tq : ℕ} {δ : ℝ}
    (P : SrProver
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (j : Fin tq) :
    uniformProb ((Fin tq → F) × (Fin (ch.length + 1) → F))
      (LinkedHitBad C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P j)
      ≤ 1 / (Fintype.card F : ℝ) := by
  refine le_trans (uniformProb_mono ?_) (uniformProb_prod_coord_le j 0)
  rintro ⟨c, dd⟩ ⟨hev, i, hhit, hbad⟩
  show c j = 0
  by_contra hne
  obtain ⟨hz, -, x', y', hacc, -⟩ := hev
  have hans := hitAt_answerOf P hhit
  have hchal : srFinalChal P c dd i.castSucc = c j := by
    rw [srFinalChal_eq_answerOf, hans]
    rfl
  have hdata := linked_fiatShamir_accept_data C foldRoot ch hm hch δs hδpos
    hδone S dom d q wv (srOut P c) (srFinalChal P c dd) hacc
  have hlink := hdata.2 i
  rw [hchal] at hlink
  have hpin : linkedShiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S
      dom d q wv s (srOut P c) (srTrace P c) i = wv i := by
    unfold linkedShiftedLogExtractor linkedLogIncrement
    rw [hans, Option.map_some, Option.getD_some]
    exact linkOpened_increment_pinned_free S dom hdt hq (hwv i) rfl hne hlink
  rw [hpin] at hbad
  exact hbad (hz.2 i)

/-! ## `(t + k)` assembly and the corrected target -/

/-- The full corrected log-sound event costs at most one field inverse per
fresh source link and per game-query slot.  The reduction has one additional
inert final challenge, so this is bounded by the advertised `(t + k)/|F|`. -/
theorem linkedLogSoundEvent_le_inv
    {dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hδsC : δs ≤ dC / 2)
    (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    {s tq : ℕ} {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) δs)
    (P : SrProver
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s) :
    uniformProb ((Fin tq → F) × (Fin (ch.length + 1) → F))
      (LinkedLogSoundEvent C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P)
      ≤ ((tq : ℝ) + ((ch.length + 1 : ℕ) : ℝ)) /
        (Fintype.card F : ℝ) := by
  refine le_trans (uniformProb_mono
    (linkedLogSoundEvent_cover C foldRoot ch hm hch δs hδpos hδone S dom d q
      wv hδ.1.le P)) ?_
  refine le_trans (uniformProb_or_le _ _) ?_
  refine le_trans (add_le_add
    (uniformProb_exists_le fun i =>
      LinkedFreshBad C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P i)
    (uniformProb_exists_le fun j =>
      LinkedHitBad C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P j)) ?_
  refine le_trans (add_le_add
    (Finset.sum_le_sum fun i _ => linkedFreshLink_le C foldRoot ch hm hch δs
      hδpos hδone S dom d q wv hdC hδsC hδ P i)
    (Finset.sum_le_sum fun j _ => linkedHitSlot_le C foldRoot ch hm hch δs
      hδpos hδone S dom d q wv hdt hq hwv P j)) ?_
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  rw [div_eq_mul_inv]
  ring_nf
  have hcard : 0 ≤ (Fintype.card F : ℝ)⁻¹ := by positivity
  linarith

/-- The same assembly at `accRbrError = errstar + 1/|F|`; only nonnegativity
of the proximity term is needed because both linked horns already price at the
sharper field-inverse bound. -/
theorem linkedLogSoundEvent_le_accRbrError
    {dC : ℝ} {errstar : ℝ → ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hδsC : δs ≤ dC / 2)
    (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ)
    {s tq : ℕ} {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) δs)
    (P : SrProver
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s) :
    uniformProb ((Fin tq → F) × (Fin (ch.length + 1) → F))
      (LinkedLogSoundEvent C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P)
      ≤ ((tq : ℝ) + ((ch.length + 1 : ℕ) : ℝ)) * accRbrError F errstar δ := by
  refine le_trans (linkedLogSoundEvent_le_inv C foldRoot ch hm hch δs hδpos
    hδone S dom d q wv hdC hδsC hdt hq hwv hδ P) ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold accRbrError
  rw [one_div]
  have hs := hstar δ hδ
  linarith

/-- The exact linked log reduction promised by the repaired target. -/
noncomputable def linkedOracleLogReduction_exact
    {dC : ℝ} (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hδsC : δs ≤ dC / 2)
    (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ) :
    OracleLogReduction
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
      (linkedStatementSet C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
      (accRbrError F errstar) where
  extractLog := linkedShiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone
    S dom d q wv
  sound_log := by
    intro s tq δ hδ P
    change uniformProb ((Fin tq → F) × (Fin (ch.length + 1) → F))
      (LinkedLogSoundEvent C foldRoot ch hm hch δs hδpos hδone S dom d q wv δ P)
      ≤ ((tq : ℝ) + ((ch.length + 1 : ℕ) : ℝ)) * accRbrError F errstar δ
    exact linkedLogSoundEvent_le_accRbrError C foldRoot ch hm hch δs hδpos
      hδone S dom d q wv hdC hδsC hdt hq hwv hstar hδ P

/-- **The corrected exact-extractor target is closed.** -/
theorem linkedAdaptiveIncrementSound_proved
    {dC : ℝ} (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hδsC : δs ≤ dC / 2)
    (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ) :
    LinkedAdaptiveIncrementSound C foldRoot ch hm hch δs hδpos hδone S dom d q
      wv errstar := by
  refine ⟨linkedOracleLogReduction_exact C foldRoot ch hm hch δs hδpos hδone S
    dom d q wv errstar hdC hδsC hdt hq hwv hstar, ?_⟩
  intro s
  rfl

/-- The implication-shaped statement boundary from the audit module, fully
discharged without changing its hypotheses or extractor constraint. -/
theorem deployedZKAdaptiveSoundLinkedTarget_proved (dC : ℝ)
    (errstar : ℝ → ℝ) :
    DeployedZKAdaptiveSoundLinkedTarget C foldRoot ch hm hch δs hδpos hδone S
      dom d q wv dC errstar := by
  intro hdt hq hwv hdC hδsC hstar
  exact linkedAdaptiveIncrementSound_proved C foldRoot ch hm hch δs hδpos
    hδone S dom d q wv errstar hdC hδsC hdt hq hwv hstar

end Linked

/-! ## Concrete premise firing -/

namespace OracleLogLinkedAssemblyExample

open RSExample LCExample AccExample ZkHidingExample ZkExtractionExample
  CommitExample AccRbrBcsExample AccRbrBcsShiftedExample AccSoundRbrExample
  AccRbrInstanceExample OracleLogProgramExample OracleLogLinkedExample

/-- The repaired theorem is not merely implication-shaped plumbing: its exact
extractor inhabitant fires on the existing `F₅` linked example, with every
distance, rate, injectivity, and proximity premise kernel-checked. -/
theorem linkedAdaptiveIncrementSound_F5 :
    LinkedAdaptiveIncrementSound
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ dom₅ 2 qPair msEx (fun _ => 0) := by
  apply linkedAdaptiveIncrementSound_proved
    (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
    (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ dom₅ 2 qPair msEx (dC := 1 / 4) (fun _ => 0)
  · intro u _ v _ hne
    simpa [Fintype.card_fin] using
      (one_div_card_le_relDist (F := ZMod 5) hne)
  · norm_num
  · norm_num
  · exact qPair_inj
  · exact msEx_mem
  · intro δ _
    norm_num

end OracleLogLinkedAssemblyExample

/-- info: 'Minidregg.Selvage.uniformProb_le_inv_card_of_subsingleton_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uniformProb_le_inv_card_of_subsingleton_public
/-- info: 'Minidregg.Selvage.padSched_challengeVectorAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padSched_challengeVectorAt
/-- info: 'Minidregg.Selvage.linked_fiatShamir_accept_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linked_fiatShamir_accept_data
/-- info: 'Minidregg.Selvage.linkedFreshOutputFibre_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkedFreshOutputFibre_le
/-- info: 'Minidregg.Selvage.linked_srFinalChal_split_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linked_srFinalChal_split_of_none
/-- info: 'Minidregg.Selvage.linkedLogSoundEvent_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkedLogSoundEvent_cover
/-- info: 'Minidregg.Selvage.linkedFreshLink_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkedFreshLink_le
/-- info: 'Minidregg.Selvage.linkedHitSlot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkedHitSlot_le
/-- info: 'Minidregg.Selvage.linkedLogSoundEvent_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkedLogSoundEvent_le_inv
/-- info: 'Minidregg.Selvage.linkedOracleLogReduction_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkedOracleLogReduction_exact
/-- info: 'Minidregg.Selvage.linkedAdaptiveIncrementSound_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkedAdaptiveIncrementSound_proved
/-- info: 'Minidregg.Selvage.deployedZKAdaptiveSoundLinkedTarget_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployedZKAdaptiveSoundLinkedTarget_proved
/-- info: 'Minidregg.Selvage.OracleLogLinkedAssemblyExample.linkedAdaptiveIncrementSound_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedAssemblyExample.linkedAdaptiveIncrementSound_F5

end Minidregg.Selvage
