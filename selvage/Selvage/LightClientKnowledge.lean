/-
# Selvage.LightClientKnowledge — the light client's knowledge soundness about ONE prover.

`Selvage/AccExtractChain.lean`'s `lightClientKnowledgeSound` takes `n + 1`
SEPARATELY-GIVEN verifying transcripts (`hbase`/`hpert`): a base word `h₀` and
one perturbed word `hs k` per link, each assumed to verify the aggregate at its
own schedule. `Selvage/LightClientSound.lean`'s `lightClientSound` is anchored
at a DIFFERENT object: the prover's committed words `ws`/`f₀`, folded at ONE
uniformly sampled schedule. Nothing coupled the two — `Assurance/SelvageV0.lean`
named the decoupling in its own docstring ("Deliberately independent
parameters `ws`/`f₀` … versus `γs`/`h₀`/`hs`"), and
`Selvage/AccSoundRbr.lean:76-83` named the reason: the natural realizer is
TWO-POINT (`extractPair` needs two fold evaluations at distinct challenges)
while a straightline extractor is seeded from ONE execution.

**This file closes that decoupling at the word level.** The material was
already landed: `Selvage/ZkExtraction.lean`'s `seamCounterfactual` synthesizes
every perturbed transcript from ONE execution's public view — the base word,
the public schedule, and the `t ≥ d` opened columns of the recommitted partial
folds (erasure decoding, `recoverFromColumns_sound`). What was missing is the
extractor that CONSUMES it as a function of one execution, and the theorem
that prices it against the SAME prover `lightClientSound` prices.

* `lcExtract` — **the one-prover light-client extractor**: a pure function of
  the execution's public view `(γs, h₀, cols)` — no second run, no witness,
  no alternate schedule supplied from outside (the extractor picks its own
  counterfactual challenge `γ + 1`, distinct from `γ` in every field:
  `succSched_ne`). `lcExtract_eq_ofFn`: under binding and codeword words it
  returns EXACTLY the prover's committed words `ms` — the extractor talks
  about one prover, by construction.
* `lightClientKnowledgeSound_seam` — `lightClientKnowledgeSound` with
  `hbase`/`hpert` DERIVED: the transcript family is `(foldWords γs f₀ ws,
  seamCounterfactual …)`, both computed from the prover's `ws`/`f₀` and its
  opened columns; the only verification hypotheses left are about the
  prover's OWN words folded at the base and the `n` counterfactual schedules.
* `lightClientKnowledgeSound_oneProver` — **the apex, the RBR-shaped
  statement about ONE prover**: for a prover with fixed committed words
  `ms`/`f₀` (the non-adaptive model `lightClientSound` already uses), over
  ONE uniformly sampled schedule,

    `Pr[ the base transcript δ-verifies ∧ ¬(attests ∧ lcExtract's output is
         linkwise δ-close to genuine witnesses) ] ≤ n · (err⋆(δ) + 2/|F|)`.

  No `hbase`, no `hpert`, no `hfalse`: the two roles the capstone kept apart
  are one event about one prover. Proof: case on whether every committed word
  is δ-close to a witness of its link. If yes, the extractor returns the words
  themselves (`lcExtract_eq_ofFn`) whenever every challenge is nonzero, so the
  bad event forces a zero challenge coordinate — `n/|F|` by the coordinate
  bound. If no, some word is δ-far-false and `lightClientSound` (REUSED
  verbatim, its `hfalse` being exactly the negation) prices the verification
  event at `n · (err⋆ + 1/|F|)`. The extra `1/|F|` per link is REAL for this
  extractor, not slack: at `γ_k = 0` link `k`'s word contributes nothing to
  any recommitted fold, so no function of the opened columns can see it.
* `lightClientKnowledgeSound_oneProver_committed` — the same with the columns
  entering ONLY through verified openings against a `BindingCommitment` of
  each recommitted partial fold (`binding_columns`, `[ACC-extract-bind]`).

**ATLAS fields (law 2), all over the landed F₅ instances:**

* satisfiable — `lcExtract_recovers_F5`: on `goodChain`'s honest prover
  `(xWord, [0, oneWord])` the one-execution extractor returns `[0, oneWord]`.
* premise inhabitation — `knowledge_seam_fires_F5` (the derived-transcript
  theorem fires at `C = RS`), `oneProver_fires_F5` (the apex fires at
  `C = ⊤`, δ = 1/16, bound `4/5`), every hypothesis discharged by landed
  witnesses.
* teeth, the seam precondition — `seam_teeth_noncodeword_F5`: a prover whose
  link-1 word is NOT a codeword (`δ₂ = (0,0,1,0)`, `δ₂_not_mem`) but meets
  the channel: the seam-derived perturbed transcript does NOT verify, while
  the TRUE perturbed transcript does. `hms` is a constraint, not decoration.
* teeth, the apex bound — `oneProver_teeth_noncodeword_F5`: for that same
  prover every OTHER hypothesis of the apex holds (`C = ⊤`, honest columns
  by `rfl`) and the bad event has probability EXACTLY `1 > 4/5`: drop `hms`
  and the theorem is FALSE. The erasure seam is where the codeword promise
  is consumed, and the `[ACC-extract-bind]` scope ("genuine codewords,
  unique decoding") is load-bearing here exactly as `Selvage/Erasure.lean`
  says.

**Honest scope.** Word level, unique decoding (`d ≤ t`, codeword words),
non-adaptive prover (words fixed before the schedule — `lightClientSound`'s
model; the grinding lift is `Selvage/LightClientGrinding.lean`'s), uniform
schedule (the FS transport is `[FS-ROM]`/`Selvage/LightClientFS.lean`). The
Def-4.2 `RbrKnowledgeSoundness` packaging of `lcExtract` (`[ACC-sound-rbr-game]`)
is NOT built here: the apex is the light-client-event form of that packaging,
and it is what `Assurance/SelvageV0.lean`'s `knowledge` field now cites.
-/
import Selvage.ZkExtraction
import Selvage.LightClientSound
import Selvage.Sumcheck

namespace Minidregg.Selvage

variable {Root : Type*} {F : Type} [Field F] {ι : Type*} {r : ℕ}

/-! ## The extractor's own counterfactual challenge -/

/-- The extractor's alternate schedule: every coordinate shifted by one.
Distinct from the base at EVERY coordinate in EVERY field (`succSched_ne`), so
the extractor never depends on an externally supplied `γalt`. -/
def succSched (γs : ℕ → F) : ℕ → F := fun m => γs m + 1

@[simp] theorem succSched_apply (γs : ℕ → F) (m : ℕ) :
    succSched γs m = γs m + 1 := rfl

theorem succSched_ne (γs : ℕ → F) (m : ℕ) : γs m ≠ succSched γs m := by
  intro h
  have := congrArg (· - γs m) h
  simp at this

/-! ## The one-prover extractor -/

/-- **The one-prover light-client extractor.** A pure function of ONE
execution's public view: the schedule `γs`, the base transcript word `h₀`,
and the opened columns `cols` of the `n + 1` recommitted partial folds at the
`t` query positions `q`. The `n` counterfactual transcripts are synthesized by
`seamCounterfactual` (erasure decoding of each round's increment) at the
extractor's own alternate challenge `γ + 1`, and `extractChain` peels the
links. No witness, no second run, no external alternate schedule in the type. -/
noncomputable def lcExtract (dom : ι ↪ F) (d : ℕ) {t : ℕ} (q : Fin t → ι) (n : ℕ)
    (γs : ℕ → F) (h₀ : ι → F) (cols : ℕ → Fin t → F) : List (ι → F) :=
  extractChain γs (succSched γs) h₀
    (seamCounterfactual (n := n) dom d q γs (succSched γs) h₀ cols)

/-- **The extractor recovers the prover's own words, exactly.** When the
opened columns are the recommitted partial folds' symbols and every round word
is a codeword, `lcExtract` on the prover's base word `foldWords γs f₀ ws`
returns `ws` on the nose — `extractChain_seamCounterfactual` (CITED) through
`foldWords_ofFn`, with the extractor's own alternate challenge. -/
theorem lcExtract_eq_ofFn (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q)) {n : ℕ} {γs : ℕ → F} {f₀ : ι → F}
    {ms : Fin n → ι → F} {cols : ℕ → Fin t → F}
    (hγ0 : ∀ k : Fin n, γs (k : ℕ) ≠ 0)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (hcols : ∀ c : ℕ, c ≤ n → ∀ j, cols c j = partialFold γs f₀ ms c (q j)) :
    lcExtract dom d q n γs (foldWords γs f₀ (List.ofFn ms)) cols = List.ofFn ms := by
  unfold lcExtract
  rw [foldWords_ofFn]
  exact extractChain_seamCounterfactual dom hdt hq (fun k => succSched_ne γs k)
    hγ0 hms hcols

/-- The committed form: the columns enter ONLY through verified openings
against a `BindingCommitment` of each recommitted partial fold
(`binding_columns`, `[ACC-extract-bind]`); nothing is assumed about how the
prover produced them. -/
theorem lcExtract_eq_ofFn_committed {Root' Op : Type*}
    (S : BindingCommitment Root' F ι Op) (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) {n : ℕ} {γs : ℕ → F}
    {f₀ : ι → F} {ms : Fin n → ι → F} {rts : ℕ → Root'} {cols : ℕ → Fin t → F}
    {ops : ℕ → Fin t → Op}
    (hγ0 : ∀ k : Fin n, γs (k : ℕ) ≠ 0)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (hrts : ∀ c : ℕ, c ≤ n → rts c = S.commit (partialFold γs f₀ ms c))
    (hver : ∀ c : ℕ, c ≤ n → ∀ j,
      S.verifyOpen (rts c) (q j) (cols c j) (ops c j)) :
    lcExtract dom d q n γs (foldWords γs f₀ (List.ofFn ms)) cols = List.ofFn ms :=
  lcExtract_eq_ofFn dom hdt hq hγ0 hms fun c hc j =>
    binding_columns S (hrts c hc) (hver c hc) j

/-! ## List plumbing: a link and its committed word sit in the zip -/

/-- Link `k` paired with the prover's `k`-th word is an element of
`ch.zip (List.ofFn ms)` — the shape `lightClientSound`'s `hfalse` consumes. -/
theorem zip_ofFn_mem {α β : Type*} (l : List α) (f : Fin l.length → β)
    (k : Fin l.length) : (l.get k, f k) ∈ l.zip (List.ofFn f) := by
  rw [List.mem_iff_getElem]
  refine ⟨k, ?_, ?_⟩
  · simp
  · rw [List.getElem_zip, List.getElem_ofFn]
    rfl

section Fold

variable (foldRoot : Root → F → Root → Root)

/-! ## `lightClientKnowledgeSound` with its transcripts DERIVED -/

/-- **`lightClientKnowledgeSound`, transcripts derived from one execution.**
The base word is the prover's fold `foldWords γs f₀ ws`; the `n` perturbed
words are `seamCounterfactual`'s synthesis from the prover's opened columns —
nothing is separately given. Under the seam's preconditions (unique decoding,
codeword words, honest columns, nonzero challenges) the extractor's output IS
the prover's word list, and the only verification hypotheses are about the
prover's OWN words at the base schedule and at the `n` counterfactual
schedules `γ_k ↦ γ_k + 1`. Conclusion: the extractor returns `ws`, the chain
attests, and `ws` `Forall₂`-witnesses it. -/
theorem lightClientKnowledgeSound_seam {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch)
    (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q))
    {γs : ℕ → F} {f₀ : ι → F} {ms : Fin ch.length → ι → F} {cols : ℕ → Fin t → F}
    (hγ0 : ∀ k : Fin ch.length, γs (k : ℕ) ≠ 0)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (hcols : ∀ c : ℕ, c ≤ ch.length → ∀ j, cols c j = partialFold γs f₀ ms c (q j))
    (hbase : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch)
      (foldWords γs f₀ (List.ofFn ms)))
    (hpert : ∀ k : Fin ch.length, AccClaim.Satisfies C
      (aggregate foldRoot (updSched γs (succSched γs) k) A₀ ch)
      (foldWords (updSched γs (succSched γs) k) f₀ (List.ofFn ms))) :
    lcExtract dom d q ch.length γs (foldWords γs f₀ (List.ofFn ms)) cols
        = List.ofFn ms ∧
    attests C ch ∧
    List.Forall₂ (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w)
      ch (lcExtract dom d q ch.length γs (foldWords γs f₀ (List.ofFn ms)) cols) := by
  have hext := lcExtract_eq_ofFn dom hdt hq hγ0 hms hcols
  have hseamk : ∀ k : Fin ch.length,
      seamCounterfactual (n := ch.length) dom d q γs (succSched γs)
          (foldWords γs f₀ (List.ofFn ms)) cols k
        = foldWords (updSched γs (succSched γs) k) f₀ (List.ofFn ms) := by
    intro k
    simp only [foldWords_ofFn]
    exact seamCounterfactual_sound dom hdt hq (hγ0 k) (hms k) hcols
  have hkey := lightClientKnowledgeSound foldRoot halign hseam
    (fun k => succSched_ne γs k)
    (hs := seamCounterfactual (n := ch.length) dom d q γs (succSched γs)
      (foldWords γs f₀ (List.ofFn ms)) cols)
    hbase (fun k => by rw [hseamk k]; exact hpert k)
  exact ⟨hext, hkey.1, hkey.2⟩

/-! ## The apex: knowledge soundness of ONE prover, priced -/

/-- **Knowledge soundness of one prover** — the light client's RBR-shaped
statement. A prover holding committed words `ms` (one per link) and genesis
word `f₀`, opening the columns `cols γv` of its recommitted partial folds at
whatever schedule `γv` is sampled: the probability, over ONE uniform schedule,
that its base transcript δ-verifies AND the one-execution extractor fails to
deliver an attestation with linkwise δ-close witnesses is at most

  `n · (err⋆(δ) + 2/|F|)`.

The two `1/|F|` per link: `lightClientSound`'s exact-word term, REUSED (the
words are δ-far-false somewhere), and the zero-challenge event (link `k`'s
word is invisible to every recommitted fold when `γ_k = 0`, so no function of
the columns recovers it — a real limit of this extractor, priced, not hidden).
No transcript is given separately: `hbase`/`hpert` of
`lightClientKnowledgeSound` and `hfalse` of `lightClientSound` have all become
the two arms of one case split inside the proof. -/
theorem lightClientKnowledgeSound_oneProver [Fintype ι] [DecidableEq ι]
    [DecidableEq F] [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)} {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2) (herr0 : 0 ≤ errstar δ)
    (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q))
    {f₀ : ι → F} {ms : Fin ch.length → ι → F}
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    {cols : (Fin ch.length → F) → ℕ → Fin t → F}
    (hcols : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length → ∀ j,
      cols γv c j = partialFold (padSched γv) f₀ ms c (q j)) :
    uniformProb (Fin ch.length → F) (fun γv =>
        (∃ u, relDist (foldWords (padSched γv) f₀ (List.ofFn ms)) u ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u) ∧
        ¬ (attests C ch ∧
          List.Forall₂ (fun (l : Link Root F ι r) w =>
              ∃ v, relDist w v ≤ δ ∧ AccClaim.Satisfies C l.claim v) ch
            (lcExtract dom d q ch.length (padSched γv)
              (foldWords (padSched γv) f₀ (List.ofFn ms)) (cols γv))))
      ≤ (ch.length : ℝ) * (errstar δ + 2 / (Fintype.card F : ℝ)) := by
  classical
  have hsplit : (2 : ℝ) / (Fintype.card F : ℝ)
      = 1 / (Fintype.card F : ℝ) + 1 / (Fintype.card F : ℝ) := by ring
  have hF : (0 : ℝ) ≤ 1 / (Fintype.card F : ℝ) := by positivity
  by_cases hgood : ∀ k : Fin ch.length, ∃ v, relDist (ms k) v ≤ δ ∧
      AccClaim.Satisfies C (ch.get k).claim v
  · -- every committed word is δ-close to a witness: the extractor returns the
    -- words themselves unless some challenge coordinate is zero
    have hatt : attests C ch := by
      refine ⟨hseam, fun l hl => ?_⟩
      obtain ⟨i, hi, hl'⟩ := List.mem_iff_getElem.mp hl
      obtain ⟨v, -, hv⟩ := hgood ⟨i, hi⟩
      refine ⟨v, ?_⟩
      rw [← hl']
      exact hv
    have hforall : List.Forall₂ (fun (l : Link Root F ι r) w =>
        ∃ v, relDist w v ≤ δ ∧ AccClaim.Satisfies C l.claim v) ch (List.ofFn ms) := by
      rw [List.forall₂_iff_get]
      refine ⟨by simp, fun i h₁ h₂ => ?_⟩
      rw [List.get_ofFn]
      exact hgood ⟨i, h₁⟩
    have himp : ∀ γv : Fin ch.length → F,
        ((∃ u, relDist (foldWords (padSched γv) f₀ (List.ofFn ms)) u ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u) ∧
        ¬ (attests C ch ∧
          List.Forall₂ (fun (l : Link Root F ι r) w =>
              ∃ v, relDist w v ≤ δ ∧ AccClaim.Satisfies C l.claim v) ch
            (lcExtract dom d q ch.length (padSched γv)
              (foldWords (padSched γv) f₀ (List.ofFn ms)) (cols γv))))
        → ∃ k : Fin ch.length, γv k = 0 := by
      rintro γv ⟨-, hbad⟩
      by_contra hnz
      push Not at hnz
      have hγ0 : ∀ k : Fin ch.length, padSched γv (k : ℕ) ≠ 0 := fun k => by
        rw [padSched_lt _ k.isLt]
        exact hnz k
      have hext := lcExtract_eq_ofFn dom hdt hq hγ0 hms (hcols γv)
      refine hbad ⟨hatt, ?_⟩
      rw [hext]
      exact hforall
    calc uniformProb (Fin ch.length → F) _
        ≤ uniformProb (Fin ch.length → F) (fun γv => ∃ k : Fin ch.length, γv k = 0) :=
          uniformProb_mono himp
      _ ≤ ∑ k : Fin ch.length, uniformProb (Fin ch.length → F) (fun γv => γv k = 0) :=
          uniformProb_exists_le _
      _ ≤ ∑ _k : Fin ch.length, 1 / (Fintype.card F : ℝ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have h := uniformProb_coord_mem (F := F) k ({0} : Finset F)
          rw [Finset.card_singleton, Nat.cast_one] at h
          calc uniformProb (Fin ch.length → F) (fun γv => γv k = 0)
              = uniformProb (Fin ch.length → F) (fun γv => γv k ∈ ({0} : Finset F)) :=
                uniformProb_congr fun γv => by simp
            _ ≤ 1 / (Fintype.card F : ℝ) := h
      _ = (ch.length : ℝ) * (1 / (Fintype.card F : ℝ)) := by simp
      _ ≤ (ch.length : ℝ) * (errstar δ + 2 / (Fintype.card F : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          rw [hsplit]
          linarith
  · -- some committed word is δ-far-false: `lightClientSound` prices verification
    push Not at hgood
    obtain ⟨k, hk⟩ := hgood
    have hfalse : ∃ p ∈ ch.zip (List.ofFn ms), ∀ v ∈ C, relDist p.2 v ≤ δ →
        ¬ AccClaim.Satisfies C p.1.claim v :=
      ⟨(ch.get k, ms k), zip_ofFn_mem ch ms k,
        fun v _ hclose hsat => hk v hclose hsat⟩
    have hsound := lightClientSound foldRoot (f₀ := f₀) halign hdC hMCA hδ0 hδB hδC
      herr0 (by simp) hfalse
    calc uniformProb (Fin ch.length → F) _
        ≤ uniformProb (Fin ch.length → F) (fun γv =>
            ∃ u, relDist (foldWords (padSched γv) f₀ (List.ofFn ms)) u ≤ δ ∧
              AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u) :=
          uniformProb_mono fun _ h => h.1
      _ ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)) := hsound
      _ ≤ (ch.length : ℝ) * (errstar δ + 2 / (Fintype.card F : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          rw [hsplit]
          linarith

/-- **The apex through binding**: the columns enter ONLY through verified
openings against a `BindingCommitment` of each recommitted partial fold
(`binding_columns`). This is the form `Assurance/SelvageV0.lean`'s `knowledge`
field cites. -/
theorem lightClientKnowledgeSound_oneProver_committed [Fintype ι] [DecidableEq ι]
    [DecidableEq F] [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)} {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2) (herr0 : 0 ≤ errstar δ)
    {Root' Op : Type*} (S : BindingCommitment Root' F ι Op)
    (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q))
    {f₀ : ι → F} {ms : Fin ch.length → ι → F}
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    {rts : (Fin ch.length → F) → ℕ → Root'}
    {cols : (Fin ch.length → F) → ℕ → Fin t → F}
    {ops : (Fin ch.length → F) → ℕ → Fin t → Op}
    (hrts : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length →
      rts γv c = S.commit (partialFold (padSched γv) f₀ ms c))
    (hver : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length → ∀ j,
      S.verifyOpen (rts γv c) (q j) (cols γv c j) (ops γv c j)) :
    uniformProb (Fin ch.length → F) (fun γv =>
        (∃ u, relDist (foldWords (padSched γv) f₀ (List.ofFn ms)) u ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u) ∧
        ¬ (attests C ch ∧
          List.Forall₂ (fun (l : Link Root F ι r) w =>
              ∃ v, relDist w v ≤ δ ∧ AccClaim.Satisfies C l.claim v) ch
            (lcExtract dom d q ch.length (padSched γv)
              (foldWords (padSched γv) f₀ (List.ofFn ms)) (cols γv))))
      ≤ (ch.length : ℝ) * (errstar δ + 2 / (Fintype.card F : ℝ)) :=
  lightClientKnowledgeSound_oneProver foldRoot halign hseam hdC hMCA hδ0 hδB hδC
    herr0 dom hdt hq hms fun γv c hc j =>
      binding_columns S (hrts γv c hc) (hver γv c hc) j

end Fold

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All over `LCExample.goodChain` (genesis `(q2, 2)` witnessed by `xWord`; link 0
`(q2, 0)` witnessed by `0`; link 1 `(q2, 1)` witnessed by `oneWord`), with the
honest words `ZkExtractionExample.wsEx = [0, oneWord]` and the opening set
`qLow = {0, 1}` at `t = d = 2` — chosen so that the channel position `2` is
UNOPENED, which is what lets the non-codeword falsifier below fool the seam. -/

namespace LightClientKnowledgeExample

open RSExample AccExample LCExample AccExtractChainExample ZkExtractionExample

/-- The opening positions `{0, 1}` — distinct under `dom₅`, and missing the
channel position `2`. -/
def qLow : Fin 2 → Fin 4 := ![0, 1]

theorem qLow_inj : Function.Injective (dom₅ ∘ qLow) := by decide

/-- The honest prover's columns: the recommitted partial folds' symbols at
`qLow`, at any schedule. -/
def colsHonest (γs : ℕ → ZMod 5) : ℕ → Fin 2 → ZMod 5 :=
  fun c j => partialFold γs xWord wsEx c (qLow j)

theorem wsEx_mem : ∀ k, wsEx k ∈ reedSolomonCode dom₅ 2 := fun k => (wsEx_sat k).1

/-- **Satisfiable / the extractor computes**: from the honest prover's base
word and opened columns at the base schedule `(1, 1)`, the one-execution
extractor returns EXACTLY `[0, oneWord]`. -/
theorem lcExtract_recovers_F5 :
    lcExtract dom₅ 2 qLow 2 γbase (foldWords γbase xWord (List.ofFn wsEx))
        (colsHonest γbase)
      = [0, oneWord] :=
  lcExtract_eq_ofFn dom₅ le_rfl qLow_inj (by decide) wsEx_mem (fun _ _ _ => rfl)

/-- **Premise inhabitation, the derived-transcript theorem**:
`lightClientKnowledgeSound_seam` fires on `goodChain` at `C = RS(dom₅, 2)` —
the base and the two counterfactual verifications are
`goodChain_aggregate_satisfied` (the honest words fold to a satisfied
aggregate at EVERY schedule), the seam's preconditions by `decide`/`rfl`. -/
theorem knowledge_seam_fires_F5 :
    lcExtract dom₅ 2 qLow 2 γbase (foldWords γbase xWord (List.ofFn wsEx))
        (colsHonest γbase) = List.ofFn wsEx ∧
    attests (reedSolomonCode dom₅ 2) goodChain ∧
    List.Forall₂ (fun (l : Link (ZMod 5) (ZMod 5) (Fin 4) 1) w =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2) l.claim w) goodChain
      (lcExtract dom₅ 2 qLow 2 γbase (foldWords γbase xWord (List.ofFn wsEx))
        (colsHonest γbase)) :=
  lightClientKnowledgeSound_seam linRoot goodChain_aligned goodChain_seamOk dom₅
    le_rfl qLow_inj (by decide) wsEx_mem (fun _ _ _ => rfl)
    (goodChain_aggregate_satisfied γbase)
    (fun k => goodChain_aggregate_satisfied (updSched γbase (succSched γbase) k))

/-- The honest prover's columns as a function of the sampled schedule. -/
def colsHonestAt (γv : Fin 2 → ZMod 5) : ℕ → Fin 2 → ZMod 5 :=
  colsHonest (padSched γv)

theorem hmax₄ : max (1 - 1 / (Fintype.card (Fin 4) : ℝ) / 2) 0 = 7 / 8 := by
  rw [Fintype.card_fin, max_eq_left (by norm_num)]
  norm_num

/-- **Premise inhabitation, the apex**: `lightClientKnowledgeSound_oneProver`
fires on `goodChain`'s honest prover at `C = ⊤` (mutual CA with `err⋆ = 0`,
`hasMutualCorrelatedAgreement_top_affine`; `dC = 1/4`, `minDistLB_inhabited`),
δ = 1/16, bound `2 · (0 + 2/5) = 4/5`. Every hypothesis discharged by landed
witnesses; the columns are honest by `rfl`. -/
theorem oneProver_fires_F5 :
    uniformProb (Fin 2 → ZMod 5) (fun γv =>
        (∃ u, relDist (foldWords (padSched γv) xWord (List.ofFn wsEx)) u ≤ (1 / 16 : ℝ) ∧
          AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
            (aggregate linRoot (padSched γv) genesis goodChain) u) ∧
        ¬ (attests (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) goodChain ∧
          List.Forall₂ (fun (l : Link (ZMod 5) (ZMod 5) (Fin 4) 1) w =>
              ∃ v, relDist w v ≤ (1 / 16 : ℝ) ∧
                AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) l.claim v)
            goodChain
            (lcExtract dom₅ 2 qLow 2 (padSched γv)
              (foldWords (padSched γv) xWord (List.ofFn wsEx)) (colsHonestAt γv))))
      ≤ 4 / 5 := by
  have h := lightClientKnowledgeSound_oneProver linRoot (C := ⊤) (δ := 1 / 16)
    (errstar := fun _ => 0) (ms := wsEx) (f₀ := xWord) (cols := colsHonestAt)
    goodChain_aligned goodChain_seamOk (minDistLB_inhabited _)
    hasMutualCorrelatedAgreement_top_affine (by norm_num) (by rw [hmax₄]; norm_num)
    (by norm_num [Fintype.card_fin]) (le_refl 0) dom₅ le_rfl qLow_inj wsEx_mem
    (fun _ _ _ _ => rfl)
  have h' : ((goodChain.length : ℕ) : ℝ) * (0 + 2 / (Fintype.card (ZMod 5) : ℝ))
      = 4 / 5 := by
    rw [ZMod.card]
    show ((2 : ℕ) : ℝ) * (0 + 2 / ((5 : ℕ) : ℝ)) = 4 / 5
    norm_num
  rw [← h']
  exact h

/-! ### Teeth: the seam's codeword precondition is load-bearing -/

/-- The falsifier's link-1 word: the indicator of position `2`. It meets
`claim₁`'s channel (`q2 δ₂ = 1`) but is NOT a degree-`< 2` evaluation
(`δ₂_not_mem`), and it vanishes at both opened positions of `qLow`. -/
def δ₂ : Fin 4 → ZMod 5 := ![0, 0, 1, 0]

theorem δ₂_not_mem : δ₂ ∉ reedSolomonCode dom₅ 2 := by
  intro hmem
  have h := open_determines dom₅ (le_refl 2) qLow_inj hmem (Submodule.zero_mem _)
    (by decide)
  exact absurd h (by decide)

/-- The falsifying prover: link 0's honest `0`, link 1's non-codeword `δ₂`. At
`C = ⊤` it is an HONEST prover (both words meet their channels), so its base
transcript verifies at every schedule. -/
def msBad : Fin 2 → Fin 4 → ZMod 5 := ![0, δ₂]

/-- The falsifying prover's columns: its own recommitted partial folds'
symbols at `qLow` — honest openings of a dishonest code promise. -/
def colsBad (γs : ℕ → ZMod 5) : ℕ → Fin 2 → ZMod 5 :=
  fun c j => partialFold γs xWord msBad c (qLow j)

/-- The seam's round-1 decode sees ZERO increment: `δ₂` vanishes at both opened
positions, so the erasure decoder (correctly!) returns the zero codeword. -/
theorem colsBad_step (γs : ℕ → ZMod 5) (j : Fin 2) :
    (γs ((1 : Fin 2) : ℕ))⁻¹ * (colsBad γs (((1 : Fin 2) : ℕ) + 1) j
        - colsBad γs ((1 : Fin 2) : ℕ) j)
      = (0 : Fin 4 → ZMod 5) (qLow j) := by
  have hstep := congrFun (partialFold_succ γs xWord msBad 1) (qLow j)
  have hz : msBad 1 (qLow j) = 0 := by fin_cases j <;> rfl
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz, mul_zero, add_zero] at hstep
  show (γs ((1 : Fin 2) : ℕ))⁻¹ * (partialFold γs xWord msBad (((1 : Fin 2) : ℕ) + 1) (qLow j)
      - partialFold γs xWord msBad ((1 : Fin 2) : ℕ) (qLow j)) = 0
  rw [hstep, sub_self, mul_zero]

/-- **The seam is fooled**: at EVERY schedule the synthesized link-1
counterfactual is just the base word — the prover's non-codeword contribution
is invisible through the unopened position. -/
theorem seam_link1_bad (γs : ℕ → ZMod 5) :
    seamCounterfactual (n := 2) dom₅ 2 qLow γs (succSched γs)
        (flatFold γs xWord msBad) (colsBad γs) 1
      = flatFold γs xWord msBad := by
  have hrec : recoverFromColumns dom₅ 2 qLow (fun j =>
      (γs ((1 : Fin 2) : ℕ))⁻¹ * (colsBad γs (((1 : Fin 2) : ℕ) + 1) j
        - colsBad γs ((1 : Fin 2) : ℕ) j)) = 0 :=
    recoverFromColumns_sound dom₅ le_rfl qLow_inj (Submodule.zero_mem _)
      (colsBad_step γs)
  unfold seamCounterfactual
  rw [hrec, smul_zero, add_zero]

/-- **Teeth, the seam precondition**: at the base schedule `(1, 1)`, the
seam-derived link-1 transcript does NOT verify the aggregate at the perturbed
schedule `(1, 2)` (the channel reads `3`, the perturbed target is `4`), while
the TRUE perturbed transcript `flatFold (1, 2) xWord msBad` DOES. Same
prover, same columns, same schedule — only `hms` fails, and with it the
derived transcript. -/
theorem seam_teeth_noncodeword_F5 :
    msBad 1 ∉ reedSolomonCode dom₅ 2 ∧
    ¬ AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      (aggregate linRoot (updSched γbase (succSched γbase) (1 : Fin 2)) genesis goodChain)
      (seamCounterfactual (n := 2) dom₅ 2 qLow γbase (succSched γbase)
        (flatFold γbase xWord msBad) (colsBad γbase) 1) ∧
    AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      (aggregate linRoot (updSched γbase (succSched γbase) (1 : Fin 2)) genesis goodChain)
      (flatFold (updSched γbase (succSched γbase) (1 : Fin 2)) xWord msBad) := by
  refine ⟨δ₂_not_mem, ?_, Submodule.mem_top, by decide⟩
  rw [seam_link1_bad]
  exact fun h => absurd (h.2 0) (by decide)

/-- The extracted list of the falsifying prover, entrywise. -/
noncomputable def gBad (γs : ℕ → ZMod 5) : Fin 2 → Fin 4 → ZMod 5 := fun k =>
  (extractPair (flatFold γs xWord msBad)
    (seamCounterfactual (n := 2) dom₅ 2 qLow γs (succSched γs)
      (flatFold γs xWord msBad) (colsBad γs) k)
    (γs (k : ℕ)) (succSched γs (k : ℕ))).2

theorem lcExtract_bad_eq (γs : ℕ → ZMod 5) :
    lcExtract dom₅ 2 qLow 2 γs (foldWords γs xWord (List.ofFn msBad)) (colsBad γs)
      = [gBad γs 0, gBad γs 1] := by
  unfold lcExtract
  rw [foldWords_ofFn]
  rfl

/-- The extractor's link-1 output for the falsifying prover is `0` at EVERY
schedule: the two-point peel sees two EQUAL transcripts. -/
theorem gBad_one (γs : ℕ → ZMod 5) : gBad γs 1 = 0 := by
  unfold gBad
  rw [seam_link1_bad, extractPair_snd, sub_self, smul_zero]

private theorem eq_of_relDist_le_of_lt_inv_card' {f u : Fin 4 → ZMod 5} {δ : ℝ}
    (h : relDist f u ≤ δ) (hδ : δ < 1 / (Fintype.card (Fin 4) : ℝ)) : f = u := by
  by_contra hne
  exact absurd (le_trans (one_div_card_le_relDist hne) h) (not_le.mpr hδ)

private theorem uniformProb_of_forall' (C : Type) [Fintype C] [Nonempty C]
    {p : C → Prop} (h : ∀ c, p c) : uniformProb C p = 1 := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h), Nat.card_eq_fintype_card,
    div_self]
  exact_mod_cast Fintype.card_ne_zero

/-- The falsifying prover's base transcript δ-verifies at EVERY schedule
(`C = ⊤`, both words meet their channels): the honest fold, at distance `0`. -/
theorem msBad_verifies (γv : Fin 2 → ZMod 5) :
    ∃ u, relDist (foldWords (padSched γv) xWord (List.ofFn msBad)) u ≤ (1 / 16 : ℝ) ∧
      AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
        (aggregate linRoot (padSched γv) genesis goodChain) u := by
  refine ⟨foldWords (padSched γv) xWord (List.ofFn msBad), by simp [relDist], ?_⟩
  refine aggregate_satisfies linRoot (padSched γv) ?_ goodChain_aligned
    ⟨Submodule.mem_top, by decide⟩
  exact .cons ⟨Submodule.mem_top, by decide⟩
    (.cons ⟨Submodule.mem_top, by decide⟩ .nil)

/-- The falsifying prover's extraction FAILS at every schedule: the link-1
output `0` is δ-far from every witness of `claim₁` (quantization pins the
δ-ball to `0`, and `q2 0 = 0 ≠ 1`). -/
theorem msBad_extraction_fails (γv : Fin 2 → ZMod 5) :
    ¬ (attests (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) goodChain ∧
      List.Forall₂ (fun (l : Link (ZMod 5) (ZMod 5) (Fin 4) 1) w =>
          ∃ v, relDist w v ≤ (1 / 16 : ℝ) ∧
            AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) l.claim v)
        goodChain
        (lcExtract dom₅ 2 qLow 2 (padSched γv)
          (foldWords (padSched γv) xWord (List.ofFn msBad)) (colsBad (padSched γv)))) := by
  rintro ⟨-, hf⟩
  rw [lcExtract_bad_eq, gBad_one] at hf
  unfold goodChain at hf
  rcases hf with _ | ⟨-, hf⟩
  rcases hf with _ | ⟨h1, -⟩
  obtain ⟨v, hclose, hsat⟩ := h1
  have hv : (0 : Fin 4 → ZMod 5) = v :=
    eq_of_relDist_le_of_lt_inv_card' hclose (by norm_num [Fintype.card_fin])
  have h := hsat.2 0
  rw [← hv] at h
  exact absurd h (by decide)

/-- **Teeth, the apex bound**: for the falsifying prover every hypothesis of
`lightClientKnowledgeSound_oneProver` EXCEPT `hms` holds (`C = ⊤`, honest
columns by `rfl`, the same dials as `oneProver_fires_F5`), and the bad event —
base transcript δ-verifies AND extraction fails — has probability EXACTLY
`1`, strictly above the theorem's `2 · (0 + 2/5) = 4/5`. Drop the codeword
promise and the theorem is FALSE: the erasure seam is where it is consumed. -/
theorem oneProver_teeth_noncodeword_F5 :
    msBad 1 ∉ reedSolomonCode dom₅ 2 ∧
    uniformProb (Fin 2 → ZMod 5) (fun γv =>
        (∃ u, relDist (foldWords (padSched γv) xWord (List.ofFn msBad)) u ≤ (1 / 16 : ℝ) ∧
          AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
            (aggregate linRoot (padSched γv) genesis goodChain) u) ∧
        ¬ (attests (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) goodChain ∧
          List.Forall₂ (fun (l : Link (ZMod 5) (ZMod 5) (Fin 4) 1) w =>
              ∃ v, relDist w v ≤ (1 / 16 : ℝ) ∧
                AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) l.claim v)
            goodChain
            (lcExtract dom₅ 2 qLow 2 (padSched γv)
              (foldWords (padSched γv) xWord (List.ofFn msBad)) (colsBad (padSched γv)))))
      = 1 ∧
    (4 / 5 : ℝ) < 1 :=
  ⟨δ₂_not_mem,
    uniformProb_of_forall' _ fun γv => ⟨msBad_verifies γv, msBad_extraction_fails γv⟩,
    by norm_num⟩

end LightClientKnowledgeExample

/-! ## Axiom pins (house law) -/

/-- info: 'Minidregg.Selvage.lcExtract_eq_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lcExtract_eq_ofFn
/-- info: 'Minidregg.Selvage.lightClientKnowledgeSound_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lightClientKnowledgeSound_seam
/-- info: 'Minidregg.Selvage.lightClientKnowledgeSound_oneProver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lightClientKnowledgeSound_oneProver
/-- info: 'Minidregg.Selvage.lightClientKnowledgeSound_oneProver_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lightClientKnowledgeSound_oneProver_committed
/-- info: 'Minidregg.Selvage.LightClientKnowledgeExample.oneProver_fires_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LightClientKnowledgeExample.oneProver_fires_F5
/-- info: 'Minidregg.Selvage.LightClientKnowledgeExample.oneProver_teeth_noncodeword_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LightClientKnowledgeExample.oneProver_teeth_noncodeword_F5

/-! ## Ledger

* `succSched` / `succSched_ne` — the extractor's own counterfactual challenge,
  distinct from the base in every field.
* `lcExtract` — DEFINED: the one-prover extractor, a function of `(γs, h₀,
  cols)` only. `lcExtract_eq_ofFn` / `_committed` — PROVED: it returns the
  prover's own words under the seam's preconditions.
* `lightClientKnowledgeSound_seam` — PROVED: `lightClientKnowledgeSound` with
  `hbase`/`hpert` derived from one execution's data.
* `lightClientKnowledgeSound_oneProver` / `_committed` — PROVED: the
  one-prover RBR-shaped bound `n · (err⋆(δ) + 2/|F|)`, `lightClientSound`
  REUSED as one arm, the seam as the other.
* Keystones — `lcExtract_recovers_F5`, `knowledge_seam_fires_F5`,
  `oneProver_fires_F5` (satisfiable + premise inhabitation);
  `seam_teeth_noncodeword_F5`, `oneProver_teeth_noncodeword_F5` (teeth:
  `hms` is load-bearing; without it the apex bound is violated at
  probability `1 > 4/5`).
* What remains, unchanged and named elsewhere — `[ACC-sound-rbr-game]`
  (`Selvage/AccSoundRbr.lean`: the Def-4.2 `RbrKnowledgeSoundness` quadruple
  around `lcExtract`; the obstruction there was the two-point/one-point
  mismatch, which `lcExtract` resolves at the light-client-event level but
  which is not re-packaged as a `KStateFn` here), `[FS-ROM]` (uniform →
  hash-derived schedule), `[COMMIT-CR]` (the deployed `BindingCommitment`),
  `[ZK-RBR-extract]` lemma A (the seam below unique decoding). The exact-word
  sharpening of the apex to `1/|F| + n/|F|` (a two-point counting argument on
  the prover's own fold, in the shape of `lightClientSound_exact`) is not
  landed: the δ-form above is what the capstone needs. -/

end Minidregg.Selvage
