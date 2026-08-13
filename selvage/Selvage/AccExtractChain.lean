/-
# Selvage.AccExtractChain — [ACC-extract-chain]: knowledge soundness over the CHAIN.

`Selvage/AccExtract.lean` proved the single-fold knowledge core: `extractPair`
inverts one γ-fold from transcript words at two distinct challenges
(`extractPair_sound`), `accKnowledgeSound` turns two verifying folds into
genuine witnesses of the two folded claims, and `extractPair_peel₂` iterated
the backwards peel at depth 2. `Selvage/LightClientSound.lean` proved the ∃-form
over the whole chain: `link_satisfiable_of_verifies_pair` recovers that SOME
witness of each link EXISTS from verification at two schedules. This file
closes the gap between them — the knowledge upgrade of the light client at
ARBITRARY depth: the per-link witnesses are BUILT by `extractPair`, not merely
shown to exist.

**The mechanism — every link is one fold away.** The aggregate's channel is
affine in the schedule (`aggregate_targets`), so at ANY schedule the aggregate
IS, channel-exactly, a single γ-fold: the peeled remainder claim (`peelClaim` —
genesis plus every OTHER link's γ-weighted contribution) folded with link `k`'s
claim at link `k`'s own challenge (`aggregate_channel_peel`). Two verifying
transcripts whose schedules differ exactly at link `k` are therefore two
verifying folds of ONE claim pair at two distinct challenges — precisely
`accKnowledgeSound`'s hypothesis, REUSED verbatim, never re-derived: `.2` of
`extractPair` witnesses link `k`, `.1` witnesses the peeled remainder, and the
pair explains both transcript words (`extractLink_knowledge`).

* `extractChain` — the chain extractor: from the prover's words at the flat
  schedule family (one base schedule + one `k`-perturbed schedule per link —
  `n + 1` transcripts for an `n`-link chain, WARP's per-step backwards
  extraction rendered flat, exactly the residual's plan in
  `Selvage/AccExtract.lean`), the LIST of per-link witnesses — each entry one
  `extractPair`.
* `extractChain_sound` — every entry genuinely witnesses its link
  (`List.Forall₂` against the chain), at ARBITRARY chain length. The
  anticipated induction residual `[ACC-extract-chain-ind]` is EMPTY and is
  not named: the flat rendering needs no induction, because `peelClaim`
  reaches every link in one step.
* `extract_head_recurses` — the backwards recursion step made a theorem:
  peeling the head link leaves the extractor holding a witness of the TAIL
  chain's aggregate at the shifted schedule (`peelClaim_head_channel`) — the
  `wAt` shape of `Selvage/Depth.lean`'s Construction B.5 ("each level's extractor
  consumes the next level's output") on the chain algebra, extending
  `extractPair_peel₂` from depth 2 to the generic step.
* `lightClientKnowledgeSound` — the apex: seam-ok + verifying words at the
  `n + 1` schedules yield `attests` WITH the built witness list — the
  knowledge upgrade of `lightClient_attests` (which needed EVERY schedule and
  delivered only ∃) and of `link_satisfiable_of_verifies_pair` (which
  delivered one link's ∃ at a time).

**Transcription notes (read before auditing):**

* **Where the `n + 1` transcripts come from.** Everything here consumes folded
  WORDS at the named schedules as transcript data. In deployment a SINGLE
  Fiat–Shamir execution furnishes the perturbed evaluations through the `t`
  opened columns plus erasure correction inside the mutual-agreement set
  (WARP App. B) — that commitment-layer seam is `[ACC-extract-bind]`,
  UNCHANGED from `Selvage/AccExtract.lean`, and it is exactly why this file's
  honest label is knowledge soundness AT THE WORD LEVEL. The base transcript's
  schedule is FS-derived (`Selvage/LightClientFS.lean`); the perturbed schedules
  are the extractor's counterfactuals, resolved by the same seam.
* **The failure probability is the landed one.** Extraction here is EXACT
  (no error term): whenever the words verify and the challenge pairs are
  distinct, the witnesses are recovered on the nose. The probabilistic price
  lives where it always did: a chain with an unsatisfiable link cannot even
  furnish the BASE transcript except with probability `1/|F|`
  (`lightClientSound_exact`, REUSED as `lightClientKnowledge_failure_prob`),
  and a δ-far-false link survives at `n · (err⋆(δ) + 1/|F|)`
  (`lightClientSound`, cited); the composition of per-step knowledge errors
  across unbounded depth in the SR-game rendering is WARP Thm B.4 =
  `OB2_depth_composition_nonneg_proved` (`Selvage/Depth.lean`, PROVED — cited
  below, never re-derived).
* **Flat vs. grid.** `extractPair_peel₂`'s nested grid needs `2^depth`
  transcripts; the flat family needs `n + 1` because the aggregate is LINEAR
  in the schedule — one subtraction per link. Both are the same algebra
  (`extract_head_recurses` is the bridge: the flat peel at the head IS the
  grid recursion's step).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Selvage.AccExtract
import Selvage.LightClientSound
import Selvage.Depth

namespace Minidregg.Selvage

section ChainExtract

/- `F : Type` (not `Type*`): the aggregate's closed-form channel algebra
(`aggregate_targets`, `Selvage/LightClientSound.lean`) lives there, matching the
sampled-schedule universe discipline of that file. -/
variable {Root : Type*} {F : Type} [Field F] {ι : Type*} {r : ℕ}

/-! ## The peeled remainder: the aggregate minus one link -/

/-- **The peeled remainder claim**: the aggregate's channel with link `k`'s
γ-weighted contribution removed — genesis functionals (the fold never moves
them), genesis targets plus every OTHER link's `γₘ`-weighted target. The
aggregate at any schedule is exactly the γ-fold of this claim with link `k`'s
claim at `γs k` (`aggregate_channel_peel` below) — which is what makes every
link ONE `accKnowledgeSound` application away. The root is the genesis's: the
peel is a channel object, and the algebra never reads roots. -/
def peelClaim (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r) (γs : ℕ → F)
    (k : Fin ch.length) : AccClaim Root F ι r :=
  ⟨A₀.rt, fun i => (A₀.weights i,
    A₀.targets i + ∑ m ∈ Finset.univ.erase k,
      γs (m : ℕ) * (ch.get m).claim.targets i)⟩

@[simp] theorem peelClaim_weights (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) (γs : ℕ → F) (k : Fin ch.length) (i : Fin r) :
    (peelClaim A₀ ch γs k).weights i = A₀.weights i := rfl

/-- The peel only reads the schedule OFF `k`: schedules agreeing away from
link `k` peel to the same remainder. -/
theorem peelClaim_congr {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {γs γs' : ℕ → F} {k : Fin ch.length}
    (hagree : ∀ m : ℕ, m ≠ (k : ℕ) → γs m = γs' m) :
    peelClaim A₀ ch γs k = peelClaim A₀ ch γs' k := by
  unfold peelClaim
  congr 1
  funext i
  refine congrArg (Prod.mk _) (congrArg (A₀.targets i + ·) ?_)
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hagree (m : ℕ) fun hc => (Finset.mem_erase.mp hm).1 (Fin.ext hc)]

section Fold

variable (foldRoot : Root → F → Root → Root)

/-- **The aggregate splits at every link**: at ANY schedule, the aggregate's
channel IS the γ-fold of the peeled remainder with link `k`'s claim, at link
`k`'s own challenge. `aggregate_targets`' affine form, re-associated so that
link `k`'s term is the fold's γ-linear contribution. Channel-level (the root
tracks the prover's recommitment schedule, on which the algebra imposes
nothing — `Selvage/Accumulator.lean`'s module header). -/
theorem aggregate_channel_peel (γs : ℕ → F) (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) (k : Fin ch.length) :
    (aggregate foldRoot γs A₀ ch).channel
      = (foldClaims foldRoot (peelClaim A₀ ch γs k) (ch.get k).claim
          (γs (k : ℕ))).channel := by
  funext i
  refine Prod.ext ?_ ?_
  · exact congrFun (aggregate_weights foldRoot γs A₀ ch) i
  · show (aggregate foldRoot γs A₀ ch).targets i
        = (A₀.targets i + ∑ m ∈ Finset.univ.erase k,
            γs (m : ℕ) * (ch.get m).claim.targets i)
          + γs (k : ℕ) * (ch.get k).claim.targets i
    rw [aggregate_targets, add_assoc,
      Finset.sum_erase_add Finset.univ _ (Finset.mem_univ k)]

/-- **The per-link knowledge core** — `accKnowledgeSound` transported to the
chain: two verifying transcripts whose schedules differ in EXACTLY link `k`'s
coordinate are two verifying folds of the pair (peeled remainder, link `k`'s
claim) at two distinct challenges, so the two-point extractor recovers BUILT
witnesses of both — `.2` witnesses link `k`, `.1` witnesses the remainder —
together with the transcript-consistency identities (the extracted pair
actually explains both words, so by `fold_decomposition_unique` it is THE
pair). This is `link_satisfiable_of_verifies_pair`'s subtraction algebra with
the ∃ upgraded to the constructed witness. -/
theorem extractLink_knowledge {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) {γs γs' : ℕ → F} {k : Fin ch.length}
    (hagree : ∀ m : ℕ, m ≠ (k : ℕ) → γs m = γs' m)
    (hne : γs (k : ℕ) ≠ γs' (k : ℕ)) {h h' : ι → F}
    (hagg : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) h)
    (hagg' : AccClaim.Satisfies C (aggregate foldRoot γs' A₀ ch) h') :
    AccClaim.Satisfies C (peelClaim A₀ ch γs k)
      (extractPair h h' (γs (k : ℕ)) (γs' (k : ℕ))).1 ∧
    AccClaim.Satisfies C (ch.get k).claim
      (extractPair h h' (γs (k : ℕ)) (γs' (k : ℕ))).2 ∧
    h = (extractPair h h' (γs (k : ℕ)) (γs' (k : ℕ))).1
        + γs (k : ℕ) • (extractPair h h' (γs (k : ℕ)) (γs' (k : ℕ))).2 ∧
    h' = (extractPair h h' (γs (k : ℕ)) (γs' (k : ℕ))).1
        + γs' (k : ℕ) • (extractPair h h' (γs (k : ℕ)) (γs' (k : ℕ))).2 := by
  have hshare : ∀ i, (ch.get k).claim.weights i
      = (peelClaim A₀ ch γs k).weights i :=
    fun i => halign (ch.get k) (ch.get_mem k) i
  have hfold : AccClaim.Satisfies C
      (foldClaims foldRoot (peelClaim A₀ ch γs k) (ch.get k).claim
        (γs (k : ℕ))) h :=
    AccClaim.satisfies_of_channel_eq (aggregate_channel_peel foldRoot γs A₀ ch k)
      hagg
  have hch' := aggregate_channel_peel foldRoot γs' A₀ ch k
  rw [peelClaim_congr (fun m hm => (hagree m hm).symm)] at hch'
  have hfold' : AccClaim.Satisfies C
      (foldClaims foldRoot (peelClaim A₀ ch γs k) (ch.get k).claim
        (γs' (k : ℕ))) h' :=
    AccClaim.satisfies_of_channel_eq hch' hagg'
  exact accKnowledgeSound foldRoot hne hshare hfold hfold'

/-! ## The backwards recursion step, made a theorem -/

/-- Peeling the HEAD link leaves exactly the TAIL chain's aggregate at the
shifted schedule — the remainder claim of a `cons` chain at coordinate 0 IS
the aggregate of the tail (channel-level). -/
theorem peelClaim_head_channel (A₀ : AccClaim Root F ι r)
    (l : Link Root F ι r) (ls : Chain Root F ι r) (γs : ℕ → F) :
    (peelClaim A₀ (l :: ls) γs ⟨0, Nat.succ_pos ls.length⟩).channel
      = (aggregate foldRoot (fun k => γs (k + 1)) A₀ ls).channel := by
  funext i
  refine Prod.ext ?_ ?_
  · exact (congrFun (aggregate_weights foldRoot (fun k => γs (k + 1)) A₀ ls)
      i).symm
  · show A₀.targets i + ∑ m ∈ Finset.univ.erase
          (⟨0, Nat.succ_pos ls.length⟩ : Fin (ls.length + 1)),
        γs (m : ℕ) * ((l :: ls).get m).claim.targets i
      = (aggregate foldRoot (fun k => γs (k + 1)) A₀ ls).targets i
    rw [aggregate_targets]
    congr 1
    set f : Fin (ls.length + 1) → F :=
      fun m => γs (m : ℕ) * ((l :: ls).get m).claim.targets i with hf
    have h1 : (∑ m ∈ Finset.univ.erase
          (⟨0, Nat.succ_pos ls.length⟩ : Fin (ls.length + 1)), f m)
        + f ⟨0, Nat.succ_pos ls.length⟩ = ∑ m, f m :=
      Finset.sum_erase_add _ _ (Finset.mem_univ _)
    have h2 : (∑ m, f m)
        = f ⟨0, Nat.succ_pos ls.length⟩ + ∑ m : Fin ls.length, f m.succ := by
      rw [Fin.sum_univ_succ f]
      rfl
    have h3 : ∑ m ∈ Finset.univ.erase
          (⟨0, Nat.succ_pos ls.length⟩ : Fin (ls.length + 1)), f m
        = ∑ m : Fin ls.length, f m.succ := by
      have h12 := h1.trans h2
      rw [add_comm (f ⟨0, Nat.succ_pos ls.length⟩)] at h12
      exact add_right_cancel h12
    rw [h3]
    exact Finset.sum_congr rfl fun m _ => rfl

/-- **The backwards recursion step**: extracting at the head coordinate hands
`.2` to the head link and `.1` to the TAIL chain — the extractor's remainder
output is a genuine transcript word of the shorter chain at the shifted
schedule. `Selvage/Depth.lean`'s `wAt` recursion ("each level's extractor
consumes the next level's output", Construction B.5) realized on the chain
algebra; `extractPair_peel₂` is its depth-2 grid instance. -/
theorem extract_head_recurses {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {l : Link Root F ι r} {ls : Chain Root F ι r}
    (halign : Aligned A₀ (l :: ls)) {γs γs' : ℕ → F}
    (hagree : ∀ m : ℕ, m ≠ 0 → γs m = γs' m) (hne : γs 0 ≠ γs' 0)
    {h h' : ι → F}
    (hagg : AccClaim.Satisfies C (aggregate foldRoot γs A₀ (l :: ls)) h)
    (hagg' : AccClaim.Satisfies C (aggregate foldRoot γs' A₀ (l :: ls)) h') :
    AccClaim.Satisfies C l.claim (extractPair h h' (γs 0) (γs' 0)).2 ∧
    AccClaim.Satisfies C (aggregate foldRoot (fun k => γs (k + 1)) A₀ ls)
      (extractPair h h' (γs 0) (γs' 0)).1 := by
  have hkey := extractLink_knowledge foldRoot halign
    (k := ⟨0, Nat.succ_pos ls.length⟩) hagree hne hagg hagg'
  exact ⟨hkey.2.1, AccClaim.satisfies_of_channel_eq
    (peelClaim_head_channel foldRoot A₀ l ls γs) hkey.1⟩

end Fold

/-! ## The chain extractor -/

omit [Field F] in
/-- The `k`-perturbed schedule: the base schedule with link `k`'s coordinate
replaced by the alternate challenge — the schedule of the `k`-th extra
transcript in the flat family. -/
def updSched {n : ℕ} (γs γalt : ℕ → F) (k : Fin n) : ℕ → F := fun m =>
  if m = (k : ℕ) then γalt m else γs m

omit [Field F] in
@[simp] theorem updSched_self {n : ℕ} (γs γalt : ℕ → F) (k : Fin n) :
    updSched γs γalt k (k : ℕ) = γalt (k : ℕ) := if_pos rfl

omit [Field F] in
theorem updSched_ne {n : ℕ} (γs γalt : ℕ → F) {k : Fin n} {m : ℕ}
    (hm : m ≠ (k : ℕ)) : updSched γs γalt k m = γs m := if_neg hm

/-- **The chain extractor** — [ACC-extract-chain]'s object: from the base
transcript word `h₀` and the `n` perturbed transcript words `hs k`, the LIST
of per-link witnesses — link `k`'s entry is the two-point extractor applied
at link `k`'s challenge pair. One `extractPair` per link, REUSED; no decoder,
no rewinding, `n` field inversions total. -/
def extractChain {n : ℕ} (γs γalt : ℕ → F) (h₀ : ι → F)
    (hs : Fin n → ι → F) : List (ι → F) :=
  List.ofFn fun k : Fin n =>
    (extractPair h₀ (hs k) (γs (k : ℕ)) (γalt (k : ℕ))).2

@[simp] theorem extractChain_length {n : ℕ} (γs γalt : ℕ → F) (h₀ : ι → F)
    (hs : Fin n → ι → F) : (extractChain γs γalt h₀ hs).length = n := by
  simp [extractChain]

/-- **The diagonal collapse, chain form**: with the SAME schedule on both
sides every entry of the extraction is erased to `0` (`extractPair_self`
linkwise) — the whole witness list degenerates, whatever the prover's words.
The per-link challenge distinctness in `extractChain_sound` is load-bearing
at EVERY link. -/
theorem extractChain_self {n : ℕ} (γs : ℕ → F) (h₀ : ι → F)
    (hs : Fin n → ι → F) :
    extractChain γs γs h₀ hs = List.replicate n 0 := by
  unfold extractChain
  rw [← List.ofFn_const n (0 : ι → F)]
  exact congrArg List.ofFn (funext fun k => by rw [extractPair_self])

section Fold

variable (foldRoot : Root → F → Root → Root)

/-- **Soundness of the chain extractor** — [ACC-extract-chain] closed at the
word level, ARBITRARY depth: if the prover's words verify the aggregate at the
base schedule and at every `k`-perturbed schedule (challenge pairs distinct
linkwise), then the extracted list genuinely witnesses the chain — entry `k`
satisfies link `k`'s claim, `List.Forall₂`-aligned. Per link this is
`extractLink_knowledge` = `accKnowledgeSound` through the `peelClaim` split;
no induction over the chain is needed (the anticipated
`[ACC-extract-chain-ind]` residual is EMPTY), because the flat schedule
family reaches every link in one peel. -/
theorem extractChain_sound {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) {γs γalt : ℕ → F}
    (hne : ∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ))
    {h₀ : ι → F} {hs : Fin ch.length → ι → F}
    (hbase : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) h₀)
    (hpert : ∀ k : Fin ch.length, AccClaim.Satisfies C
      (aggregate foldRoot (updSched γs γalt k) A₀ ch) (hs k)) :
    List.Forall₂ (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w)
      ch (extractChain γs γalt h₀ hs) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h₁ h₂ => ?_⟩
  have hkey := (extractLink_knowledge foldRoot halign
    (k := ⟨i, h₁⟩) (γs' := updSched γs γalt ⟨i, h₁⟩)
    (fun m hm => (updSched_ne γs γalt hm).symm)
    (by rw [updSched_self]; exact hne ⟨i, h₁⟩)
    hbase (hpert ⟨i, h₁⟩)).2.1
  rw [updSched_self] at hkey
  have hget : (extractChain γs γalt h₀ hs).get ⟨i, h₂⟩
      = (extractPair h₀ (hs ⟨i, h₁⟩) (γs i) (γalt i)).2 := by
    simp only [extractChain, List.get_ofFn]
    rfl
  rw [hget]
  exact hkey

/-- **The knowledge-sound light client** — the apex of [ACC-extract-chain]:
a seam-ok aligned chain whose aggregate the prover can verify at the flat
schedule family (base + one perturbation per link, challenge pairs distinct)
ATTESTS — and not merely with ∃-witnesses: the whole history's witnesses are
BUILT by `extractChain`, link by link. This upgrades `lightClient_attests`
(which consumed verification at EVERY schedule and delivered only
satisfiability) to knowledge soundness at `n + 1` transcripts. The
probabilistic price of the hypotheses for a false chain is the landed
`Selvage/LightClientSound.lean` bound, unchanged
(`lightClientKnowledge_failure_prob` below). -/
theorem lightClientKnowledgeSound {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch) {γs γalt : ℕ → F}
    (hne : ∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ))
    {h₀ : ι → F} {hs : Fin ch.length → ι → F}
    (hbase : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) h₀)
    (hpert : ∀ k : Fin ch.length, AccClaim.Satisfies C
      (aggregate foldRoot (updSched γs γalt k) A₀ ch) (hs k)) :
    attests C ch ∧
    List.Forall₂ (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w)
      ch (extractChain γs γalt h₀ hs) := by
  have hf := extractChain_sound foldRoot halign hne hbase hpert
  obtain ⟨hlen, hall⟩ := List.forall₂_iff_get.mp hf
  refine ⟨⟨hseam, fun l hl => ?_⟩, hf⟩
  obtain ⟨i, hi, hl'⟩ := List.mem_iff_getElem.mp hl
  refine ⟨(extractChain γs γalt h₀ hs).get ⟨i, by omega⟩, ?_⟩
  have hkey := hall i hi (by omega)
  rw [← hl']
  simpa using hkey

end Fold

/-- The depth-composition carrier of the SR-game rendering is PROVED upstream
(`Selvage/Depth.lean`, WARP Thm B.4 repaired, `ε_sr ≤ (t+k)·ε_rbr`, loss-free,
straightline): cited so the import is load-bearing — the chain extraction
above is the fold-algebra face of the same backwards recursion, and its
game-level packaging rides `[ACC-sound-rbr]`, never re-derived here. -/
example : OB2_depth_composition_nonneg := OB2_depth_composition_nonneg_proved

end ChainExtract

/-! ## The failure probability is the landed one -/

section Probability

variable {Root : Type*} {F : Type} [Field F] {ι : Type*} {r : ℕ}

/-- **The knowledge game's failure price, unchanged**: a chain that CANNOT
attest (some link unsatisfiable, seam-ok) cannot even furnish the BASE
transcript of the extraction family, except with probability `1/|F|` over one
uniformly sampled schedule — `lightClientSound_of_not_attests`, REUSED
verbatim. Together with `lightClientKnowledgeSound`: except with the landed
`[LC-sound]` probability (sharp `1/|F|` exact-word; `n · (err⋆(δ) + 1/|F|)`
in the δ regime — `lightClientSound`, cited), a verifying prover's history
yields BUILT witnesses, not just satisfiable claims. -/
theorem lightClientKnowledge_failure_prob [Fintype F]
    (foldRoot : Root → F → Root → Root) {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch) (hnot : ¬ attests C ch) :
    uniformProb (Fin ch.length → F) (fun γv =>
        Verifies C (aggregate foldRoot (padSched γv) A₀ ch))
      ≤ 1 / (Fintype.card F : ℝ) :=
  lightClientSound_of_not_attests foldRoot halign hseam hnot

end Probability

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All BUILT, all computing, over `LCExample`'s landed F₅ chain `goodChain`
(genesis `(q2, 2)` witnessed by `xWord`; link 0 `(q2, 0)` witnessed by `0`;
link 1 `(q2, 1)` witnessed by `oneWord`) — REUSED, not rebuilt:

* **satisfiable / the extractor computes** — `extractChain_recovers`: from
  the three transcript words of the honest chain at base schedule `(1, 1)`
  and perturbed schedules `(2, 1)`, `(1, 2)`, the chain extractor returns
  EXACTLY `[0, oneWord]` — the per-link witnesses, by `decide` (the field
  inversions computed in the kernel).
* **premise inhabitation** — `knowledge_chain_fires`:
  `lightClientKnowledgeSound` fires non-vacuously — every hypothesis
  discharged by landed witnesses (`goodChain_aggregate_satisfied` at each of
  the three schedules), the conclusion delivering `attests` plus the built
  witness list.
* **teeth, the diagonal** — `extract_chain_teeth_diagonal`: with the base
  schedule on BOTH sides the extraction collapses (`extractChain_self`:
  every entry `0`) and does NOT return the witnesses — the per-link
  distinct-challenge hypothesis is load-bearing.
* **teeth, information-theoretic** — `chain_single_schedule_ambiguous`: two
  DISTINCT witness lists for the SAME chain, each genuinely `Forall₂`-
  satisfying every link, with the SAME folded transcript word at the single
  base schedule — no extractor whatsoever recovers "the" witnesses from ONE
  schedule's transcript; the perturbed transcripts are what break the tie
  (`Selvage/AccExtract.lean`'s `single_fold_ambiguous`, lifted to the chain). -/

namespace AccExtractChainExample

open RSExample AccExample LCExample

/-- The keystone base schedule: `(1, 1)`. -/
def γbase : ℕ → ZMod 5 := padSched ![1, 1]

/-- The keystone alternate challenges: `(2, 2)` — distinct from the base at
every link. -/
def γalt₂ : ℕ → ZMod 5 := padSched ![2, 2]

/-- **Satisfiable / the chain extractor computes**: from the honest chain's
three transcript words — base fold `xWord + oneWord` at `(1, 1)`, the same
word at `(2, 1)` (link 0's witness is `0`, so its coordinate moves nothing),
and `xWord + 2·oneWord` at `(1, 2)` — `extractChain` recovers EXACTLY the
per-link witness list `[0, oneWord]`. Kernel computation over F₅. -/
theorem extractChain_recovers :
    extractChain (ι := Fin 4) γbase γalt₂ (xWord + oneWord)
      ![xWord + oneWord, xWord + (2 : ZMod 5) • oneWord]
      = [0, oneWord] := by
  decide

/-- **Premise inhabitation**: `lightClientKnowledgeSound` fires on the landed
keystone chain — alignment, seam, challenge distinctness, and all three
transcript satisfactions discharged by `goodChain`'s landed witnesses; the
conclusion delivers the attestation together with the BUILT witness list. -/
theorem knowledge_chain_fires :
    attests (reedSolomonCode dom₅ 2) goodChain ∧
    List.Forall₂ (fun (l : Link (ZMod 5) (ZMod 5) (Fin 4) 1) w =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2) l.claim w) goodChain
      (extractChain γbase γalt₂
        (foldWords γbase xWord [0, oneWord])
        fun k : Fin goodChain.length =>
          foldWords (updSched γbase γalt₂ k) xWord [0, oneWord]) :=
  lightClientKnowledgeSound linRoot goodChain_aligned goodChain_seamOk
    (by decide) (goodChain_aggregate_satisfied γbase)
    (fun k => goodChain_aggregate_satisfied (updSched γbase γalt₂ k))

/-- **Teeth, the diagonal**: with the SAME schedule for base and alternate the
extraction does NOT return the witnesses — every entry collapses to `0`
(`extractChain_self`), so link 1's genuine witness `oneWord` is erased.
Exhibited by computation. -/
theorem extract_chain_teeth_diagonal :
    extractChain (ι := Fin 4) γbase γbase (xWord + oneWord)
      ![xWord + oneWord, xWord + (2 : ZMod 5) • oneWord]
      ≠ [0, oneWord] := by
  decide

/-- The honest witness list of `goodChain`. -/
def ambig₁ : List (Fin 4 → ZMod 5) := [0, oneWord]

/-- A SECOND witness list for the same chain: link 0 witnessed by the line
`X − 2` (value `0` at the query point), link 1 by `3 − X` (value `1`) — both
genuine codewords, folding to the same word as `ambig₁` at `(1, 1)`. -/
def ambig₂ : List (Fin 4 → ZMod 5) :=
  [xWord - (2 : ZMod 5) • oneWord, (3 : ZMod 5) • oneWord - xWord]

/-- **Teeth, information-theoretic**: the single-schedule transcript does not
DETERMINE the chain's witnesses — two distinct witness lists, each genuinely
satisfying every link of `goodChain`, fold to the SAME transcript word at the
base schedule `(1, 1)`. No function of one schedule's transcript returns
"the" witness list; the perturbed transcripts (in deployment: the opened
columns, `[ACC-extract-bind]`) break the tie. -/
theorem chain_single_schedule_ambiguous :
    ∃ ws₁ ws₂ : List (Fin 4 → ZMod 5),
      ws₁ ≠ ws₂ ∧
      foldWords γbase xWord ws₁ = foldWords γbase xWord ws₂ ∧
      List.Forall₂ (fun (l : Link (ZMod 5) (ZMod 5) (Fin 4) 1) w =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2) l.claim w) goodChain ws₁ ∧
      List.Forall₂ (fun (l : Link (ZMod 5) (ZMod 5) (Fin 4) 1) w =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2) l.claim w) goodChain ws₂ := by
  refine ⟨ambig₁, ambig₂, by decide, by decide, ?_, ?_⟩
  · exact .cons ⟨Submodule.zero_mem _, fun _ => map_zero q2⟩
      (.cons ⟨oneWord_mem, fun _ => rfl⟩ .nil)
  · exact .cons ⟨Submodule.sub_mem _ xWord_mem
        (Submodule.smul_mem _ _ oneWord_mem), by decide⟩
      (.cons ⟨Submodule.sub_mem _ (Submodule.smul_mem _ _ oneWord_mem)
        xWord_mem, by decide⟩ .nil)

end AccExtractChainExample

/-! ## Residual obligations — prose, not stubs

**[ACC-extract-chain] — CLOSED at the word level, arbitrary depth.** The
residual named in `Selvage/AccExtract.lean` asked for the `extractPair`-built
witness of EVERY link from `n + 1` verifying schedules; `extractChain_sound`
and `lightClientKnowledgeSound` are exactly that, with no induction residual
(the flat schedule family reaches every link through `peelClaim` in one step,
and `extract_head_recurses` exhibits the backwards recursion the grid form
would iterate). What remains is NOT chain bookkeeping but the two seams
already named elsewhere, unchanged:

* **[ACC-extract-bind]** (`Selvage/AccExtract.lean`, unchanged) — everything
  here consumes folded WORDS at the named schedules as transcript data. In
  deployment the perturbed evaluations come out of ONE straightline FS
  execution via the `t` opened columns + erasure correction inside the
  mutual-agreement set (WARP App. B; mutual correlated agreement PROVED at
  unique decoding in `Selvage/CorrelatedAgreement.lean`), and the words must be
  BOUND to the prover's committed roots (Merkle/BCS). Until that lands, the
  honest label here is: knowledge soundness AT THE WORD LEVEL, whole-chain.
* **[ACC-sound-rbr]** (`Selvage/AccSound.lean`, unchanged) — packaging the
  per-fold bounds and this extractor as an `RbrKnowledgeSoundness` round
  function, so that the SR-game depth composition
  (`OB2_depth_composition_nonneg_proved`, `Selvage/Depth.lean` — cited above,
  PROVED) applies to the deployed game verbatim. The fold-algebra recursion
  here (`extract_head_recurses`) is that game's `wAt` shape; the attachment
  is the packaging residual, not new algebra.

## Ledger

* `peelClaim` / `aggregate_channel_peel` — PROVED: the aggregate at ANY
  schedule is channel-exactly ONE γ-fold of the peeled remainder with link
  `k`'s claim at `γs k` — every link is one `accKnowledgeSound` away.
* `extractLink_knowledge` — PROVED: two transcripts differing at link `k`
  yield BUILT witnesses of link `k` AND the remainder + both transcript
  identities (`accKnowledgeSound` REUSED; the ∃ of
  `link_satisfiable_of_verifies_pair` upgraded to the constructed word).
* `peelClaim_head_channel` / `extract_head_recurses` — PROVED: the backwards
  recursion step — head extraction hands `.1` to the tail chain's aggregate
  (Construction B.5's `wAt` shape on the chain; `extractPair_peel₂` extended
  from depth 2 to the generic step).
* `extractChain` — DEFINED: one `extractPair` per link (`n` field
  inversions, no decoder, no rewinding); `extractChain_self` — PROVED: the
  diagonal collapse erases the whole list.
* `extractChain_sound` — PROVED, arbitrary depth: the extracted list
  `Forall₂`-witnesses the chain. `[ACC-extract-chain-ind]` is EMPTY.
* `lightClientKnowledgeSound` — PROVED: seam + flat-family verification ⟹
  attestation WITH built witnesses — the knowledge upgrade of
  `lightClient_attests`.
* `lightClientKnowledge_failure_prob` — the failure price is the landed
  `[LC-sound]` bound, REUSED (`1/|F|` sharp exact-word;
  `n·(err⋆ + 1/|F|)` δ-form cited); depth composition of game-level errors:
  `OB2_depth_composition_nonneg_proved`, cited.
* Keystones — `extractChain_recovers`, `knowledge_chain_fires`,
  `extract_chain_teeth_diagonal`, `chain_single_schedule_ambiguous`: all by
  construction / `decide` over F₅ on the landed `goodChain`.
* Residuals — `[ACC-extract-bind]`, `[ACC-sound-rbr]` (both pre-existing,
  unchanged; prose above).
* `#print axioms lightClientKnowledgeSound`: `propext`, `Classical.choice`,
  `Quot.sound`. -/

end Minidregg.Selvage
