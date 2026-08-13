/-
# Selvage.DeciderProximity — `[DEC-proximity]`: the DEPLOYED decider — accept δ-close, reject δ-far.

`Selvage/Decider.lean` is the strict side of LOOM §1's promise split: `decider`
checks EXACT membership `f ∈ C` — the right contract at claim level — and
names what the deployed verifier at rate < 1 does instead as `[DEC-proximity]`.
This file is that deployed decider, COMPOSED from the two layers landed beside
it: Proximity's folding LDT is the membership realizer, Commitment's binding
is the word attribution. Soundness is composed from `proximity_sound`, never
re-derived; nothing here adds LDT content.

Two renderings, one per resolution:

* `deciderProx C A f δ` — the PROMISE-side acceptance relation: δ-closeness
  (`close δ C f`) replaces exact membership; the channel conjunct is the
  decider's own, unchanged. This is the relation the deployed run certifies.
  At sub-quantization radius it COLLAPSES to the exact decider
  (`deciderProx_iff_decider_of_lt_inv_card`: for `δ < 1/|ι|` the δ-ball around
  any code is the code, so `deciderProx ↔ decider ↔ AccClaim.Satisfies`) — the
  strict contract is the δ → 0 end of this one, on the nose.
* `deciderProxLDT T deg A f αs` — the DEPLOYED run: ONE descent of Proximity's
  folding tower (`proximityTest`, the WHIR descent LOOM §6 defers from every
  link to this single final check) plus the same `r` channel checks on the
  final claim.

**PROVED (all composition):**

* `deciderProxLDT_complete` — an honest satisfying word passes the deployed
  decider for EVERY challenge stream (`proximity_complete` + the channels);
  `deciderProx_complete` / `deciderProx_of_decider` on the promise side.
* **`deciderProx_sound`** — the soundness head: a δ-FAR word passes the
  deployed decider for at most `m·b·|F|^{m−1}` of the `|F|^m` challenge tuples
  — the deployed acceptance set is CONTAINED in the LDT acceptance set
  (`deciderProxAcceptSet_subset`), and `proximity_sound` bounds that.
  `deciderProx_sound_prob` is the probability rendering, ≤ `m·b/|F|`.
* The two regimes, EXACTLY as Proximity delivers `[PROX-fold-distance]`:
  - `deciderProx_sound_subquant` — sub-quantization δ (per level
    `δ < 1/|ι_{j+1}|`): UNCONDITIONAL, `b = 1`, bound `m·|F|^{m−1}` — the
    deployed decider at exact-membership resolution is end-to-end sound
    TODAY, zero residual hypotheses;
  - `deciderProx_sound_of_proximityGenerator` — macroscopic δ ∈ (0, 1−B):
    rides the ONE standing RS proximity-gap hypothesis (WHIR Thm 4.8 / BCIKS
    2020/654 — the same `hPG` Selvage/ReedSolomon.lean carries), consumed per
    level as a hypothesis, NOT claimed.
* `deciderProx_of_card_gt` — the certification bridge, closing the loop
  between the renderings: accepted on MORE tuples than the error mass ⇒ the
  semantic verdict `deciderProx` holds. The deployed count is quantified
  evidence for the promise relation.
* Depth independence (`deciderProx_depth_independent`,
  `deciderProxLDT_depth_independent`) — LOOM §6's compression survives the
  relaxation: on the fold of ANY chain the proximity decider's verdict is ONE
  proximity check of the final word plus the INITIAL accumulator's `r`
  functionals against the final claim's scalars (`foldChain_weights`); the
  descent runs once, never per link.
* The opened-word seam (`deciderProx_open_sound`, `deciderProxLDT_open_sound`)
  — under a `BindingCommitment`, the word the proximity decider checked, fully
  opened from the final root, IS the committed word: `[DEC-open]`'s closure
  (Selvage/Commitment.lean) transported to the deployed decider, same
  all-positions resolution.

**Keystones (ATLAS: satisfiable + teeth + premise inhabitation, BUILT,
computing over F₅, reusing Proximity's one-round tower):** the LINE
`![1,2,3,4]` passes the deployed decider at EVERY challenge stream
(`deciderProxLDT_accepts`) and the promise decider at δ = 0
(`deciderProx_accepts`); the certification bridge fires on its full acceptance
set (`line_certified`: 5 accepting tuples > error mass 1 ⇒ the semantic
verdict). Teeth through EACH conjunct separately: the 1/5-FAR spike
`![0,1,0,0]` meets every channel (`spikeClaim_channels_ok`) yet is rejected —
semantically at δ = 1/5 (`deciderProx_rejects_spike`, farness alone) and by
the deployed run at the good challenge (`deciderProxLDT_rejects_spike`); its
deployed acceptance set is computed EXACTLY (`= {![3]}` — the one laundering
challenge is real, the bound `m·b·|F|^{m−1} = 1` is ATTAINED with equality);
the honest codeword against a doctored channel is rejected on the channel
conjunct alone (`deciderProxLDT_rejects_offchannel`, at EVERY stream). The
sub-quantization head fires with all premises discharged by built objects
(`spike_bound_subquant` — no residual hypothesis anywhere in the chain).

**Honest scope, and what remains under `[DEC-prox-query]` (prose below):**
the deployed verifier here READS WHOLE LEVEL WORDS — Proximity's stated
resolution. The spot-check phase (per-round `t`-column openings against
per-round Merkle roots, consistency checks, the `t = λ/−log(1−δ)` repetition
accounting) and the checked cost constants (621 KiB / 4.8 ms / 10k hashes at
UD; 299 KiB / 2.5 ms at Johnson — LOOM §6) are NOT modeled; they ride the
commitment layer (`[COMMIT-CR]`, `[ACC-extract-bind]`(b)). Until that lands,
"the deployed decider" is priced at word-read resolution, macroscopic δ
conditional on `hPG` — sub-quantization δ unconditional.
-/
import Selvage.Decider
import Selvage.Proximity
import Selvage.Commitment

namespace Minidregg.Selvage

variable {Root : Type*} {F : Type*} [Field F]

/-! ## The promise-side decider: δ-closeness replaces exact membership -/

section Relaxed

variable {ι : Type*} {r : ℕ} [Fintype ι] [DecidableEq F]

/-- **The proximity decider, promise side** — `[DEC-proximity]`'s acceptance
relation: the exact-membership conjunct of `decider` relaxed to δ-closeness
(`close δ C f`), the channel conjunct unchanged. This is what the deployed
LDT run (`deciderProxLDT` below) certifies; at `δ = 0` — indeed anywhere below
the quantization radius — it IS the exact decider
(`deciderProx_iff_decider_of_lt_inv_card`). -/
def deciderProx (C : Submodule F (ι → F)) (A : AccClaim Root F ι r) (f : ι → F)
    (δ : ℝ) : Prop :=
  close δ C f ∧ ∀ i, A.weights i f = A.targets i

/-- Completeness: an honest satisfying word passes the proximity decider at
every radius δ ≥ 0 — membership is 0-closeness (`close_of_mem`). -/
theorem deciderProx_complete {C : Submodule F (ι → F)} {A : AccClaim Root F ι r}
    {f : ι → F} {δ : ℝ} (hδ : 0 ≤ δ) (h : AccClaim.Satisfies C A f) :
    deciderProx C A f δ :=
  ⟨close_of_mem h.1 hδ, h.2⟩

/-- The exact decider's verdict transfers: whatever `D_ACC` accepts, the
proximity decider accepts at every δ ≥ 0. -/
theorem deciderProx_of_decider {C : Submodule F (ι → F)}
    {A : AccClaim Root F ι r} {f : ι → F} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : decider C A f) : deciderProx C A f δ :=
  deciderProx_complete hδ ((decider_sound C A f).mp h)

/-- Promise-side soundness, definitional: a word δ-far from the code is
REJECTED — outright, no error probability. (The error enters only when the
deployed LDT run REALIZES the closeness conjunct; that is `deciderProx_sound`
below.) -/
theorem deciderProx_rejects_far {C : Submodule F (ι → F)}
    {A : AccClaim Root F ι r} {f : ι → F} {δ : ℝ}
    (hfar : ¬ close δ C f) : ¬ deciderProx C A f δ :=
  fun h => hfar h.1

/-- Acceptance is monotone in the radius: the promise only weakens as δ
grows. -/
theorem deciderProx_mono {C : Submodule F (ι → F)} {A : AccClaim Root F ι r}
    {f : ι → F} {δ δ' : ℝ} (h : δ ≤ δ') (hd : deciderProx C A f δ) :
    deciderProx C A f δ' :=
  ⟨hd.1.imp fun _u hu => ⟨hu.1, hu.2.trans h⟩, hd.2⟩

/-- Below the quantization radius the δ-ball around ANY code is the code:
`close δ C f ↔ f ∈ C` for `0 ≤ δ < 1/|ι|` — distinct words are at least
`1/|ι|` apart (`one_div_card_le_relDist`). (The `private` copies of this
collapse in AccSound/LightClientSound become reusable here.) -/
theorem close_iff_mem_of_lt_inv_card [Nonempty ι] {C : Submodule F (ι → F)}
    {f : ι → F} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / (Fintype.card ι : ℝ)) :
    close δ C f ↔ f ∈ C := by
  constructor
  · rintro ⟨u, huC, hu⟩
    have heq : f = u := by
      by_contra hne
      exact absurd (le_trans (one_div_card_le_relDist hne) hu) (not_le.mpr hδ)
    rw [heq]; exact huC
  · exact fun h => close_of_mem h hδ0

/-- **The exact-membership collapse**: below the quantization radius the
proximity decider IS the exact decider — the relaxation is invisible, and the
strict contract of `Selvage/Decider.lean` is recovered on the nose. -/
theorem deciderProx_iff_decider_of_lt_inv_card [Nonempty ι]
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {f : ι → F} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ < 1 / (Fintype.card ι : ℝ)) :
    deciderProx C A f δ ↔ decider C A f :=
  and_congr_left' (close_iff_mem_of_lt_inv_card hδ0 hδ)

/-- Below the quantization radius the proximity decider decides EXACTLY the
accumulated claim — `AccClaim.Satisfies`, the relation every fold-soundness
bound bounds. -/
theorem deciderProx_iff_satisfies_of_lt_inv_card [Nonempty ι]
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {f : ι → F} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ < 1 / (Fintype.card ι : ℝ)) :
    deciderProx C A f δ ↔ AccClaim.Satisfies C A f :=
  (deciderProx_iff_decider_of_lt_inv_card hδ0 hδ).trans (decider_sound C A f)

/-- **Depth independence survives the relaxation** (LOOM §6's compression):
on the fold of ANY chain the proximity decider's verdict is one δ-closeness
check plus the INITIAL accumulator's `r` functionals — fixed, independent of
`links.length` — against the scalars carried by the final claim
(`foldChain_weights`). The chain enters only through those scalars. -/
theorem deciderProx_depth_independent (foldRoot : Root → F → Root → Root)
    (C : Submodule F (ι → F)) (A : AccClaim Root F ι r)
    (links : List (AccClaim Root F ι r × F)) (f : ι → F) (δ : ℝ) :
    deciderProx C (foldChain foldRoot A links) f δ
      ↔ close δ C f
          ∧ ∀ i, A.weights i f = (foldChain foldRoot A links).targets i := by
  simp only [deciderProx, foldChain_weights]

/-- The `[DEC-open]` seam, transported: under a binding commitment, the word
the proximity decider checked — fully opened from the final accumulator's
root — IS the committed word, and the verdict transfers to it
(`opened_eq_committed`, exactly as `decider_open_sound`). -/
theorem deciderProx_open_sound {Op : Type*} (S : BindingCommitment Root F ι Op)
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {w f : ι → F} {δ : ℝ}
    {of : ι → Op} (hrt : A.rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen A.rt i (f i) (of i))
    (hdec : deciderProx C A f δ) :
    f = w ∧ deciderProx C A w δ := by
  have hf : f = w := S.opened_eq_committed fun i => hrt ▸ hopen i
  exact ⟨hf, hf ▸ hdec⟩

end Relaxed

/-! ## The deployed decider: one LDT descent + the channel checks -/

section Deployed

variable {r : ℕ} {ι : ℕ → Type*} {m : ℕ}

/-- **The deployed proximity decider** — what the real verifier runs at
rate < 1: ONE descent of the folding tower on the final word (`proximityTest`,
the WHIR descent deferred from every link — LOOM §6) plus the same `r` channel
checks of the final accumulated claim. The exact-membership conjunct of
`decider` is replaced by the spot-checkable test; everything else is
unchanged. -/
def deciderProxLDT (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (A : AccClaim Root F (ι 0) r) (f : ι 0 → F) (αs : ℕ → F) : Prop :=
  proximityTest T deg f αs ∧ ∀ i, A.weights i f = A.targets i

/-- **Completeness of the deployed decider, PROVED**: an honest satisfying
word passes for EVERY challenge stream — `proximity_complete` carries the
descent, the claim carries the channels. -/
theorem deciderProxLDT_complete (T : FoldingTower F ι m) {deg : ℕ → ℕ}
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
    {A : AccClaim Root F (ι 0) r} {f : ι 0 → F}
    (hsat : AccClaim.Satisfies (reedSolomonCode (T.dom 0) (deg 0)) A f)
    (αs : ℕ → F) : deciderProxLDT T deg A f αs :=
  ⟨proximity_complete T hdeg hsat.1 αs, hsat.2⟩

/-- Depth independence of the deployed decider: the descent runs ONCE, on the
final word, whatever the chain depth — and the functional channel after any
fold is the initial accumulator's own (`foldChain_weights`). -/
theorem deciderProxLDT_depth_independent (foldRoot : Root → F → Root → Root)
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) (A : AccClaim Root F (ι 0) r)
    (links : List (AccClaim Root F (ι 0) r × F)) (f : ι 0 → F) (αs : ℕ → F) :
    deciderProxLDT T deg (foldChain foldRoot A links) f αs
      ↔ proximityTest T deg f αs
          ∧ ∀ i, A.weights i f = (foldChain foldRoot A links).targets i := by
  simp only [deciderProxLDT, foldChain_weights]

/-- The `[DEC-open]` seam for the deployed decider: the word the descent ran
on, fully opened from the final root, IS the committed word — the deployed
verdict is a verdict on THE word `rt` binds. -/
theorem deciderProxLDT_open_sound {Op : Type*}
    (S : BindingCommitment Root F (ι 0) Op) {T : FoldingTower F ι m}
    {deg : ℕ → ℕ} {A : AccClaim Root F (ι 0) r} {w f : ι 0 → F}
    {of : ι 0 → Op} {αs : ℕ → F} (hrt : A.rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen A.rt i (f i) (of i))
    (hdec : deciderProxLDT T deg A f αs) :
    f = w ∧ deciderProxLDT T deg A w αs := by
  have hf : f = w := S.opened_eq_committed fun i => hrt ▸ hopen i
  exact ⟨hf, hf ▸ hdec⟩

section Count

variable [Fintype F]

/-- The deployed decider's acceptance set: the challenge tuples on which a
fixed word passes the descent AND the channels (classically measurable, like
`acceptSet`). -/
noncomputable def deciderProxAcceptSet (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (A : AccClaim Root F (ι 0) r) (f : ι 0 → F) : Finset (Fin m → F) :=
  letI : DecidablePred fun c : Fin m → F => deciderProxLDT T deg A f (chalExt c) :=
    fun _ => Classical.propDecidable _
  Finset.univ.filter fun c => deciderProxLDT T deg A f (chalExt c)

theorem mem_deciderProxAcceptSet {T : FoldingTower F ι m} {deg : ℕ → ℕ}
    {A : AccClaim Root F (ι 0) r} {f : ι 0 → F} {c : Fin m → F} :
    c ∈ deciderProxAcceptSet T deg A f ↔ deciderProxLDT T deg A f (chalExt c) := by
  simp [deciderProxAcceptSet]

/-- The channel conjunct only SHRINKS the acceptance event: the deployed
decider's acceptance set is contained in the LDT's — the containment through
which `proximity_sound` prices the deployed decider. -/
theorem deciderProxAcceptSet_subset (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (A : AccClaim Root F (ι 0) r) (f : ι 0 → F) :
    deciderProxAcceptSet T deg A f ⊆ acceptSet T deg f := fun _c hc =>
  mem_acceptSet.mpr (mem_deciderProxAcceptSet.mp hc).1

variable [∀ n, Fintype (ι n)] [DecidableEq F]

/-- **`deciderProx_sound` — the deployed decider rejects δ-far words** (the
`[DEC-proximity]` soundness head): a word δ-FAR from the level-0 code passes
the deployed decider for at most `m·b·|F|^{m−1}` of the `|F|^m` challenge
tuples — the acceptance set is contained in the LDT's (`deciderProxAcceptSet_subset`)
and `proximity_sound` bounds that. Residual hypothesis: exactly Proximity's
per-level `[PROX-fold-distance]` (`hfold`), delivered unconditionally at
sub-quantization δ (`deciderProx_sound_subquant`) and via the standing RS
proximity gap at macroscopic δ (`deciderProx_sound_of_proximityGenerator`). -/
theorem deciderProx_sound (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    (A : AccClaim Root F (ι 0) r) {f : ι 0 → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (deciderProxAcceptSet T deg A f).card ≤ m * (b * Fintype.card F ^ (m - 1)) :=
  le_trans (Finset.card_le_card (deciderProxAcceptSet_subset T deg A f))
    (proximity_sound T deg hδ hfold hfar)

/-- `deciderProx_sound`, probability rendering: a δ-far word passes the
deployed decider with probability at most `m·b/|F|` over the uniform challenge
tuple — the FRI/WHIR soundness shape, inherited whole. -/
theorem deciderProx_sound_prob (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    (A : AccClaim Root F (ι 0) r) {f : ι 0 → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    ((deciderProxAcceptSet T deg A f).card : ℝ) / (Fintype.card F : ℝ) ^ m
      ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
  refine le_trans ?_ (proximity_sound_prob T deg hδ hfold hfar)
  have hFm : (0 : ℝ) < (Fintype.card F : ℝ) ^ m := by
    have h : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  exact (div_le_div_iff_of_pos_right hFm).mpr
    (by exact_mod_cast Finset.card_le_card (deciderProxAcceptSet_subset T deg A f))

/-- **The exact-membership regime, UNCONDITIONAL**: below the per-level
quantization radius (`δ < 1/|ι_{j+1}|` at every level) the deployed decider is
end-to-end sound TODAY with `b = 1` — the fold-distance hypothesis is
discharged by the PROVED sub-quantization realizer
(`foldDistancePreserving_of_lt_inv_card`); no residual hypothesis remains. -/
theorem deciderProx_sound_subquant (T : FoldingTower F ι m) {deg : ℕ → ℕ}
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
    (hne : ∀ j, j < m → Nonempty (ι (j + 1)))
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδκ : ∀ j, j < m → δ < 1 / (Fintype.card (ι (j + 1)) : ℝ))
    (A : AccClaim Root F (ι 0) r) {f : ι 0 → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (deciderProxAcceptSet T deg A f).card ≤ m * Fintype.card F ^ (m - 1) := by
  have hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ 1 := by
    intro j hj
    haveI := hne j hj
    have h := foldDistancePreserving_of_lt_inv_card (T.data j hj) (deg (j + 1))
      hδ0 (hδκ j hj)
    rwa [← hdeg j hj] at h
  simpa using deciderProx_sound T deg hδ0 hfold A hfar

/-- **The macroscopic regime, riding the standing `hPG`**: for
`δ ∈ (0, 1−B)`, if the affine generator is a proximity generator for every
folded code of the tower — WHIR Theorem 4.8 / BCIKS 2020/654, the ONE standing
Reed–Solomon hypothesis of `Selvage/ReedSolomon.lean`, consumed here per level
and NOT claimed — the deployed decider inherits the bound with
`b ≥ err(δ)·|F|`. -/
theorem deciderProx_sound_of_proximityGenerator [∀ n, DecidableEq (ι n)]
    (T : FoldingTower F ι m) {deg : ℕ → ℕ}
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
    (hne : ∀ j, j < m → Nonempty (ι j))
    {B : ℝ} {err : ℝ → ℝ}
    (hPG : ∀ j, j < m →
      IsProximityGenerator (affineGenerator F)
        (reedSolomonCode (T.dom (j + 1)) (deg (j + 1))) B err)
    {δ : ℝ} (hδ0 : 0 < δ) (hδB : δ < 1 - B) {b : ℕ}
    (hb : err δ * (Fintype.card F : ℝ) ≤ (b : ℝ))
    (A : AccClaim Root F (ι 0) r) {f : ι 0 → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (deciderProxAcceptSet T deg A f).card ≤ m * (b * Fintype.card F ^ (m - 1)) := by
  have hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b := by
    intro j hj
    haveI := hne j hj
    have h := foldDistancePreserving_of_isProximityGenerator (T.data j hj)
      (deg (j + 1)) (hPG j hj) hδ0 hδB hb
    rwa [← hdeg j hj] at h
  exact deciderProx_sound T deg hδ0.le hfold A hfar

/-- **The certification bridge**: a word accepted by the deployed decider on
MORE challenge tuples than the error mass genuinely satisfies the promise-side
relation — δ-close AND every channel holds. The deployed count is quantified
evidence for `deciderProx`; contrapositive of `deciderProx_sound` on the
closeness conjunct, any accepting tuple on the channels. -/
theorem deciderProx_of_card_gt (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    (A : AccClaim Root F (ι 0) r) {f : ι 0 → F}
    (hbig : m * (b * Fintype.card F ^ (m - 1))
      < (deciderProxAcceptSet T deg A f).card) :
    deciderProx (reedSolomonCode (T.dom 0) (deg 0)) A f δ := by
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbig)
  refine ⟨?_, (mem_deciderProxAcceptSet.mp hc).2⟩
  by_contra hfar
  exact absurd (deciderProx_sound T deg hδ hfold A hfar) (not_le.mpr hbig)

end Count

end Deployed

/-! ## Keystones over F₅ (ATLAS: satisfiable + teeth + premise inhabitation)

Proximity's one-round tower (`{1,2,3,4} → {1,4}`, degree schedule `2 → 1`) and
its two words: the LINE `![1,2,3,4]` (a codeword) and the 1/5-FAR spike
`![0,1,0,0]`. New here: WARP-shape claims whose channels the words meet or
violate, so BOTH conjuncts of the deployed decider fire separately. -/

namespace DeciderProxExample

open ProximityExample AccExample

/-- The line's claim on the tower's level-0 domain `{1,2,3,4}`: `f 2 = 3`,
`∑ f = 0` — a WARP-shape channel the honest word genuinely meets. -/
def lineClaim : AccClaim Unit (ZMod 5) (Fin 4) 2 :=
  AccClaim.warp () (q2, 3) (consv, 0)

theorem lineClaim_channels_ok :
    ∀ i, lineClaim.weights i xWord = lineClaim.targets i := by decide

theorem lineClaim_satisfies :
    AccClaim.Satisfies (reedSolomonCode dom0 2) lineClaim xWord :=
  ⟨xWord_mem, lineClaim_channels_ok⟩

/-! ### Satisfiable: both renderings ACCEPT the honest word -/

/-- **Satisfiable, promise side**: the honest word passes the proximity
decider at δ = 0 — the relaxation costs the honest prover nothing. -/
theorem deciderProx_accepts :
    deciderProx (reedSolomonCode dom0 2) lineClaim xWord 0 :=
  deciderProx_complete le_rfl lineClaim_satisfies

/-- **Satisfiable, deployed**: the honest word passes the deployed decider —
descent AND channels — for EVERY challenge stream. -/
theorem deciderProxLDT_accepts (αs : ℕ → ZMod 5) :
    deciderProxLDT ldtTower degSched lineClaim xWord αs :=
  deciderProxLDT_complete ldtTower degSched_halving lineClaim_satisfies αs

/-! ### Teeth: rejection through EACH conjunct separately -/

/-- A claim whose channels the far spike `![0,1,0,0]` MEETS (`f 2 = 0`,
`∑ f = 1`) — so every rejection of the spike below is carried by the
proximity conjunct alone. -/
def spikeClaim : AccClaim Unit (ZMod 5) (Fin 4) 2 :=
  AccClaim.warp () (q2, 0) (consv, 1)

theorem spikeClaim_channels_ok :
    ∀ i, spikeClaim.weights i spikeWord = spikeClaim.targets i := by decide

/-- **Proximity teeth, promise side**: the 1/5-far spike is rejected at
δ = 1/5 with its channels all HOLDING — farness alone carries the
rejection. -/
theorem deciderProx_rejects_spike :
    ¬ deciderProx (reedSolomonCode dom0 2) spikeClaim spikeWord (1 / 5) :=
  deciderProx_rejects_far spikeWord_far

/-- **Proximity teeth, deployed, computing**: at the good challenge `α = 1`
the deployed decider REJECTS the far spike — the descent catches it
(`spike_accept_iff`), channels notwithstanding. -/
theorem deciderProxLDT_rejects_spike :
    ¬ deciderProxLDT ldtTower degSched spikeClaim spikeWord (chalExt ![1]) :=
  fun h => absurd ((spike_accept_iff 1).mp h.1) (by decide)

/-- The one laundering challenge is REAL: at `α = 3` the far spike passes the
deployed decider — the soundness error is a genuine phenomenon, not slack. -/
theorem deciderProxLDT_spike_bad :
    deciderProxLDT ldtTower degSched spikeClaim spikeWord (chalExt ![3]) :=
  ⟨(spike_accept_iff 3).mpr rfl, spikeClaim_channels_ok⟩

/-- **Channel teeth, deployed**: the honest CODEWORD — which passes the
descent at every challenge — is rejected against a doctored channel
(`f 2 = 3 ≠ 2`) at EVERY stream: the channel conjunct is load-bearing too. -/
def offClaim : AccClaim Unit (ZMod 5) (Fin 4) 2 :=
  AccClaim.warp () (q2, 2) (consv, 0)

theorem deciderProxLDT_rejects_offchannel (αs : ℕ → ZMod 5) :
    ¬ deciderProxLDT ldtTower degSched offClaim xWord αs :=
  fun h => absurd (h.2 0) (by decide)

/-- Channel teeth on the promise side, at every radius: no amount of
δ-generosity repairs a violated channel. -/
theorem deciderProx_rejects_offchannel (δ : ℝ) :
    ¬ deciderProx (reedSolomonCode dom0 2) offClaim xWord δ :=
  fun h => absurd (h.2 0) (by decide)

/-! ### The acceptance set computed exactly; the bound attained -/

/-- With the spike's channels holding identically, the deployed acceptance set
IS the LDT acceptance set — the containment `deciderProxAcceptSet_subset` is
an equality on this instance. -/
theorem deciderProxAcceptSet_spike :
    deciderProxAcceptSet ldtTower degSched spikeClaim spikeWord
      = acceptSet ldtTower degSched spikeWord := by
  ext c
  rw [mem_deciderProxAcceptSet, mem_acceptSet]
  exact ⟨fun h => h.1, fun h => ⟨h, spikeClaim_channels_ok⟩⟩

/-- The deployed acceptance set of the far spike, EXACTLY: the single
laundering tuple `![3]`. -/
theorem deciderProxAcceptSet_spike_eq :
    deciderProxAcceptSet ldtTower degSched spikeClaim spikeWord = {![3]} := by
  rw [deciderProxAcceptSet_spike, acceptSet_spike]

/-- **`deciderProx_sound` fires end-to-end, zero residual hypotheses**: the
far spike's deployed acceptance count is bounded by `m·b·|F|^{m−1} = 1`,
with the fold-distance premise discharged by Proximity's packaged
sub-quantization realizer (`ldtTower_hfold`). -/
theorem spike_bound :
    (deciderProxAcceptSet ldtTower degSched spikeClaim spikeWord).card ≤ 1 := by
  simpa using deciderProx_sound (δ := 1 / 5) ldtTower degSched (by norm_num)
    ldtTower_hfold spikeClaim spikeWord_far

/-- The UNCONDITIONAL sub-quantization head fires with every premise
discharged by built objects — degree halving, nonempty folded level,
`1/5 < 1/2` below the level-1 quantization radius. -/
theorem spike_bound_subquant :
    (deciderProxAcceptSet ldtTower degSched spikeClaim spikeWord).card ≤ 1 := by
  have h := deciderProx_sound_subquant (δ := 1 / 5) ldtTower degSched_halving
    (fun j hj => by
      have h0 : j = 0 := by omega
      subst h0
      exact ⟨(0 : Fin 2)⟩)
    (by norm_num)
    (fun j hj => by
      have h0 : j = 0 := by omega
      subst h0
      show (1 : ℝ) / 5 < 1 / (Fintype.card (Fin 2) : ℝ)
      rw [Fintype.card_fin]
      norm_num)
    spikeClaim spikeWord_far
  simpa using h

/-- The bound is ATTAINED: deployed acceptance count exactly 1 —
`deciderProx_sound` is tight on this instance (1/5 acceptance probability,
exactly `m·b/|F|`). -/
theorem spike_bound_attained :
    (deciderProxAcceptSet ldtTower degSched spikeClaim spikeWord).card = 1 := by
  rw [deciderProxAcceptSet_spike_eq]
  exact Finset.card_singleton _

/-! ### The exact-membership collapse fires -/

/-- Below the level-0 quantization floor (`1/5 < 1/4`) the proximity decider
IS the exact decider — for EVERY claim and EVERY word: the relaxation is
invisible at the keystone radius, so the strict contract of
`Selvage/Decider.lean` (and with it `AccClaim.Satisfies`) is exactly what the
deployed decider certifies here. -/
theorem collapse_at_fifth (A : AccClaim Unit (ZMod 5) (Fin 4) 2)
    (f : Fin 4 → ZMod 5) :
    deciderProx (reedSolomonCode dom0 2) A f (1 / 5)
      ↔ decider (reedSolomonCode dom0 2) A f :=
  deciderProx_iff_decider_of_lt_inv_card (by norm_num)
    (by rw [Fintype.card_fin]; norm_num)

/-! ### The certification bridge fires -/

/-- **Premise inhabitation for `deciderProx_of_card_gt`**: the line is
accepted on ALL 5 challenge tuples — strictly more than the error mass 1 —
so the deployed counts alone certify the semantic verdict at δ = 1/5. -/
theorem line_certified :
    deciderProx (reedSolomonCode dom0 2) lineClaim xWord (1 / 5) := by
  refine deciderProx_of_card_gt (δ := 1 / 5) ldtTower degSched (by norm_num)
    ldtTower_hfold lineClaim ?_
  have huniv : deciderProxAcceptSet ldtTower degSched lineClaim xWord
      = Finset.univ :=
    Finset.eq_univ_of_forall fun c =>
      mem_deciderProxAcceptSet.mpr (deciderProxLDT_accepts (chalExt c))
  rw [huniv, Finset.card_univ]
  decide

end DeciderProxExample

/-! ## Residual obligation — prose, not a stub

Named residual with its realizer; it becomes a real theorem, never a
`def : Prop := True` (the audit discipline).

**[DEC-prox-query]** — the spot-check phase of the deployed descent. The
verifier modeled here reads WHOLE level words (Proximity's stated resolution);
the deployed WHIR verifier instead opens `t` spot-checked columns per round
against per-round Merkle roots, checks fold-consistency on the opened symbols
only, and repeats to `t = λ/−log(1−δ)`. What this residual owes: (i) the
per-round commitment of level words and the consistency check ON OPENED
SYMBOLS as derived objects — riding `[COMMIT-CR]` (the Merkle realizer) and
`[ACC-extract-bind]`(b) (the `t`-column erasure lift, owed in
`Selvage/AccExtract.lean`'s ledger); (ii) the query-repetition soundness
accounting composing with `deciderProx_sound`'s per-round bound; (iii) the
checked cost constants (621 KiB / 4.8 ms / 10k hashes at UD, 299 KiB / 2.5 ms
at Johnson — LOOM §6), which belong to `[DEC-succinct]`'s cost model. Until it
lands, the honest label: the deployed decider is PROVED to accept δ-close and
reject δ-far at word-read resolution — unconditionally below quantization,
modulo the ONE standing `hPG` at macroscopic δ — and the oracle/query layer is
priced, not assumed.

## Ledger

* `deciderProx` — the promise-side relation (`close δ` + channels);
  `deciderProxLDT` — the deployed run (one descent + channels).
* `deciderProx_complete` / `deciderProx_of_decider` /
  `deciderProxLDT_complete` — completeness, both renderings, every stream.
* `deciderProx_sound` (+ `_prob`) — δ-far acceptance ≤ `m·b·|F|^{m−1}`
  (probability `m·b/|F|`), by containment into `proximity_sound`.
* `deciderProx_sound_subquant` — UNCONDITIONAL, `b = 1`, sub-quantization δ;
  `deciderProx_sound_of_proximityGenerator` — macroscopic δ on the standing
  `hPG`, consumed not claimed.
* `close_iff_mem_of_lt_inv_card` → `deciderProx_iff_decider_of_lt_inv_card` /
  `deciderProx_iff_satisfies_of_lt_inv_card` — the exact-membership collapse.
* `deciderProx_of_card_gt` — the certification bridge (deployed counts ⇒
  semantic verdict).
* `deciderProx_depth_independent` / `deciderProxLDT_depth_independent` — one
  descent, `r` functionals, any depth.
* `deciderProx_open_sound` / `deciderProxLDT_open_sound` — `[DEC-open]`
  transported (all-positions resolution, as in `Selvage/Commitment.lean`).
* Keystones — accept both renderings (`deciderProx_accepts`,
  `deciderProxLDT_accepts`), teeth per conjunct (`deciderProx_rejects_spike`,
  `deciderProxLDT_rejects_spike`, `deciderProxLDT_rejects_offchannel`,
  `deciderProx_rejects_offchannel`), the laundering challenge real
  (`deciderProxLDT_spike_bad`), acceptance set exact + bound attained
  (`deciderProxAcceptSet_spike_eq`, `spike_bound_attained`), the
  unconditional head fired (`spike_bound_subquant`), the bridge fired
  (`line_certified`).
* Residual — `[DEC-prox-query]` (prose above).
* `#print axioms`: every theorem above — `propext`, `Classical.choice`,
  `Quot.sound` only (audited; `Classical.choice` enters through ℝ and the
  classical acceptance-set measurability, exactly as in Selvage/Proximity.lean). -/

end Minidregg.Selvage
