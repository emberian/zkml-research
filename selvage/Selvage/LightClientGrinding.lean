/-
# Selvage.LightClientGrinding — [LC-fs-adaptive]: the grinding adversary pays the
# try-count factor.

`Selvage/LightClientFS.lean` closed [LC-sound-fs] at the FIXED-chain level — the
non-interactive light client inherits both bounds when the chain is committed
before the oracle samples — and named exactly one strengthening residual:
**[LC-fs-adaptive]**, the grinding adversary, who queries the ROM and chooses
(or REORDERS) the chain AFTER seeing the answers, paying the `(t + n)` factor
of WARP Thm B.4 — whose general form is already PROVED as
`fsKeystone_proved`/`FsOfRbrSound` (`Selvage/FiatShamir.lean`, `(t+k)·ε_rbr`,
unconditional). This file closes the deployment-bookkeeping piece: the
grinding model rendered honestly, and the composition of the fixed-chain
bound with the try-count factor — a real union-bound proof with the
per-candidate marginals EXACT.

The model (one shared oracle, real correlations):
* `Oracle.ofList` — the handler after the adversary's whole query run: fold
  `respond` over its duplicate-free query list, one game coin per cell. ONE
  handler serves EVERY candidate chain; prefixes shared between candidates
  replay the same coin — grinding's actual correlation, kept, not idealized
  away.
* `grindIdx` / `grindSchedule_eq` — a fully-queried candidate's FS-derived
  schedule is the pullback of the shared coin tuple along its prefix-index
  map (injective by `linkPrefix_injective`, REUSED), for every lazy
  fallback.
* `injSplit` / `uniformProb_comp_injective` — the marginal along an
  injection: read through pairwise-distinct cells, the shared coins are
  EXACTLY uniform. Each candidate faces the fixed-chain distribution
  unchanged — `lightClientSound`/`lightClientSound_exact` (the engines
  `lightClientFS_sound`/`lightClientFS_exact` transport) price every try
  verbatim; only the union over tries costs.
* The `∃ i` in every statement IS the post-answer chain selection: any rule
  the adversary uses to pick its submission from the grind set is dominated
  by it. And `grindCandidates_le_budget`: distinct nonempty candidates have
  distinct full prefixes, so `T ≤ t` — a `t`-query adversary genuinely has
  at most `t` tries.

The bounds (statement-first, proven parameters only):
* `lightClientGrinding_exact` — exact-word: `T · 1/|F|` (`≤ (t+n)·1/|F|`) —
  at the exact-word level the union-bound composition already attains the
  keystone's per-query `(t+k)·ε` SHAPE at the per-fold price.
* `lightClientGrinding_union` — δ-proximity, the sharp Σ form:
  `∑ᵢ nᵢ · (err⋆(δ) + 1/|F|)`.
* `lightClientGrinding_sound` — THE (t+n)-SCALED HEADLINE:
  `(t + n) · [n · (err⋆(δ) + 1/|F|)]`, the grinding factor scaling the
  fixed-chain bound of `lightClientFS_sound`. Union-bound accounting pays
  per-try·per-chain; the per-query·per-fold sharpening
  `(t+n)·(err⋆ + 1/|F|)` is the native RBR form — `[LC-grinding-native]`,
  end of file.

**Keystones (F₅, computing):** the grinding adversary of the residual's own
phrase — it REORDERS the chain: candidates = the landed `phantomChain` and
its swap. Four distinct prefixes, budget `t = 4`; each try alone forges at
EXACTLY the fixed-chain sharp bound `1/5` (`grindFirst_marginal_prob`,
attained); the grind forges at `9/25 > 1/5` (`phantomGrind_forging_prob`,
EXACT via inclusion–exclusion; `phantomGrind_beats_fixed_bound` — the
try-count factor is LOAD-BEARING: no fixed-chain-shaped bound survives
grinding). The general theorems fire with every hypothesis discharged
(`phantomGrind_caught_probably` at `2/5`, slack = the computed overlap
`1/25`; `phantomGrind_delta_fired` at `4/5`), and both poles compute: coins
`(1,0,1,1)` catch the phantom while its REORDER forges — the post-answer
selection genuinely at work; coins `(1,0,2,1)` catch every candidate.

**What this does NOT close (honest residuals, end of file):**
`[LC-grinding-native]` — the per-fold-sharp `(t+n)·(err⋆(δ)+1/|F|)` with
full query adaptivity. Its RBR engine LANDED while this file was being
written: `accFsSound_native` (Selvage/AccRbrInstance.lean) FS-compiles the
accumulator chain's OWN reduction at `(t+k)·accRbrError` — exactly that
bound, at the IOR resolution, adaptive over all `SrProver` strategies. What
remains here is the TRANSPORT of that SR-game statement into this file's
light-client event vocabulary (LcQuery prefixes ↔ `SrMove`s,
`Verifies ∘ aggregate` ↔ the reduction's target relation), inheriting
`[ACC-rbr-bcs]` for the deployed message alphabet; `[FS-ROM]` and
`[ACC-extract]` inherited unchanged.
-/
import Selvage.LightClientSound
import Selvage.FiatShamir
import Selvage.LightClientFS

namespace Minidregg.Selvage

/-! ## Counting plumbing: marginals of the shared coin space

`Selvage/Depth.lean` owns the public `uniformProb` toolkit (REUSED below:
`uniformProb_congr/_mono/_equiv/_prod_le/_exists_le`). The three facts it
lacks — the product-first marginal, inclusion–exclusion, and the marginal
along an injection — are new vocabulary here. The first two stay `private`
(the `Selvage/AccSound.lean` discipline); the injection marginal is this file's
transfer engine and is public: it is what lets ONE shared oracle serve every
candidate chain of a grind while each candidate still sees an exactly-uniform
schedule. -/

section Marginals

private def prodFstSubtype {A B : Type} (p : A → Prop) :
    {y : A × B // p y.1} ≃ {a : A // p a} × B where
  toFun y := (⟨y.1.1, y.2⟩, y.1.2)
  invFun x := ⟨(x.1.1, x.2), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Marginalizing out an untouched second factor: an event reading only the
first component of a product coin space keeps its probability. (The `Nonempty`
guard is real: over an empty second factor the product probability degenerates
to `0` while the first-factor probability need not.) -/
private theorem uniformProb_fst {A B : Type} [Fintype A] [Fintype B]
    [Nonempty B] (p : A → Prop) :
    uniformProb (A × B) (fun y => p y.1) = uniformProb A p := by
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold uniformProb
  rw [Nat.card_congr (prodFstSubtype p), Nat.card_prod,
    Nat.card_eq_fintype_card (α := B), Fintype.card_prod]
  push_cast
  rw [← div_mul_div_comm, div_self hB, mul_one]

/-- Inclusion–exclusion for `uniformProb`, as an equality — what prices the
union bound's slack EXACTLY (the keystones below compute the overlap term). -/
private theorem uniformProb_or_eq {C : Type} [Fintype C] (p q : C → Prop) :
    uniformProb C (fun c => p c ∨ q c)
      = uniformProb C p + uniformProb C q
        - uniformProb C (fun c => p c ∧ q c) := by
  classical
  have h : ({c | p c} ∪ {c | q c} : Set C).ncard
        + ({c | p c} ∩ {c | q c} : Set C).ncard
      = ({c | p c} : Set C).ncard + ({c | q c} : Set C).ncard :=
    Set.ncard_union_add_ncard_inter _ _ (Set.toFinite _) (Set.toFinite _)
  have key : (Nat.card {c : C // p c ∨ q c} : ℝ)
      = (Nat.card {c : C // p c} : ℝ) + (Nat.card {c : C // q c} : ℝ)
        - (Nat.card {c : C // p c ∧ q c} : ℝ) := by
    have h' : Nat.card {c : C // p c ∨ q c} + Nat.card {c : C // p c ∧ q c}
        = Nat.card {c : C // p c} + Nat.card {c : C // q c} := h
    have := congrArg (Nat.cast (R := ℝ)) h'
    push_cast at this
    linarith
  unfold uniformProb
  rw [key, sub_div, add_div]

open Classical in
/-- **Split a tuple space along an injection** — coordinates in the range,
read back through `e`, beside the coordinates outside it. Hand-rolled so the
first component is DEFINITIONALLY the pullback `fun a => c (e a)` (the
`schedCons` discipline of `Selvage/LightClientSound.lean`). -/
noncomputable def injSplit {α β : Type} {e : α → β}
    (he : Function.Injective e) (G : Type) :
    (β → G) ≃ ((α → G) × ({x : β // ∀ a, e a ≠ x} → G)) where
  toFun c := (fun a => c (e a), fun x => c x.1)
  invFun y x :=
    if h : ∃ a, e a = x then y.1 h.choose
    else y.2 ⟨x, fun a ha => h ⟨a, ha⟩⟩
  left_inv c := by
    funext x
    dsimp only
    by_cases h : ∃ a, e a = x
    · rw [dif_pos h]
      exact congrArg c h.choose_spec
    · rw [dif_neg h]
  right_inv y := by
    refine Prod.ext (funext fun a => ?_) (funext fun x => ?_)
    · have h : ∃ a', e a' = e a := ⟨a, rfl⟩
      dsimp only
      rw [dif_pos h]
      exact congrArg y.1 (he h.choose_spec)
    · obtain ⟨x, hx⟩ := x
      have h : ¬ ∃ a, e a = x := fun hex => hex.elim fun a ha => hx a ha
      dsimp only
      rw [dif_neg h]

/-- **The marginal along an injection**: an event that reads a uniform tuple
only through pairwise-distinct coordinates has EXACTLY the probability of the
event on those coordinates' own uniform space. This is the whole reason one
shared oracle can serve every candidate of a grind: each candidate's schedule
is the pullback of the shared coin tuple along its (injective,
`linkPrefix_injective`) prefix-index map, so each candidate faces the
fixed-chain distribution unchanged — only the UNION over candidates costs. -/
theorem uniformProb_comp_injective {α β G : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype G] [Nonempty G] {e : α → β}
    (he : Function.Injective e) (p : (α → G) → Prop) :
    uniformProb (β → G) (fun c => p (fun a => c (e a)))
      = uniformProb (α → G) p := by
  classical
  haveI : Nonempty ({x : β // ∀ a, e a ≠ x} → G) :=
    ⟨fun _ => Classical.arbitrary G⟩
  have h := uniformProb_equiv (injSplit he G)
    (fun y : (α → G) × ({x : β // ∀ a, e a ≠ x} → G) => p y.1)
  rw [show (fun c : β → G => p (fun a => c (e a)))
      = (fun c : β → G => p ((injSplit he G) c).1) from rfl, h,
    uniformProb_fst]

end Marginals

/-! ## The shared grind oracle: one handler, every candidate -/

namespace Oracle

variable {Q C : Type}

/-- **The oracle a query list builds**: fold `respond` over the list, coin
`c j` at position `j` — the lazy-sampling handler after the grinding
adversary's whole query run. ONE handler for ALL candidates: prefixes shared
between candidate chains are logged once and REPLAY the same coin — the
correlation grinding actually has, kept, not idealized away. (`fsDerive`,
Selvage/LightClientFS.lean, is the one-candidate instance of this shape.) -/
noncomputable def ofList (qs : List Q) (c : Fin qs.length → C) : Oracle Q C :=
  (List.finRange qs.length).foldl
    (fun O j => (O.respond (qs.get j) (c j)).2) Oracle.empty

/-- Every listed query is logged with exactly its position's coin — the
duplicate-free query run draws one fresh coin per cell
(`Oracle.lookup_foldl_respond`, Selvage/LightClientFS.lean, REUSED; distinctness
is the `Nodup` hypothesis). -/
theorem lookup_ofList {qs : List Q} (hnd : qs.Nodup) (c : Fin qs.length → C)
    (j : Fin qs.length) : (ofList qs c).lookup (qs.get j) = some (c j) := by
  unfold ofList
  exact Oracle.lookup_foldl_respond (fun j : Fin qs.length => qs.get j) c
    (List.finRange qs.length) Oracle.empty
    (fun j₁ _ j₂ _ h => List.nodup_iff_injective_get.mp hnd h)
    (List.nodup_finRange _) (fun _ _ => Oracle.lookup_empty _)
    j (List.mem_finRange j)

end Oracle

variable {Root ι : Type} {F : Type} [Field F] {r : ℕ}

/-! ## The candidate's index map into the shared query list -/

/-- **The grinding index map**: where candidate `ch`'s round-`k` transcript
prefix sits in the adversary's query list. Exists whenever the adversary
actually queried every prefix of the candidate (`hcov` — a candidate with an
unqueried prefix faces a FRESH coin at verification and is fixed-chain
territory, `lightClientFS_sound`). -/
noncomputable def grindIdx (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    (qs : List (LcQuery Root F ι r))
    (hcov : ∀ k : Fin ch.length, linkPrefix A₀ ch (k : ℕ) ∈ qs) :
    Fin ch.length → Fin qs.length :=
  fun k => ⟨(List.mem_iff_getElem.mp (hcov k)).choose,
    (List.mem_iff_getElem.mp (hcov k)).choose_spec.choose⟩

theorem grindIdx_get (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    (qs : List (LcQuery Root F ι r))
    (hcov : ∀ k : Fin ch.length, linkPrefix A₀ ch (k : ℕ) ∈ qs)
    (k : Fin ch.length) :
    qs.get (grindIdx A₀ ch qs hcov k) = linkPrefix A₀ ch (k : ℕ) :=
  (List.mem_iff_getElem.mp (hcov k)).choose_spec.choose_spec

/-- The index map is injective: distinct links have distinct prefixes
(`linkPrefix_injective`, Selvage/LightClientFS.lean — the load-bearing
distinctness, REUSED), hence distinct positions. This is what feeds
`uniformProb_comp_injective`: each candidate reads the shared coins at
pairwise-distinct cells. -/
theorem grindIdx_injective (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) (qs : List (LcQuery Root F ι r))
    (hcov : ∀ k : Fin ch.length, linkPrefix A₀ ch (k : ℕ) ∈ qs) :
    Function.Injective (grindIdx A₀ ch qs hcov) := fun k₁ k₂ h =>
  linkPrefix_injective A₀ ch
    (by rw [← grindIdx_get A₀ ch qs hcov k₁, ← grindIdx_get A₀ ch qs hcov k₂, h])

/-- **The candidate's FS schedule under the shared oracle, in closed form**:
the pullback of the shared coin tuple along its index map — for EVERY lazy
fallback (every prefix is logged, the fallback is never consulted). The
grinding mirror of `fsSchedule_fsDerive`: distinctness made the cells
pairwise-distinct, the `Nodup` run made each cell its own fresh coin. -/
theorem grindSchedule_eq (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    {qs : List (LcQuery Root F ι r)} (hnd : qs.Nodup)
    (hcov : ∀ k : Fin ch.length, linkPrefix A₀ ch (k : ℕ) ∈ qs)
    (c : Fin qs.length → F) (d : Fin ch.length → F) :
    fsSchedule (Oracle.ofList qs c) A₀ ch d
      = fun k => c (grindIdx A₀ ch qs hcov k) := by
  funext k
  show ((Oracle.ofList qs c).lookup (linkPrefix A₀ ch (k : ℕ))).getD (d k) = _
  rw [← grindIdx_get A₀ ch qs hcov k, Oracle.lookup_ofList hnd c _]
  rfl

/-- **Candidate count ≤ query budget**: distinct nonempty candidate chains
have distinct FULL prefixes — which are entries of the query list — so a
`t`-query grind fields at most `t` candidates. "A `t`-query adversary
genuinely has `t` tries" is this inequality; the `T` in the bounds below is
dominated by the budget `qs.length`. -/
theorem grindCandidates_le_budget {A₀ : AccClaim Root F ι r} {T : ℕ}
    {chs : Fin T → Chain Root F ι r} {qs : List (LcQuery Root F ι r)}
    (hcov : ∀ (i : Fin T) (k : Fin (chs i).length),
      linkPrefix A₀ (chs i) (k : ℕ) ∈ qs)
    (hne : ∀ i, chs i ≠ []) (hinj : Function.Injective chs) :
    T ≤ qs.length := by
  classical
  have hfull : ∀ i, (A₀, chs i) ∈ qs := by
    intro i
    have hpos : 0 < (chs i).length := List.length_pos_of_ne_nil (hne i)
    have h := hcov i ⟨(chs i).length - 1, by omega⟩
    have hlen : (chs i).length - 1 + 1 = (chs i).length := by omega
    unfold linkPrefix at h
    rw [hlen, List.take_length] at h
    exact h
  let f : Fin T → Fin qs.length := fun i =>
    ⟨(List.mem_iff_getElem.mp (hfull i)).choose,
      (List.mem_iff_getElem.mp (hfull i)).choose_spec.choose⟩
  have hf : ∀ i, qs.get (f i) = (A₀, chs i) := fun i =>
    (List.mem_iff_getElem.mp (hfull i)).choose_spec.choose_spec
  have hfinj : Function.Injective f := fun i j h => by
    apply hinj
    have hij : (A₀, chs i) = (A₀, chs j) := by rw [← hf i, ← hf j, h]
    exact congrArg Prod.snd hij
  simpa using Fintype.card_le_of_injective f hfinj

/-! ## The grinding light client: the union-bound composition -/

section Grinding

variable (foldRoot : Root → F → Root → Root)

/-- **[LC-fs-adaptive], exact-word grinding form.** A grinding adversary holds
`T` candidate chains, every candidate's transcript prefixes among its `t`
distinct oracle queries (`hcov`; `t = qs.length`), each candidate carrying an
unsatisfiable link. After the oracle answers, it submits whichever candidate
it likes — ANY selection rule is dominated by the `∃` below. Its success
probability over the shared oracle's coins is at most

  `T · 1/|F|  (≤ t · 1/|F| ≤ (t+n) · 1/|F|)`,

the fixed-chain sharp bound (`lightClientSound_exact` /
`lightClientFS_exact`, REUSED) times the number of tries: per candidate the
shared-oracle schedule is EXACTLY uniform (`grindSchedule_eq` +
`uniformProb_comp_injective`), and the union bound sums the tries. At the
exact-word level the union-bound composition already ATTAINS the
`(t + k)·ε` per-query shape of `fsKeystone_proved` (Selvage/FiatShamir.lean):
the per-try price is the PER-FOLD error `1/|F|`, not the whole-chain bound. -/
theorem lightClientGrinding_exact [Fintype F] {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {T : ℕ} {chs : Fin T → Chain Root F ι r}
    {qs : List (LcQuery Root F ι r)} (hnd : qs.Nodup)
    (hcov : ∀ (i : Fin T) (k : Fin (chs i).length),
      linkPrefix A₀ (chs i) (k : ℕ) ∈ qs)
    (halign : ∀ i, Aligned A₀ (chs i))
    (huns : ∀ i, ∃ l ∈ chs i, ¬ ∃ f, AccClaim.Satisfies C l.claim f)
    (d : (i : Fin T) → Fin (chs i).length → F) :
    uniformProb (Fin qs.length → F) (fun c => ∃ i,
        Verifies C (aggregate foldRoot
          (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
          A₀ (chs i)))
      ≤ (T : ℝ) * (1 / (Fintype.card F : ℝ)) := by
  haveI : Nonempty F := ⟨0⟩
  refine le_trans (uniformProb_exists_le fun i c =>
    Verifies C (aggregate foldRoot
      (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
      A₀ (chs i))) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (le_of_eq (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]))
  have hev : ∀ c : Fin qs.length → F,
      Verifies C (aggregate foldRoot
        (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
        A₀ (chs i))
      ↔ Verifies C (aggregate foldRoot
        (padSched (fun k => c (grindIdx A₀ (chs i) qs (hcov i) k)))
        A₀ (chs i)) := fun c => by
    rw [grindSchedule_eq A₀ (chs i) hnd (hcov i) c (d i)]
  exact le_of_eq_of_le (Eq.trans (uniformProb_congr hev)
    (uniformProb_comp_injective (grindIdx_injective A₀ (chs i) qs (hcov i))
      (fun γv => Verifies C (aggregate foldRoot (padSched γv) A₀ (chs i)))))
    (lightClientSound_exact foldRoot (halign i) (huns i))

section Proximity

variable [Fintype ι] [DecidableEq ι] [DecidableEq F]

/-- **The union-bound composition, δ-proximity form — the sharp Σ shape.** A
grinding adversary's `T` candidates, each carrying a δ-far-false link, each
fully queried; its post-answer selection (any rule — the `∃`) succeeds with
probability at most the SUM over its candidates of the fixed-chain bound

  `∑ᵢ nᵢ · (err⋆(δ) + 1/|F|)`

(`lightClientSound` / `lightClientFS_sound` per candidate — the fixed-chain
theorem REUSED verbatim through the marginal; the events stay anchored at the
honest fold of each candidate's committed words, `[ACC-extract]` unchanged).
Shared prefixes between candidates share coins — the model keeps grinding's
real correlation; the union bound never needed independence. -/
theorem lightClientGrinding_union [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {T : ℕ} {chs : Fin T → Chain Root F ι r}
    {qs : List (LcQuery Root F ι r)}
    {wss : Fin T → List (ι → F)} {f0s : Fin T → ι → F}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (hnd : qs.Nodup)
    (hcov : ∀ (i : Fin T) (k : Fin (chs i).length),
      linkPrefix A₀ (chs i) (k : ℕ) ∈ qs)
    (halign : ∀ i, Aligned A₀ (chs i))
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ)
    (hlen : ∀ i, (wss i).length = (chs i).length)
    (hfalse : ∀ i, ∃ p ∈ (chs i).zip (wss i), ∀ v ∈ C, relDist p.2 v ≤ δ →
        ¬ AccClaim.Satisfies C p.1.claim v)
    (d : (i : Fin T) → Fin (chs i).length → F) :
    uniformProb (Fin qs.length → F) (fun c => ∃ i,
        ∃ w, relDist (foldWords
            (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
            (f0s i) (wss i)) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot
            (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
            A₀ (chs i)) w)
      ≤ ∑ i : Fin T,
          ((chs i).length : ℝ)
            * (errstar δ + 1 / (Fintype.card F : ℝ)) := by
  haveI : Nonempty F := ⟨0⟩
  refine le_trans (uniformProb_exists_le fun i c =>
    ∃ w, relDist (foldWords
        (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
        (f0s i) (wss i)) w ≤ δ ∧
      AccClaim.Satisfies C (aggregate foldRoot
        (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
        A₀ (chs i)) w) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have hev : ∀ c : Fin qs.length → F,
      (∃ w, relDist (foldWords
          (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
          (f0s i) (wss i)) w ≤ δ ∧
        AccClaim.Satisfies C (aggregate foldRoot
          (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
          A₀ (chs i)) w)
      ↔ (∃ w, relDist (foldWords
          (padSched (fun k => c (grindIdx A₀ (chs i) qs (hcov i) k)))
          (f0s i) (wss i)) w ≤ δ ∧
        AccClaim.Satisfies C (aggregate foldRoot
          (padSched (fun k => c (grindIdx A₀ (chs i) qs (hcov i) k)))
          A₀ (chs i)) w) := fun c => by
    rw [grindSchedule_eq A₀ (chs i) hnd (hcov i) c (d i)]
  exact le_of_eq_of_le (Eq.trans (uniformProb_congr hev)
    (uniformProb_comp_injective (grindIdx_injective A₀ (chs i) qs (hcov i))
      (fun γv => ∃ w, relDist (foldWords (padSched γv) (f0s i) (wss i)) w ≤ δ ∧
        AccClaim.Satisfies C
          (aggregate foldRoot (padSched γv) A₀ (chs i)) w)))
    (lightClientSound foldRoot (halign i) hdC hMCA hδ0 hδB hδC herr0
      (hlen i) (hfalse i))

/-- **[LC-fs-adaptive], THE GRINDING HEADLINE — the (t+n)-scaled deployable
form.** The FS light client against a grinding adversary: `t = qs.length`
distinct oracle queries, `T` distinct nonempty candidate chains assembled
from them (so `T ≤ t`, `grindCandidates_le_budget` — a `t`-query adversary
genuinely has at most `t` tries), every candidate of length ≤ `n` carrying a
δ-far-false link, the submitted chain chosen by ANY post-answer rule (the
`∃`). Success probability at most

  `(t + n) · [ n · (err⋆(δ) + 1/|F|) ]`

— the GRINDING FACTOR `(t + n)` of WARP Thm B.4 / `fsKeystone_proved`'s
`(t + k)·ε_rbr` (Selvage/FiatShamir.lean, PROVED), here scaling the FIXED-CHAIN
bound `n·(err⋆ + 1/|F|)` of `lightClientFS_sound`: the union-bound
composition pays per-try·per-chain (`≤ T·n·ε ≤ t·n·ε ≤ (t+n)·n·ε`), whereas
the native per-round accounting pays per-query·per-fold — the `n`-sharper
`(t+n)·(err⋆ + 1/|F|)`, LANDED at the IOR resolution as `accFsSound_native`
(Selvage/AccRbrInstance.lean, `(t+k)·accRbrError` on the accumulator's own
reduction); transporting it into THIS event vocabulary is
`[LC-grinding-native]` (end of file). Nothing about the bound SHAPE is open;
the proven factor is deployable now. -/
theorem lightClientGrinding_sound [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {T : ℕ} {chs : Fin T → Chain Root F ι r}
    {qs : List (LcQuery Root F ι r)}
    {wss : Fin T → List (ι → F)} {f0s : Fin T → ι → F}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ} {n : ℕ}
    (hnd : qs.Nodup)
    (hcov : ∀ (i : Fin T) (k : Fin (chs i).length),
      linkPrefix A₀ (chs i) (k : ℕ) ∈ qs)
    (hn : ∀ i, (chs i).length ≤ n)
    (hne : ∀ i, chs i ≠ []) (hinj : Function.Injective chs)
    (halign : ∀ i, Aligned A₀ (chs i))
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ)
    (hlen : ∀ i, (wss i).length = (chs i).length)
    (hfalse : ∀ i, ∃ p ∈ (chs i).zip (wss i), ∀ v ∈ C, relDist p.2 v ≤ δ →
        ¬ AccClaim.Satisfies C p.1.claim v)
    (d : (i : Fin T) → Fin (chs i).length → F) :
    uniformProb (Fin qs.length → F) (fun c => ∃ i,
        ∃ w, relDist (foldWords
            (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
            (f0s i) (wss i)) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot
            (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
            A₀ (chs i)) w)
      ≤ ((qs.length : ℝ) + (n : ℝ))
          * ((n : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ))) := by
  have hε : 0 ≤ errstar δ + 1 / (Fintype.card F : ℝ) :=
    add_nonneg herr0 (by positivity)
  refine le_trans (lightClientGrinding_union foldRoot hnd hcov halign hdC hMCA
    hδ0 hδB hδC herr0 hlen hfalse d) ?_
  refine le_trans (le_trans (Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast hn i : ((chs i).length : ℝ) ≤ (n : ℝ)) hε)
    (le_of_eq (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]))) ?_
  have hT : (T : ℝ) ≤ (qs.length : ℝ) + (n : ℝ) := by
    have hTq : (T : ℝ) ≤ (qs.length : ℝ) := by
      exact_mod_cast grindCandidates_le_budget hcov hne hinj
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact mul_le_mul_of_nonneg_right hT (mul_nonneg (Nat.cast_nonneg _) hε)

end Proximity

end Grinding

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All BUILT, computing where decidable, over the landed F₅ chains — REUSED, not
rebuilt. The grinding adversary here is the residual's own phrase made flesh:
it REORDERS the chain after seeing the oracle's answers. Candidates: the
landed `phantomChain` and its reorder `phantomSwapChain` (same two false
links, swapped) — four distinct transcript prefixes, budget `t = 4`. Each
candidate alone forges at exactly the fixed-chain sharp bound `1/5`
(`grindFirst_verifies_iff` + the marginal — the landed diagonal, at its own
oracle cells); the GRIND forges at `9/25 > 1/5`
(`phantomGrind_forging_prob`): the fixed-chain bound alone is INSUFFICIENT
against grinding — the try-count factor is load-bearing, teeth
(`phantomGrind_beats_fixed_bound`). The general theorems fire with every
hypothesis discharged (`phantomGrind_caught_probably` at `2·(1/5) = 2/5` —
union-bound slack over the true `9/25` EXACTLY the computed overlap `1/25`;
`phantomGrind_delta_fired` at `4/5`), and both poles compute: coins
`(1,0,1,1)` catch the phantom but its REORDER forges — the post-answer
selection genuinely at work; coins `(1,0,2,1)` catch every candidate. -/

section KeystonePlumbing

/- Private mirror of Selvage/LightClientSound.lean's private keystone plumbing
(the module-private discipline: the aggregate build never sees two public
copies). -/
private theorem eq_of_relDist_le_of_lt_inv_card {ι : Type*} [Fintype ι]
    [Nonempty ι] {F : Type*} [DecidableEq F] {f u : ι → F} {δ : ℝ}
    (h : relDist f u ≤ δ) (hδ : δ < 1 / (Fintype.card ι : ℝ)) : f = u := by
  by_contra hne
  exact absurd (le_trans (one_div_card_le_relDist hne) h) (not_le.mpr hδ)

end KeystonePlumbing

namespace LCGrindExample

open RSExample AccExample LCExample LCSoundExample

/-- **The reordered phantom** — the grinding adversary's second candidate:
the SAME two individually-false links, swapped. Assembled from the same claim
material; only the order (and hence the transcript prefixes, and hence the
derived schedule) differs. -/
def phantomSwapChain : Chain (ZMod 5) (ZMod 5) (Fin 4) 1 :=
  [⟨1, 2, phantomClaim₁⟩, ⟨0, 1, phantomClaim₀⟩]

theorem phantomSwapChain_aligned :
    Aligned phantomGenesis phantomSwapChain := by
  intro l hl i
  rcases List.mem_cons.mp hl with rfl | hl
  · rfl
  · rcases List.mem_cons.mp hl with rfl | hl
    · rfl
    · simp at hl

/-- The reorder's forging set is ALSO the diagonal — in its OWN challenges:
`γ₀·4 + γ₁·1 = 0` in `F₅` iff `γ₀ = γ₁`. Same set shape, different oracle
cells: that separation is exactly what the grind exploits. -/
theorem phantomSwap_verifies_iff (γv : Fin 2 → ZMod 5) :
    Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot (padSched γv) phantomGenesis phantomSwapChain)
    ↔ γv 0 = γv 1 := by
  have key : ∀ a b : ZMod 5, ((0 : ZMod 5) = 0 + a * 4 + b * 1 ↔ a = b) := by
    decide
  constructor
  · rintro ⟨fw, -, hc⟩
    exact (key (γv 0) (γv 1)).mp (hc 0)
  · intro h
    refine ⟨0, Submodule.zero_mem _, fun i => ?_⟩
    show (0 : ZMod 5) = 0 + γv 0 * 4 + γv 1 * 1
    rw [h]
    exact (by decide : ∀ b : ZMod 5, (0 : ZMod 5) = 0 + b * 4 + b * 1) (γv 1)

/-- The grinding pair: the phantom and its reorder. -/
def grindChs : Fin 2 → Chain (ZMod 5) (ZMod 5) (Fin 4) 1 :=
  ![phantomChain, phantomSwapChain]

/-- The adversary's query run: both candidates' transcript prefixes — four
distinct oracle cells, budget `t = 4`. -/
def grindQs : List (LcQuery (ZMod 5) (ZMod 5) (Fin 4) 1) :=
  [linkPrefix phantomGenesis phantomChain 0,
   linkPrefix phantomGenesis phantomChain 1,
   linkPrefix phantomGenesis phantomSwapChain 0,
   linkPrefix phantomGenesis phantomSwapChain 1]

/- The four prefixes are pairwise distinct: lengths separate rounds
(`1 ≠ 2`), head pre-roots separate the candidates (`0 ≠ 1` — the reorder
changes the FIRST link, so every prefix moves). Claims carry linear maps, so
plain `decide` on `LcQuery` equality is unavailable; each disequality
projects to a decidable component first. -/

private theorem ne01 : linkPrefix phantomGenesis phantomChain 0
    ≠ linkPrefix phantomGenesis phantomChain 1 := fun h =>
  absurd (congrArg
    (fun q : LcQuery (ZMod 5) (ZMod 5) (Fin 4) 1 => q.2.length) h) (by decide)

private theorem ne02 : linkPrefix phantomGenesis phantomChain 0
    ≠ linkPrefix phantomGenesis phantomSwapChain 0 := fun h =>
  absurd (congrArg
    (fun q : LcQuery (ZMod 5) (ZMod 5) (Fin 4) 1 =>
      (q.2.map Link.pre).head?) h) (by decide)

private theorem ne03 : linkPrefix phantomGenesis phantomChain 0
    ≠ linkPrefix phantomGenesis phantomSwapChain 1 := fun h =>
  absurd (congrArg
    (fun q : LcQuery (ZMod 5) (ZMod 5) (Fin 4) 1 => q.2.length) h) (by decide)

private theorem ne12 : linkPrefix phantomGenesis phantomChain 1
    ≠ linkPrefix phantomGenesis phantomSwapChain 0 := fun h =>
  absurd (congrArg
    (fun q : LcQuery (ZMod 5) (ZMod 5) (Fin 4) 1 => q.2.length) h) (by decide)

private theorem ne13 : linkPrefix phantomGenesis phantomChain 1
    ≠ linkPrefix phantomGenesis phantomSwapChain 1 := fun h =>
  absurd (congrArg
    (fun q : LcQuery (ZMod 5) (ZMod 5) (Fin 4) 1 =>
      (q.2.map Link.pre).head?) h) (by decide)

private theorem ne23 : linkPrefix phantomGenesis phantomSwapChain 0
    ≠ linkPrefix phantomGenesis phantomSwapChain 1 := fun h =>
  absurd (congrArg
    (fun q : LcQuery (ZMod 5) (ZMod 5) (Fin 4) 1 => q.2.length) h) (by decide)

/-- The query run is duplicate-free — each cell draws its own fresh coin. -/
theorem grindQs_nodup : grindQs.Nodup := by
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
    List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩⟩
  · intro hmem
    rcases List.mem_cons.mp hmem with h | hmem
    · exact ne01 h
    rcases List.mem_cons.mp hmem with h | hmem
    · exact ne02 h
    rcases List.mem_cons.mp hmem with h | hmem
    · exact ne03 h
    · simp at hmem
  · intro hmem
    rcases List.mem_cons.mp hmem with h | hmem
    · exact ne12 h
    rcases List.mem_cons.mp hmem with h | hmem
    · exact ne13 h
    · simp at hmem
  · intro hmem
    rcases List.mem_cons.mp hmem with h | hmem
    · exact ne23 h
    · simp at hmem

/-- Every candidate prefix was queried — the adversary ground over BOTH
orders before choosing. -/
theorem grindChs_cover : ∀ (i : Fin 2) (k : Fin ((grindChs i)).length),
    linkPrefix phantomGenesis (grindChs i) (k : ℕ) ∈ grindQs := by
  intro i k
  fin_cases i <;> fin_cases k
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- Candidate 1's verdict in coin space: the phantom forges iff the shared
oracle's cells 0 and 1 agree — the landed diagonal, at ITS prefixes. -/
theorem grindFirst_verifies_iff (d₀ : Fin 2 → ZMod 5)
    (c : Fin 4 → ZMod 5) :
    Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot
        (padSched (fsSchedule (Oracle.ofList grindQs c) phantomGenesis
          phantomChain d₀))
        phantomGenesis phantomChain)
    ↔ c 0 = c 1 := by
  have hs : fsSchedule (Oracle.ofList grindQs c) phantomGenesis
      phantomChain d₀ = ![c 0, c 1] := by
    funext k
    fin_cases k
    · show ((Oracle.ofList grindQs c).lookup
          (linkPrefix phantomGenesis phantomChain 0)).getD _ = _
      rw [show linkPrefix phantomGenesis phantomChain 0
          = grindQs.get ⟨0, by decide⟩ from rfl,
        Oracle.lookup_ofList grindQs_nodup]
      rfl
    · show ((Oracle.ofList grindQs c).lookup
          (linkPrefix phantomGenesis phantomChain 1)).getD _ = _
      rw [show linkPrefix phantomGenesis phantomChain 1
          = grindQs.get ⟨1, by decide⟩ from rfl,
        Oracle.lookup_ofList grindQs_nodup]
      rfl
  rw [hs]
  exact (phantom_verifies_iff _).trans (by simp)

/-- Candidate 2's verdict in coin space: the REORDER forges iff cells 2 and 3
agree — its OWN diagonal, at its own prefixes. Reordering moved every
prefix, so the two candidates' verdicts live on disjoint oracle cells. -/
theorem grindSwap_verifies_iff (d₁ : Fin 2 → ZMod 5)
    (c : Fin 4 → ZMod 5) :
    Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot
        (padSched (fsSchedule (Oracle.ofList grindQs c) phantomGenesis
          phantomSwapChain d₁))
        phantomGenesis phantomSwapChain)
    ↔ c 2 = c 3 := by
  have hs : fsSchedule (Oracle.ofList grindQs c) phantomGenesis
      phantomSwapChain d₁ = ![c 2, c 3] := by
    funext k
    fin_cases k
    · show ((Oracle.ofList grindQs c).lookup
          (linkPrefix phantomGenesis phantomSwapChain 0)).getD _ = _
      rw [show linkPrefix phantomGenesis phantomSwapChain 0
          = grindQs.get ⟨2, by decide⟩ from rfl,
        Oracle.lookup_ofList grindQs_nodup]
      rfl
    · show ((Oracle.ofList grindQs c).lookup
          (linkPrefix phantomGenesis phantomSwapChain 1)).getD _ = _
      rw [show linkPrefix phantomGenesis phantomSwapChain 1
          = grindQs.get ⟨3, by decide⟩ from rfl,
        Oracle.lookup_ofList grindQs_nodup]
      rfl
  rw [hs]
  exact (phantomSwap_verifies_iff _).trans (by simp)

/-- **The grind's forging set, closed form**: the best-of-both submission
forges iff EITHER candidate's diagonal fires — `c₀ = c₁ ∨ c₂ = c₃` over the
shared oracle's four cells. The `∃` IS the post-answer selection. -/
theorem phantomGrind_verifies_iff
    (d : (i : Fin 2) → Fin ((grindChs i)).length → ZMod 5)
    (c : Fin 4 → ZMod 5) :
    (∃ i, Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot
        (padSched (fsSchedule (Oracle.ofList grindQs c) phantomGenesis
          (grindChs i) (d i)))
        phantomGenesis (grindChs i)))
    ↔ (c 0 = c 1 ∨ c 2 = c 3) := by
  rw [Fin.exists_fin_two]
  exact or_congr (grindFirst_verifies_iff (d 0) c)
    (grindSwap_verifies_iff (d 1) c)

/-- The single-candidate diagonal's probability — the landed `1/5`
(`phantom_forging_prob` read back through `phantom_verifies_iff`). -/
private theorem diag_prob :
    uniformProb (Fin 2 → ZMod 5) (fun γv => γv 0 = γv 1) = 1 / 5 :=
  (uniformProb_congr fun γv => (phantom_verifies_iff γv).symm).trans
    phantom_forging_prob

private def emb01 : Fin 2 → Fin 4 := ![0, 1]

private def emb23 : Fin 2 → Fin 4 := ![2, 3]

private theorem emb01_inj : Function.Injective emb01 := by decide

private theorem emb23_inj : Function.Injective emb23 := by decide

/-- **Each single try pays exactly the fixed-chain price**: candidate 1's
marginal forging probability under the SHARED oracle is `1/5 = 1/|F₅|` — the
sharp fixed-chain bound, attained, through the injection marginal (the
transfer exercised concretely). -/
theorem grindFirst_marginal_prob :
    uniformProb (Fin 4 → ZMod 5) (fun c => c 0 = c 1) = 1 / 5 :=
  (uniformProb_comp_injective emb01_inj
    (fun γv : Fin 2 → ZMod 5 => γv 0 = γv 1)).trans diag_prob

theorem grindSwap_marginal_prob :
    uniformProb (Fin 4 → ZMod 5) (fun c => c 2 = c 3) = 1 / 5 :=
  (uniformProb_comp_injective emb23_inj
    (fun γv : Fin 2 → ZMod 5 => γv 0 = γv 1)).trans diag_prob

/-- The overlap — BOTH diagonals fire — counted exactly: `1/25`. Disjoint
cells make the candidates independent; this is the union bound's whole
slack, computed. -/
private def andSubtypeEquiv :
    {c : Fin 4 → ZMod 5 // c 0 = c 1 ∧ c 2 = c 3} ≃ ZMod 5 × ZMod 5 where
  toFun x := (x.1 0, x.1 2)
  invFun y := ⟨![y.1, y.1, y.2, y.2], by constructor <;> rfl⟩
  left_inv x := Subtype.ext (funext fun j => by
    fin_cases j
    · rfl
    · exact x.2.1
    · rfl
    · exact x.2.2)
  right_inv y := rfl

private theorem and_prob :
    uniformProb (Fin 4 → ZMod 5) (fun c => c 0 = c 1 ∧ c 2 = c 3)
      = 1 / 25 := by
  unfold uniformProb
  rw [Nat.card_congr andSubtypeEquiv, Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

/-- **The grind's forging probability, EXACT**: `9/25` — inclusion–exclusion
over the two diagonals, `1/5 + 1/5 − 1/25`. Two tries genuinely stack: the
grind beats every single candidate's `1/5`, and undershoots the union
bound's `2/5` by exactly the computed overlap. -/
theorem phantomGrind_forging_prob
    (d : (i : Fin 2) → Fin ((grindChs i)).length → ZMod 5) :
    uniformProb (Fin 4 → ZMod 5) (fun c => ∃ i,
        Verifies (reedSolomonCode dom₅ 2)
          (aggregate linRoot
            (padSched (fsSchedule (Oracle.ofList grindQs c) phantomGenesis
              (grindChs i) (d i)))
            phantomGenesis (grindChs i)))
      = 9 / 25 := by
  rw [uniformProb_congr (fun c => phantomGrind_verifies_iff d c),
    uniformProb_or_eq, grindFirst_marginal_prob, grindSwap_marginal_prob,
    and_prob]
  norm_num

/-- **Teeth — the grinding factor is load-bearing.** The grind's success
`9/25` STRICTLY EXCEEDS the fixed-chain sharp bound `1/|F₅| = 1/5` — which
each candidate alone attains (`grindFirst_marginal_prob`). No bound of the
fixed-chain form (no try-count factor) can hold against a grinding
adversary; the `T`/`(t+n)` scaling in the theorems above is necessary, not
bookkeeping. -/
theorem phantomGrind_beats_fixed_bound
    (d : (i : Fin 2) → Fin ((grindChs i)).length → ZMod 5) :
    1 / (Fintype.card (ZMod 5) : ℝ)
      < uniformProb (Fin 4 → ZMod 5) (fun c => ∃ i,
          Verifies (reedSolomonCode dom₅ 2)
            (aggregate linRoot
              (padSched (fsSchedule (Oracle.ofList grindQs c) phantomGenesis
                (grindChs i) (d i)))
              phantomGenesis (grindChs i))) := by
  rw [phantomGrind_forging_prob d, ZMod.card]
  norm_num

/-- **Premise inhabitation — the exact grinding theorem FIRES**:
`lightClientGrinding_exact` applied to the landed pair, every hypothesis
discharged by built witnesses (`Nodup` run, full cover, alignment, an
unsatisfiable link per candidate), bound `T·(1/|F|) = 2/5` — honest against
the true `9/25`, the union-bound slack exactly the computed overlap
`1/25`. -/
theorem phantomGrind_caught_probably
    (d : (i : Fin 2) → Fin ((grindChs i)).length → ZMod 5) :
    uniformProb (Fin 4 → ZMod 5) (fun c => ∃ i,
        Verifies (reedSolomonCode dom₅ 2)
          (aggregate linRoot
            (padSched (fsSchedule (Oracle.ofList grindQs c) phantomGenesis
              (grindChs i) (d i)))
            phantomGenesis (grindChs i)))
      ≤ 2 / 5 := by
  have h := lightClientGrinding_exact linRoot grindQs_nodup grindChs_cover
    (fun i => by
      fin_cases i
      · exact phantomChain_aligned
      · exact phantomSwapChain_aligned)
    (fun i => by
      fin_cases i
      · exact ⟨⟨0, 1, phantomClaim₀⟩, List.mem_cons_self ..,
          phantomClaim₀_unsatisfiable⟩
      · exact ⟨⟨0, 1, phantomClaim₀⟩,
          List.mem_cons_of_mem _ (List.mem_cons_self ..),
          phantomClaim₀_unsatisfiable⟩)
    d
  have h25 : ((2 : ℕ) : ℝ) * (1 / ((5 : ℕ) : ℝ)) = 2 / 5 := by norm_num
  rw [← h25]
  simpa [ZMod.card] using h

/-- Coins `(1,0,1,1)`: the phantom itself is CAUGHT (`c₀ ≠ c₁`) — but its
REORDER forges (`c₂ = c₃`), and the grinding adversary submits THAT one. The
post-answer selection is genuinely at work: pole 1. -/
example (d : (i : Fin 2) → Fin ((grindChs i)).length → ZMod 5) :
    ∃ i, Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot
        (padSched (fsSchedule (Oracle.ofList grindQs ![1, 0, 1, 1])
          phantomGenesis (grindChs i) (d i)))
        phantomGenesis (grindChs i)) :=
  (phantomGrind_verifies_iff d ![1, 0, 1, 1]).mpr (Or.inr (by decide))

/-- …and at the same coins, candidate 1 ALONE fails — without the reorder in
hand, the adversary loses this throw. -/
example (d₀ : Fin 2 → ZMod 5) :
    ¬ Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot
        (padSched (fsSchedule (Oracle.ofList grindQs ![1, 0, 1, 1])
          phantomGenesis phantomChain d₀))
        phantomGenesis phantomChain) := fun h =>
  absurd ((grindFirst_verifies_iff d₀ ![1, 0, 1, 1]).mp h) (by decide)

/-- Coins `(1,0,2,1)`: EVERY candidate is caught — the whole grind fails:
pole 2. The verdict is the oracle's doing at every cell. -/
example (d : (i : Fin 2) → Fin ((grindChs i)).length → ZMod 5) :
    ¬ ∃ i, Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot
        (padSched (fsSchedule (Oracle.ofList grindQs ![1, 0, 2, 1])
          phantomGenesis (grindChs i) (d i)))
        phantomGenesis (grindChs i)) := fun h => by
  rcases (phantomGrind_verifies_iff d ![1, 0, 2, 1]).mp h with hc | hc <;>
    exact absurd hc (by decide)

/-- **The budget inequality fires**: two distinct nonempty candidates, four
queries — `T = 2 ≤ 4 = t` (`grindCandidates_le_budget`, every hypothesis
discharged). -/
example : (2 : ℕ) ≤ grindQs.length := by
  have hswap : phantomChain ≠ phantomSwapChain := fun h =>
    absurd (congrArg
      (fun ch : Chain (ZMod 5) (ZMod 5) (Fin 4) 1 =>
        (ch.map Link.pre).head?) h) (by decide)
  refine grindCandidates_le_budget grindChs_cover
    (fun i => by fin_cases i <;> simp [grindChs, phantomChain, phantomSwapChain])
    ?_
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij hswap
  · exact absurd hij.symm hswap
  · rfl

/-- **Premise inhabitation, δ-form — the union theorem FIRES**: over `C = ⊤`
(mutual CA with `err⋆ = 0` from the landed
`hasMutualCorrelatedAgreement_top_affine`, `dC = 1/4` from
`minDistLB_inhabited`), both candidates' committed zero words carry a
δ-far-false link at `δ = 1/16`, and the grind's δ-proximity event is bounded
by `∑ᵢ 2·(err⋆ + 1/5) = 4/5` — every hypothesis of
`lightClientGrinding_union` discharged by landed witnesses, the bound
non-vacuous. (The `(t+n)`-scaled headline evaluates to `6·(2/5) = 12/5 > 1`
on this deliberately tiny field — the grinding factor prices the deployment
regime `|F| ≫ t·n`; the F₅ keystones exercise the sharp forms.) -/
theorem phantomGrind_delta_fired
    (d : (i : Fin 2) → Fin ((grindChs i)).length → ZMod 5) :
    uniformProb (Fin 4 → ZMod 5) (fun c => ∃ i,
        ∃ w, relDist (foldWords
            (padSched (fsSchedule (Oracle.ofList grindQs c) phantomGenesis
              (grindChs i) (d i)))
            0 [0, 0]) w ≤ 1 / 16 ∧
          AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
            (aggregate linRoot
              (padSched (fsSchedule (Oracle.ofList grindQs c) phantomGenesis
                (grindChs i) (d i)))
              phantomGenesis (grindChs i)) w)
      ≤ 4 / 5 := by
  have hmax : max (1 - 1 / (Fintype.card (Fin 4) : ℝ) / 2) 0 = 7 / 8 := by
    rw [Fintype.card_fin, max_eq_left (by norm_num)]
    norm_num
  have h := lightClientGrinding_union linRoot
    (wss := fun _ => [0, 0]) (f0s := fun _ => 0) (δ := 1 / 16)
    grindQs_nodup grindChs_cover
    (fun i => by
      fin_cases i
      · exact phantomChain_aligned
      · exact phantomSwapChain_aligned)
    (minDistLB_inhabited _) hasMutualCorrelatedAgreement_top_affine
    (by norm_num) (by rw [hmax]; norm_num) (by norm_num [Fintype.card_fin])
    (le_refl 0) (fun i => by fin_cases i <;> rfl)
    (fun i => by
      fin_cases i
      · exact ⟨(⟨0, 1, phantomClaim₀⟩, 0), List.mem_cons_self ..,
          fun v _ hclose => by
            rintro ⟨-, hc⟩
            have h0v : (0 : Fin 4 → ZMod 5) = v :=
              eq_of_relDist_le_of_lt_inv_card hclose
                (by norm_num [Fintype.card_fin])
            have h1 := hc 0
            rw [← h0v] at h1
            exact absurd h1 (by decide)⟩
      · exact ⟨(⟨1, 2, phantomClaim₁⟩, 0), List.mem_cons_self ..,
          fun v _ hclose => by
            rintro ⟨-, hc⟩
            have h0v : (0 : Fin 4 → ZMod 5) = v :=
              eq_of_relDist_le_of_lt_inv_card hclose
                (by norm_num [Fintype.card_fin])
            have h1 := hc 0
            rw [← h0v] at h1
            exact absurd h1 (by decide)⟩)
    d
  refine le_trans h (le_of_eq ?_)
  rw [Fin.sum_univ_two]
  show ((phantomChain.length : ℝ)) * (0 + 1 / ((5 : ℕ) : ℝ))
      + ((phantomSwapChain.length : ℝ)) * (0 + 1 / ((5 : ℕ) : ℝ)) = 4 / 5
  norm_num [phantomChain, phantomSwapChain]

end LCGrindExample

/-! ## Ledger, and what remains of [LC-fs-adaptive] (honest residuals, prose)

**Closed here** (no `sorry`; axioms: `propext`, `Classical.choice`,
`Quot.sound` only — checked on every headline):

* **The honest grinding model.** One shared lazy-sampling handler over the
  adversary's whole query run (`Oracle.ofList`; the fold laws
  `Oracle.lookup_foldl_respond` REUSED from Selvage/LightClientFS.lean), every
  candidate's schedule read from the SAME oracle — candidates sharing a
  prefix share its challenge. The post-answer chain selection is the `∃`
  (any selection rule is dominated by it), and the try-count is tied to the
  query budget: `grindCandidates_le_budget` (`T ≤ t` — distinct nonempty
  candidates have distinct full prefixes, which are queries).
* **The transfer.** `grindSchedule_eq` + `uniformProb_comp_injective`
  (+ `injSplit`): a fully-queried candidate's schedule is the pullback of
  the shared coins along an injection, hence distributed EXACTLY uniformly —
  the grinding mirror of `fsSchedule_uniform`. The fixed-chain theorems
  (`lightClientSound`, `lightClientSound_exact` — the same engines
  `lightClientFS_sound`/`lightClientFS_exact` transport to FS form) price
  every try VERBATIM, cited not re-derived.
* **The composition.** The union bound over tries (`uniformProb_exists_le`,
  Depth's toolkit, REUSED): `lightClientGrinding_exact` (`T·1/|F|`),
  `lightClientGrinding_union` (`∑ᵢ nᵢ·(err⋆(δ)+1/|F|)`, sharp Σ form),
  `lightClientGrinding_sound` (`(t+n)·[n·(err⋆(δ)+1/|F|)]`, the deployable
  (t+n)-scaled headline). `[LC-fs-adaptive]` is closed at THIS level: the
  grinding adversary's factor is proved, the fixed-chain bound composes,
  and the numbers on the label are theorems.

**Remaining, named, with realizers:**

* **[LC-grinding-native]** — two sharpenings, both supplied by the native
  route, one transport short of this file's vocabulary:
  (a) the `n`-sharper bound `(t+n)·(err⋆(δ) + 1/|F|)` — per-QUERY·per-FOLD
  accounting where this file's union bound pays per-TRY·per-CHAIN (at the
  exact-word level the gap already closes: `lightClientGrinding_exact`'s
  `T·1/|F| ≤ (t+n)·1/|F|` has the native shape); and (b) full QUERY
  adaptivity — here the grind SET is committed before the coins sample (the
  submission choice is fully post-hoc via the `∃`, but answer-dependent
  query GENERATION is not modeled). The RBR ENGINE for both LANDED in
  `Selvage/AccRbrInstance.lean` while this file was written:
  `accReduction`/`accRbrKnowledgeSound` (the WARP-Def-4.2-native quadruple
  for the accumulator chain, `err = accRbrError`, PROVED via `accSound_rbr`
  cited) and `accFsSound_native` — `fsKeystone_proved`/`FsOfRbrSound`
  (Selvage/FiatShamir.lean, PROVED, unconditional) fired on the native pair at
  `(t+k)·accRbrError`, `k = ch.length = n`, adaptive over every `SrProver`
  strategy. What `[LC-grinding-native]` still names is the TRANSPORT: the
  SR-game statement speaks the reduction's transcript vocabulary
  (`SrMove` salted prefixes, `RelaxedMem` on the target relation); this
  file's events speak the light client's (`LcQuery` transcript prefixes,
  `Verifies ∘ aggregate` over the shared handler). Identifying the two
  games — the light-client mirror of `fsStraightline_iff_sr`'s BCS bridge —
  is the remaining lemma, and it inherits `[ACC-rbr-bcs]`
  (Selvage/AccRbrInstance.lean: the deployed root-and-columns message
  alphabet) for the deployed transcript. Nothing about the bound SHAPE is
  open — only this identification.
* **[FS-ROM]** (inherited, Selvage/FiatShamir.lean) — the deployed hash
  realizing the lazy-sampling handler is the one named idealization; domain
  separation of `LcQuery` from the stack's other oracle uses is priced
  there.
* **[ACC-extract]** (unchanged, Selvage/Accumulator.lean) — the δ-events here
  anchor at the honest fold of each candidate's committed words
  (`foldWords`); binding a forging prover's recommitments to that fold is
  the erasure-extraction obligation.

**Audit notes (is the grinding bound genuine, non-vacuous?).**
* The MODEL is the deployed experiment: one oracle, each cell logged once
  (`Oracle.ofList` + `Nodup`), candidates sharing a prefix share its
  challenge. NO independence is assumed anywhere — the union bound never
  needs it. The F₅ keystone's two candidates happen to occupy disjoint
  cells, and their independence is COMPUTED (`and_prob` = `1/25`), not
  assumed.
* The try-count factor is LOAD-BEARING, exhibited: each candidate alone
  pays exactly the fixed-chain sharp bound `1/5`
  (`grindFirst_marginal_prob` — the bound ATTAINED through the marginal),
  while the two-candidate grind pays `9/25 > 1/5`
  (`phantomGrind_forging_prob`, EXACT). So no bound of the fixed-chain form
  — no factor scaling with the tries — can hold against grinding:
  `phantomGrind_beats_fixed_bound`. This is precisely why
  `lightClientFS_sound` needed the fixed-before-sampling hypothesis.
* The bounds are honest with the slack visible: claimed `2/5` vs true
  `9/25` — the union-bound slack IS the computed inclusion–exclusion
  overlap `1/25`. The δ union form fires at `4/5 < 1` (non-vacuous, every
  hypothesis discharged by landed witnesses); the (t+n)-scaled headline
  evaluates `> 1` on F₅ — the tiny keystone field prices it vacuous, said
  plainly: the grinding factor is for the deployment regime `|F| ≫ t·n`,
  and the F₅ keystones exercise the sharp forms instead.
* The fallbacks `d i` are universally quantified everywhere — every
  candidate prefix is logged, so no conclusion leans on the lazy default.
* The `∃ i` dominates every post-answer submission rule, so the theorems
  price ALL of them; what they do not price is the query-generation
  adaptivity named in `[LC-grinding-native]`. -/

end Minidregg.Selvage
