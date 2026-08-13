/-
# Selvage.LightClient — the whole-history aggregation object and its attestation.

THE v0 MILESTONE APEX (docs/SELVAGE-RECOMPOSITION.md §1/§6, docs/HYPEREDGE-DESIGN.md
§4): a verifier checking ONE aggregate accumulated claim learns that every link
of the history is a well-formed accumulated claim, executed IN ORDER. A history
is a chain of links; each link carries an `AccClaim` (`Selvage/Accumulator.lean`)
plus the SEAM binding it to its predecessor — `post-root i = pre-root (i+1)`,
the chain seam of HYPEREDGE-DESIGN §4 ("including the chain seam … as an
accumulated claim") — and the aggregate is the γ-fold of the chain: `foldClaims`
iterated link by link, exactly WARP's accumulation loop (the accumulator
REPLACES the PCS opening at every link; the folding PCS appears once, at the
final compression the light client pays — LOOM §1).

**The light-client property (WARP/Arc):** the seam pins step `i`'s post-root to
step `i+1`'s pre-root, so a reordered or tampered chain forces the binding
false — no seam, no attestation, and the anti-tamper teeth below exhibit it on
BUILT chains. What this file PROVES, and what it does not:

* **Proved — completeness/closure** (`aggregate_satisfies`,
  `lightClient_complete`): the aggregate of an honestly-witnessed aligned chain
  is a satisfied CRS claim, with the folded word BUILT (`foldWords`) — the
  closure `foldClaims_satisfies` iterated along the history.
* **Proved — the derandomized attestation** (`lightClient_attests`): if the
  aggregate verifies at EVERY challenge schedule (and the seam checks), then
  every link's claim is genuinely satisfiable — `attests`. This is the
  exact-word skeleton of the light-client theorem: at nonzero challenges the
  fold algebra is invertible, so per-link witnesses are recovered by
  SUBTRACTION (`links_satisfiable_of_verifies` — the algebraic shadow of WARP's
  backwards extractor, which also peels the chain from the back).
* **Refuted — the naive one-shot form** (`LCExample.oneShot_lightClient_false`):
  at a SINGLE fixed challenge schedule the implication is FALSE — a built
  phantom chain of two individually-UNSATISFIABLE claims folds, at the rigged
  schedule, to a verifying aggregate (the γ-cancellation event whose
  probability `[ACC-sound]` bounds). Machine-checked, Depth.lean-style: the
  statement one would naively want is false as stated, and the TRUE one-shot
  statement is probabilistic — that is `[LC-sound]` below, not a theorem here.
* **Residual `[LC-sound]`** (prose, end of file): the straightline SOUNDNESS —
  a prover cannot forge a verifying aggregate for a false chain except with
  RBR probability — rides the extraction tower: WARP's straightline erasure
  extraction (`[ACC-extract]`), the per-fold challenge bound (`[ACC-sound]`,
  `(t−1)ℓ/|F|` per link), and Thm B.4 depth composition — the tower PROVED in
  `Selvage/Depth.lean` modulo its one named seam `[OB-2a]`. NOT imported here
  (statement-level file); cited, never re-derived.

**Transcription notes:**

* **The seam is an explicit decidable side-check at this level.** In the full
  receipt encoding the seam equalities are THEMSELVES accumulated claims riding
  the fold (HYPEREDGE §4; routed to the GBF public side where possible —
  LOOM §3 [OB-3′]), so the light client checks one object. Here `SeamOk` is
  carried as chain wellformedness the light client decides directly (it is
  `Decidable` — root equalities along the chain, the cheap part); its
  MIGRATION into the constraint channel is `[OB-3′]`'s receipt-encoding work
  (`docs/OB3-RECEIPT-ENCODING.md`), not this file's.
* **One root space.** Pre/post state roots and the word commitment `rt` live in
  the same opaque `Root` (HYPEREDGE §4: one commitment scheme). That a link's
  committed word BINDS its pre/post roots is receipt-encoding + commitment
  obligation (`[OB-3′]`, `[ACC-extract]`); the fold algebra never inspects
  roots, so the seam here relates carried data, exactly as the encoding will.
* **Challenge schedules, not single challenges.** `aggregate` folds link `k` at
  `γs k` (a stream — WARP samples fresh γ per accumulation step, σ before γ).
  The γ-power ladder of WHIR's flat form is the schedule `powSched γ`
  (`foldClaims_chain_target` is its length-3 instance). The derandomized
  hypothesis "verifies at EVERY schedule" is what replaces "verifies at one
  RANDOM schedule except with `[ACC-sound]` probability" until `[LC-sound]`
  lands; `oneShot_lightClient_false` machine-checks that the quantifier is
  load-bearing.
* **Alignment (`Aligned`) is the post-alignment state** of the shared
  functional channel (`hshare` of `foldClaims_satisfies`; Accumulator module
  header): WARP aligns all inputs to a fresh common point before folding, so
  every chain link presents constraints against the accumulator's functionals.
-/
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Forall2
import Selvage.Accumulator

namespace Minidregg.Selvage

variable {Root : Type*} {F : Type*} [Field F] {ι : Type*} {r : ℕ}

/-! ## Links, chains, and the seam -/

/-- **A history link**: one step's accumulated claim (`Selvage/Accumulator.lean`)
plus the seam data binding it into the history — the pre-state and post-state
roots of HYPEREDGE-DESIGN §4's committed turn. The claim's word encodes
(body, Q, seam) in the full receipt encoding; here the roots are carried
opaquely and the seam relates them chain-wise. -/
structure Link (Root : Type*) (F : Type*) [Field F] (ι : Type*) (r : ℕ) where
  /-- The pre-state root this step claims to start from. -/
  pre : Root
  /-- The post-state root this step claims to produce. -/
  post : Root
  /-- The step's accumulated claim (WARP's `acc.𝕩` shape). -/
  claim : AccClaim Root F ι r

/-- A history: the chain of links, oldest first. -/
abbrev Chain (Root : Type*) (F : Type*) [Field F] (ι : Type*) (r : ℕ) :=
  List (Link Root F ι r)

/-- **The chain seam** (HYPEREDGE-DESIGN §4, LOOM §3 [OB-3′]): every
consecutive pair of links agrees `post-root i = pre-root (i+1)`. This is the
wellformedness that pins ORDER: a reordered or spliced history breaks some
consecutive equality. -/
def SeamOk (ch : Chain Root F ι r) : Prop :=
  List.IsChain (fun a b => a.post = b.pre) ch

/-- The seam is CHECKABLE: root equality along the chain is decidable — the
cheap side-check the v0 light client runs beside the aggregate. -/
instance [DecidableEq Root] (ch : Chain Root F ι r) : Decidable (SeamOk ch) :=
  haveI : DecidableRel fun a b : Link Root F ι r => a.post = b.pre :=
    fun _ _ => inferInstance
  inferInstanceAs (Decidable (List.IsChain _ ch))

@[simp] theorem seamOk_nil : SeamOk ([] : Chain Root F ι r) := .nil

@[simp] theorem seamOk_singleton (l : Link Root F ι r) : SeamOk [l] :=
  .singleton l

theorem seamOk_cons_cons {a b : Link Root F ι r} {ch : Chain Root F ι r} :
    SeamOk (a :: b :: ch) ↔ a.post = b.pre ∧ SeamOk (b :: ch) :=
  List.isChain_cons_cons

/-- **The anti-tamper tooth, general form**: ONE broken seam anywhere in the
history — `a.post ≠ b.pre` at any consecutive pair — refutes `SeamOk` for the
whole chain. Tampering with a single link's roots, or splicing links out of
order, is caught by the binding it breaks. -/
theorem not_seamOk_of_broken (ch₁ ch₂ : Chain Root F ι r)
    {a b : Link Root F ι r} (h : a.post ≠ b.pre) :
    ¬ SeamOk (ch₁ ++ a :: b :: ch₂) := fun hs =>
  h (List.isChain_append_cons_cons.mp hs).2.1

/-! ## The aggregate: the γ-fold composed along the history -/

section Aggregate

/- The prover's recommitment schedule, as in `Selvage/Accumulator.lean`: opaque —
binding is the commitment layer's obligation, consumed by `[ACC-extract]`. -/
variable (foldRoot : Root → F → Root → Root)

/-- **The whole-history aggregation object**: the running accumulator after
folding every link's claim, link `k` at challenge `γs k` — `foldClaims`
(WHIR Constr. 7.4 / WARP's accumulation step) composed along the chain,
starting from the genesis accumulator `A₀`. REUSES the one pairwise fold;
nothing re-derived. This single claim (plus the seam check) is what the light
client hands to the one decider pass. -/
def aggregate (γs : ℕ → F) (A₀ : AccClaim Root F ι r) :
    Chain Root F ι r → AccClaim Root F ι r
  | [] => A₀
  | l :: ls =>
      aggregate (fun k => γs (k + 1)) (foldClaims foldRoot A₀ l.claim (γs 0)) ls

@[simp] theorem aggregate_nil (γs : ℕ → F) (A₀ : AccClaim Root F ι r) :
    aggregate foldRoot γs A₀ [] = A₀ := rfl

@[simp] theorem aggregate_cons (γs : ℕ → F) (A₀ : AccClaim Root F ι r)
    (l : Link Root F ι r) (ls : Chain Root F ι r) :
    aggregate foldRoot γs A₀ (l :: ls)
      = aggregate foldRoot (fun k => γs (k + 1))
          (foldClaims foldRoot A₀ l.claim (γs 0)) ls := rfl

omit [Field F] in
/-- Prepend a challenge to a schedule (the stream-cons the chain recursion
peels). -/
def consSched (c : F) (γs : ℕ → F) : ℕ → F
  | 0 => c
  | k + 1 => γs k

omit [Field F] in
@[simp] theorem consSched_zero (c : F) (γs : ℕ → F) : consSched c γs 0 = c :=
  rfl

omit [Field F] in
@[simp] theorem consSched_succ (c : F) (γs : ℕ → F) (k : ℕ) :
    consSched c γs (k + 1) = γs k := rfl

/-- Peeling one link off an aggregate at a consed schedule. -/
theorem aggregate_consSched (c : F) (γs : ℕ → F) (A₀ : AccClaim Root F ι r)
    (l : Link Root F ι r) (ls : Chain Root F ι r) :
    aggregate foldRoot (consSched c γs) A₀ (l :: ls)
      = aggregate foldRoot γs (foldClaims foldRoot A₀ l.claim c) ls := rfl

/-- The γ-power ladder: link `k` folded at `γ^(k+1)` — the schedule whose flat
target form is WHIR's `∑ γ^i·σᵢ` (`foldClaims_chain_target` is the length-3
instance). -/
def powSched (γ : F) : ℕ → F := fun k => γ ^ (k + 1)

/-- The aggregate keeps the genesis accumulator's functionals: `foldClaims`
folds targets and words, never the (aligned) functional channel. -/
theorem aggregate_weights (γs : ℕ → F) (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) :
    (aggregate foldRoot γs A₀ ch).weights = A₀.weights := by
  induction ch generalizing γs A₀ with
  | nil => rfl
  | cons l ls ih =>
    rw [aggregate_cons, ih]
    funext i
    rfl

/-- An all-zero schedule leaves the channel unchanged: folding at `γ = 0`
contributes nothing to any target. (The workhorse behind the head case of the
derandomized attestation: choosing the indicator schedule isolates one link.) -/
theorem aggregate_channel_of_zero {γs : ℕ → F} (h : ∀ k, γs k = 0)
    (A : AccClaim Root F ι r) (ch : Chain Root F ι r) :
    (aggregate foldRoot γs A ch).channel = A.channel := by
  induction ch generalizing γs A with
  | nil => rfl
  | cons l ls ih =>
    rw [aggregate_cons, ih fun k => h (k + 1)]
    funext i
    rw [foldClaims_channel, h 0]
    simp

end Aggregate

/-- Satisfaction only reads the channel (the root is opaque to the fold
algebra — Accumulator module header), so channel-equal claims are satisfied by
the same words. -/
theorem AccClaim.satisfies_of_channel_eq {C : Submodule F (ι → F)}
    {A B : AccClaim Root F ι r} (h : B.channel = A.channel) {f : ι → F}
    (hs : AccClaim.Satisfies C B f) : AccClaim.Satisfies C A f := by
  refine ⟨hs.1, fun i => ?_⟩
  have h2 := hs.2 i
  simp only [AccClaim.weights_apply, AccClaim.targets_apply, h] at h2 ⊢
  exact h2

/-! ## The attestation statement -/

/-- **Alignment**: every link's claim presents its constraints against the
genesis accumulator's functional channel — the post-alignment state WARP
establishes before any fold (fresh common point; `hshare` of
`foldClaims_satisfies`). -/
def Aligned (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r) : Prop :=
  ∀ l ∈ ch, ∀ i, l.claim.weights i = A₀.weights i

/-- **Verification of one accumulated claim**: some word witnesses it — the
promise the one decider pass establishes for the final accumulator (LOOM §1:
all queries, all Merkle paths, deferred to ONE WHIR descent). -/
def Verifies (C : Submodule F (ι → F)) (A : AccClaim Root F ι r) : Prop :=
  ∃ f, AccClaim.Satisfies C A f

/-- **The light-client attestation** — what checking the aggregate is meant to
teach the verifier about the WHOLE history: the seam binds every consecutive
pair (the chain executed IN ORDER), and every link's accumulated claim is
genuinely satisfiable (each step is a well-formed accumulated claim). Words
stay existential: claims are what the light client holds, words are witnesses
(Accumulator's day-one interface split). -/
def attests (C : Submodule F (ι → F)) (ch : Chain Root F ι r) : Prop :=
  SeamOk ch ∧ ∀ l ∈ ch, ∃ f, AccClaim.Satisfies C l.claim f

section Aggregate

variable (foldRoot : Root → F → Root → Root)

/-! ### Completeness: honest histories aggregate to satisfied claims -/

/-- The folded witness word along the chain: `w_k` joins at challenge `γs k` —
the word-level mirror of `aggregate` (WHIR's `g := ∑ γ_{i,j} · f_{i,j}`,
reached by iterating the pairwise `f + γ • g`). -/
def foldWords (γs : ℕ → F) (f₀ : ι → F) : List (ι → F) → (ι → F)
  | [] => f₀
  | w :: ws => foldWords (fun k => γs (k + 1)) (f₀ + γs 0 • w) ws

@[simp] theorem foldWords_nil (γs : ℕ → F) (f₀ : ι → F) :
    foldWords γs f₀ [] = f₀ := rfl

@[simp] theorem foldWords_cons (γs : ℕ → F) (f₀ w : ι → F)
    (ws : List (ι → F)) :
    foldWords γs f₀ (w :: ws)
      = foldWords (fun k => γs (k + 1)) (f₀ + γs 0 • w) ws := rfl

/-- **The aggregate of an honestly-witnessed chain is well-formed** — closure
composed along the history: per-link witnesses fold to the BUILT witness
`foldWords γs f₀ ws` of the aggregate, for every challenge schedule.
`foldClaims_satisfies` iterated; nothing re-derived. -/
theorem aggregate_satisfies {C : Submodule F (ι → F)} (γs : ℕ → F)
    {A₀ : AccClaim Root F ι r} {f₀ : ι → F} {ch : Chain Root F ι r}
    {ws : List (ι → F)}
    (hws : List.Forall₂
      (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w) ch ws) :
    Aligned A₀ ch → AccClaim.Satisfies C A₀ f₀ →
      AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch)
        (foldWords γs f₀ ws) := by
  induction hws generalizing γs A₀ f₀ with
  | nil => intro _ h; exact h
  | @cons l w ls ws' hlw _ ih =>
    intro halign hA₀
    rw [aggregate_cons, foldWords_cons]
    exact ih _ (fun l' hl' i => halign l' (List.mem_cons_of_mem _ hl') i)
      (foldClaims_satisfies foldRoot (γs 0)
        (fun i => halign l (List.mem_cons_self ..) i) hA₀ hlw)

/-- Completeness in the light client's vocabulary: an attested, aligned history
with a verifying genesis produces a verifying aggregate at EVERY challenge
schedule — the honest prover always convinces. -/
theorem lightClient_complete {C : Submodule F (ι → F)} {ch : Chain Root F ι r} :
    ∀ {A₀ : AccClaim Root F ι r}, Aligned A₀ ch → Verifies C A₀ →
      (∀ l ∈ ch, ∃ f, AccClaim.Satisfies C l.claim f) →
      ∀ γs : ℕ → F, Verifies C (aggregate foldRoot γs A₀ ch) := by
  induction ch with
  | nil => intro A₀ _ hA₀ _ γs; exact hA₀
  | cons l ls ih =>
    intro A₀ halign hA₀ hlinks γs
    obtain ⟨f₀, hf₀⟩ := hA₀
    obtain ⟨g, hg⟩ := hlinks l (List.mem_cons_self ..)
    rw [aggregate_cons]
    exact ih (A₀ := foldClaims foldRoot A₀ l.claim (γs 0))
      (fun l'' hl'' i => halign l'' (List.mem_cons_of_mem _ hl'') i)
      ⟨f₀ + γs 0 • g, foldClaims_satisfies foldRoot (γs 0)
        (fun i => halign l (List.mem_cons_self ..) i) hf₀ hg⟩
      (fun l' hl' => hlinks l' (List.mem_cons_of_mem _ hl')) _

/-! ### The apex: verifying the aggregate attests the history -/

/-- The tooth-bearing lemma of the light-client theorem, exact-word
(derandomized) form: if the aggregate verifies at EVERY challenge schedule,
every link's claim is satisfiable. The proof is the algebraic shadow of WARP's
backwards extractor: peel the chain from the front, isolate link `k` with the
indicator schedule (fold it at `1`, everything after at `0`), and recover its
witness by SUBTRACTING the genesis witness — the fold algebra is invertible at
nonzero challenges. The gap from "every schedule" down to "one random schedule,
except with `(t−1)ℓ/|F|`-shaped probability per fold" is `[ACC-sound]`;
replacing satisfiability by EXTRACTED words against a forging prover is
`[ACC-extract]` + Thm B.4 — together `[LC-sound]`, prose below. -/
theorem links_satisfiable_of_verifies {C : Submodule F (ι → F)}
    {ch : Chain Root F ι r} :
    ∀ {A₀ : AccClaim Root F ι r}, Aligned A₀ ch → Verifies C A₀ →
      (∀ γs : ℕ → F, Verifies C (aggregate foldRoot γs A₀ ch)) →
      ∀ l ∈ ch, ∃ f, AccClaim.Satisfies C l.claim f := by
  induction ch with
  | nil => intro A₀ _ _ _ l hl; simp at hl
  | cons l ls ih =>
    intro A₀ halign hA₀ hver l' hl'
    obtain ⟨f₀, hf₀⟩ := hA₀
    rcases List.mem_cons.mp hl' with rfl | hmem
    · -- Head link: indicator schedule (1, 0, 0, …) isolates it.
      obtain ⟨h₁, hh₁⟩ := hver (consSched 1 fun _ => 0)
      rw [aggregate_consSched] at hh₁
      have hsat := AccClaim.satisfies_of_channel_eq
        (aggregate_channel_of_zero foldRoot (fun _ => rfl) _ ls) hh₁
      refine ⟨h₁ - f₀, C.sub_mem hsat.1 hf₀.1, fun i => ?_⟩
      have hfold := hsat.2 i
      have hf := hf₀.2 i
      have hw := halign l' (List.mem_cons_self ..) i
      simp only [AccClaim.weights_apply, AccClaim.targets_apply,
        foldClaims_channel] at hfold hf hw ⊢
      rw [hw, map_sub, hfold, hf]
      ring
    · -- Tail: shift the schedule past a zero-challenge head fold and recurse.
      have hA₁ : AccClaim.Satisfies C (foldClaims foldRoot A₀ l.claim 0) f₀ := by
        refine ⟨hf₀.1, fun i => ?_⟩
        have hf := hf₀.2 i
        simp only [AccClaim.weights_apply, AccClaim.targets_apply,
          foldClaims_channel] at hf ⊢
        rw [hf]
        ring
      refine ih (A₀ := foldClaims foldRoot A₀ l.claim 0)
        (fun l'' hl'' i => halign l'' (List.mem_cons_of_mem _ hl'') i)
        ⟨f₀, hA₁⟩ (fun γs => ?_) l' hmem
      have h := hver (consSched 0 γs)
      rw [aggregate_consSched] at h
      exact h

/-- **THE LIGHT-CLIENT THEOREM, v0 apex (derandomized form)** — LOOM §1's
product: a verifier checking the single aggregate object (here: at every
challenge schedule — see `[LC-sound]` for the one-shot probabilistic upgrade)
plus the decidable seam learns that the WHOLE history attests: every link is a
well-formed (satisfiable) accumulated claim and the chain is seam-bound in
order. A tampered or reordered chain fails `SeamOk` (teeth below), and a chain
with any unsatisfiable link fails verification at some schedule
(`links_satisfiable_of_verifies`). -/
theorem lightClient_attests {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) (hA₀ : Verifies C A₀) (hseam : SeamOk ch)
    (hver : ∀ γs : ℕ → F, Verifies C (aggregate foldRoot γs A₀ ch)) :
    attests C ch :=
  ⟨hseam, links_satisfiable_of_verifies foldRoot halign hA₀ hver⟩

end Aggregate

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All BUILT, all computing, over `RS[F₅, {0,1,2,3}, 2]` — the words are
`Selvage/ReedSolomon.lean`'s `xWord` and `Selvage/Accumulator.lean`'s `oneWord` and
`q2` functional, REUSED. Roots live in `ZMod 5` so seam equalities have real
teeth (a `Unit` root would make every seam vacuously true — the tooth would be
toothless):

* **satisfiable** — `goodChain`: a 2-link seam-ok chain whose links are
  witnessed by genuine codewords; it attests (`goodChain_attests`), its
  aggregate is satisfied by the BUILT folded word at every schedule
  (`goodChain_aggregate_satisfied`), and the apex theorem FIRES on it with
  every hypothesis discharged (`lightClient_fires` — premise inhabitation).
* **teeth, seam** — `brokenChain` (same claims, one root tampered:
  `post₀ = 1 ≠ 3 = pre₁`) fails `SeamOk` by `decide`, hence cannot attest;
  the general tooth `not_seamOk_of_broken` fires on it concretely.
* **teeth, order** — `reorderedChain` is a genuine PERMUTATION of `goodChain`
  (`reorderedChain_perm`) yet fails `SeamOk`: the seam pins the ORDER, not
  just the multiset of links.
* **teeth, one-shot forgery** — `phantomChain`: two links whose claims are
  individually UNSATISFIABLE (zero functional, nonzero target), yet at the
  rigged schedule `(1, 1)` the folded targets cancel (`1 + 4 = 0` in `F₅`) and
  the aggregate VERIFIES (`phantom_forged`). The naive one-shot light-client
  implication is therefore FALSE (`oneShot_lightClient_false`), while the
  indicator schedule catches the forgery (`phantom_caught`) — the ∀-schedule
  quantifier in `lightClient_attests` is load-bearing, and its probabilistic
  replacement is exactly `[LC-sound]`. -/

namespace LCExample

open RSExample AccExample

/-- A toy recommitment schedule on transparent `ZMod 5` roots (opaque to all
theorems — the algebra never reads it). -/
def linRoot : ZMod 5 → ZMod 5 → ZMod 5 → ZMod 5 := fun a γ b => a + γ * b

/-- The genesis accumulator: the evaluation constraint `q2 = 2`, satisfied by
`xWord`. -/
def genesis : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1 := ⟨0, fun _ => (q2, 2)⟩

theorem genesis_satisfied :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) genesis xWord :=
  ⟨xWord_mem, fun _ => q2_xWord⟩

/-- Step 1's claim: `q2 = 0`, witnessed by the zero codeword. -/
def claim₀ : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1 := ⟨1, fun _ => (q2, 0)⟩

/-- Step 2's claim: `q2 = 1`, witnessed by `oneWord`. -/
def claim₁ : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1 := ⟨2, fun _ => (q2, 1)⟩

/-- Link 1: state root 0 → 1. -/
def link₀ : Link (ZMod 5) (ZMod 5) (Fin 4) 1 := ⟨0, 1, claim₀⟩

/-- Link 2: state root 1 → 2 — seam-bound to `link₀`. -/
def link₁ : Link (ZMod 5) (ZMod 5) (Fin 4) 1 := ⟨1, 2, claim₁⟩

/-- **The satisfiable keystone chain**: two links, seam-bound `0 → 1 → 2`. -/
def goodChain : Chain (ZMod 5) (ZMod 5) (Fin 4) 1 := [link₀, link₁]

/-- The seam checks — COMPUTED (the decidable side-check the light client
runs). -/
theorem goodChain_seamOk : SeamOk goodChain := by decide

theorem goodChain_aligned : Aligned genesis goodChain := by
  intro l hl i
  rcases List.mem_cons.mp hl with rfl | hl
  · rfl
  · rcases List.mem_cons.mp hl with rfl | hl
    · rfl
    · simp at hl

/-- **Satisfiable**: the keystone history attests — seam-ok, every link
witnessed by a genuine codeword. -/
theorem goodChain_attests :
    attests (reedSolomonCode dom₅ 2) goodChain := by
  refine ⟨goodChain_seamOk, fun l hl => ?_⟩
  rcases List.mem_cons.mp hl with rfl | hl
  · exact ⟨0, Submodule.zero_mem _, fun _ => map_zero q2⟩
  · rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨oneWord, oneWord_mem, fun _ => rfl⟩
    · simp at hl

/-- The aggregate of the keystone chain is satisfied by the BUILT folded word
`(xWord + γs 0 • 0) + γs 1 • oneWord`, at EVERY challenge schedule — closure
composed along a real history. -/
theorem goodChain_aggregate_satisfied (γs : ℕ → ZMod 5) :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2)
      (aggregate linRoot γs genesis goodChain)
      (foldWords γs xWord [0, oneWord]) :=
  aggregate_satisfies linRoot γs
    (.cons ⟨Submodule.zero_mem _, fun _ => map_zero q2⟩
      (.cons ⟨oneWord_mem, fun _ => rfl⟩ .nil))
    goodChain_aligned genesis_satisfied

theorem goodChain_verifies (γs : ℕ → ZMod 5) :
    Verifies (reedSolomonCode dom₅ 2) (aggregate linRoot γs genesis goodChain) :=
  ⟨_, goodChain_aggregate_satisfied γs⟩

/-- **Premise inhabitation**: the apex theorem `lightClient_attests` FIRES on
the keystone chain — every hypothesis (alignment, genesis, seam, verification
at all schedules) discharged by built witnesses, nothing vacuous. -/
theorem lightClient_fires : attests (reedSolomonCode dom₅ 2) goodChain :=
  lightClient_attests linRoot goodChain_aligned ⟨xWord, genesis_satisfied⟩
    goodChain_seamOk goodChain_verifies

/-- The γ-power ladder computed on the keystone chain: at `powSched 3` the
aggregate target is `2 + 3·0 + 3²·1 = 11 = 1` in `F₅` — WHIR's flat
`∑ γ^i·σᵢ` form, reached by iterating the one pairwise fold. -/
example : ((aggregate linRoot (powSched 3) genesis goodChain).channel 0).2
    = 1 := by decide

/-! ### Teeth: tamper and reorder are caught at the seam -/

/-- `link₁` with a TAMPERED pre-root (`3` instead of `1`) — the claim itself is
untouched and still satisfiable; only the seam is broken. -/
def brokenLink : Link (ZMod 5) (ZMod 5) (Fin 4) 1 := ⟨3, 2, claim₁⟩

/-- The tampered history: same claims as `goodChain`, one root changed. -/
def brokenChain : Chain (ZMod 5) (ZMod 5) (Fin 4) 1 := [link₀, brokenLink]

/-- **The anti-tamper tooth, computed**: the broken seam (`post₀ = 1 ≠ 3 =
pre₁`) refutes `SeamOk` — decided, not assumed. -/
theorem brokenChain_not_seamOk : ¬ SeamOk brokenChain := by decide

/-- The general tooth `not_seamOk_of_broken` fires on the concrete break. -/
example : ¬ SeamOk brokenChain :=
  not_seamOk_of_broken [] [] (by decide : link₀.post ≠ brokenLink.pre)

/-- A tampered chain cannot attest, whatever its claims: no verifying
aggregate speaks for a history whose links do not bind. -/
theorem brokenChain_not_attests :
    ¬ attests (reedSolomonCode dom₅ 2) brokenChain :=
  fun h => brokenChain_not_seamOk h.1

/-- `goodChain` REORDERED: the same two links, swapped. -/
def reorderedChain : Chain (ZMod 5) (ZMod 5) (Fin 4) 1 := [link₁, link₀]

/-- The reordering is a genuine permutation — same multiset of links. -/
theorem reorderedChain_perm : reorderedChain.Perm goodChain :=
  .swap link₀ link₁ []

/-- **The anti-reorder tooth, computed**: swapping the links breaks the seam
(`post link₁ = 2 ≠ 0 = pre link₀`) — the seam pins ORDER, not just content. -/
theorem reorderedChain_not_seamOk : ¬ SeamOk reorderedChain := by decide

theorem reorderedChain_not_attests :
    ¬ attests (reedSolomonCode dom₅ 2) reorderedChain :=
  fun h => reorderedChain_not_seamOk h.1

/-! ### Teeth: the one-shot forgery — why `[LC-sound]` is probabilistic -/

/-- A genesis with the ZERO functional and target 0 — satisfiable (by the zero
word), aligned with the phantom links below. -/
def phantomGenesis : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1 :=
  ⟨0, fun _ => (0, 0)⟩

/-- Phantom claim: zero functional, target `1` — UNSATISFIABLE (`0 ≠ 1`). -/
def phantomClaim₀ : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1 :=
  ⟨1, fun _ => (0, 1)⟩

/-- Phantom claim: zero functional, target `4 = −1` — UNSATISFIABLE, rigged to
cancel `phantomClaim₀` under the fold at challenge `1`. -/
def phantomClaim₁ : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1 :=
  ⟨2, fun _ => (0, 4)⟩

/-- A seam-OK chain of two individually-false links: the seam is honest, the
CLAIMS are forgeries. -/
def phantomChain : Chain (ZMod 5) (ZMod 5) (Fin 4) 1 :=
  [⟨0, 1, phantomClaim₀⟩, ⟨1, 2, phantomClaim₁⟩]

theorem phantomChain_seamOk : SeamOk phantomChain := by decide

theorem phantomClaim₀_unsatisfiable :
    ¬ ∃ f, AccClaim.Satisfies (reedSolomonCode dom₅ 2) phantomClaim₀ f := by
  rintro ⟨f, -, hc⟩
  have h0 := hc 0
  simp [phantomClaim₀, AccClaim.weights, AccClaim.targets] at h0

theorem phantomChain_not_attests :
    ¬ attests (reedSolomonCode dom₅ 2) phantomChain := by
  rintro ⟨-, hlinks⟩
  exact phantomClaim₀_unsatisfiable
    (hlinks ⟨0, 1, phantomClaim₀⟩ (List.mem_cons_self ..))

theorem phantomGenesis_verifies :
    Verifies (reedSolomonCode dom₅ 2) phantomGenesis :=
  ⟨0, Submodule.zero_mem _, fun _ => rfl⟩

theorem phantomChain_aligned : Aligned phantomGenesis phantomChain := by
  intro l hl i
  rcases List.mem_cons.mp hl with rfl | hl
  · rfl
  · rcases List.mem_cons.mp hl with rfl | hl
    · rfl
    · simp at hl

/-- **The γ-cancellation forgery, computed**: at the rigged constant schedule
`(1, 1, …)` the two false targets cancel (`0 + 1·1 + 1·4 = 0` in `F₅`) and the
phantom aggregate VERIFIES — witnessed by the zero word. This is the
soundness-error event whose probability `[ACC-sound]` bounds per fold; here it
is exhibited, not bounded. -/
theorem phantom_forged :
    Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot (fun _ => 1) phantomGenesis phantomChain) := by
  refine ⟨0, Submodule.zero_mem _, fun i => ?_⟩
  simp [phantomChain, phantomGenesis, phantomClaim₀, phantomClaim₁, aggregate,
    foldClaims, AccClaim.weights, AccClaim.targets]
  decide

/-- The indicator schedule CATCHES the forgery: at `(1, 0, …)` the aggregate
target is `1` on the zero functional — unsatisfiable. The ∀-schedule
hypothesis of `lightClient_attests` sees this schedule; a one-shot verifier at
the rigged schedule does not. -/
theorem phantom_caught :
    ¬ Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot (consSched 1 fun _ => 0) phantomGenesis
        phantomChain) := by
  rintro ⟨f, -, hc⟩
  have h0 := hc 0
  simp [phantomChain, phantomGenesis, phantomClaim₀, phantomClaim₁, aggregate,
    foldClaims, consSched, AccClaim.weights, AccClaim.targets] at h0

/-- **The naive one-shot light-client statement is FALSE** — machine-checked
(Depth.lean discipline: refute the statement one would naively want, then name
the true one). Verifying the aggregate at a SINGLE fixed schedule, even with a
seam-ok chain, aligned claims, and an honest genesis, does NOT attest the
history: `phantomChain` is a counterexample. The true one-shot statement is
probabilistic over the challenge — that is `[LC-sound]`, and this refutation
is why it cannot be an algebraic theorem of this file. -/
theorem oneShot_lightClient_false :
    ¬ (∀ (A₀ : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1)
        (ch : Chain (ZMod 5) (ZMod 5) (Fin 4) 1),
        Aligned A₀ ch → Verifies (reedSolomonCode dom₅ 2) A₀ → SeamOk ch →
        Verifies (reedSolomonCode dom₅ 2)
          (aggregate linRoot (fun _ => 1) A₀ ch) →
        attests (reedSolomonCode dom₅ 2) ch) := by
  intro h
  exact phantomChain_not_attests
    (h phantomGenesis phantomChain phantomChain_aligned phantomGenesis_verifies
      phantomChain_seamOk phantom_forged)

end LCExample

/-! ## Residual obligations — prose, not stubs

Named residual with its realizer; becomes a real theorem, never a
`def : Prop := True` (the vacuous-obligation sin — audit discipline as in
`Selvage/Accumulator.lean`).

**[LC-sound]** — straightline soundness of the one-shot light client. The
theorem proved here (`lightClient_attests`) consumes verification at EVERY
challenge schedule; the deployed light client checks ONE aggregate produced
along ONE schedule sampled σ-before-γ by Fiat–Shamir. The upgrade is exactly
the accumulated-claim tower, cited not re-derived:

* per fold, a false link survives only on the bad-challenge set —
  `[ACC-sound]`'s `(t−1)ℓ/|F|` same-word / `err★ + (s−1)ℓ/|F|` cross-word RBR
  bounds (WHIR Constr. 5.5/7.4 via mutual correlated agreement, PROVED at
  unique decoding in `Selvage/CorrelatedAgreement.lean`); the cancellation event
  is EXHIBITED here (`LCExample.phantom_forged`), its probability is that
  residual's number;
* against a forging PROVER, satisfiability is replaced by extraction: WARP's
  straightline erasure extractor recovers each link's word backwards through
  the chain ([ACC-extract]; erasure correction only, no decoder), and the
  per-link RBR errors compose loss-free at deployed depth by WARP Thm B.4,
  `ε_sr ≤ (t+k)·ε_rbr` — the tower PROVED in `Selvage/Depth.lean` modulo its one
  named seam `[OB-2a]` (the lazy-`rnd` game-slot resolver), with Fiat–Shamir
  of RBR preserving straightline extraction (`Selvage/FiatShamir.lean`, modulo
  the same seam);
* the seam side: `SeamOk` here is a decidable side-check; its encoding as
  accumulated claims riding the same fold (one object for the light client,
  GBF public side where possible) is `[OB-3′]`'s receipt-encoding work
  (docs/OB3-RECEIPT-ENCODING.md), consumed by `[LC-sound]` when it lands.

The derandomized skeleton (`links_satisfiable_of_verifies`) already carries
the extraction SHAPE — backwards through the chain, witness by subtraction —
so `[LC-sound]` is a probability bound over this file's algebra, not new
algebra. -/

end Minidregg.Selvage
