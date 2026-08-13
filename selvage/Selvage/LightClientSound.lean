/-
# Selvage.LightClientSound — [LC-sound]: the one-shot probabilistic light client.

Closes the quantifier gap `Selvage/LightClient.lean` proved load-bearing: the v0
apex `lightClient_attests` consumes verification at EVERY challenge schedule,
and the naive single-FIXED-schedule form is FALSE (`oneShot_lightClient_false`
— `phantomChain` forges at the rigged schedule `(1,1)`). The TRUE one-shot
statement is probabilistic: a UNIFORMLY SAMPLED schedule catches a false chain
except with small probability. This file proves it, in two complementary
forms, both over the finite schedule space `Fin ch.length → F` (one fresh
challenge per link, WARP's σ-before-γ sampling rendered as one uniform draw
per accumulation step):

* **`lightClientSound_exact` — the exact-word one-shot bound, SHARP at
  `1/|F|`.** If ANY link's claim is unsatisfiable, the aggregate verifies at a
  uniformly random schedule with probability ≤ `1/|F|` — not merely
  `n/|F|`: at the exact-word level satisfiability of the aggregate is a
  linear condition in the schedule, so the forging schedules of a false chain
  form (a coset slice of) a proper subspace. The engine is
  `link_satisfiable_of_verifies_pair`: verification at TWO schedules differing
  in exactly the false link's coordinate recovers that link's witness by
  subtraction — `links_satisfiable_of_verifies`' backwards-extractor algebra,
  re-run at two points instead of all of them. Conditioning on every other
  coordinate (`splitCoord` + `uniformProb_prod_le`, the Depth toolkit) leaves
  ≤ 1 surviving value of the false link's challenge.
* **`lightClientSound` — THE DEPLOYABLE HEADLINE, `n·(err⋆(δ) + 1/|F|)`.**
  The δ-proximity form the deployed light client needs: the event is anchored
  at the honestly-folded committed words (`foldWords`, the strict fold
  interface — the prover's recommitment being BOUND to this fold is
  `[ACC-extract]`'s obligation, exactly as in `Selvage/AccSound.lean`'s "strict
  fold events" note), and a chain with a δ-far-false link survives with
  probability ≤ `ch.length · (err⋆(δ) + 1/|F|)`. PROVED for the WHOLE chain,
  arbitrary length, by induction: per step, `foldClaims_sound_proximity_UD`
  (AccSound's headline — mutual correlated agreement genuinely consumed,
  REUSED not re-derived) prices the step's fold event at `err⋆ + 1/|F|`, and
  the chain composes by the RBR pattern of `Selvage/Depth.lean`'s Thm B.4 union
  bound — here in its binary per-step form `uniformProb_or_le` +
  `uniformProb_prod_le` (condition on the current challenge; a step either
  fires its per-fold bad event or hands the NEXT step a still-false
  accumulator), the same straightline no-rewinding structure
  `OB2_depth_composition_nonneg_proved` closes in general.

Together: the ∀-schedule hypothesis of `lightClient_attests` is discharged by
ONE uniform schedule up to the proved probability — the contrapositive
probabilistic form. What this file does NOT do (honest residuals, end of
file): Fiat–Shamir transport of "uniform schedule" to "hash-derived schedule"
(`[LC-sound-fs]`, riding `Selvage/FiatShamir.lean` + `[ACC-sound-rbr]`), and
extraction against a forging prover (`[ACC-extract]`, unchanged).

**Keystones (F₅, all computing, reusing `LCExample`'s chains):** the payoff is
`phantom_forging_prob`: the phantom chain that FORGED at the rigged schedule
`(1,1)` forges at EXACTLY the diagonal schedules `{γ₀ = γ₁}` — 5 of the 25
schedules, probability `1/5 = 1/|F|`, the exact-word bound ATTAINED — and the
general theorem fires on it (`phantom_caught_probably`). The honest
`goodChain` verifies at EVERY sampled schedule (`goodChain_verifies_prob_one`
— probability 1, the completeness side untouched by sampling). The δ-headline
fires on the phantom too (`phantom_delta_fired`, over `C = ⊤` where the landed
`hasMutualCorrelatedAgreement_top_affine` supplies err⋆ = 0), with the true
event probability computed (`phantom_delta_prob_eq` = 1/5 ≤ 2/5: the union
bound's factor-of-n slack made visible).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Selvage.LightClient
import Selvage.AccSound
import Selvage.Depth

namespace Minidregg.Selvage

variable {Root : Type*} {ι : Type*}
variable {F : Type} [Field F]
variable {r : ℕ}

/-! ## The sampled schedule

The deployed light client draws ONE challenge per link — a tuple in
`Fin ch.length → F` — where the theorems of `Selvage/LightClient.lean` quantify
over streams `ℕ → F`. `padSched` embeds the tuple (zero past the chain's
length; `aggregate` never reads there), and `padSched_cons` is the
stream-cons compatibility that lets the chain recursion peel one sampled
challenge at a time (`consSched` is LightClient's stream-cons). -/

/-- A finite sampled schedule, as the stream the fold algebra consumes:
coordinate `k` below `n`, zero above (never read by a length-`n` chain). -/
def padSched {n : ℕ} (γv : Fin n → F) : ℕ → F := fun k =>
  if h : k < n then γv ⟨k, h⟩ else 0

@[simp] theorem padSched_lt {n : ℕ} (γv : Fin n → F) {k : ℕ} (h : k < n) :
    padSched γv k = γv ⟨k, h⟩ := dif_pos h

theorem padSched_of_le {n : ℕ} (γv : Fin n → F) {k : ℕ} (h : n ≤ k) :
    padSched γv k = 0 := dif_neg (Nat.not_lt.mpr h)

/-- Padding a consed tuple is consing the padded tuple — the bridge from the
sampled space `Fin (m+1) → F` to LightClient's stream recursion. -/
theorem padSched_cons {m : ℕ} (c : F) (γv : Fin m → F) :
    padSched (Fin.cons c γv) = consSched c (padSched γv) := by
  funext k
  cases k with
  | zero => simp [padSched]
  | succ k =>
    rw [consSched_succ]
    by_cases h : k < m
    · rw [padSched_lt _ (Nat.succ_lt_succ h), padSched_lt _ h]
      exact Fin.cons_succ (α := fun _ => F) c γv ⟨k, h⟩
    · rw [padSched_of_le _ (Nat.not_lt.mp h),
        padSched_of_le _ (Nat.succ_le_succ (Nat.not_lt.mp h))]

/-- The word-side mirror of `aggregate_consSched`: folding words at a consed
schedule peels the head challenge. -/
theorem foldWords_consSched (c : F) (γs : ℕ → F) (f₀ w : ι → F)
    (ws : List (ι → F)) :
    foldWords (consSched c γs) f₀ (w :: ws)
      = foldWords γs (f₀ + c • w) ws := rfl

/-! ## The aggregate's channel, in closed form

`aggregate_weights` (landed) says the functional channel never moves; here the
target channel is the affine form `A₀-target + ∑ₖ γₖ·(link-k target)` — the
algebra that makes the schedule-linearity of verification VISIBLE, and with it
both soundness arguments below. -/

section Aggregate

variable (foldRoot : Root → F → Root → Root)

/-- The aggregate's targets are affine in the schedule: genesis target plus
the γ-weighted link targets. (`foldClaims` iterated on the target channel.) -/
theorem aggregate_targets (γs : ℕ → F) (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) (i : Fin r) :
    (aggregate foldRoot γs A₀ ch).targets i
      = A₀.targets i
        + ∑ k : Fin ch.length, γs (k : ℕ) * (ch.get k).claim.targets i := by
  induction ch generalizing γs A₀ with
  | nil => simp
  | cons l ls ih =>
    rw [aggregate_cons, ih]
    simp only [AccClaim.targets_apply, foldClaims_channel, List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    show (A₀.channel i).2 + γs 0 * ((l.claim.channel i).2)
        + ∑ k : Fin ls.length, γs (k + 1) * ((ls.get k).claim.channel i).2
      = (A₀.channel i).2 + (γs 0 * (l.claim.channel i).2
        + ∑ k : Fin ls.length, γs (k + 1) * ((ls.get k).claim.channel i).2)
    ring

/-- **The two-point extractor** — `links_satisfiable_of_verifies`' subtraction
algebra at TWO schedules instead of every schedule: if the aggregate verifies
at two schedules that differ in EXACTLY link `k`'s coordinate, link `k`'s
claim is satisfiable — the two witnesses' difference, rescaled by the
challenge difference, witnesses it. This is the entire mechanism of the sharp
one-shot bound: a false link leaves at most ONE surviving value of its own
challenge, whatever the other coordinates do. -/
theorem link_satisfiable_of_verifies_pair {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) {γs γs' : ℕ → F} {k : Fin ch.length}
    (hagree : ∀ m : ℕ, m ≠ (k : ℕ) → γs m = γs' m)
    (hne : γs (k : ℕ) ≠ γs' (k : ℕ))
    (h₁ : Verifies C (aggregate foldRoot γs A₀ ch))
    (h₂ : Verifies C (aggregate foldRoot γs' A₀ ch)) :
    ∃ f, AccClaim.Satisfies C (ch.get k).claim f := by
  obtain ⟨h1, hm1, hc1⟩ := h₁
  obtain ⟨h2, hm2, hc2⟩ := h₂
  have hc : γs (k : ℕ) - γs' (k : ℕ) ≠ 0 := sub_ne_zero_of_ne hne
  refine ⟨(γs (k : ℕ) - γs' (k : ℕ))⁻¹ • (h1 - h2),
    C.smul_mem _ (C.sub_mem hm1 hm2), fun i => ?_⟩
  have hw := halign (ch.get k) (ch.get_mem k) i
  have t1 := hc1 i
  have t2 := hc2 i
  rw [show (aggregate foldRoot γs A₀ ch).weights = A₀.weights from
      aggregate_weights .., aggregate_targets] at t1
  rw [show (aggregate foldRoot γs' A₀ ch).weights = A₀.weights from
      aggregate_weights .., aggregate_targets] at t2
  -- the schedules' target difference collapses to link k's term
  have hsum : A₀.weights i h1 - A₀.weights i h2
      = (γs (k : ℕ) - γs' (k : ℕ)) * (ch.get k).claim.targets i := by
    rw [t1, t2]
    have hdiff : (A₀.targets i
          + ∑ m : Fin ch.length, γs (m : ℕ) * (ch.get m).claim.targets i)
        - (A₀.targets i
          + ∑ m : Fin ch.length, γs' (m : ℕ) * (ch.get m).claim.targets i)
        = ∑ m : Fin ch.length,
            (γs (m : ℕ) - γs' (m : ℕ)) * (ch.get m).claim.targets i :=
      calc (A₀.targets i
              + ∑ m : Fin ch.length, γs (m : ℕ) * (ch.get m).claim.targets i)
            - (A₀.targets i
              + ∑ m : Fin ch.length, γs' (m : ℕ) * (ch.get m).claim.targets i)
          = (∑ m : Fin ch.length, γs (m : ℕ) * (ch.get m).claim.targets i)
            - ∑ m : Fin ch.length, γs' (m : ℕ) * (ch.get m).claim.targets i := by
            ring
        _ = ∑ m : Fin ch.length, (γs (m : ℕ) * (ch.get m).claim.targets i
              - γs' (m : ℕ) * (ch.get m).claim.targets i) := by
            rw [← Finset.sum_sub_distrib]
        _ = ∑ m : Fin ch.length,
              (γs (m : ℕ) - γs' (m : ℕ)) * (ch.get m).claim.targets i :=
            Finset.sum_congr rfl fun m _ => (sub_mul ..).symm
    rw [hdiff]
    rw [Finset.sum_eq_single k]
    · intro m _ hmk
      rw [hagree (m : ℕ) (fun hc' => hmk (Fin.ext hc')), sub_self, zero_mul]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [hw, map_smul, map_sub, smul_eq_mul, hsum, inv_mul_cancel_left₀ hc]

end Aggregate

/-! ## Counting plumbing (private — `Selvage/Depth.lean` owns the public
`uniformProb` toolkit, REUSED below; these two facts are the only ones it
lacks, kept `private` by the `Selvage/AccSound.lean` discipline so the aggregate
build never sees two copies). -/

private theorem uniformProb_le_inv_card_of_subsingleton (F : Type) [Fintype F]
    {p : F → Prop} (h : ∀ a b, p a → p b → a = b) :
    uniformProb F p ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  unfold uniformProb
  have hcard : (Nat.card {c : F // p c} : ℝ) ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_le_one_iff.mpr fun a b =>
      Subtype.ext (h _ _ a.2 b.2)
  gcongr

private theorem uniformProb_of_forall (F : Type) [Fintype F] [Nonempty F]
    {p : F → Prop} (h : ∀ c, p c) : uniformProb F p = 1 := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h), Nat.card_eq_fintype_card,
    div_self]
  exact_mod_cast Fintype.card_ne_zero

/-! ## The exact-word one-shot bound — sharp at `1/|F|`

The probabilistic replacement for `lightClient_attests`' ∀-schedule
hypothesis, exact-word regime: ONE uniformly sampled schedule, and a chain
with ANY unsatisfiable link verifies with probability at most `1/|F|` — the
γ-cancellation event `LCExample.phantom_forged` exhibits, now BOUNDED. Sharp,
not `n/|F|`: conditioned on every other link's challenge, the two-point
extractor leaves at most one surviving value of the false link's own
challenge (the union bound over links is only needed once proximity slack
decouples the steps — the δ-form below). -/

section Exact

variable (foldRoot : Root → F → Root → Root)

/-- **[LC-sound], exact-word form.** If some link's claim is unsatisfiable,
the aggregate verifies at a uniformly sampled schedule (one fresh challenge
per link) with probability at most `1/|F|`. Contrapositive-probabilistic form
of `lightClient_attests`: the ∀-schedule hypothesis is discharged by one
uniform draw, up to this probability. No hypothesis on the genesis is needed —
the subtraction extractor never touches it. -/
theorem lightClientSound_exact [Fintype F] {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch)
    (huns : ∃ l ∈ ch, ¬ ∃ f, AccClaim.Satisfies C l.claim f) :
    uniformProb (Fin ch.length → F) (fun γv =>
        Verifies C (aggregate foldRoot (padSched γv) A₀ ch))
      ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  obtain ⟨l, hl, hluns⟩ := huns
  obtain ⟨j, hj, hgetl⟩ := List.mem_iff_getElem.mp hl
  set kF : Fin ch.length := ⟨j, hj⟩ with hkF
  -- condition on every coordinate except the false link's
  rw [← uniformProb_equiv (splitCoord kF).symm (fun γv =>
    Verifies C (aggregate foldRoot (padSched γv) A₀ ch))]
  refine uniformProb_prod_le (by positivity) fun rest => ?_
  refine uniformProb_le_inv_card_of_subsingleton F fun ρ₁ ρ₂ hp₁ hp₂ => ?_
  by_contra hρ
  -- two verifying schedules differing exactly at link j: extract its witness
  refine hluns ?_
  rw [← hgetl]
  refine link_satisfiable_of_verifies_pair foldRoot halign
    (γs := padSched ((splitCoord kF).symm (rest, ρ₁)))
    (γs' := padSched ((splitCoord kF).symm (rest, ρ₂)))
    (k := kF) (fun m hm => ?_) ?_ hp₁ hp₂
  · by_cases hmn : m < ch.length
    · rw [padSched_lt _ hmn, padSched_lt _ hmn,
        splitCoord_symm_apply_ne (i := kF) (fun hc => hm (congrArg Fin.val hc)),
        splitCoord_symm_apply_ne (i := kF) (fun hc => hm (congrArg Fin.val hc))]
    · rw [padSched_of_le _ (Nat.not_lt.mp hmn),
        padSched_of_le _ (Nat.not_lt.mp hmn)]
  · rw [padSched_lt _ hj, padSched_lt _ hj]
    show (splitCoord kF).symm (rest, ρ₁) kF ≠ (splitCoord kF).symm (rest, ρ₂) kF
    rw [splitCoord_symm_apply_self, splitCoord_symm_apply_self]
    exact hρ

/-- The `attests` interface form: a seam-ok chain that does NOT attest has an
unsatisfiable link (the seam side is the light client's decidable side-check,
caught deterministically — `brokenChain`/`reorderedChain` teeth in
`Selvage/LightClient.lean`), so it survives one sampled schedule with probability
at most `1/|F|`. -/
theorem lightClientSound_of_not_attests [Fintype F] {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch)
    (hnot : ¬ attests C ch) :
    uniformProb (Fin ch.length → F) (fun γv =>
        Verifies C (aggregate foldRoot (padSched γv) A₀ ch))
      ≤ 1 / (Fintype.card F : ℝ) := by
  refine lightClientSound_exact foldRoot halign ?_
  by_contra hall
  push Not at hall
  exact hnot ⟨hseam, hall⟩

end Exact

/-! ## The deployable headline: δ-proximity soundness of the sampled chain

The event the deployed light client actually adjudicates: the prover has
committed per-link words; verification means the honestly-folded word
(`foldWords` — the strict fold interface; binding the prover's recommitments
to this fold is `[ACC-extract]`) lands δ-close to a codeword satisfying the
aggregate claim. A chain carrying a δ-far-false link survives with
probability at most `n · (err⋆(δ) + 1/|F|)` — WHIR Constr. 7.4's per-step
`err⋆ + (s−1)ℓ/|F|` (s = 2, ℓ = 1 at unique decoding,
`foldClaims_sound_proximity_UD` REUSED) × the chain length, by the RBR
union-bound pattern: conditioning on the current challenge, each step either
fires its per-fold bad event or hands the next step a still-δ-far-false
accumulator. The exact-word sharpening to `1/|F|` does NOT survive the δ
relaxation — proximity slack decouples the steps (each fold can move the
δ-ball), which is exactly why WARP's Thm B.4 pays `(t+k)·ε_rbr` and not
`ε_rbr` (`Selvage/Depth.lean`); the bound here has the same per-move shape. -/

section Proximity

variable [Fintype ι] [DecidableEq ι] [DecidableEq F]

/-- δ-far-falsity of an accumulated claim at an anchor word: EVERY codeword
δ-close to the anchor violates some channel constraint. The chain induction's
running invariant ("the accumulator has gone false, and no δ-ball repair can
save it"). -/
def FarFalse (C : Submodule F (ι → F)) (δ : ℝ) (A : AccClaim Root F ι r)
    (f : ι → F) : Prop :=
  ∀ u ∈ C, relDist f u ≤ δ → ∃ i, A.weights i u ≠ A.targets i

/-- Head-splitting equivalence for the sampled schedule space — hand-rolled so
both directions reduce definitionally (Depth's `consSplit` discipline). -/
def schedCons (m : ℕ) (F : Type) : (F × (Fin m → F)) ≃ (Fin (m + 1) → F) where
  toFun y := Fin.cons y.1 y.2
  invFun γv := (γv 0, Fin.tail γv)
  left_inv y := by simp
  right_inv γv := Fin.cons_self_tail γv

variable (foldRoot : Root → F → Root → Root)

/-- **The chain induction behind `lightClientSound`** — the accumulated form:
either the running accumulator is already δ-far-false at its anchor, or some
remaining link is δ-far-false at its committed word (falsity phrased against
the accumulator's functional channel, which the fold preserves). Then the
δ-proximity verification event at one uniformly sampled schedule has
probability at most `n · (err⋆(δ) + 1/|F|)`.

Per step: `foldClaims_sound_proximity_UD` (AccSound's headline, mutual CA
consumed — REUSED) prices the step's fold event; `uniformProb_prod_le` +
`uniformProb_or_le` (Depth's toolkit) run the conditioning and the union
bound; a step whose fold event does NOT fire hands the tail a δ-far-false
accumulator, which is the induction hypothesis' left disjunct. -/
theorem lightClientSound_chain [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)} {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ) :
    ∀ (ch : Chain Root F ι r) (ws : List (ι → F)) (A : AccClaim Root F ι r)
      (f : ι → F), ws.length = ch.length →
      (FarFalse C δ A f ∨ ∃ p ∈ ch.zip ws, ∀ v ∈ C, relDist p.2 v ≤ δ →
        ∃ i, A.weights i v ≠ p.1.claim.targets i) →
      uniformProb (Fin ch.length → F) (fun γv =>
          ∃ w, relDist (foldWords (padSched γv) f ws) w ≤ δ ∧
            AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A ch) w)
        ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)) := by
  intro ch
  induction ch with
  | nil =>
    intro ws A f hlen hfalse
    obtain rfl := List.length_eq_zero_iff.mp hlen
    have hFF : FarFalse C δ A f := by
      rcases hfalse with h | ⟨p, hp, -⟩
      · exact h
      · simp at hp
    have h0 : uniformProb (Fin (List.length ([] : Chain Root F ι r)) → F)
        (fun γv => ∃ w, relDist (foldWords (padSched γv) f []) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A []) w)
        = 0 :=
      uniformProb_false fun γv ⟨w, hwc, hwC, hwsat⟩ =>
        (hFF w hwC hwc).elim fun i hi => hi (hwsat i)
    rw [h0]
    simp
  | cons l ls ih =>
    intro ws A f hlen hfalse
    obtain ⟨g, gs, rfl⟩ : ∃ g gs, ws = g :: gs := by
      cases ws with
      | nil => simp at hlen
      | cons g gs => exact ⟨g, gs, rfl⟩
    have hlen' : gs.length = ls.length := by simpa using hlen
    have hε0 : 0 ≤ errstar δ + 1 / (Fintype.card F : ℝ) :=
      add_nonneg herr0 (by positivity)
    -- the falsity hypothesis, split at the head fold
    have hsplit : (∀ u ∈ C, ∀ v ∈ C, relDist f u ≤ δ → relDist g v ≤ δ →
          ∃ i, ¬(A.weights i u = A.targets i ∧
            A.weights i v = l.claim.targets i))
        ∨ ∃ p ∈ ls.zip gs, ∀ v ∈ C, relDist p.2 v ≤ δ →
            ∃ i, A.weights i v ≠ p.1.claim.targets i := by
      rcases hfalse with hFF | ⟨p, hp, hpfar⟩
      · exact Or.inl fun u hu v hv hcu hcv =>
          (hFF u hu hcu).imp fun i hi hpair => hi hpair.1
      · rcases List.mem_cons.mp (by simpa [List.zip_cons_cons] using hp) with
          rfl | htail
        · exact Or.inl fun u hu v hv hcu hcv =>
            (hpfar v hv hcv).imp fun i hi hpair => hi hpair.2
        · exact Or.inr ⟨p, htail, hpfar⟩
    -- the bound on the head-split product space
    have hprod : uniformProb (F × (Fin ls.length → F)) (fun y =>
        ∃ w, relDist (foldWords (padSched y.2) (f + y.1 • g) gs) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched y.2)
            (foldClaims foldRoot A l.claim y.1) ls) w)
        ≤ ((ls.length : ℝ) + 1)
          * (errstar δ + 1 / (Fintype.card F : ℝ)) := by
      rcases hsplit with hfar | ⟨p, hpt, hpfar⟩
      · -- the head fold is false: price its fold event, recurse on its miss
        have hSbound : uniformProb F (fun c =>
            ∃ w, relDist (f + c • g) w ≤ δ ∧
              AccClaim.Satisfies C (foldClaims foldRoot A l.claim c) w)
            ≤ errstar δ + 1 / (Fintype.card F : ℝ) :=
          foldClaims_sound_proximity_UD foldRoot hdC hMCA hδ0 hδB hδC hfar
        refine le_trans (uniformProb_mono (q := fun y =>
            (∃ w, relDist (f + y.1 • g) w ≤ δ ∧
              AccClaim.Satisfies C (foldClaims foldRoot A l.claim y.1) w) ∨
            (¬ (∃ w, relDist (f + y.1 • g) w ≤ δ ∧
                AccClaim.Satisfies C (foldClaims foldRoot A l.claim y.1) w) ∧
              ∃ w, relDist (foldWords (padSched y.2) (f + y.1 • g) gs) w ≤ δ ∧
                AccClaim.Satisfies C (aggregate foldRoot (padSched y.2)
                  (foldClaims foldRoot A l.claim y.1) ls) w))
          fun y hy => ?_) (le_trans (uniformProb_or_le _ _) ?_)
        · by_cases hc : ∃ w, relDist (f + y.1 • g) w ≤ δ ∧
              AccClaim.Satisfies C (foldClaims foldRoot A l.claim y.1) w
          · exact Or.inl hc
          · exact Or.inr ⟨hc, hy⟩
        have hfst : uniformProb (F × (Fin ls.length → F)) (fun y =>
            ∃ w, relDist (f + y.1 • g) w ≤ δ ∧
              AccClaim.Satisfies C (foldClaims foldRoot A l.claim y.1) w)
            ≤ errstar δ + 1 / (Fintype.card F : ℝ) := by
          rw [← uniformProb_equiv (Equiv.prodComm (Fin ls.length → F) F)
            (fun y => ∃ w, relDist (f + y.1 • g) w ≤ δ ∧
              AccClaim.Satisfies C (foldClaims foldRoot A l.claim y.1) w)]
          exact uniformProb_prod_le hε0 fun _ => hSbound
        have hsnd : uniformProb (F × (Fin ls.length → F)) (fun y =>
            ¬ (∃ w, relDist (f + y.1 • g) w ≤ δ ∧
                AccClaim.Satisfies C (foldClaims foldRoot A l.claim y.1) w) ∧
              ∃ w, relDist (foldWords (padSched y.2) (f + y.1 • g) gs) w ≤ δ ∧
                AccClaim.Satisfies C (aggregate foldRoot (padSched y.2)
                  (foldClaims foldRoot A l.claim y.1) ls) w)
            ≤ (ls.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)) := by
          refine uniformProb_prod_le
            (mul_nonneg (Nat.cast_nonneg _) hε0) fun c => ?_
          by_cases hSc : ∃ w, relDist (f + c • g) w ≤ δ ∧
              AccClaim.Satisfies C (foldClaims foldRoot A l.claim c) w
          · exact le_of_eq_of_le
              (uniformProb_false fun γv' hcon => hcon.1 hSc)
              (mul_nonneg (Nat.cast_nonneg _) hε0)
          · refine le_trans (uniformProb_mono fun γv' hcon => hcon.2) ?_
            refine ih gs (foldClaims foldRoot A l.claim c) (f + c • g) hlen'
              (Or.inl fun u hu hclose => ?_)
            by_contra hall
            push Not at hall
            exact hSc ⟨u, hclose, hu, hall⟩
        exact le_trans (add_le_add hfst hsnd) (le_of_eq (by ring))
      · -- the falsity sits deeper: recurse at EVERY head challenge
        refine le_trans (uniformProb_prod_le
          (ε := (ls.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)))
          (mul_nonneg (Nat.cast_nonneg _) hε0) fun c => ?_) ?_
        · refine ih gs (foldClaims foldRoot A l.claim c) (f + c • g) hlen'
            (Or.inr ⟨p, hpt, fun v hv hclose => ?_⟩)
          obtain ⟨i, hi⟩ := hpfar v hv hclose
          exact ⟨i, hi⟩
        · exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.le_succ ls.length) hε0
    -- transport along the head-splitting equivalence
    show uniformProb (Fin (ls.length + 1) → F) (fun γv =>
        ∃ w, relDist (foldWords (padSched γv) f (g :: gs)) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A (l :: ls)) w)
      ≤ ((ls.length + 1 : ℕ) : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ))
    calc uniformProb (Fin (ls.length + 1) → F) (fun γv =>
          ∃ w, relDist (foldWords (padSched γv) f (g :: gs)) w ≤ δ ∧
            AccClaim.Satisfies C
              (aggregate foldRoot (padSched γv) A (l :: ls)) w)
        = uniformProb (F × (Fin ls.length → F)) (fun y =>
            ∃ w, relDist (foldWords (padSched y.2) (f + y.1 • g) gs) w ≤ δ ∧
              AccClaim.Satisfies C (aggregate foldRoot (padSched y.2)
                (foldClaims foldRoot A l.claim y.1) ls) w) := by
          rw [← uniformProb_equiv (schedCons ls.length F) (fun γv =>
            ∃ w, relDist (foldWords (padSched γv) f (g :: gs)) w ≤ δ ∧
              AccClaim.Satisfies C
                (aggregate foldRoot (padSched γv) A (l :: ls)) w)]
          refine uniformProb_congr fun y => ?_
          obtain ⟨c, γv'⟩ := y
          show (∃ w, relDist (foldWords (padSched (Fin.cons c γv')) f
                (g :: gs)) w ≤ δ ∧
              AccClaim.Satisfies C (aggregate foldRoot
                (padSched (Fin.cons c γv')) A (l :: ls)) w) ↔ _
          rw [padSched_cons, foldWords_consSched, aggregate_consSched]
      _ ≤ ((ls.length : ℝ) + 1) * (errstar δ + 1 / (Fintype.card F : ℝ)) :=
          hprod
      _ = ((ls.length + 1 : ℕ) : ℝ)
            * (errstar δ + 1 / (Fintype.card F : ℝ)) := by push_cast; ring

/-- **[LC-sound], THE DEPLOYABLE HEADLINE.** A history chain carrying a
δ-far-false link — some link whose committed word has NO δ-close codeword
satisfying that link's claim — survives verification at ONE uniformly sampled
Fiat–Shamir challenge schedule with probability at most

  `ch.length · (err⋆(δ) + 1/|F|)`,

`err⋆` the mutual-correlated-agreement error (realized at unique decoding by
the landed WHIR Lemma 4.10 — free given a proximity generator), `1/|F|` the
per-fold exact-word term. This replaces `lightClient_attests`' ∀-schedule
hypothesis with one uniform draw: the contrapositive-probabilistic light
client. The event is anchored at the honest fold of the committed words
(`foldWords`); binding the prover's recommitments to that fold is
`[ACC-extract]`, and transporting "uniform schedule" to "hash-derived
schedule" is `[LC-sound-fs]` (end-of-file residuals). -/
theorem lightClientSound [Fintype F] [Nonempty ι] {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r} {ws : List (ι → F)}
    {f₀ : ι → F} {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ) (hlen : ws.length = ch.length)
    (hfalse : ∃ p ∈ ch.zip ws, ∀ v ∈ C, relDist p.2 v ≤ δ →
        ¬ AccClaim.Satisfies C p.1.claim v) :
    uniformProb (Fin ch.length → F) (fun γv =>
        ∃ w, relDist (foldWords (padSched γv) f₀ ws) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) w)
      ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)) := by
  refine lightClientSound_chain foldRoot hdC hMCA hδ0 hδB hδC herr0
    ch ws A₀ f₀ hlen (Or.inr ?_)
  obtain ⟨⟨lk, wd⟩, hp, hpfar⟩ := hfalse
  refine ⟨(lk, wd), hp, fun v hv hclose => ?_⟩
  by_contra hall
  push Not at hall
  refine hpfar v hv hclose ⟨hv, fun i => ?_⟩
  rw [halign lk (List.of_mem_zip hp).1 i]
  exact hall i

end Proximity

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All BUILT, all computing, over `LCExample`'s landed F₅ chains — REUSED, not
rebuilt. THE PAYOFF: `phantomChain` — the chain of two individually-false
claims that FORGED at the rigged schedule `(1,1)`
(`LCExample.phantom_forged`, the refuter of the naive one-shot form) — forges
at EXACTLY the diagonal schedules `{γ₀ = γ₁}`: 5 of the 25 sampled schedules,
probability `1/5 = 1/|F₅|`, the exact-word bound ATTAINED with equality. A
uniform sampler catches the phantom with probability 4/5; the ∀-schedule
quantifier is discharged by one draw at the proved price. -/

section KeystonePlumbing

private theorem eq_of_relDist_le_of_lt_inv_card {ι : Type*} [Fintype ι]
    [Nonempty ι] {F : Type*} [DecidableEq F] {f u : ι → F} {δ : ℝ}
    (h : relDist f u ≤ δ) (hδ : δ < 1 / (Fintype.card ι : ℝ)) : f = u := by
  by_contra hne
  exact absurd (le_trans (one_div_card_le_relDist hne) h) (not_le.mpr hδ)

end KeystonePlumbing

namespace LCSoundExample

open RSExample AccExample LCExample

/-- The forging set is the diagonal, in closed form: the phantom aggregate
verifies at a sampled schedule iff `γ₀ = γ₁` — the two false targets `1` and
`4 = −1` cancel exactly on the diagonal (`γ₀·1 + γ₁·4 = 0` in `F₅`). The
rigged `(1,1)` sits on it; the indicator `(1,0)` does not. -/
theorem phantom_verifies_iff (γv : Fin 2 → ZMod 5) :
    Verifies (reedSolomonCode dom₅ 2)
      (aggregate linRoot (padSched γv) phantomGenesis phantomChain)
    ↔ γv 0 = γv 1 := by
  have key : ∀ a b : ZMod 5, ((0 : ZMod 5) = 0 + a * 1 + b * 4 ↔ a = b) := by
    decide
  constructor
  · rintro ⟨fw, -, hc⟩
    exact (key (γv 0) (γv 1)).mp (hc 0)
  · intro h
    refine ⟨0, Submodule.zero_mem _, fun i => ?_⟩
    show (0 : ZMod 5) = 0 + γv 0 * 1 + γv 1 * 4
    rw [h]
    exact (by decide : ∀ b : ZMod 5, (0 : ZMod 5) = 0 + b * 1 + b * 4) (γv 1)

/-- The diagonal's probability, counted: 5 of 25 schedules — `1/5`. -/
private theorem diag_count :
    uniformProb (Fin 2 → ZMod 5) (fun γv => γv 0 = γv 1) = 1 / 5 := by
  classical
  unfold uniformProb
  rw [Nat.card_congr
    (⟨fun x => x.1 0, fun a => ⟨fun _ => a, rfl⟩,
      fun x => by
        obtain ⟨γv, h⟩ := x
        refine Subtype.ext (funext fun i => ?_)
        fin_cases i
        · rfl
        · exact h,
      fun a => rfl⟩ :
      {γv : Fin 2 → ZMod 5 // γv 0 = γv 1} ≃ ZMod 5)]
  rw [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  norm_num

/-- **The forging probability, EXACT**: the phantom chain's aggregate verifies
at a uniformly sampled schedule with probability EXACTLY `1/5 = 1/|F₅|` — the
sharp exact-word bound of `lightClientSound_exact` is attained. The chain
that beat one fixed schedule loses to a sampled one with probability 4/5. -/
theorem phantom_forging_prob :
    uniformProb (Fin 2 → ZMod 5) (fun γv =>
      Verifies (reedSolomonCode dom₅ 2)
        (aggregate linRoot (padSched γv) phantomGenesis phantomChain))
    = 1 / 5 := by
  rw [uniformProb_congr fun γv => phantom_verifies_iff γv]
  exact diag_count

/-- **Premise inhabitation — the general theorem FIRES on the phantom**:
`lightClientSound_exact` applied to the landed false chain, every hypothesis
(alignment, the unsatisfiable link witness) discharged by landed witnesses,
bound `1/5` — met with equality by `phantom_forging_prob`. -/
theorem phantom_caught_probably :
    uniformProb (Fin 2 → ZMod 5) (fun γv =>
      Verifies (reedSolomonCode dom₅ 2)
        (aggregate linRoot (padSched γv) phantomGenesis phantomChain))
      ≤ 1 / 5 := by
  have h := lightClientSound_exact linRoot phantomChain_aligned
    ⟨⟨0, 1, phantomClaim₀⟩, List.mem_cons_self ..,
      phantomClaim₀_unsatisfiable⟩
  simpa [ZMod.card] using h

/-- The rigged schedule `(1,1)` of `LCExample.phantom_forged` is IN the
forging set — it is a diagonal schedule. -/
example : Verifies (reedSolomonCode dom₅ 2)
    (aggregate linRoot (padSched ![1, 1]) phantomGenesis phantomChain) :=
  (phantom_verifies_iff _).mpr (by decide)

/-- The indicator schedule `(1,0)` of `LCExample.phantom_caught` is OUT — the
sampled verifier catches the phantom there, as at every off-diagonal draw. -/
example : ¬ Verifies (reedSolomonCode dom₅ 2)
    (aggregate linRoot (padSched ![1, 0]) phantomGenesis phantomChain) :=
  fun h => absurd ((phantom_verifies_iff _).mp h) (by decide)

/-- **Satisfiable side**: the honest keystone chain verifies at EVERY sampled
schedule — probability 1; sampling costs the honest prover nothing
(completeness `LCExample.goodChain_verifies`, untouched). -/
theorem goodChain_verifies_prob_one :
    uniformProb (Fin 2 → ZMod 5) (fun γv =>
      Verifies (reedSolomonCode dom₅ 2)
        (aggregate linRoot (padSched γv) genesis goodChain)) = 1 :=
  uniformProb_of_forall _ fun γv => goodChain_verifies (padSched γv)

/-- **The δ-headline FIRED** (premise inhabitation for `lightClientSound`):
over `C = ⊤` — where the landed `hasMutualCorrelatedAgreement_top_affine`
supplies mutual CA with `err⋆ = 0` and `minDistLB_inhabited` supplies
`dC = 1/4` — the phantom prover commits the zero word for both links, link 1
is δ-far-false at δ = 1/16 (quantization pins the δ-ball to the zero word,
which misses target 1), and the sampled δ-proximity event is bounded by
`2 · (err⋆ + 1/5) = 2/5`. Every hypothesis discharged by landed witnesses. -/
theorem phantom_delta_fired :
    uniformProb (Fin 2 → ZMod 5) (fun γv =>
        ∃ w, relDist (foldWords (padSched γv) 0 [0, 0]) w ≤ 1 / 16 ∧
          AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
            (aggregate linRoot (padSched γv) phantomGenesis phantomChain) w)
      ≤ 2 / 5 := by
  have hmax : max (1 - 1 / (Fintype.card (Fin 4) : ℝ) / 2) 0 = 7 / 8 := by
    rw [Fintype.card_fin, max_eq_left (by norm_num)]
    norm_num
  have h := lightClientSound linRoot (f₀ := (0 : Fin 4 → ZMod 5))
    (ws := [0, 0]) (δ := 1 / 16) phantomChain_aligned
    (minDistLB_inhabited _) hasMutualCorrelatedAgreement_top_affine
    (by norm_num) (by rw [hmax]; norm_num) (by norm_num [Fintype.card_fin])
    (le_refl 0) rfl
    ⟨(⟨0, 1, phantomClaim₀⟩, 0), List.mem_cons_self ..,
      fun v _ hclose => ?_⟩
  · have h' : (2 : ℝ) * (0 + 1 / 5) = 2 / 5 := by norm_num
    rw [← h']
    simpa [ZMod.card] using h
  · rintro ⟨-, hc⟩
    have h0v : (0 : Fin 4 → ZMod 5) = v :=
      eq_of_relDist_le_of_lt_inv_card hclose (by norm_num [Fintype.card_fin])
    have h1 := hc 0
    rw [← h0v] at h1
    exact absurd h1 (by decide)

/-- **The δ-event's TRUE probability**: exactly `1/5` — quantization pins the
δ-ball to the folded zero word, so the δ-event IS the diagonal again. The
headline's `2/5` holds with the union bound's factor-of-`n` slack visible:
per-step pricing pays `n·(err⋆ + 1/|F|)` where this two-link event costs
`1/5` — the δ-composition is honest, not tight. -/
theorem phantom_delta_prob_eq :
    uniformProb (Fin 2 → ZMod 5) (fun γv =>
        ∃ w, relDist (foldWords (padSched γv) 0 [0, 0]) w ≤ 1 / 16 ∧
          AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
            (aggregate linRoot (padSched γv) phantomGenesis phantomChain) w)
      = 1 / 5 := by
  have key : ∀ a b : ZMod 5, ((0 : ZMod 5) = 0 + a * 1 + b * 4 ↔ a = b) := by
    decide
  have hfold : ∀ γv : Fin 2 → ZMod 5,
      foldWords (padSched γv) (0 : Fin 4 → ZMod 5) [0, 0] = 0 := by
    intro γv
    show (0 : Fin 4 → ZMod 5) + padSched γv 0 • 0 + padSched γv 1 • 0 = 0
    simp
  have hev : ∀ γv : Fin 2 → ZMod 5,
      ((∃ w, relDist (foldWords (padSched γv) (0 : Fin 4 → ZMod 5) [0, 0]) w
          ≤ 1 / 16 ∧
        AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
          (aggregate linRoot (padSched γv) phantomGenesis phantomChain) w)
        ↔ γv 0 = γv 1) := by
    intro γv
    constructor
    · rintro ⟨w, hwc, -, hc⟩
      rw [hfold γv] at hwc
      have h0w : (0 : Fin 4 → ZMod 5) = w :=
        eq_of_relDist_le_of_lt_inv_card hwc (by norm_num [Fintype.card_fin])
      have h1 := hc 0
      rw [← h0w] at h1
      exact (key (γv 0) (γv 1)).mp h1
    · intro h
      refine ⟨0, ?_, Submodule.mem_top, fun i => ?_⟩
      · rw [hfold γv]
        simp [relDist]
      · show (0 : ZMod 5) = 0 + γv 0 * 1 + γv 1 * 4
        rw [h]
        exact (by decide : ∀ b : ZMod 5, (0 : ZMod 5) = 0 + b * 1 + b * 4)
          (γv 1)
  rw [uniformProb_congr hev]
  exact diag_count

end LCSoundExample

/-! ## Ledger, and what remains of [LC-sound] (honest residuals, prose)

**Closed here** (no sorry, no new axioms — `propext`, `Classical.choice`,
`Quot.sound` only):

* `lightClientSound_exact` — one uniform schedule catches any chain with an
  unsatisfiable link except with probability `1/|F|` (SHARP — the two-point
  extractor `link_satisfiable_of_verifies_pair` + per-coordinate
  conditioning); `lightClientSound_of_not_attests` is its `attests`-interface
  form. This is the ∀-schedule quantifier of `lightClient_attests`
  discharged: `∀ γs` becomes `Pr_γ` at the exhibited price, and
  `oneShot_lightClient_false`'s counterexample is priced exactly
  (`phantom_forging_prob` = the bound, attained).
* `lightClientSound` — the deployable δ-form: `n · (err⋆(δ) + 1/|F|)` for a
  chain with a δ-far-false link, whole-chain induction, per-step
  `foldClaims_sound_proximity_UD` (mutual CA consumed at UD — `[ACC-sound]`'s
  headline REUSED) composed by the Depth-toolkit union bound. The
  general-`err⋆` threading needed NO wiring beyond what AccSound exposes —
  the anticipated `[LC-sound-delta]` residual is EMPTY and is not named.

**Remaining, named, with realizers:**

* **[LC-sound-fs]** — this file samples the schedule UNIFORMLY (`uniformProb`
  over `Fin n → F`, fresh independent challenge per link). The deployed light
  client derives it by Fiat–Shamir from the transcript hash (σ-before-γ). The
  transport "uniform per-round challenge → ROM hash-derived challenge at the
  RBR price" is `Selvage/FiatShamir.lean`'s compilation (FS-of-RBR ⟺ [OB-2′],
  BCS bridge PROVED there, idealization `[FS-ROM]`), consumed once
  `[ACC-sound-rbr]` (named in `Selvage/AccSound.lean`) packages these per-fold
  bounds as an RBR round function. Nothing about the BOUNDS changes; only the
  sampler. — CLOSED at the fixed-chain level in `Selvage/LightClientFS.lean`
  (`lightClientFS_sound`/`lightClientFS_exact`: prefix distinctness proved,
  the FS-derived schedule IS the fresh coins, both bounds inherited verbatim);
  the `t`-query grinding strengthening is `[LC-fs-adaptive]` there.
* **[ACC-extract]** (unchanged, `Selvage/Accumulator.lean`) — both theorems here
  bound events at the HONEST fold interface: the exact form asks whether the
  aggregate claim is satisfiable at all; the δ-form anchors at
  `foldWords` of the committed words. Binding a forging PROVER's recommitted
  roots to that fold — replacing satisfiability by straightline-extracted
  witnesses — is the erasure-extraction obligation, riding WARP Thm B.4 =
  `OB2_depth_composition_nonneg_proved` (`Selvage/Depth.lean`, PROVED) through
  the same `[ACC-sound-rbr]` packaging.
* **[ACC-sound-list]** (unchanged, `Selvage/AccSound.lean`) — beyond unique
  decoding, `ℓ > 1` re-enters the δ-form's per-step price as
  `err⋆ + (s−1)·ℓ/|F|`; the chain composition here is regime-agnostic and
  will consume the Johnson-rung per-fold bound as-is.

**Audit notes (is the upgrade genuine, not vacuous?).** The exact theorem's
event is the SAME `Verifies ∘ aggregate` as `lightClient_attests`' hypothesis
— no strengthened event, no weakened conclusion; its hypothesis (one
unsatisfiable link) is the negation of `attests`' claim half. Non-vacuity is
computed: the phantom chain inhabits the hypothesis
(`phantomClaim₀_unsatisfiable`, landed) and its event probability is exactly
the bound (`phantom_forging_prob`), so the bound is tight and the event
nonempty (`phantom_forged`'s rigged schedule sits in it). The δ-form fires
end-to-end with every hypothesis discharged by landed witnesses
(`phantom_delta_fired`) and its true event probability computed
(`phantom_delta_prob_eq` — bound honest, slack visible). The honest chain
pays nothing (`goodChain_verifies_prob_one` = 1). -/

end Minidregg.Selvage
