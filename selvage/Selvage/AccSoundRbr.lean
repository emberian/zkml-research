/-
# Selvage.AccSoundRbr — [ACC-sound-rbr]: the γ-fold's bound as an RBR round error.

Closes the PACKAGING half of `Selvage/AccSound.lean`'s `[ACC-sound-rbr]` residual:
the accumulator's cross-word fold (WHIR Constr. 7.4, `Selvage/Accumulator.lean`'s
`foldClaims`) IS one round of an RBR game (`Selvage/Rbr.lean`'s WARP Def 4.2
vocabulary) — its challenge is a uniform field element, its per-round error is
`AccSound`'s proved bound. Supplying that error function in the exact shape
`RbrKnowledgeSoundness.err` expects is what lets `Selvage/FiatShamir.lean`'s
`FsOfRbrSound` (PROVED, unconditional) price the accumulator's Fiat–Shamir
compilation with the `(t + k)·ε_rbr` grinding factor — the connective tissue
`[LC-fs-adaptive]` (`Selvage/LightClientFS.lean`) names and rides.

## What is PROVED here (no sorry, no axioms)

* `accRbrError` — the round-error function: `err⋆(δ) + 1/|F|`, literally
  `foldClaims_sound_proximity_UD`'s RHS (WHIR Constr. 7.4 at `s = 2`, `ℓ = 1`,
  unique decoding), read as a bound on `Selvage/Rbr.lean`'s own `uniformProb`
  (imported, not re-derived — the SAME probability function `RbrKnowledgeSoundness
  .extract_sound` measures its per-round event with). At `errstar ≡ 0`
  (available whenever mutual CA is exact, e.g. `C = ⊤`,
  `hasMutualCorrelatedAgreement_top_affine`) it specializes to the exact-word
  bound `1/|F| = (s−1)/|F|`.
* `accSound_rbr` — **the round-error bound, PROVED**: the fold's δ-proximity
  event, measured by `uniformProb F` (`F` playing the role of an RBR round's
  challenge type `r.Chal`), is `≤ accRbrError`. This is `foldClaims_sound_proximity_UD`
  verbatim, renamed into Rbr's vocabulary — REUSE, no re-derivation.
* `accSound_rbr_exact` — the exact-word specialization (`errstar ≡ 0`), from
  `foldClaims_sound_exact` verbatim.
* `accRbrError_nonneg` — `accRbrError` is a legitimate `εrbr` candidate:
  nonnegative whenever `errstar` is (the first hypothesis `FsOfRbrSound` and
  `OB2_depth_composition` both demand of any uniform round-error bound).
* `accFsSound` — **[LC-fs-adaptive] discharged for the accumulator, MODULO the
  game instance**: given ANY `Reduction`/`RbrKnowledgeSoundness` pair whose
  per-round error is bounded by `accRbrError` on a statement set `Z` (exactly
  what `[ACC-sound-rbr-game]` below must supply), Fiat–Shamir of it is
  straightline knowledge-sound with the `(t + k)·accRbrError` grinding factor.
  Cites `fsKeystone_proved.sound` (`FsOfRbrSound`, `Selvage/FiatShamir.lean`,
  PROVED, unconditional) — does NOT re-derive the FS/BCS argument.

## What REMAINS: `[ACC-sound-rbr-game]` (honest residual, prose)

`accSound_rbr` supplies the NUMBER and the MEASURE (`uniformProb` over the
fold's own challenge field `F`) that a round of an RBR game must bound. It
does **not** assemble a concrete `Reduction`/`KStateFn`/`extract`/
`RbrKnowledgeSoundness r` quadruple for the accumulator — i.e. `accFsSound`'s
`rbr` and its `hbound` hypothesis are still supplied by the caller, not built
here. That assembly is `[ACC-sound-rbr-game]`, and it is genuinely heavy, not
bureaucratically heavy — an audit finding worth recording plainly:

* **The naive single-round embedding does not close.** The obvious attempt —
  one round, `Chal := F`, prover message trivial (`PMsg := Unit`, no
  interactive content before the challenge, matching the fold's actual
  shape), knowledge-state witness `W := (ι → F) × (ι → F)` (the claimed
  decomposition `(u, v)` of the folded word), `extract := id` — does **not**
  discharge `RbrKnowledgeSoundness.extract_sound` from `foldClaims_sound_proximity_UD`
  as stated. The obstruction is real, not a formalization nuisance: WARP
  Def 4.2's per-round bound is **unconditional** over every `(u, v)`
  satisfying the target relation at the extended transcript, whereas
  `foldClaims_sound_proximity_UD`'s hypothesis `hfar` is a **falseness**
  assumption (no NEARBY pair jointly satisfies the individual claims). Given
  an arbitrary claimed `(u, v) ∈ C × C` with `u + γ • v` merely `δ`-close to
  the fold `f + γ • g`, there is in general NO bound on how far `(u, v)` sits
  from the true `(f, g)`: since `C` is a linear code, `(u, v) ↦ u + γ • v` has
  a large kernel (`(c, 0)` and `(0, c/γ)` both sum to `c` for any codeword
  `c`), so closeness of the SUM to the fold says nothing about closeness of
  the SUMMANDS without the mutual-correlated-agreement argument's
  agreement-SET structure — which reads off `(u, v)` from the *specific*
  nearby codeword's disagreement pattern with `f + γ • g` (`AccSound`'s
  `hgood`/`hfu`/`hgv`), not from an externally supplied candidate pair. A
  faithful `extract` has to run that argument internally (Classical-choice
  the decomposition from the mutual-CA non-failure witness, δ-obliviously —
  Def 4.2 gives `extract` no `δ` input, so it must fix a canonical radius,
  naturally the unique-decoding one `dC/2` baked into the `Reduction`'s
  index data rather than threaded per-call).
* **The natural realizer is two-point, not one-point.** `Selvage/AccExtract.lean`'s
  `extractPair` — the straightline extractor this residual names as the
  intended realizer — recovers `(f, g)` from TWO fold evaluations at distinct
  challenges, not one. WARP's backward round extractor (Def 4.2) is seeded
  from a SINGLE extended transcript per round; reconciling that shape with a
  genuinely two-point recovery is exactly the `[ACC-extract]`/`[ACC-extract-chain]`
  machinery's job (`accKnowledgeSound`, `extractChain`'s per-link peeling),
  not a fix internal to a single round's `KStateFn`. The chain-level
  `Reduction` (`k` = the light-client's `n` links, one challenge per fold,
  matching `Selvage/LightClientFS.lean`'s schedule) is the right level for
  `[ACC-sound-rbr-game]`'s assembly, not a single fold in isolation — WARP
  Thm B.4's SR game already unions over *all* rounds' output-prefix queries,
  which is where the second evaluation a straightline extractor needs
  naturally arises.
* **What is NOT at risk**: the NUMBER (`accRbrError`) and its proof
  (`accSound_rbr`) are real theorems, unconditionally correct as bounds on
  `uniformProb F` events — nothing above casts doubt on the bound itself,
  only on the bureaucratic-looking-but-substantive work of exhibiting a
  `KStateFn`/`extract` pair whose OWN `extract_sound` event refines into
  (implies) the fold event `accSound_rbr` bounds. Realizer named:
  `Selvage/AccExtract.lean`'s `extractPair` + `Selvage/AccExtractChain.lean`'s
  `extractChain`, assembled at the chain level.
-/
import Selvage.AccSound
import Selvage.Rbr
import Selvage.FiatShamir

namespace Minidregg.Selvage

variable {Root : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]
variable {r : ℕ}

/-! ## `accRbrError` — the fold's round-error function -/

/-- **`accRbrError`** — the accumulator's cross-word fold, read as one round of
an RBR game: the per-round knowledge error at proximity `δ`, for challenge
field `F` and mutual-CA error `errstar`. Exactly `foldClaims_sound_proximity_UD`'s
RHS (WHIR Constr. 7.4, `s = 2`, `ℓ = 1`, unique decoding) — `err⋆(δ) + 1/|F|`.
At `errstar ≡ 0` this is `foldClaims_sound_exact`'s bound `1/|F| = (s−1)/|F|`,
so `accRbrError` covers both forms named by `[ACC-sound-rbr]`: the
δ-proximity headline generalizes the exact-word specialization. -/
noncomputable def accRbrError (F : Type) [Fintype F] (errstar : ℝ → ℝ)
    (δ : ℝ) : ℝ :=
  errstar δ + 1 / (Fintype.card F : ℝ)

omit [Field F] [DecidableEq F] in
/-- `accRbrError` at `errstar ≡ 0` computes to the plain `1/|F|` — independent
of `δ`, matching the exact-word case (which carries no proximity slack). -/
theorem accRbrError_const_zero [Fintype F] (δ : ℝ) :
    accRbrError F (fun _ => 0) δ = 1 / (Fintype.card F : ℝ) := by
  unfold accRbrError
  ring

omit [Field F] [DecidableEq F] in
/-- `accRbrError` is a legitimate uniform round-error bound whenever `errstar`
is nonnegative at `δ` — the first hypothesis `FsOfRbrSound` and
`OB2_depth_composition_nonneg` both demand of any candidate `εrbr`. -/
theorem accRbrError_nonneg [Fintype F] {δ : ℝ} {errstar : ℝ → ℝ}
    (herrstar : 0 ≤ errstar δ) : 0 ≤ accRbrError F errstar δ := by
  unfold accRbrError
  positivity

/-! ## `accSound_rbr` — the round-error bound, PROVED -/

/-- **[ACC-sound-rbr], the round-error bound.** The accumulator's cross-word
fold, at a uniformly random challenge `γ` ranging over `F` — `Selvage/Rbr.lean`'s
own `uniformProb`, the SAME probability function `RbrKnowledgeSoundness
.extract_sound` bounds its per-round event with, imported here (via
`Selvage/AccSound.lean`'s reuse) and not re-derived — satisfies the RBR
round-error bound `accRbrError`. Literally `foldClaims_sound_proximity_UD`,
renamed into Rbr's vocabulary: this is the shape match `extract_sound`
demands (a `uniformProb` event bounded by a `δ`-indexed real number), not
just the numeral — see the module header for the honest audit of how far
that shape match extends (as far as the BOUND; not, without further work, all
the way to a built `RbrKnowledgeSoundness` instance). -/
theorem accSound_rbr [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)} (foldRoot : Root → F → Root → Root)
    {A B : AccClaim Root F ι r} {f g : ι → F} {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (hfar : ∀ u ∈ C, ∀ v ∈ C, relDist f u ≤ δ → relDist g v ≤ δ →
      ∃ i, ¬(A.weights i u = A.targets i ∧ A.weights i v = B.targets i)) :
    uniformProb F (fun γ => ∃ w, relDist (f + γ • g) w ≤ δ ∧
        AccClaim.Satisfies C (foldClaims foldRoot A B γ) w)
      ≤ accRbrError F errstar δ :=
  foldClaims_sound_proximity_UD foldRoot hdC hMCA hδ0 hδB hδC hfar

omit [DecidableEq ι] in
/-- **[ACC-sound-rbr], the exact-word specialization.** A pair violating some
individual claim satisfies the fold with probability `≤ accRbrError F (fun _
=> 0) δ` for EVERY `δ` (the exact-word bound carries no proximity slack) —
`foldClaims_sound_exact` verbatim, renamed. -/
theorem accSound_rbr_exact [Fintype F] {C : Submodule F (ι → F)}
    (foldRoot : Root → F → Root → Root) {A B : AccClaim Root F ι r}
    {f g : ι → F}
    (hviol : ∃ i, ¬(A.weights i f = A.targets i ∧ A.weights i g = B.targets i))
    (δ : ℝ) :
    uniformProb F (fun γ =>
        AccClaim.Satisfies C (foldClaims foldRoot A B γ) (f + γ • g))
      ≤ accRbrError F (fun _ => 0) δ := by
  rw [accRbrError_const_zero]
  exact foldClaims_sound_exact foldRoot hviol

/-! ## `accFsSound` — [LC-fs-adaptive] discharged modulo the game instance -/

omit [Field F] [DecidableEq F] in
/-- **[LC-fs-adaptive], the accumulator's grinding-adversary bound — discharged
MODULO `[ACC-sound-rbr-game]`.** Given a reduction `red`, an RBR instance
`rbr`, a statement set `Z`, and a proof that `rbr.err` is bounded by
`accRbrError` on `Z` (exactly what `[ACC-sound-rbr-game]` above must supply,
using `accSound_rbr` at each round of the accumulator's actual game), the
Fiat–Shamir compilation of `red` is straightline knowledge-sound with the
`(t + k)·accRbrError` grinding factor — WARP Thm B.4's shape, `k` becoming the
chain length `n` once `[ACC-sound-rbr-game]` instantiates it at the
light-client's schedule. Cites `fsKeystone_proved.sound` (`FsOfRbrSound`,
`Selvage/FiatShamir.lean`, PROVED unconditionally from the discharged `[OB-2a]`)
— does NOT re-derive the FS/BCS argument, only supplies `accRbrError` as the
`εrbr` witness. -/
theorem accFsSound (red : Reduction) (rbr : RbrKnowledgeSoundness red)
    (Z : Set (Stmt red)) (Fchal : Type) [Fintype Fchal] (errstar : ℝ → ℝ)
    (hstar_nonneg : ∀ δ ∈ Set.Ioo (0 : ℝ) red.δstar, 0 ≤ errstar δ)
    (hbound : ∀ (i : Fin red.k) (st : Stmt red), st ∈ Z →
      ∀ δ ∈ Set.Ioo (0 : ℝ) red.δstar,
        rbr.err i st δ ≤ accRbrError Fchal errstar δ) :
    FsStraightlineKnowledgeSoundness red Z
      (fun _s t δ => ((t : ℝ) + (red.k : ℝ)) * accRbrError Fchal errstar δ) :=
  fsKeystone_proved.sound red rbr Z (accRbrError Fchal errstar)
    (fun δ hδ => accRbrError_nonneg (hstar_nonneg δ hδ)) hbound

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All BUILT over the landed F₅ instances (`AccSoundExample`'s headline and
exact-word keystones, `Selvage/AccSound.lean`) — `accRbrError` and `accSound_rbr`
FIRED on the SAME data those keystones already computed the fold event's
probability on, so the numbers agree by construction, not by coincidence. -/

namespace AccSoundRbrExample

open RSExample AccExample CRSExample AccSoundExample

/-- `accRbrError` on the concrete F₅ headline data computes to `1/5` for EVERY
`δ` — `errstar = 0` (available at `C = ⊤`, `hasMutualCorrelatedAgreement_top_affine`),
`|ZMod 5| = 5`. Not a free symbol: the SAME number `AccSoundExample.fold_proximity_prob_eq`
/ `fold_prob_eq` compute as the actual fold event's probability, below. -/
theorem accRbrError_zero_five (δ : ℝ) :
    accRbrError (ZMod 5) (fun _ => 0) δ = 1 / 5 := by
  unfold accRbrError
  norm_num [ZMod.card]

/-- **Satisfiable**: `accRbrError` computes, and the headline δ-proximity
event ATTAINS it exactly — `1/5 = err⋆ + (s−1)·ℓ/|F|` at `err⋆ = 0`, `s = 2`,
`ℓ = 1`, `|F| = 5`, reusing `AccSoundExample.fold_proximity_prob_eq` verbatim
(no re-computation). -/
theorem accRbrError_attained :
    uniformProb (ZMod 5) (fun γ =>
        ∃ w, relDist (xWord + γ • (0 : Fin 4 → ZMod 5)) w ≤ 1 / 16 ∧
        AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
          (foldClaims trivialRoot evalA evalB1 γ) w)
      = accRbrError (ZMod 5) (fun _ => 0) (1 / 16) := by
  rw [accRbrError_zero_five]
  exact fold_proximity_prob_eq

/-- **Premise-inhabitation**: `accSound_rbr`'s hypotheses (`hdC`, `hMCA`, `hδ0`,
`hδB`, `hδC`, `hfar`) are jointly, non-vacuously satisfiable — the general
round-error-bound theorem FIRES on landed witnesses. `accSound_rbr`'s proof
term IS `foldClaims_sound_proximity_UD` (`accRbrError` unfolds to its exact
RHS), so `AccSoundExample.fold_proximity_fired` — which discharges those same
six hypotheses against `minDistLB_inhabited`, `hasMutualCorrelatedAgreement_top_affine`,
and the `evalA`/`evalB1` claim pair — IS `accSound_rbr` fired on this data;
reused verbatim, not re-derived (the discharge needs a `Selvage/AccSound.lean`
`private` quantization lemma this file cannot see directly). -/
theorem accSound_rbr_fired :
    uniformProb (ZMod 5) (fun γ =>
        ∃ w, relDist (xWord + γ • (0 : Fin 4 → ZMod 5)) w ≤ 1 / 16 ∧
        AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
          (foldClaims trivialRoot evalA evalB1 γ) w)
      ≤ accRbrError (ZMod 5) (fun _ => 0) (1 / 16) := by
  rw [accRbrError_zero_five]
  exact fold_proximity_fired

/-- **Teeth**: a VIOLATING fold (the false link `evalB1` into the honest
`evalA`, exact-word case) hits `accRbrError` with EQUALITY — the bound is
attained, not slack, for an adversarial instance. Reuses
`AccSoundExample.fold_prob_eq` verbatim. -/
theorem accSound_rbr_exact_attained :
    uniformProb (ZMod 5) (fun γ =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2)
          (foldClaims trivialRoot evalA evalB1 γ) (xWord + γ • 0))
      = accRbrError (ZMod 5) (fun _ => 0) 0 := by
  rw [accRbrError_zero_five]
  exact fold_prob_eq

/-- The exact-word round-error theorem FIRED on the same violating instance:
`≤ accRbrError`, met with equality by `accSound_rbr_exact_attained` above —
teeth confirmed from the general theorem's side, not just the raw number. -/
theorem accSound_rbr_exact_fired :
    uniformProb (ZMod 5) (fun γ =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2)
          (foldClaims trivialRoot evalA evalB1 γ) (xWord + γ • 0))
      ≤ accRbrError (ZMod 5) (fun _ => 0) 0 :=
  accSound_rbr_exact (C := reedSolomonCode dom₅ 2) trivialRoot
    (A := evalA) (B := evalB1) (f := xWord) (g := 0) ⟨0, by decide⟩ 0

end AccSoundRbrExample

end Minidregg.Selvage
