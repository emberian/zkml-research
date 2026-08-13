# Multilinear PCS landscape — which one is *provable soonest* on top of Selvage?

**Lane**: research + design. Started 2026-08-13.
**Question**: of the hash-based multilinear PCS over a small prime field, which has the
shortest path from Selvage's existing machine-checked FRI/proximity cone to a
machine-checked *multilinear opening*? And what exactly would the theorem say?

**Status**: COMPLETE. Written incrementally; four paper-reading lanes integrated (§6 BaseFold
family, §7 jagged/adapters, §8 WHIR/STIR/MCA, §9 tensor codes). **The answer is §11**; the
master table is §12. Sections still marked ⟨draft⟩ are superseded by the lane findings that
follow them and are kept only to show what changed.

**One-line answer**: **BaseFold at Reed–Solomon, in Selvage's own unconditional `(1−ρ)/3` band,
packaged as an `RbrKnowledgeSoundness` instance** — five new items, no conjecture, no new
proximity result, and the commitment layer untouched. Then WHIR-UD. The highest-leverage
*independent* item is elementary MCA at the 1.5-Johnson bound (GKL / Khatam), which upgrades
the radius of everything downstream.

---

## 0. The headline, stated early so it is not lost

**The brief's framing of the gap is subtly wrong in a way that matters, and correcting
it makes the job much smaller.**

The brief says `OpeningScheme.openAt : (ι → F) → ι → Op` is "positional, i.e. a vector
commitment, the wrong shape for a multilinear claim", and that what is needed is
`openAt : (ι → F) → (Fin m → F) → Op`.

That second shape is the **KZG/homomorphic** shape: a point goes in, a short proof
object comes out, a verifier equation is checked. **No hash-based multilinear PCS has
that shape.** In BaseFold, WHIR, Ligerito, Blaze, and every Ligero/Brakedown descendant,
the commitment *is* a Merkle vector commitment to a codeword — exactly Selvage's
`OpeningScheme` — and the evaluation opening is an **interactive reduction** (a sumcheck
braided with a folding/proximity argument), made non-interactive by the BCS transform
**that Selvage already has proved at the deployed alphabet**.

So the correct Lean shape is not a new field in `OpeningScheme`. It is:

```lean
structure EvalClaim (Root F : Type*) (m : ℕ) where
  rt : Root            -- the SAME Merkle root the vector commitment produced
  pt : Fin m → F       -- the evaluation point
  val : F              -- the claimed value
```

plus an IOP whose round-by-round soundness is proved against `EvalClaim`, then compiled
by the existing `Selvage/Rbr.lean` → `Selvage/FiatShamir.lean` → `Selvage/AccRbrBcs.lean`
pipeline. `Commitment.lean` is **not the wrong shape**; it is the *right* shape and it is
already done. Changing `openAt`'s index type would build a KZG-shaped abstraction that no
hash-based scheme can instantiate — a mirror, not a bridge.

⚠ This is a **falsifiable** claim about every candidate below and it is the first thing
each candidate section checks.

**Second headline**: the single most valuable measured fact in this note is in §2 —
Selvage's FRI fold operator and Selvage's MLE fold operator are **already the same term**.
`Selvage/Proximity.lean:321` and `Selvage/MultiplicativeMleTerminal.lean:210` define the
same polynomial operation, and the second file already proves the fold stack lands on
`mle f r`. BaseFold's *completeness* direction is therefore a composition of theorems
Selvage already holds, not new work.

---

## 1. Inventory: what Selvage actually holds (read from source, 2026-08-13)

All paths relative to `/Users/ember/dev/minidregg/`.

### 1.1 The code

`Selvage/ReedSolomon.lean:87`
```lean
noncomputable def reedSolomonCode (dom : ι ↪ F) (d : ℕ) : Submodule F (ι → F) :=
  (Polynomial.degreeLT F d).map (evalOnDomain dom)
```
Note `dom : ι ↪ F` is an **arbitrary embedding** — not required to be a multiplicative
coset, not required to be smooth. The code layer is domain-general. `d` is the
*dimension* (degree bound), so rate ρ = d / |ι|.

`Selvage/ReedSolomon.lean:149` — minimum distance, attained form:
```lean
theorem reedSolomonCode_minDist (dom : ι ↪ F) (d : ℕ) :
    ∀ u ∈ reedSolomonCode dom d, ∀ v ∈ reedSolomonCode dom d, u ≠ v →
      1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ) ≤ relDist u v
```

### 1.2 The fold

`Selvage/Proximity.lean:178` — `FoldingData F dom domSq`, an abstract 2-to-1 structure
(`sq : ι → κ`, `neg : ι → ι`, `sec : κ → ι`) modelling `x ↦ x²`, with the coherence
proved rather than assumed (`neg_ne`, `neg_neg`, `sq_neg`, `eq_or_eq_neg_of_sq_eq`).

```lean
def fold (D : FoldingData F dom domSq) (f : ι → F) (α : F) : κ → F :=
  fun k => foldEven D f k + α * foldOdd D f k          -- :236,:240,:245

theorem fold_eval (p : Polynomial F) (α : F) (k : κ) :                    -- :321
    fold D (fun i => p.eval (dom i)) α k
      = (evenPart p + C α * oddPart p).eval (domSq k)

theorem fold_preserves_code {d : ℕ} {f : ι → F}                           -- :329
    (hf : f ∈ reedSolomonCode dom (2 * d)) (α : F) :
    fold D f α ∈ reedSolomonCode domSq d
```

### 1.3 The tower and the two directions

```lean
structure FoldingTower (F) [Field F] (ι : ℕ → Type*) (m : ℕ)              -- :377
def proximityTest (T) (deg : ℕ → ℕ) (f : ι 0 → F) (αs : ℕ → F) : Prop :=  -- :421
  T.word f αs m le_rfl ∈ reedSolomonCode (T.dom m) (deg m)

theorem proximity_complete (hdeg : ∀ j, j < m → deg j = 2 * deg (j+1))    -- :445
    (hf : f ∈ reedSolomonCode (T.dom 0) (deg 0)) (αs) : proximityTest T deg f αs

theorem proximity_sound_prob (hδ : 0 ≤ δ)                                 -- :706
    (hfold : ∀ j hj, FoldDistancePreserving (T.data j hj) (deg j) (deg (j+1)) δ b)
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    ((acceptSet T deg f).card : ℝ) / (Fintype.card F : ℝ) ^ m
      ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ)
```

The per-round hypothesis is isolated as a **definition**, not an axiom:
```lean
def FoldDistancePreserving (D) (dbig dsmall : ℕ) (δ : ℝ) (b : ℕ) : Prop :=  -- :486
  ∀ f : ι → F, ¬ close δ (reedSolomonCode dom dbig) f →
    ∃ bad : Finset F, bad.card ≤ b ∧
      ∀ α, α ∉ bad → ¬ close δ (reedSolomonCode domSq dsmall) (fold D f α)
```
and it is **discharged** twice: `foldDistancePreserving_of_lt_inv_card` (:855, the
trivial sub-1/|κ| regime, b = 1) and — the load-bearing one —
```lean
theorem foldDistancePreserving_of_isProximityGenerator                    -- :960
    (hPG : IsProximityGenerator (affineGenerator F) (reedSolomonCode domSq d) B err)
    (hδ0 : 0 < δ) (hδB : δ < 1 - B) (hb : err δ * (Fintype.card F : ℝ) ≤ (b : ℝ)) :
    FoldDistancePreserving D (2 * d) d δ b
```
whose engine is
```lean
theorem close_of_correlatedAgreement (D) {d} {f} {δ}                      -- :926
    (hCA : CorrelatedAgreement (reedSolomonCode domSq d) δ ![foldEven D f, foldOdd D f]) :
    close δ (reedSolomonCode dom (2 * d)) f
```
— *"correlated agreement of the two fold halves reflects closeness of the parent."*
**This is the single most reusable theorem in the cone for any candidate below.**

### 1.4 Correlated agreement

`Selvage/CorrelatedAgreement.lean`
```lean
def CorrelatedAgreement (C : Submodule F (ι → F)) (δ : ℝ) (f : Fin ℓ → ι → F) : Prop := -- :253
  ∃ S : Finset ι, (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) ∧ ∀ i, ∃ u ∈ C, AgreesOn S (f i) u

def IsProximityGenerator (G) (C) (B : ℝ) (err : ℝ → ℝ) : Prop :=                        -- :264
  ∀ f δ, 0 < δ → δ < 1 - B → err δ < G.pr (fun r => close δ C (comb r f)) → CorrelatedAgreement C δ f

def HasMutualCorrelatedAgreement (G) (C) (Bstar : ℝ) (errstar : ℝ → ℝ) : Prop :=        -- :289
  ∀ f δ, 0 < δ → δ < 1 - Bstar → G.pr (MutualCAFailure C δ f) ≤ errstar δ

theorem hasMutualCorrelatedAgreement_of_isProximityGenerator                            -- :325
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v) (hPG : IsProximityGenerator G C B err)
    (herr_mono) (herr_nonneg) :
    HasMutualCorrelatedAgreement G C (max (1 - dC / 2) B) err
```
CA ⟹ MCA **with the same `err`**, paying only a radius restriction to half the minimum
distance. Specialized to RS at `ReedSolomon.lean:207/220/237/256` (the last giving the
√ρ / Johnson-shaped bound `(1 + ρ)/2`).

### 1.5 The multilinear side

`Selvage/MultilinearExtension.lean` — `mle`, `chiEval`, `mle_multilinear`,
`multiAffine_eq_mle` (uniqueness), `roundPoly`/`roundSum` (sumcheck round algebra),
and
```lean
theorem mle_sumcheck_soundness {f} {prover} {H}                           -- :567
    (hpm : PrefixMeasurable prover)
    (hProverDeg : ∀ χ i, i < m → (prover χ i).degree < ((1+1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → F) (AdaptiveAcceptsFalse prover (mleHonest f) H (∑ b, f b))
      ≤ (m : ℝ) * (1 / Fintype.card F)
```
— **adaptive** (round-by-round / state-restoration flavoured) sumcheck soundness for the
multilinear case, error m/|F|. Degree bound is hard-wired to 1 here (`d = 1` passed to
`adaptive_sumcheck_soundness`), which is the degree-genericity gap SELVAGE.md §4 item 4
already names.

### 1.6 ⭐ The bridge that already exists

`Selvage/MultiplicativeMleTerminal.lean:210`
```lean
noncomputable def mleCoefficientFold (p : F[X]) (r : F) : F[X] := evenPart p + C r * oddPart p
```
Compare `Proximity.lean:321`'s `fold_eval` right-hand side: `evenPart p + C α * oddPart p`.
**These are the same term.** The codeword-level FRI fold induces, on the underlying
polynomial, *exactly* the MLE coefficient fold.

And the file closes the loop:
```lean
theorem foldMleVariables_booleanMobiusPolynomial (m : ℕ)                  -- :318
    (f : (Fin m → Bool) → F) (r : Fin m → F) :
    foldMleVariables m (booleanMobiusPolynomial m f) r = C (mle f r)
```
Möbius-transform the Boolean table into LSB-first monomial coefficients, apply the fold
stack at `r`, and the surviving constant **is the MLE at `r`**.

This is BaseFold's central algebraic identity, already machine-checked, at
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## 2. ⟨draft⟩ Candidate sections follow — see git history for incremental fills

### 1.7 The rest of the cone — larger than the brief assumed

Read from source, same date. **Selvage already holds most of WHIR's vocabulary**, not
merely "a univariate FRI".

| Object | Where | Status |
|---|---|---|
| WHIR **Def 4.5 constrained RS code** `CRS[F,L,m,ŵ,σ]` | `Selvage/ConstrainedCode.lean:158` `constrainedRS` | proved, with the *linear-weight* restriction stated honestly in the header (nonlinear ŵ explicitly out of scope) |
| Constraint batching, defect polynomial, `card_batch_satisfying_le` | same file, `:236–:393` | proved |
| **Out-of-domain sampling** — `oodEval`, list-size bound, unique pinning, OOD-as-a-linear-constraint | `Selvage/OutOfDomain.lean` `:207,:334,:410,:527,:571,:612` | proved |
| WHIR **Conjecture 4.12** as a named `Prop` (never an axiom), + the Haböck 2025/2110 bridge | `Selvage/JohnsonRegime.lean:457`, `Selvage/JohnsonMcaBridge.lean` | conjecture *named*, bridge proved, the hard core (`HaboeckTheorem2`) isolated as a hypothesis |
| Johnson list bound for RS | `JohnsonRegime.lean:403` | proved |
| **Adaptive, committed, queried FRI** — words and roots may depend on the challenge prefix; `m·b/|F| + (1−τ)^q` | `Selvage/HalfThresholdFriQuery.lean:415` `friAdaptive_sampled_sound` | proved (with an honest caveat: independent per-round query batches, not coherent paths — the coherent-path version needs a uniform-pushforward theorem for iterated squaring, named and not done) |
| `t` opened columns → full word (MDS/erasure lift) | `Selvage/Erasure.lean:128` `recoverFromColumns_sound` | proved for `t ≥ d` |
| Extension-field lifting, incl. `fold` commuting with lift | `Selvage/SmallField.lean:270` `fold_liftWord_mem` | proved |
| Constrained-mask surjectivity/hiding at `r` constraints (ZK) | `ConstrainedMaskMulti.lean:139,:188` | proved, bound `t + r ≤ d` |

### 1.8 The compilation pipeline is real, and it defines the deliverable's *shape*

`Selvage/Rbr.lean` transcribes WARP 2025/753 Defs 4.1/4.2/B.1/B.2 as **statements only**.
The composition theorem is proved next door:

- `Selvage/Depth.lean:545` `OB2_depth_composition_false` — the published Thm B.4 is
  **refuted** at `Z = ∅` (machine-checked), and
- `Selvage/Depth.lean:1982` `OB2_depth_composition_nonneg_proved` — the repaired obligation
  (nonnegativity guard on `εrbr`) is **PROVED**, no seam.

and there is a **worked instance to copy**: `Selvage/AccRbrInstance.lean` builds
`accReduction` / `accKState` / `accRbrKnowledgeSound` (all three Def-4.1 clauses proved,
`extract_sound` proved) and fires Fiat–Shamir on it (`accFsSound_native:813`).

**Therefore the deliverable for any candidate below is exactly one object:**

```lean
-- 1. the protocol as a WARP Reduction
def basefoldReduction (…) : Reduction := { Idx, X, A, X', A', W, n, n', R, R', k, PMsg, Chal, δstar, verify, … }
-- 2. the knowledge state function, three clauses proved
def basefoldKState (…) : KStateFn (basefoldReduction …) := { state, empty_iff, prover_monotone, full_iff }
-- 3. round-by-round knowledge soundness, extract_sound proved
def basefoldRbr (…) : RbrKnowledgeSoundness (basefoldReduction …) := { kstate, extract, err, extractTime, extract_sound }
```
and then `OB2_depth_composition_nonneg_proved` + `FiatShamir` + `AccRbrBcs` carry it to a
non-interactive verifier **for free**. Nothing about "a positional `openAt`" stands in the way.

`RbrKnowledgeSoundness.err : Fin r.k → Stmt r → ℝ → ℝ` is **per-round**, which is exactly
right for a braided protocol: the folding error and the sumcheck error land in the *same*
round's `err` and **add**, rather than needing a union bound over two independent
challenge spaces. This is a real structural fit, not a coincidence — WARP's Def 4.2 was
designed for exactly this.

---

## 2. The BaseFold bridge, priced against the actual Lean

This section is my own derivation from the source above; the paper-side confirmation is
§3 (lane reports). Read the two together before acting.

### 2.1 Completeness — a composition, ~200 lines, no new mathematics

Set `deg j := 2^(m-j)`, so `deg m = 1` (constants) and `deg j = 2 * deg (j+1)` — exactly
`proximity_complete`'s `hdeg` hypothesis, satisfied on the nose.

Three steps:

**(C1)** `booleanMobiusPolynomial m : ((Fin m → Bool) → F) → F[X]` is a linear bijection
onto `Polynomial.degreeLT F (2^m)`. The degree half is already proved
(`booleanMobiusPolynomial_coeff_eq_zero_of_two_pow_le`); the missing half is the inverse
`coeffsToTable p b := p.coeff (bitsToNat b)` and the round-trip. Both spaces have
dimension `2^m`; injectivity follows from `mle_injective` ∘ the terminal theorem. **~60–100 lines.**

**(C2)** The tower fold *is* the coefficient fold:
```lean
theorem word_eq_evalOnDomain_foldMle (T : FoldingTower F ι m) (p : F[X]) (αs : ℕ → F) :
    ∀ n (hn : n ≤ m),
      T.word (fun i => p.eval (T.dom 0 i)) αs n hn
        = fun k => (foldMleVariables n p (fun j : Fin n => αs j)).eval (T.dom n k)
```
Induction on `n`, one `fold_eval` per step. **~40 lines.** (`fold_eval`'s RHS is
`evenPart p + C α * oddPart p`, `mleCoefficientFold`'s body is `evenPart p + C r * oddPart p`
— *the same term*, so the step is `rfl` after rewriting.)

**(C3)** Compose with `foldMleVariables_booleanMobiusPolynomial` (already proved):
```lean
theorem basefold_terminal_is_mle (T : FoldingTower F ι m)
    (table : (Fin m → Bool) → F) (r : Fin m → F) (k : ι m) :
    T.word (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i)) (chalExt r) m le_rfl k
      = mle table r
```
**~30 lines.** The honest prover's terminal FRI word is the **constant word whose value is
the multilinear evaluation**. That is BaseFold's completeness, and it is a corollary.

⚠ Under-claim check: (C1)–(C3) are *my* derivation, not built. The signatures they cite
are real and quoted above; the line counts are estimates and the repo's own memory note
says my estimates have run ~10× long. Treat them as *shape*, not schedule.

### 2.2 Soundness — where the genuinely new work is, and it is one lemma-shaped thing

The naive soundness route **does not work and it is important to say why**, because it is
the trap a formalization lane would walk into:

> *"`f` is δ-close to codeword `u`; therefore `fold f α` is δ-close to `fold u α`."*

False in the useful direction. Folding is 2-to-1, so a corrupted position of `f` corrupts a
position of `fold f α` over a domain **half the size**: `relDist` can *double* each round,
giving `2^m δ` after `m` rounds. This is exactly why BaseFold/WHIR argue by the
**contrapositive** (far stays far) — which is precisely the shape Selvage already proved
(`FoldDistancePreserving`, `proximity_sound_prob`). Any lane that starts from "closeness is
preserved" has already lost.

So the residual content is:

**(S1) — REUSED, no new work.** *Far ⟹ far.* `foldDistancePreserving_of_isProximityGenerator`
(`Proximity.lean:960`) discharged from an `IsProximityGenerator` for the affine generator,
whose engine is `close_of_correlatedAgreement` (`:926`). Then `proximity_sound_prob` (`:706`)
for the tower, and `friAdaptive_sampled_sound` (`HalfThresholdFriQuery.lean:415`) for the
adaptive, committed, queried version.

**(S2) — the linking lemma. This is the new work, and I believe it is an MCA consequence.**
On the accepting path the verifier learns "each level's word is δ-close to *some* codeword".
Soundness needs more: that the level-(j+1) decoded codeword is *the fold of* the level-j
decoded codeword — otherwise the terminal constant is the MLE of *nothing in particular* and
the whole argument is vacuous. Ordinary correlated agreement does not give this; **mutual**
correlated agreement does, because MCA's failure event
(`MutualCAFailure`, `CorrelatedAgreement.lean:277`) is exactly *"the combination agrees with a
codeword but some component does not"* — the disagreement between "the fold decodes" and "the
parts decode".

Selvage holds MCA: `hasMutualCorrelatedAgreement_of_isProximityGenerator`
(`CorrelatedAgreement.lean:325`), CA ⟹ MCA with the **same `err`**, at radius
`max (1 - dC/2) B`; specialized to RS at `ReedSolomon.lean:207/220/237/256`.

**This is my central technical claim and it is the thing to check first against the papers:
that the "decoded codewords form a consistent fold chain" step is exactly an MCA
application, and that Selvage's `HasMutualCorrelatedAgreement` is the right shape for it.**
If true, BaseFold soundness on Selvage is: (S1) reused + (S2) an MCA corollary + (S3) below.
If false — if the chain-consistency needs a proximity result we do not hold — then BaseFold
is much further away than it looks and the honest verdict changes.

**(S3) — degree 2.** BaseFold's sumcheck is over `g(b) = f̃(b)·eq(z,b)`, degree **2** per
variable. `mle_sumcheck_soundness` (`MultilinearExtension.lean:567`) hard-wires `d := 1`
(`hProverDeg : (prover χ i).degree < ((1+1 : ℕ) : WithBot ℕ)`) even though the underlying
`adaptive_sumcheck_soundness` takes `d` as a parameter. Needed: a degree-2 `roundPoly`
(three interpolation points instead of two) and the multiaffine-times-multiaffine degree
lemma. This is SELVAGE.md §4 item 4 already, and it is on the critical path for **every**
candidate that uses a sumcheck — i.e. all of them.

**(S4) — the RBR packaging.** Build `Reduction` / `KStateFn` / `RbrKnowledgeSoundness` for
the braided protocol, copying `AccRbrInstance.lean`. The knowledge state at round `j` is a
conjunction: *"the level-`j` word is δ-close to the code"* ∧ *"the running sumcheck claim is
true of the decoded word's MLE"*. A δ-decoder by choice already exists as a pattern
(`AccRbrInstance.decodeLink:465`). `prover_monotone` should be nearly free (the state is
pending-blind, as in `accKState`); `extract_sound` is where (S1)+(S2)+(S3) get spent.

### 2.3 The commit shape — BaseFold reuses our commitment *unchanged*

BaseFold commits `evalOnDomain dom (booleanMobiusPolynomial m table)` — **an ordinary RS
codeword, Merkle-committed**. That is `Selvage/Commitment.lean`'s `OpeningScheme` /
`BindingCommitment` with **zero changes**, `[COMMIT-CR]` unchanged, `Erasure.lean`'s column
lift unchanged. Every piece of new work is in the *opening protocol*.

This is the criterion that should dominate the ranking, and §0 is its general form.

---

## 3. The Lean-shaped theorem statements

These are written in Selvage's actual vocabulary, so every identifier below either exists
today (quoted in §1) or is named as new. Paper-side confirmation of the *error terms* is
§4; the *shapes* are derived from the Lean and are the part I am most confident in.

### 3.0 The claim object, shared by every candidate

```lean
/-- A multilinear evaluation claim: the root the vector commitment produced, the point,
the value. Note `rt : Root` is the SAME `Root` as `Commitment.lean`'s — no new
commitment layer. -/
structure MleEvalClaim (Root F : Type*) (m : ℕ) where
  rt  : Root
  pt  : Fin m → F
  val : F

/-- What it MEANS for the claim to be true, for an RS-committed BaseFold/WHIR-shape
scheme: the root commits the RS encoding of the Möbius packing of some Boolean table
whose multilinear extension at `pt` is `val`. Every identifier here exists today. -/
def MleEvalClaim.Holds (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (c : MleEvalClaim Root F m) : Prop :=
  ∃ table : (Fin m → Bool) → F,
    c.rt = S.commit (fun i => (booleanMobiusPolynomial m table).eval (dom i)) ∧
    mle table c.pt = c.val
```

**Why this and not `openAt : … → (Fin m → F) → Op`:** the truth of the claim is a property
of the *committed word*, and the proof of it is a *transcript*, not a value. Making `Op`
carry the whole opening would force the abstraction to quantify over transcripts anyway —
i.e. it would be the `Reduction` below, wearing a function's clothes. Binding
(`S.commit_injective`, `Commitment.lean:161`) already makes `table` unique when it exists,
so `Holds` is a genuine predicate on `(rt, pt, val)` and not accidentally existential.

### 3.1 BaseFold — the RBR deliverable

The theorem is not one statement; it is **one instance and one bound**, because the
compilation to non-interactive is already proved (§1.8).

```lean
/-- The braided BaseFold opening as a WARP reduction: `k = m` rounds, one per variable;
the round-`i` challenge is BOTH the sumcheck challenge and the FRI folding challenge;
the prover's round message is (the round polynomial, the folded oracle). -/
noncomputable def basefoldReduction
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) (δstar : ℝ) : Reduction

/-- The Def-4.1 knowledge state: at a length-`j` transcript, the bit is 1 iff
  (a) the level-`j` word is δ-close to `reedSolomonCode (T.dom j) (deg j)`, AND
  (b) the running sumcheck claim is TRUE of the multilinear read off the decoded
      level-`j` codeword's coefficients.
Both clauses have existing vocabulary: (a) is `close δ (reedSolomonCode …)`
(`CorrelatedAgreement.lean:112`); (b) is `mle (coeffsToTable (codewordPoly …)) … = …`
using `OutOfDomain.lean:153`'s `codewordPoly` and the new `coeffsToTable` of §2.1 (C1). -/
noncomputable def basefoldKState (…) : KStateFn (basefoldReduction T deg δstar)

/-- The deliverable. `extract_sound` is the theorem; everything downstream is free. -/
noncomputable def basefoldRbr (…) : RbrKnowledgeSoundness (basefoldReduction T deg δstar)

/-- The BOUND — the thing to quote, per round. -/
theorem basefoldRbr_err_le
    (hfold : ∀ j hj, FoldDistancePreserving (T.data j hj) (deg j) (deg (j+1)) δ b)
    (hMCA  : ∀ j hj, HasMutualCorrelatedAgreement (affineGenerator F)
                       (reedSolomonCode (T.dom (j+1)) (deg (j+1))) Bstar errstar)
    (i : Fin m) (st) (hδ : δ ∈ Set.Ioo 0 δstar) :
    (basefoldRbr …).err i st δ
      ≤ (b : ℝ) / (Fintype.card F : ℝ)      -- folding: from hfold, REUSED
        + errstar δ                          -- chain consistency: from hMCA, REUSED
        + 2 / (Fintype.card F : ℝ)           -- degree-2 sumcheck round: NEW (S3)
```

and then, **already proved, no new work**:
`OB2_depth_composition_nonneg_proved` (`Depth.lean:1982`) turns the per-round `err` into
state-restoration soundness `≤ (t + m) · max_i err_i`; `FiatShamir.lean` +
`AccRbrBcs.lean` turn that into a non-interactive verifier at the deployed alphabet; and
`friAdaptive_sampled_sound` (`HalfThresholdFriQuery.lean:415`) supplies the `(1−τ)^q`
query term separately.

**What is quantified**: over the challenge space `Chal` (one round at a time — that is the
whole point of RBR), for *every* statement and *every* prover message, with `δ` universally
quantified over `(0, δstar)`. No expectation over the prover, no "for all efficient
adversaries" — knowledge soundness is via the carried extractor.

**What it assumes about the code and field**: RS over an arbitrary `dom : ι ↪ F`; the
folding needs a `FoldingData` (a 2-to-1 structure, i.e. a smooth/coset domain in
deployment); `Fintype F`; and — critically — `δ` in the regime where `hfold` and `hMCA` are
*dischargeable*. At unique decoding both are unconditional
(`foldDistancePreserving_of_lt_inv_card`, `hasMutualCorrelatedAgreement_of_isProximityGenerator`);
at Johnson they route through `JohnsonMcaBridge.HaboeckTheorem2`, which is a **named
hypothesis, not a theorem in the tree**; above Johnson they route through
`JohnsonRegime.WHIRConjecture412`, which is a **named conjecture**. This is the honest
regime ladder and it is already built.

**Small-field reality**: `Fintype.card F ≈ 2^31` makes every `1/|F|` term ≈ 2^-31, so `Chal`
must be an extension. `SmallField.lean` holds the lifting (`extension_secure_iff`,
`liftWord_mem_reedSolomonCode`, `fold_liftWord_mem:270`) — the challenge alphabet is `K`, a
degree-4 or -5 extension, and the fold commutes with the lift. Already there.

### 3.2 WHIR — the same deliverable, more rounds, better bound ⟨awaiting §4 confirmation⟩

WHIR is BaseFold's braid plus (i) `k`-ary folding instead of binary, (ii) a *domain shift*
each round (STIR's move), (iii) an out-of-domain sample each round to pin the decoded
codeword out of the list. In Selvage's vocabulary the extra ingredients are:
`OutOfDomain.lean`'s `oodEval` + `uniformProb_ood_pin_fails_le:527` + `oodConstraint:571`
+ `mem_constrainedRS_ood_iff:612` for (iii), and `ConstrainedCode.lean`'s `constrainedRS`
for the claim object — **all of which already exist**. (i) and (ii) do not.

```lean
theorem whirRbr_err_le (…) (i : Fin rounds) (st) (hδ : δ ∈ Set.Ioo 0 δstar) :
    (whirRbr …).err i st δ
      ≤ errstar δ                                    -- MCA (WHIR needs MUTUAL, not plain CA)
        + (oodListSize : ℝ) ^ 2 * (deg i : ℝ) / (Fintype.card F : ℝ)   -- OOD pinning
        + (foldArity : ℝ) / (Fintype.card F : ℝ)     -- sumcheck rounds inside one WHIR round
```

⚠ The error expression above is a **shape I expect, not a bound I have read**. The WHIR
lane is reading Theorem statements; §4 replaces this line or refutes it.

### 3.3 What "new work" means, made concrete

For BaseFold, the entire delta is:
| # | Item | Reuses | New |
|---|---|---|---|
| C1 | `coeffsToTable` + Möbius round-trip | — | linear-algebra lemma |
| C2 | tower fold = coefficient fold | `fold_eval` | induction |
| C3 | terminal word is the MLE | `foldMleVariables_booleanMobiusPolynomial` | corollary |
| S1 | far ⟹ far | `foldDistancePreserving_of_isProximityGenerator`, `proximity_sound_prob`, `friAdaptive_sampled_sound` | **nothing** |
| S2 | decoded chain is a fold chain | `hasMutualCorrelatedAgreement_of_isProximityGenerator` | the application ⟨key risk⟩ |
| S3 | degree-2 sumcheck | `adaptive_sumcheck_soundness` (already `d`-generic) | `roundPoly` at degree 2 |
| S4 | RBR packaging | `AccRbrInstance.lean` as template, `Depth.lean` composition, `FiatShamir` | instance + `extract_sound` |

**S2 is the whole risk.** If mutual correlated agreement does *not* suffice to pin the
decoded chain, BaseFold needs a proximity result we do not hold, and the honest verdict for
every RS-based candidate changes at once — because they all need the same step.

### 3.4 S3 verified at source (not relayed)

I claimed the sumcheck layer is "already degree-generic". **Checked**:
`Selvage/SumcheckReduction.lean:296`
```lean
theorem adaptive_sumcheck_soundness {v d : ℕ}
    {prover honest : (ℕ → F) → ℕ → Polynomial F} {H S : F}
    (hpm : PrefixMeasurable prover) (hhm : PrefixMeasurable honest)
    (hProverDeg : ∀ χ i, i < v → (prover χ i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ χ i, i < v → (honest χ i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest  : ∀ r i, i < v → (honest (chalOf r) i).eval 0 + (honest (chalOf r) i).eval 1
                                 = scChain S (honest (chalOf r)) (chalOf r) i) :
    uniformProb (Fin v → F) (AdaptiveAcceptsFalse prover honest H S)
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F)
```
`d` is a free parameter and the bound is `v·d/|F|`. `mle_sumcheck_soundness` merely
*instantiates* it at `d := 1`. So S3 is not "make the sumcheck degree-generic" — that is
done — it is only: **supply the honest degree-2 round-polynomial family for
`g(b) = f̃(b)·eq(z,b)` and discharge `hHonestDeg` + `hHonest` for it.** Concretely a
degree-2 `roundPoly` (Lagrange through three points instead of two) and the
"multiaffine × multiaffine is degree ≤ 2 per coordinate" lemma. This is the smallest item
on the list and it is **shared by every candidate**, so it should be done first regardless
of which scheme wins.

---

## 4. Extending the candidate list — what the brief did not name

Searched beyond the corpus because the local eprint mirror ends ~April 2026 and today is
2026-08-13. Instrument: `WebSearch` over eprint.iacr.org, plus `ls ~/paperbin | grep -iE …`
to check presence.

| Scheme | eprint | In `~/paperbin`? | Verdict for *us* |
|---|---|---|---|
| **Bolt** (Gurkan–Novakovic–Rothblum, Feb 2026) | 2026/310 | **absent** — fetched via `/tmp/eprint.sh 2026/310` | ⛔ see below |
| **LigeSIS** | 2026/751 | **absent** — fetched | ⛔ replaces Merkle with an SIS/lattice homomorphic hash over Goldilocks64. That swaps our `[COMMIT-CR]` floor for a *lattice assumption* and discards the hash-based premise entirely. Out of scope, but worth knowing it exists for the distributed-prover question. |
| Titan (IOPs over groups) | 2026/908 | absent | ⛔ group-based, not hash-based. |
| Vela / Carina | 2026/1438 | absent | ⛔ pairing-based. |
| "Multilinear polys via tree-based circuit + sumcheck" | 2026/1469 | absent | prover-side optimization, not a soundness route. |
| SwitchFold | 2026/1489 | present (`switchfold-code-agnostic-pcs-2026-1489.pdf`); **not in the eprint mirror** (`/tmp/eprint.sh 2026/1489` → `MISSING`) | assigned to the BaseFold lane |

### 4.1 Bolt (2026/310) — read directly, and it sharpens the whole ranking

Bolt is "code-switching": commit under a *cheap* code (a random LDPC), then switch to RS
and finish with **WHIR**. Its §2 cites `Theorem 2.7 (Constrained RS-IOPP [ACFY25])` — i.e.
WHIR — as a **subroutine**, and `Theorem 2.8 (Correlated Agreement for Linear Codes
[BKS18, Thm 4.1])`.

Two findings that matter to us:

1. **It confirms the modular decomposition.** A high-performance 2026 scheme is literally
   built as *(cheap code + code-switch) ∘ WHIR*. So a machine-checked WHIR/BaseFold is not
   only a scheme, it is the **composable core** the fast schemes are calling. That is an
   argument for formalizing the RS-based core first even on pure cost grounds.

2. **⛔ The code assumption is fatal for a Lean target, and this generalizes.** Bolt's
   distance is a property of a *randomly sampled* code:
   > "similarly to the codes that underlie [GLS⁺23, BCF⁺25] … distance δ **with high
   > probability**" (p.4, ll.182–184); "a good parity check matrix with high probability
   > (the associated codes are called random …)" (l.303); "induces a code of distance at
   > least 0.013 (with high probability)" (l.349); Theorem 6.1 is Gallager's ensemble
   > minimum-distance theorem.

   In Lean, `reedSolomonCode_minDist` is ~30 lines of Vandermonde. Replacing it with
   Gallager's random-ensemble distance theorem — plus the "sample once, then it is fixed
   forever" argument — is a **research-scale formalization of its own**, in combinatorics
   we hold none of. **The same objection applies to Brakedown, Blaze, and every
   expander/LDPC/RAA-code candidate**, and it is a stronger objection than their
   square-root verifier costs.

   ⚠ This is the single cleanest disqualifier in the whole landscape and it is *not* about
   speed: those schemes are faster. It is that their soundness rests on a distance
   parameter we cannot currently prove and would have to assume — turning a proved floor
   into a named assumption, which is exactly the move the repo's doctrine forbids doing
   quietly.

### 4.2 ArkLib — check before duplicating ⟨partial⟩

`SELVAGE.md` states "ArkLib's composition theorems are `sorry`". I did **not** verify that
at source. What I did verify: the ArkLib README lists as *actively being worked on*
Sum-Check, Spartan, Merkle Trees, **FRI and coding theory prerequisites**, **STIR and
WHIR**, and Binius; BaseFold and multilinear PCS are not named. Completion status is not
stated on the README. Corpus: `~/paperbin/arklib-rwc2026-compositional-fv-snarks-slides.pdf`
mentions FRI / STIR / WHIR / Binius as a layer diagram only.

**Action before any build**: clone ArkLib and count `sorry` in its STIR/WHIR cone. If their
WHIR is real, the right move may be to *use* it rather than rebuild — and if it is `sorry`,
that is worth saying precisely rather than by reputation.

---

## 5. ⭐ CORRECTION to §2.2 — S2 is *not* the risk I said it was, and the fix is elementary

I wrote in §2.2 that the fold-chain-consistency step (S2) "is an MCA consequence" and
called it "the whole risk". **That is true only in the list-decoding regime. At a modestly
reduced radius it is elementary, and Selvage already selects exactly that radius.**

### 5.1 The elementary argument

The step needed is: *on an accepting transcript, the codeword each level decodes to is the
fold of the previous level's.* Without it the terminal constant is the MLE of nothing in
particular and the whole scheme is vacuous.

At level `j`, write `π_j` for the word and `u_j` for a codeword with `relDist π_j u_j ≤ δ`.

1. **Folding at most doubles relative distance.** If `f` and `u` agree at both `sec k` and
   `neg (sec k)` then their folds agree at `k`; the fibres `{sec k, neg (sec k)}` are
   disjoint across `k`, so `#disagree_κ ≤ #disagree_ι`, and since
   `Fintype.card ι = 2 * Fintype.card κ` (**proved**, `Proximity.lean:908`
   `card_eq_two_mul_card`, via `card_sq_preimage:881`):
   ```lean
   theorem relDist_fold_le (D : FoldingData F dom domSq) (f u : ι → F) (α : F) :
       relDist (fold D f α) (fold D u α) ≤ 2 * relDist f u
   ```
   **NEW, ~40 lines, elementary counting.** Every ingredient is present.

2. `fold D u_j α ∈ reedSolomonCode domSq (deg (j+1))` — **proved**, `fold_preserves_code`
   (`Proximity.lean:329`).

3. So `fold D u_j α` and `u_{j+1}` are two codewords, at distance `≤ 2δ` and `≤ δ` from
   `π_{j+1}`; triangle gives `relDist (fold D u_j α) u_{j+1} ≤ 3δ`. If `3δ < dC` they are
   **equal**, by a mild generalization of the **already-proved**
   ```lean
   theorem codeword_eq_of_close_of_close [Nonempty ι] {C} {dC δ}     -- CorrelatedAgreement.lean:165
       (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
       (hu : u ∈ C) (hv : v ∈ C) (hδ : δ < dC / 2)
       (hgu : relDist g u ≤ δ) (hgv : relDist g v ≤ δ) : u = v
   ```
   (its body is four lines of `relDist_triangle` + `linarith`; the asymmetric version
   `relDist g u ≤ δ₁ → relDist g v ≤ δ₂ → δ₁ + δ₂ < dC → u = v` is the same proof).

With `dC = 1 - (d-1)/n ≈ 1 - ρ` (`reedSolomonCode_minDist`, **proved**), the condition is

> **δ < (1 − ρ) / 3.**

### 5.2 ⭐ Selvage already has exactly this regime, unconditionally

`Selvage/RateRegimeSelector.lean:138` — the `RateRegimeRequest.oneThirdUD` constructor:
```lean
(hband : ∀ j, j < m →
    delta < 1 - (2 + (deg (j + 1) : ℝ) / (Fintype.card (ι (j + 1)) : ℝ)) / 3)
```
`1 - (2 + ρ)/3 = (1 - ρ)/3`. **The same radius, arrived at independently.** It is one of
four typed regimes the selector exposes (`exactSubquant`, `oneThirdUD`, `halfThenUD`,
`haboeckJohnson`), each carrying `PlainRSCapacityGuard` and *"selects a typed certificate
for the event each landed theorem actually controls"* — refusing, by construction, to
"turn the different rate regimes into one fictitious radius theorem"
(`no_plain_rs_capacity_guard_at_capacity:38`).

This is not a coincidence: the `(1−ρ)/3` radius arises from the *same* factor-2 fold blowup
plus triangle inequality. The unconditional FRI branch and the unconditional BaseFold
chain-consistency step want the same band.

### 5.3 The revised risk picture — a three-tier answer

| Tier | Radius | Chain consistency from | Status of the ingredients |
|---|---|---|---|
| **1** | `δ < (1−ρ)/3` | triangle + `codeword_eq_of_close_of_close` + `relDist_fold_le` | **fully proved except one ~40-line counting lemma.** No conjecture, no named hypothesis. |
| **2** | `δ < 1 − √ρ` (Johnson) | mutual correlated agreement | routes through `JohnsonMcaBridge.HaboeckTheorem2` — a **named hypothesis**; its hard core (Guruswami–Sudan over `F(Z)`, Hensel lifting, useful-factor) is unformalized and Selvage says so. |
| **3** | `δ → 1 − ρ` (capacity) | `JohnsonRegime.WHIRConjecture412` | a **named conjecture** — and see §5.4. |

The cost of Tier 1 versus Tier 2 is **query count**, i.e. proof size, not soundness: `t ≈
λ / log₂(1/(1−δ))`, so a radius of `(1−ρ)/3` instead of `1−√ρ` costs roughly a constant
factor more openings. **That is a proof-size tax, and it buys an unconditional theorem.**
For a first machine-checked multilinear PCS that is obviously the right trade.

### 5.4 ⚠ Tier 3 is not merely unproved — the corpus contains refutations at prime fields

The capacity-regime proximity-gap conjectures are **disproved**, and the papers are already
here (names as filed; I have not re-read their theorem statements in this pass and am
citing their presence and titles, not a bound):
`crites-stewart-DISPROOF-capacity-proximity-gap-conjectures-2025-2046.pdf`,
`fri-proximity-gaps-conjectures-DISPROVED-2025-2046.pdf`,
`krachun-kazanin-habock-proximity-gap-FAILURE-prime-fields-2026-782.pdf`,
`kambire-arxiv2604.09724-proximity-gaps-fails-near-capacity-prime-fields.pdf`,
`bchks-proximity-gaps-BINARY-COUNTEREXAMPLES-2025-2055.pdf`,
`failure-proximity-gaps-capacity-2026-782.pdf`.

**We are on a 31-bit prime field.** Any recommendation that reaches for the capacity regime
to make the numbers look good is reaching for something the corpus says fails *in our
setting*. Tier 3 is off the table; the real choice is Tier 1 versus Tier 2.

### 5.5 The Tier-1 error budget, with every term sourced

The unconditional band's fold theorem, read at source:
```lean
theorem foldDistancePreserving_UD                            -- ProximityGapUD.lean:534
    (D : FoldingData F dom domSq) (d : ℕ) {δ : ℝ} (hδ0 : 0 < δ)
    (hδB : δ < 1 - (2 + (d : ℝ) / (Fintype.card κ : ℝ)) / 3) :
    FoldDistancePreserving D (2 * d) d δ (Fintype.card κ)
```
— unconditional, with bad-set size `b = |κ|` (i.e. `err δ = n/|F|`). Its sharpening to the
full unique-decoding band `δ < (1−ρ)/2` exists but is **conditional on a named hypothesis**:
```lean
theorem foldDistancePreserving_UD_full                       -- ProximityGapUDTight.lean:1002
    (hPS : PolishchukSpielman F) … (hδB : δ < 1 - (1 + (d : ℝ) / (Fintype.card κ : ℝ)) / 2) :
    FoldDistancePreserving D (2 * d) d δ (Fintype.card κ)
```

So the **per-round RBR error for Tier-1 BaseFold** is

| term | value | source | new? |
|---|---|---|---|
| folding (far ⟹ far) | `n / |K|` | `foldDistancePreserving_UD` + `proximity_sound_prob` | **no** |
| fold-chain consistency | **0** | deterministic at `3δ < 1−ρ` (§5.1) | one ~40-line lemma |
| sumcheck round (degree 2) | `2 / |K|` | `adaptive_sumcheck_soundness` at `d := 2` | honest degree-2 round poly |
| query/spot-check | `(1−τ)^q`, added once not per round | `friAdaptive_sampled_sound` | **no** |

⭐ **The chain-consistency term is ZERO at Tier 1**, because `codeword_eq_of_close_of_close`
is a deterministic uniqueness statement, not a probabilistic one. This is the strongest
single reason to do Tier 1 first: it removes a whole error term *and* a whole conjecture.

`|K|` must be an extension of the 31-bit base field — `n/|K|` with `n = 2^24` and
`|K| = 2^31` is `2^-7`, useless; with a degree-4 extension `|K| = 2^124` it is `2^-100`.
`SmallField.lean` holds the lift and `fold_liftWord_mem:270` proves the fold commutes with
it, so this is configuration, not work.

---

## 6. Paper-side findings — BaseFold family (lane report, integrated)

Corpus: all six BaseFold-family papers present on disk; text extraction succeeded for all
six, bounds checked against page images rather than text dumps.

### 6.1 ⭐ The paper confirms §5.1 — my triangle argument *is* BaseFold's Lemma 8

ZCF23 (2023/1705, the Nov 2 2023 preprint on disk) — **Lemma 7 (p.24)** requires, among
its hypotheses, **`3δ − dγ < Δ_{C_d}`**. And **Lemma 8 (p.25)**, the braiding lemma, is
proved exactly as I derived it in §5.1:

> "π_{i−1}[μ] is a bad query entry only if both μ and μ+n_{i−1} are bad query positions for
> π_i" (halving the bad count per level) ⟹ `Δ(fold_{r_k}(π_{k+1}), π_k) < δ′` ⟹ with
> `Enc_k(f_k) = fold_{r_k}(Enc_{k+1}(f_{k+1}))`, the triangle inequality gives
> `Δ(π_k, Enc_k(f_k)) ≤ δ′ + Δ*(π_{k+1}, Enc_{k+1}(f_{k+1}))`; a wrong decode at level k
> forces `Δ_{C_k} ≤ 3δ − γd`, contradiction.

The lane's summary: *"That '3δ' is the whole story of ZCF23's weak regime. The braiding is
made safe by forcing two distinct codewords to be too close."* — the same mechanism as
`codeword_eq_of_close_of_close`.

**So `δ < (1−ρ)/3` is not a concession I invented; it is BaseFold's own published regime
at RS**, and the Lean ingredients for it are the ones §5.1 lists.

⭐ **And we can do it without the paper's second distance notion.** ZCF23 threads a *coset*
distance `Δ*` (Definition 2: pairs `(j, j+n/2)` count as one disagreement) through
Definition 2 → Lemma 6 → Theorem 3 → Lemma 7/8 → Theorem 4, purely to keep the fold from
losing a factor 2. Selvage's `relDist` is plain Hamming. **The crude bound
`relDist (fold f α) (fold u α) ≤ 2 · relDist f u` (§5.1 item 1) reaches the same `3δ`
without introducing `Δ*` at all** — one ~40-line counting lemma instead of a second
distance notion threaded through five results. That is a genuine simplification of the
paper for the Lean route, and it is worth stating as such.

### 6.2 ⭐⭐ The better target is Haböck 2024/1571, not ZCF23 — and the reason is our pipeline

Haböck, *"BaseFold in the List Decoding Regime"*, re-proves the same protocol (RS only) as
**round-by-round soundness** — which is **exactly the shape `Selvage/Rbr.lean` consumes and
`Depth.lean` composes**. Theorem 1 (p.11), verbatim:

> **Theorem 1 (Basefold soundness).** Protocol 2 as an interactive oracle proof for R
> satisfies round-by-round soundness, with round-by-round soundness error
> `ε ≤ max { ε(C₀, M, 1, θ), 1/|F| + ε(C₁,1,B₁,θ), …, 1/|F| + ε(C_n,1,B_n,θ), (1 − θ)^s }`.

with `B_i = |D|/|D_i| = 2^i` and target relation (Eqn 9) a *correlated-agreement-shaped*
relation, not "the committed word is a codeword":
```
R = { (g₀,…,g_M) : ∃p₀,…,p_M ∈ P_n, d((g₀,…,g_M),(p₀,…,p_M)) < θ
                   ∧ ⋀_k P_k(ω₁,…,ω_M) = v_k, P_k = Φ_n^{-1}(p_k) }
```

Structural comparison, and it is decisive:

| | ZCF23 (2023/1705) | Haböck (2024/1571) |
|---|---|---|
| soundness shape | asymptotic — "non-negligible probability", bad event `B2` defined via a *negligible function* | **round-by-round**, concrete per-round `max` |
| lemma count, accept ⟹ claim | Lemma 6 + Thm 3 + Claim 1 + Lemma 8 + Lemma 7 + Lemma 9 + Lemma 10 + Thm 4, plus an asymptotic layer | **Lemma 1 + Lemma 2 + Lemma 3 + Theorem 3** |
| standalone sumcheck on the critical path | yes, total degree 2d, error `2d/|F|` | **no** — the only sumcheck-flavoured term is a single `1/|F|` "for the possible zero of the Lagrangian" |
| second distance notion | yes (`Δ*`, coset) | no |
| regime | `δ < min(J_γ(J_γ(Δ)), (Δ+dγ)/3)` — at RS the `3δ` binds, so `(1−ρ)/3` | `θ = 1 − (1+1/2m)√ρ` (Johnson), **and p.11: "the entire analysis … carries over verbatim to the unique decoding regime, with the adapted soundness errors for Theorem 3."** |
| codes | general foldable (needs the random-code distance theorem) | **RS only** |
| queries for λ=100 | ℓ ≈ 185 at RS ρ=1/16 *(lane's arithmetic)* | s ≈ 50 *(lane's arithmetic)* |

**Haböck's setup matches our Lean's generality exactly**: `C₀ = RS_{2^n}[F,D]` with **D any
union of cosets** of the smooth subgroup — his fn.2 says the larger-subgroup assumption
"is not necessarily needed". Selvage's `reedSolomonCode (dom : ι ↪ F) (d : ℕ)` over an
arbitrary embedding is *already* at that generality.

### 6.3 The two real gaps on the Haböck route

**(G1) Weighted correlated agreement.** Haböck's *folding* rounds (Lemma 2) need
**Theorem 3**, correlated agreement against a sub-probability measure `μ` whose density
`δ : D → [0,1] ∩ ℚ` has common denominator `B_i = 2^i` (the measure is built by Eqns
29–30: `δ_i(x) = δ*_{i−1}(x)` if the fold check passes at `x`, else 0, with
`δ*_{i−1}(x²) = ½(δ_{i−1}(x) + δ_{i−1}(−x))`). Selvage's `CorrelatedAgreement` is the
**uniform counting measure** (`(1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ)`). *Batching*
(Lemma 1) needs only the unweighted Theorem 2.

→ **This is the single largest new Lean surface on the Haböck route.** Mitigation, from the
paper itself (p.11): in the **unique decoding regime** the weighted CA statement is
elementary. A UD-regime Haböck-shaped Lean proof is plausibly the cheapest real
multilinear-PCS soundness theorem available — **and it is already better than ZCF23's
(1−ρ)/3**.

**(G2) ⚠ Subcode correlated agreement needs an intermediate Selvage does not expose.**
Haböck's Theorem 2 (CA for a *linear subcode* `C′ ⊆ RS`) is proved (§4.1) by a short
Vandermonde argument *on top of* [BCIKS20] Proposition 2, which supplies the polynomial
`P(X,Z) = p₀(X) + Z p₁(X) + … + Z^M p_M(X)` agreeing with the proximates at `> |S|/(2ℓ_m)`
points `z`; with `≥ M+1` such `z_i` in the subcode, `Λp₀ = … = Λp_M = 0` by Vandermonde.

Selvage's `IsProximityGenerator` concludes only `CorrelatedAgreement C δ f`, i.e.
`∃ S, … ∧ ∀ i, ∃ u ∈ C, AgreesOn S (f i) u` — **the final ∃-set, not the `P(X,Z)`
intermediate.** So the subcode upgrade does *not* go through from Selvage's current
interface. Either the interface must expose the `P(X,Z)` witness, or the subcode CA must be
proved directly in the regime chosen (elementary in UD, plausibly).

⚠ This is the sharpest concrete finding in the lane report and I am recording it as an
**unresolved item**, not a solved one.

### 6.4 Convention: Selvage is already on ZCF23's side of a real fork

- **ZCF23** identifies the multilinear's **coefficients** with the univariate's
  coefficients; fold is `fold_α(v) = u + α·u′`.
- **Haböck** identifies the multilinear's **values on `H_n`** with the univariate's
  coefficients; fold is `(1−λ)·even + λ·odd` (the multilinear-specialization convention).
  He flags the alternative himself (p.8): coefficients-to-coefficients "[= WHIR] works in a
  similar manner, but comes with higher encoding costs for most applications".

Selvage's `mleCoefficientFold p r = evenPart p + C r * oddPart p` and
`foldMleVariables_booleanMobiusPolynomial` are **ZCF23's convention, verbatim**, and they
match `fold`/`fold_eval` on the nose. Following Haböck *literally* would mean either
reparameterizing the challenge — `(1−λ)e + λo = (1−λ)(e + (λ/(1−λ))o)`, a Möbius
reparameterization, so **a uniform λ does not map to a uniform α** and the reparameterization
is *not* free inside probability statements — or redoing his §5 in our convention. His §4
(the CA strengthening) is **convention-independent**.

🐞 The lane also caught a **typo on Haböck p.10**: as typeset, both fold numerators read
`f_{i−1}(x) + f_{i−1}(−x)`; the odd part must be the **difference** over `2x`. Verified
against the page image. Do not transcribe as printed.

### 6.5 ⚠⚠ WHIR's list-decoding soundness is CONJECTURAL, and 1571 §6.4 says MCA is avoidable

Haböck §6.4 (p.31), verbatim:

> "While [ACFY24] prove the soundness of WHIR in the unique decoding regime, their analysis
> in the list decoding regime is based on a **conjectured** correlated agreement property,
> called **mutual correlated agreement** … we choose a different path, demonstrating that
> such a global correlated agreement property is **not needed**. Instead, the …
> generalization of the subcode correlated agreement theorem, Theorem 4, is again
> sufficient."

This lands directly on my §2.2. Selvage's `hasMutualCorrelatedAgreement_of_isProximityGenerator`
proves CA ⟹ MCA only at `max (1 − dC/2) B` — i.e. **at unique decoding**; above that,
Selvage correctly carries MCA as `JohnsonRegime.WHIRConjecture412`, a *named conjecture*.
That is consistent with the paper and it means:

- my original §2.2 framing (S2 = "an MCA application") pointed at the *conjectural* leg;
- §5's correction (S2 = elementary triangle at `(1−ρ)/3`) is the **unconditional** leg, and
  is also what ZCF23 actually does;
- and there is a **third** option — Haböck's Theorem 4 route — which reaches the Johnson
  regime *without* MCA, at the cost of the weighted/subcode CA work of (G1)+(G2).

### 6.6 Commit shape — confirmed, and it is the best news in the report

Both papers, at RS: **the commitment is an ordinary FRI/RS Merkle commitment, unchanged.**

- ZCF23 p.20, verbatim: *"the commitment to f is simply the oracle π_f … The derived
  commitment in the random oracle model is the root of the Merkle tree with leaves being
  the vector π_f ∈ F^{c2^d}."*
- Haböck p.8: *"it is committed as word f ∈ C₀, by evaluating p(X) on the evaluation
  domain D."*

One oracle. No interleaved matrix, no different leaf layout, no rate change. The opening
adds only the FRI round oracles (which *are* the folding tower) plus, **in plain**, the
round polynomials. ZCF23's tie-off (step 3, p.21) is that the **verifier re-encodes a
single field element** under the base code and compares to the last oracle —
`Enc₀(h₁(r₀)/ẽq_z(r₀,…,r_{d−1})) = π₀`.

**`Selvage/Commitment.lean` is untouched. `[COMMIT-CR]` is untouched. `Erasure.lean` is
untouched.** Everything is in the opening protocol, as §0 predicted.

### 6.7 Corrections to my earlier assumptions

- **Random foldable codes are not "conjectured distance"** — ZCF23 Theorem 2 (p.13) is a
  *proved* probabilistic bound, `Pr[∃ m ≠ 0, nzero(Enc_d(m)) ≥ t_d] ≤ d·2^{−λ}` over the
  code sampling. It is still a per-*ensemble*, not per-instance, guarantee that a
  formalization must carry, and the concrete numbers are weak (Δ ≈ .5044 at c=16, |F|=2^31,
  versus **Δ = .9375 for RS at the same rate**). **But it is only needed if you do not
  instantiate at RS** — and we do. So it is off the critical path entirely, which is a
  cleaner outcome than §4.1's LDPC objection (that one still stands for Bolt/Blaze/Brakedown).
- **ZCF23 needs an extension field for challenges over a small base field** — Remark 2,
  p.20, explicitly; Remark 1, p.16 proves the lifted code's relative distance is ≥ the base
  code's. Confirms §3.1's `SmallField.lean` note.

---

## 7. Paper-side findings — jagged and the adapter layer (lane report, integrated)

### 7.1 Corpus hygiene, first (measured, md5)

- **2025/917 jagged**: `jagged-polynomial-commitments-2025-917.pdf` ≡
  `jagged-polynomial-commitments-eprint-2025-917.pdf` (Apr 10 2026, 26pp) = **canonical**, has §7.
  `jagged-pcs-sp1.pdf` ≡ `grey-succinct-jagged-polynomial-commitments.pdf` is the **superseded v1**
  (May 2025, 24pp, no §7). "Succinct" in that filename is the *company*, not a second paper.
- **2026/1367 SoK**: **five byte-identical copies** in `~/paperbin`, plus
  `skatharoudis-sok-…pdf`. And `sok-hash-based-pcs-fri-basefold-stir-whir-2026-1367.txt` is
  **TRUNCATED** (78 597 B vs 90 086 B for the others) — a real hazard for anyone grepping it.
- `relaxed-mod-pcs.pdf` ≡ `ring-fully-succinct-integer-mod-pcs-successor-to-zinc-2026-347.pdf`:
  **the filename is wrong.** It is *Relaxed Modular PCS from Arbitrary PCS* (Shirzad–Sridhar–
  Papadopoulos–Papamanthou), a **competitor** to Zinc, not a successor by the same authors. The real
  Zinc successor is `zincplus.pdf` (Zinc+, May 2026).

### 7.2 ⚑ Jagged is an adapter with *no cryptographic content at all* — stronger than our notes assumed

Theorem 1.4 (Basic Jagged) is a **claim transformation**, not a commitment property: completeness
gives `p̂(z) = v ⟹ the verifier outputs (z′, v′) with q̂(z′) = v′`; soundness gives
`p̂(z) ≠ v ⟹ w.p. ≥ 1 − 2m/|𝔽| the verifier rejects or outputs a FALSE claim about q̂`.

> **There is no extractor, no binding, and no knowledge-soundness statement anywhere in the paper.**
> Instrument: grep over `jagged-polynomial-commitments-2025-917.txt` for
> `extract|binding|knowledge.sound|committed.*sound` → **0 hits**. Likewise
> `round-by-round|state restoration|Fiat` → **0 hits** — the soundness is **plain, not RBR**.

Its `2m/|𝔽|` is *exactly* the degree-2 m-round sumcheck error, unchanged: **jagged adds zero soundness
loss of its own.** And it composes, in the paper's own §7 and in Rothblum's Simons talk, with
**batch-BaseFold** as the dense PCS. Two independent sources, including the authors' own slides.

⚠ **Theorem 1.5 as printed is off by `1/|𝔽|`.** Its proof (Lemma 5.1, p.19) states `(2m+1)/|𝔽|`; the
extra term is the random linear combination in step 1. Footnote 9's powers-of-`r` variant costs
`(2m+K)/|𝔽|`. **Formalize Lemma 5.1's number, not Theorem 1.5's.**

### 7.3 Our internal description of the jagged machinery was correct in every particular

The memory note said *"degree-2 sumcheck plus a width-4, two-bit-state read-once branching program,
decidable per layer, with an induction on top."* Verified clause by clause:

- **degree-2 sumcheck**: Lemma 2.3, *"specialized to a product of two multilinear polynomials"*,
  error `2m/|𝔽|`. ✓
- **width-4, two-bit state**: Claim 3.2.2 verbatim — *"The function `g` is computable by a **width-4**
  read-once branching program"*, with two registers (`carry_i`, `lt_i`), *"as our registers can take on
  a total of 2² = 4 possible values"*. §1.1.1 calls it *"an extremely small space streaming algorithm —
  one that only has 2 bits of storage"*. ✓ literally.
- **decidable per layer + induction**: Lemma 4.2 (from [HR18]), proved by **reverse induction over
  layers**, per-layer step Claim 4.2.1:
  `f̂_v(ζ,z) = Σ_{σ∈{0,1}^b} eq(ζ,σ)·f̂_{Γ(v,σ)}(z)`, *proved by "both sides multilinear + equal on
  Boolean inputs + uniqueness of the MLE"*. ✓

⭐ **Every step in jagged's chain is `multiAffine_eq_mle`.** The paper's Fact 2.1 *is*
`MultilinearExtension.multiAffine_eq_mle` composed with `mle_multilinear` — both **already proved in
Selvage**. No distance, no list decoding, no code theory, no probability beyond sumcheck's
Schwartz–Zippel. **This is the single most Lean-friendly proof shape in the whole candidate set.**

⚠ **Remark 3.1 is the trap.** `f̂_t(z_r,z_c,i) = eq(row_t(i),z_r)·eq(col_t(i),z_c)` holds for
`i ∈ {0,1}^m` and *"is unlikely to hold for general i ∈ 𝔽^m as the RHS has higher degree in i"*. **A Lean
statement must quantify `i` over `Fin m → Bool`, never `Fin m → F`.** This is exactly the shape of
vacuity this repo has catalogued — an identity that looks polynomial and is only pointwise-on-the-cube.

### 7.4 ❌ But jagged does not get us a multilinear PCS — and formalizing it first would be the classic wound

Formalizing all 26 pages leaves us with `p̂(z)=v ⟼ q̂(z′)=v′` and **still needing BaseFold**. The
lane's verdict, which I endorse: *"Jagged is not the tractable thing that gets us to a multilinear PCS;
it is the tractable thing that sits on top of one. If we prove jagged first we will have a beautiful
green theorem that commits to nothing."*

**This revises SELVAGE.md §5 item 2** ("Jagged PCS, in Lean … the single most Lean-tractable big idea
available"). The tractability claim is *true*; the "big idea available" framing is what needs
correcting — it is tractable **because** it has no cryptographic content, and it is worth doing
**second**, not first.

### 7.5 ⚑ The unexpected finding: Gemini's tensor-product protocol *is* our fold

`gemini-elastic.pdf` = *Gemini: Elastic SNARKs for Diverse Environments* (Bootle–Chiesa–Hu–Orrù).
Its **tensor-product protocol** is the multilinear→univariate reduction the brief asked about.

Def 5.1: `R_TC = {(𝔽,N,ρ₀..ρ_{n−1},u; f) : ⟨f, ⊗_j(1,ρ_j)⟩ = u}`, and §2.4.2 notes
`f̂(ρ) = ⟨f, ⊗_j(1,ρ_j)⟩` — so `R_TC` **is** the multilinear evaluation relation.

Construction 1: `f^{(j)}(X) := f_e^{(j−1)}(X) + ρ_{j−1}·f_o^{(j−1)}(X)`; verifier samples `β ← 𝔽ˣ` and
checks, for all `j`, **Eq. (16)**: `ê^{(j)} = (e^{(j)}+ē^{(j)})/2 + ρ_j·(e^{(j)}−ē^{(j)})/(2β)`.
Theorem 5.2: soundness `O(N/|𝔽|)`; Lemma 5.4 gives `(N−1)/|𝔽ˣ|` by a degree-counting argument.

| Gemini | Selvage |
|---|---|
| `f^{(j)} := f_e + ρ·f_o` | `mleCoefficientFold p r = evenPart p + C r * oddPart p` — **the same definition** |
| Eq. (16) | `fold_eval : fold D (p.eval ∘ dom) α k = (evenPart p + C α * oddPart p).eval (domSq k)` — **the same identity**, with `β ↦ −β` the 2-to-1 map and `β²` the `domSq` |
| Lemma 5.3 (completeness induction) | `foldMleVariables_booleanMobiusPolynomial` — **already proved** |
| Lemma 5.4 (soundness, `(N−1)/|𝔽ˣ|`) | **new**, a short degree-counting argument, no code theory |

🐞 The lane caught **two typos in Gemini**: Construction 1 as printed renders the fold as `f_e + ρ·f_e`
(impossible), and Lemma 5.3's proof text as `f_o + ρ·f_e` (swapped). The correct form `f_e + ρ·f_o` is
fixed independently by §2.4.2 Eq. (1) and by Eq. (16) itself. **Our `mleCoefficientFold` already has the
right orientation.**

Also **Remark 2.7**, which matters for BabyBear: *"all the PIOPs in this paper work with univariate
polynomials over any field 𝔽 that is sufficiently large"* — **no smoothness requirement**.

⚠ **My scrutiny of the lane's enthusiasm, which changes the ranking:** Gemini's `f^{(j)}` are **oracles
in a PIOP**, where the verifier gets true polynomial evaluations at `β, −β, β²` for a `β` chosen *after*
commitment. Compiling that needs a **univariate PCS with evaluation openings at arbitrary points** —
DEEP/quotienting, or the constrained-RS route. **Selvage has proximity, not an assembled univariate
evaluation PCS.** BaseFold's structural advantage is precisely that it needs *no* such opening: its
tie-off (ZCF23 step 3) is `Enc₀(value) = π₀`, the verifier re-encoding **one field element** and
comparing. So the beautiful identity matches are real, but **Route B's total obligation is larger than
Route A's**, not smaller. I am recording this as a correction to the lane's ordering, with reasons, not
as a dismissal — see §8.

Cost of the Gemini route, honestly: `≈ 2×` commitment data (the `f^{(j)}` are sent), and
`O(N/|𝔽|)` is **vacuous at BabyBear** (`N=2^29`, `|𝔽|=2^31` ⟹ error ≈ 1/4). It must run over `𝔽_{P⁴}`.

### 7.6 TensorSwitch (2025/2065) — on disk, unassigned, and it takes our predicate as its hypothesis

Bünz–Fenzi–**Rothblum**–Wang, Nov 15 2025, 64 pp; `~/paperbin/tensorswitch-2025-2065.pdf`. It is a
**base** multilinear PCS (not an adapter), it is what **both** jagged (Remark 7.1) and 2026/347 (§4.3)
reach for, it is by jagged's own senior author, and **it has a round-by-round security section (§2.5)**
— the ingredient the SoK says BaseFold merely *asserts* and jagged lacks entirely.

Theorem 1.1 (informal), p.5, verbatim in relevant part:
> *"Let `C : 𝔽^k → 𝔽^ℓ` be a linear code of rate `ρ = k/ℓ`, **with mutual correlated agreement
> (Definition 3.19) and list-decoding (Definition 3.11) up to distance `δ ∈ (0,1)`** … There exists an
> IOPCS for multilinear polynomials of size `n = k²` with **soundness error `2^{−λ}`**…"*

**That is our `CorrelatedAgreement (C : Submodule F (ι → F)) (δ : ℝ)` predicate appearing as someone
else's hypothesis** — the good direction. And Remark 1.3 is directly on the small-field pain point:
*"all prior hash-based PCSs with polylogarithmic proof size require extension field
encoding/committing on data of total size `Ω̃(n)`"*, whereas TensorSwitch needs it only on
`(λn)^{0.5+o(1)}`.

⚠ **Unresolved and must be discharged by reading, not assumed**: the near-optimal proof size holds
*"under plausible conjectures on the proximity gaps and list decoding radius"*, and the hypothesis is
**mutual** correlated agreement — dated the *same month* Crites–Stewart disproved up-to-capacity MCA.
Nobody has read TensorSwitch §3.19 against 2025/2046. Until someone does, its numbers are not quotable.

### 7.6b The SoK (2026/1367) — calibrate before citing, but §5.5 is the decomposition we want

Single author (Christos Skatharoudis, PhD candidate, U. of the Aegean). **Every theorem in it is
explicitly labelled "informal"**; it restates [BCIKS20] rather than proving anything. **Cite [BCIKS20]
directly, never the SoK, for a bound.**

Its §5.5, *"The compilation layer: what IOP soundness does not give you"*, is the four-part
decomposition to mirror in Lean, and it maps onto Selvage almost exactly:

| SoK §5.5 ingredient | Selvage |
|---|---|
| 1. **round-by-round soundness** (*"Basefold's original analysis proves plain soundness and only asserts RBR soundness as 'straightforward'"*) | `Rbr.lean` + `Depth.lean` + `AccRbrInstance.lean` — **held** |
| 2. **grinding / proof-of-work** (universal in deployment, absent from theory) | `LightClientGrinding.lean` — **held** |
| 3. **batching** (*"correlated agreement … is why the proximity-gaps toolbox, and not FRI itself, is the decisive result … this is where **small fields (large n/q) are most dangerous**"*) | `CorrelatedAgreement.lean` — **held** |
| 4. **extraction in the list-decoding regime** | ⚑ **the gap** |

⚑ Item 4, verbatim: *"the gap between IOPP soundness and PCS knowledge-soundness (visible in Basefold,
whose IOPP reaches a Johnson-type radius but whose **extractor is proven only at unique decoding**) …
This is the technical locus where 'proven versus conjectured' actually bites a **commitment scheme**, as
opposed to a bare proximity test."*

**This is independent confirmation of §5.3's tier table**: even in the literature, BaseFold's
*extractor* — the thing that makes it a commitment rather than a proximity test — is proven only at
unique decoding. Choosing Tier 1 is not us settling for less than the field has; it is us matching what
the field actually has.

### 7.7 Schemes the SoK names that were not on the brief's list

**DEEP-FRI** (2019/336 — and the SoK's first correction is that the DEEP trick that survives in
deployment is **DEEP-ALI on the constraint side**, distinct from the low-degree-test modification it is
conflated with, which was superseded for FRI soundness by Proximity Gaps); **Circle-FRI / Circle
STARKs** (2024/278, live on Starknet via Stwo since Nov 2025); **FRI-Binius / Binius**; **Orion**;
**Ligero++**; **Vortex** (Linea); **Ligetron**; **Expander** (Polyhedra). Plus, from other papers in the
corpus and absent from the SoK: **TensorSwitch** (§7.6) and **Mercury** (2025/385, Q-DLOG, not PQ).

The SoK **does not analyse jagged at all** (3 mentions, all deployment-map; its ref for SP1 Hypercube is
a Succinct *engineering blog*, not 2025/917), and contains **zero** hits for Ligerito, Blaze, Hyrax,
Gemini, DeepFold, TensorSwitch, Mercury, or "stacked".

### 7.8 ❌ Zinc / integer-mod line: orthogonal, dropped from the ranking

Four independent structural reasons, each instrumented by the lane: (i) Zinc/Zip **does not use
Reed–Solomon at all** (1 grep hit, a bibliography entry); its code is integral Juxtaposed
Expand-Accumulate over ℚ. (ii) Its "field" is a random **~2λ-bit prime**, BabyBear excluded
*structurally*. (iii) 2026/347 **consumes** a multilinear PCS over `𝔽_p` as a black box — it is a
downstream consumer, not an upstream shortcut. (iv) Zinc+'s reuse hook explicitly sits *on top of* a
`𝔽_q` IOPP we do not yet have.

Two findings worth keeping anyway: **2025/316 has no formal definition of "IOP of proximity to the
integers"** (13 prose mentions, **none inside a numbered Definition**), and its "correlated agreement"
is the unique-decoding infinite-field one at `δ < dist/3` from [AHIV22] — **not** the RS proximity-gaps
result. *Do not let the shared phrase suggest reuse.* Also: Zinc explicitly ships an **interactive**
argument because *"the Zip-IOP only achieves standard knowledge soundness and not state-restoration
knowledge soundness"* — which is precisely the property Selvage's `Depth.lean` proves and would supply.

### 7.9 The Thaler survey answers the univariate question NEGATIVELY — and is silent on everything else

§3, verbatim: *"**univariate PIOPs require univariate PCSes, and multilinear PIOPs require multilinear
PCSes.**"* The survey never describes a type-crossing reduction. Instrument: over its `pdftotext`,
`Gemini` **0**, `Zeromorph` **0**, `Basefold` **0**, `STIR` **0**, `Binius` **0**, `jagged` **0**,
`Ligerito` **0**; `WHIR` 3 and `Brakedown`/`Ligero`/`Blaze` are bare citations. It is a *curve-side*
document (`Hyrax` 26 hits, `Dory` 25) and contributes nothing to this question — **except** §3.2's
general-degree sumcheck statement `dn/|𝔽|`, which is exactly the S3 generalization, and Theorem 5
(zerocheck→sumcheck, `n/|𝔽|`), which it actually proves.

Its answer being negative is *itself* the finding: the multilinear→univariate route (Gemini) is real
but is **not** what the sumcheck-native community reaches for, and §7.5 explains why — it re-imports the
univariate-evaluation-opening problem that BaseFold was designed to delete.

---

## 8. Paper-side findings — WHIR / STIR / MCA (lane report, integrated)

### 8.1 ⭐⭐ Selvage's MCA theorem is WHIR Lemma 4.10, and Selvage is CORRECT where the paper is not

The lane verified `whir.pdf` ≡ `whir-proximity-generator-mca-2024-1586.pdf` (byte-identical,
md5 `3403217f…`, 2024-11-21 — not a revision) and read §4.2 pp.22–23 with
`pdftotext -layout -f 23 -l 24`. Two defects in the printed lemma:

| | WHIR as printed | Selvage | verdict |
|---|---|---|---|
| proximity bound | `B*(C,ℓ) = **min**{1 − δ_C/2, B(C,ℓ)}` | `max (1 - dC / 2) B` | **Selvage correct; `min` is a typo** |
| δ-range in Def 4.9 | `δ ∈ (0, 1 − **B**(C,ℓ))` | `δ < 1 - Bstar` | **Selvage correct; second typo** |
| failure event / CA conclusion | Def 4.9 / Def 4.7 | `MutualCAFailure` / `CorrelatedAgreement` | identical, term for term |
| generator | abstract in Def 4.7, only `(1,α,…,α^{ℓ−1})` instantiated | abstract `G`, `comb r f` | **Selvage strictly more general** |
| `err` monotone | never stated | `herr_mono` hypothesis | **Selvage repairs a silent step** |

Three independent confirmations that `max` is right: (i) the proof needs *both* `δ < 1 − B` and
`δ < δ_C/2` (verbatim: *"because δ < δ_C/2, we have |Λ(C,g_r,δ)| ≤ 1"*), whose conjunction is
`δ < 1 − max(B, 1 − δ_C/2)`; (ii) **Corollary 4.11 prints `B*(C,ℓ) := (1+ρ)/2`**, which is
`max{(1+ρ)/2, √ρ}` by AM–GM — `min` would give `√ρ`, so the corollary is inconsistent with the
lemma as printed and consistent with Selvage; (iii) WHIR's own authors restate it in
`open-problems-…-2026-680` §4.1 p.18 as *"for any F-additive code C and **δ < δ_min(C)/2**"*.

And `herr_mono` is a **genuine repair**: the paper's last step applies the generator at proximity
parameter `1 − |T|/n ≤ δ` while holding only the bound `err(δ)`, which needs
`err(1 − |T|/n) ≤ err(δ)`. The paper never states it; it is satisfiable (both branches of BCIKS's
`err` are nondecreasing).

**SELVAGE.md's claim "correlated agreement (WHIR Lemma 4.10, domain-general)" is VERIFIED**, with
the corrections above. Domain-generality is not even a stretch — Lemma 4.10 is stated for an
arbitrary linear code `C ⊆ F^n`, no domain structure at all.

### 8.2 The WHIR theorem to target is 5.2, and its MCA hypothesis is at arity 2 — our exact shape

Theorem 5.2 (§5.1 pp.33–34) is **unconditional**, parameterized by *"Gen is a proximity generator
with mutual correlated agreement … with bound B\* and error err\*"*, and its per-round errors are
```
ε^fold_{i,s} ≤ d·ℓ_{i,s−1}/|F| + err*(C_RS^{(i,s)}, 2, δ_i)
ε^out_i     ≤ 2^{m_i}·ℓ²_{i,0}/(2·|F|)
ε^shift_i   ≤ (1 − δ_{i−1})^{t_{i−1}} + ℓ_{i,0}·(t_{i−1}+1)/|F|
ε^fin       ≤ (1 − δ_{M−1})^{t_{M−1}}
```
**The arity is 2 everywhere** — `err*(·, 2, δ)`, `B*(·, 2)` — i.e. exactly Selvage's
`![foldEven D f, foldOdd D f]`. WHIR needs arity > 2 in **one** place only (Theorem 7.5's `ε^com`,
the Σ-IOP compiler). For the PCS weight `ŵ = Z·eq(X,z)`, `d* = 3` and `d = 3`.

There is **no PCS theorem in WHIR at all** — the complete theorem list is 1, 2 (both informal),
4.3, 4.8, 4.20, 5.2, 5.6, 7.5, 7.11, A.3. *"The WHIR PCS"* is Construction 5.1 at
`CRS[F,L,m, Z·eq(z,·), σ]` plus BCS. **Binding/extractability is never stated as a theorem.** So
a Lean port would be porting an IOPP; the PCS wrapper is unformalized in the source — which is
exactly the wrapper `Selvage/Commitment.lean` + `Erasure.lean` already supply.

⚠ Theorem 7.5's hypothesis prints `δ < B*`; every other use in the paper writes `δ ∈ (0, 1 − B*)`,
and `δ < B*` is nonsense for `B* = (1+ρ)/2`. **A port copying it literally proves a different
theorem.**

### 8.3 You do NOT need STIR

The lane grepped all 17 `[ACFY24]` citations in `whir.txt`. **WHIR imports exactly one technical
result from STIR**: Lemma 4.5, restated as WHIR Lemma 4.25 (the out-of-domain sampling lemma),
whose proof is two lines — `Pr[û(r)=û′(r)] ≤ (d−1)/(|F|−|L|)` plus a union bound over `(ℓ choose 2)`.

**STIR's `Quotient` (Def 4.2), `PolyQuotient` (Def 4.3), Lemma 4.4, `DegCor` (Def 4.11/4.12) and
Lemma 4.13 — ~6 pages of its technical core — are NOT needed.** WHIR replaces them with
weight-polynomial accumulation, which is just the polynomial identity lemma. And there is no query
gain to be had: `q_STIR = q_WHIR` (WHIR Table 1 p.6). STIR also carries an *enormous* field-size
hypothesis (Theorem 5.1: `|F| = Ω(λ·2^λ·d²·|L|^{3.5}/log(1/ρ))`, with its own note *"this bound is
not tight"*). **Porting STIR is a detour.** ⇒ delete it from the candidate list as a *target*;
keep it as the source of one two-line lemma.

### 8.4 ⚑ The conjecture landscape moved, and it argues for aiming LOWER

Source: `open-problems-list-decoding-correlated-agreement-2026-680` — **Arnon–Boneh–Fenzi 2026, two
of WHIR's own authors surveying exactly this question**. It is the single most useful file in the
corpus for this lane and it was not in the brief.

- **WHIR Conjecture 4.12 item 1 (Johnson) is now a THEOREM** — survey Theorem 4.12 = [BCHKS25] Thm
  4.6; independently Haböck 2025/2110 Theorem 2. ⚠ **But do not price it as "available in Lean."**
  Haböck's own abstract says he *"**outlines** how to generalize the Guruswami–Sudan list decoder
  analysis"* and the body invokes the interpolating polynomial over `K = F_q(Z)` (rational function
  field), irreducible/separable factorization with inseparability exponents, `disc_Y(Q)`, and a
  **Hensel lift**, noting it *"requires certain familiarity with algebraic function fields."*
  **A proof sketch resting on BCIKS §5 — the hardest thing in this literature to machine-check.**
- **WHIR Conjecture 4.12 item 2 (capacity) is REFUTED in its general form.** Survey Theorem 4.16
  ([BCHKS25; KK25]) — *"the theorem above captures both **prime fields and smooth domains**"*; and
  Theorem 4.17 ([CS25] Cor. 1) gives **`ε_ca(C,δ) = 1`** outright in a regime, i.e. the proximity
  gap vanishes entirely, and `ε_ca ≤ ε_mca` so MCA dies with it. **We are on a 31-bit prime field
  with a smooth domain.** ⇒ §5.4's verdict stands and is now sourced to a theorem, not a filename.
  (The SoK's caveat (ii) — *"the refutation is established over large fields, and a small-field
  analogue … we do not claim it"* — is **behind**: `krachun-kazanin-habock-…-2026-782` states a
  counterexample *"for Reed–Solomon codes over **multiplicative subgroups of prime fields**"*, and
  the SoK does not cite it, 0 grep hits.)

**The price of being unconditional, from WHIR §6.3.4 p.53, direct quote** — at `(m,ρ)=(24,1/2)`,
λ=128: *"WHIR-UD's argument are 621 KiB, WHIR-JB's are 299 KiB, and WHIR-CB's are 156 KiB"*;
verifier *"4.8ms / 2.5ms / 1.4ms"*; prover *"49s / 50s / 47s"*.

> ⭐ **The whole conjecture buys 4× on proof size, 3.4× on verifier time, and NOTHING on prover
> time.** That is the number that should drive "which construction is provable soonest," and it
> says: take the unconditional one.

### 8.5 ⚑⚑ The highest-leverage finding in the whole lane, and it was not in the brief

**Mutual correlated agreement at the 1.5-Johnson bound is PROVEN for GENERAL LINEAR CODES by
ELEMENTARY MEANS.** Two independent papers, both already on disk:

- **GKL, `linear-proximity-gaps-1p5-johnson-2024-1810.pdf`.** Their `Bad_δ(π₁,π₂)` (Def 8) *is* the
  MCA failure set, and they say so (§1.2 p.4: *"also called **mutual correlated agreement** in
  WHIR"*).
  > **Theorem 3.** For `δ ≤ 1 − ∛(1−Δ_C) + η`: `|Bad_δ(π₁,π₂)| < 2/η + (n+6)/(η·(∛(1−Δ_C+η) − √(1−Δ_C+η)))`.
  > **Theorem 4.** For `l+1` words: `Pr_{z_l}[z_l ∈ Bad_δ] < (…)·l/q`.

  **Machinery checked by grep**: `function field|Hensel|Guruswami-Sudan|algebraic geometry|Riemann`
  → **0 hits**. The proof is Lemmas 1–8: maximal agree-domains, pairwise and 4-way intersection
  counting, a low/high-error partition at the Johnson radius, plus one imported lemma (BGKS20 Lemma
  3.1, itself elementary).
- **Khatam–Zeilberger, `khatam-zeilberger.pdf` (2024/1843)** — was **absent**, fetched by the lane.
  > **Theorem 1 (Distance Preservation within 1.5 Johnson).** `|A_{π,ϵ,η}| ≤ 1/(ϵη)`.

  Proof = Lemma 1 (an injection), Lemma 2 (triple-intersection counting), Lemma 3 (a Johnson
  generalization). **The bound is independent of `n`** — better than GKL's `O(n/η)` — at the cost of
  a proximity loss `η` the survey flags as under-explored (Remark 4.4).

**Why this matters more than anything else here.** Selvage's *unconditional* RS proximity generator
tops out at `δ < (1−ρ)/3` (`ProximityGapUD.foldDistancePreserving_UD`); the full unique-decoding
band `(1−ρ)/2` already costs a **named hypothesis**, `PolishchukSpielman F`
(`ProximityGapUDTight.foldDistancePreserving_UD_full:1002`); Johnson costs `HaboeckTheorem2`; and
capacity is refuted. **GKL/Khatam would lift Selvage from `(1−ρ)/3` to the 1.5-Johnson radius
without touching BCIKS §5, by elementary counting.** For `δ_min ≥ 0.77` — i.e. `ρ ≲ 0.23`, so rate
1/8 and below, which is where FRI-family systems actually run — 1.5-Johnson beats unique decoding
outright.

**This is a Lean target that is independent of which PCS wins, elementary, and upgrades every
theorem downstream of it at once.**

### 8.6 Also not in the brief: MCA up to CAPACITY is *proven* — for a different code

- Survey **Theorem 4.14 ([GG25] Cor. 4.10)**: for a **folded** Reed–Solomon code
  `FRS[F,L,k,s,ω]` with `s > 16η^{−2}`: `ε_mca(C, 1−ρ−η) ≤ 2n/(η|F|) + 24/(η³|F|)`.
- **Theorem 4.13**: same for τ-subspace-design codes generally.

**Changing the code rather than assuming the conjecture** is a live and apparently underexplored
option, and it is the only route to capacity-regime numbers that is not refuted. Not a
recommendation — a flagged design fork.

### 8.7 31-bit reality check — two hard constraints, on different fields

**(A) Out-of-domain sampling forces an extension for challenges.** WHIR Lemma 4.25 with `s = 1`
gives `ε^out_i ≤ 2^{m_i}·ℓ²/(2|F|)`. *Derived*: `ε^out ≤ 2^{−λ}` needs `|F| ≥ 2^{m+λ−1}·ℓ²` — at
m=24, λ=128 that is `|F| ≥ 2^{151}·ℓ²`. WHIR says so itself (§6.2 p.44): *"The argument verifier
samples challenges from a **sufficiently large extension of the base field**."* **There is no 31-bit
benchmark anywhere in the WHIR paper** — its fields are a 192-bit prime and Goldilocks with a
quadratic (λ=100) or cubic (λ=128) extension.

**(B) Two-adicity caps `m`.** `L_i` must be a smooth coset of `F*` and lives in the **base** field.
BabyBear `p = 2^31 − 2^27 + 1` has two-adicity **27**; KoalaBear `2^31 − 2^24 + 1` has **24**.
*Derived*: `m + log₂(1/ρ) ≤ 27` ⇒ **m ≤ 26 at ρ=1/2, m ≤ 23 at ρ=1/16** on BabyBear (KoalaBear:
23 / 20). WHIR hits the same wall on Goldilocks (§6.3 p.44: *"we ignore pairs where m − log ρ > 32,
as the field does not have a sufficiently large smooth evaluation domain"*).

⇒ **Base field carries the domain and the Merkle leaves and caps `m` at ~26; every verifier
challenge — folding, out-of-domain, shift, combination — comes from a degree-4/5 extension, and
post-round-0 sumcheck arithmetic is extension arithmetic.** Biggest hidden cost, and it is in no
paper. `Selvage/SmallField.lean` already holds the lift (`fold_liftWord_mem:270`).

---

## 9. Paper-side findings — tensor-code family (lane report, integrated)

### 9.1 Corpus corrections

- ⚠ **`tensorcommitments.pdf` is MISIDENTIFIED in the brief.** It is *TensorCommitments: A
  Lightweight Verifiable Inference for Language Models*, **arXiv:2602.12630, Feb 2026** — an
  ML-systems proof-of-inference paper whose crypto content is a Merkle variant with a
  position-binding definition. **Not Bootle–Chiesa–Groth, not a tensor-query PCS, no evaluation
  soundness theorem.** Not a candidate.
- The two `-487` files are **byte-identical duplicates** (md5 `4fc04733…`); one paper.
- **Absent, therefore fetched** from the local IACR mirror: Brakedown 2021/1043, Ligero 2022/1608,
  Hyrax 2017/1132. **Orion**: absent, not fetched.

### 9.2 ⭐ Diamond–Gruen 2024/1351 — the abstract-layer keystone, and it lands in Selvage unchanged

~9 pages: 3 counting lemmas + 2 theorems + 1 corollary, **stated for an arbitrary linear code**.

- **Theorem 3.1**: if `C` has proximity gaps for affine lines w.r.t. `e ≤ ⌊(d−1)/2⌋` and `ε ≥ e+1`,
  then so does every interleaving `C^m`. Proof = Lemmas 3.2/3.3/3.4 (triangle + unique decoding;
  two counting bounds) + pigeonhole. **No polynomial method, no list decoding.**
- **Theorem 3.6** (Angeris–Evans–Roh): interleaved gaps for all `m` ⟹ **tensor-style** gaps.
  Induction on `ϑ` with one probability-slicing step.
- **Corollary 3.7**: RS has tensor-style proximity gaps at `e ≤ ⌊(d−1)/2⌋`, `ε := n`.

Fit to Selvage, assessed by the lane and consistent with what I read: `d^m(U, C^m) ≤ e` **is**
`CorrelatedAgreement C δ f` at `δ = e/|ι|`, `ℓ = m`; Def 2.1 is `IsProximityGenerator` at `ℓ=2`
with `G` the affine-line distribution; **Def 2.3 is the same predicate at `ℓ = 2^ϑ` with `G` the
tensor distribution** — since `IsProximityGenerator` is *parameterized by `G`*, this is an ordinary
instance, **no signature change**. Two honest caveats: the tensor generator must be presented as a
distribution over `Fin (2^ϑ) → F` supported on tensor vectors (a `G.pr` construction — real work,
not a definitional change); and Theorem 3.1 needs **column** distance on `Fin m → ι → F`, which
`relDist` does not provide (one new definition + a bridge lemma).

⭐ **It is the shared proximity input of Ligerito *and* Binius2** — Binius2's Theorem 2.3 is BCIKS
Thm 4.1 and its Theorem 2.4 is Diamond–Gruen Cor. 1. Three independent constructions land on the
same pair. **If one abstract proximity result is proved next, that pair is it.**

### 9.3 ⚑ Gemini's cheapness is misleading — my §7.5 scrutiny confirmed independently

The tensor lane grepped `gemini-elastic.txt` for `KZG|pairing|Merkle|FRI`: **11 hits for
KZG/pairing** (§2.3 *"An elastic realization of the KZG polynomial commitment scheme"*; BLS12-381
in the experiments), **zero for FRI, zero for hash-based, zero for Merkle.**

> *"Gemini as published compiles with KZG. … the queries at `β, −β, β²` with `β ← F^×` are
> **out-of-domain**, which a FRI-based univariate PCS answers by quotienting (DEEP-style) with its
> own soundness terms. If our univariate cone stops at 'RS proximity + FRI folding' with no
> evaluation-at-a-point argument, Gemini's cheapness is misleading — **the missing work is the
> compilation, not the reduction.**"*

That is exactly the objection I raised in §7.5, reached independently. And there is a measurement:
**Blaze benchmarks this route as "ZeromorphFri" and it is the SLOWEST prover in their comparison.**

Lemma 5.4 remains, genuinely, **the cheapest soundness statement in the corpus** — ~10 lines, one
Schwartz–Zippel, `(N−1)/|F^×|`, no hypothesis on code, domain, smoothness, or characteristic. Worth
having as a *lemma*. It is not a route to a PCS on its own.

### 9.4 ❌ RAA / Blaze / 2026-487 — the distance is not a foundation

**Blaze Theorem 3.1** is genuinely proven and explicit, but what it proves is that a **randomly
generated** RAA code has distance `≥ δ` with failure probability `≥ 1 − p`, and the usable form is
conditional on `B' := max{f(α,β,δ) : (α,β) ∈ CP(r,δ)} < 0`, which the authors describe as *"quite
messy to state formally, [but] **easy to evaluate on a computer**"* — a **computer-checked
transcendental optimization**, i.e. in Lean an interval-arithmetic obligation or an axiom.
Concretely: `k=2^22`, rate 1/4 gives `δ = 0.19` except with probability **2^−13**; 2^−27 with
near-linear generation tests, 2^−42 with near-quadratic. **Nowhere near a 2^−100 bar.** And §8 p.36:
*"we do not have satisfactory distance guarantees for RAA codes of block length smaller than 2^21."*

**Blaze does not even remove RS from the stack**: code-switching produces an IOPP whose oracles are
**Reed–Solomon encoded**, and the opening *"executes a constant number of **Basefold**
commitments"*. **Blaze = RAA layer + BaseFold/RS layer.** It adds a code to our stack rather than
replacing one. Same structure as Bolt (§4.1).

**2026/487 (Generalized RAA over prime fields) is worse.** Its distance theorems are `o(1/N)` with
unspecified `K` and constants — **no failure probability at any concrete `N`** — and the central
theorems carry **"Proof Sketch"** only (grep: 4 sketches, 7 proofs, **no appendix**, file ends at
line 2237). Its Theorem 9 soundness is *"the same framework established in Brakedown"* with RAA
substituted, **asserted, not proved**. The lane's verdict, which I endorse: *"the only paper putting
RAA on a prime field, and the least rigorous document in my corpus. I would not build on it."*

⇒ **§4.1's LDPC objection generalizes to the whole expander/RAA family, and it is sharper than
their √N verifier costs.** Their soundness rests on a distance parameter we cannot prove and would
have to assume — converting a proved floor (`reedSolomonCode_minDist`, ~30 lines of Vandermonde)
into a named assumption.

### 9.5 Ligerito, Ligero, Brakedown — shapes and the honest disqualifiers

**Ligerito** (Novakovic–Angeris, May 2025 — an unrefereed *note*, no eprint number) has the best
recursion shape in the corpus: soundness composes **per level by explicit induction on `ℓ`**
(§6.3 p.15), each step = (Diamond–Gruen interleaved gap) + (partial sumcheck). Polylog verifier,
**no √N**. Any code with efficiently evaluable generator rows; unique decoding `d/2` (RS) / `d/3`
(general). Measured: 2^24 → 255 KiB / 1.3 s; 2^30 → 420 KiB / 80 s.

⚠ **But its stated error bound has at least two transcription defects**, both verified at the byte
level by the lane: eqs (4)/(15)/(17) print `(m − n − 1)/(2m)` where the quantity is `(m + n − 1)/(2m)`
(confirmed against the paper's *own* asymptotic `|S_i| = ⌈−(λ+log ℓ)/log((1+ρ)/2)⌉`, whose base is
`(1+ρ)/2 = (m+n)/(2m)`), and eq. (18)'s summand prints `(d_i/(3m_i))^{|S_i|}` where eq. (5) gives
`(1 − d_i/(3m_i))^{|S_i|}` — inconsistent with the tail term *in the same display*. **The printed
form is the more favourable one; formalizing it verbatim would prove a bound the protocol does not
have.** Also: its commitment is **interleaved, leaf = a whole row of `X`**, so `OpeningScheme` gets
re-instantiated at a row-valued type (`PositionBinding` survives verbatim, being generic in `Op`).

**Ligero / Brakedown**: the SoK's own answer to *"what is simplest to prove"* is this family —
Ligero Theorem 4.4 holds for **any linear code** at `e < d/4` with a ~30-line Lemma 4.2; Brakedown's
binding is 3 elementary steps. **The price is a √N verifier and tens-of-MB proofs**, and — the
sharper objection — **knowledge soundness needs Brakedown's Lemma 2/3, rewinding extractors in
expected polynomial time, which is substantially harder in Lean than anything else in this
document.** Binding is cheap; *knowledge* is not.

### 9.6 ❌ Hyrax is out, and ❌ Binius ring-switching is out of scope

Hyrax's multilinear commitment is **Pedersen in an elliptic curve group** (M191), and the
construction *requires* the commitment to be additively homomorphic — the verifier folds committed
rows by a linear combination **in the group**. A Merkle/BCS `OpeningScheme` is not homomorphic, so
**there is no hash-based instantiation of the technique.** Not post-quantum. Answered honestly:
this candidate does not exist in our setting.

Binius ring-switching is *characteristic-agnostic* per its own authors (2024/504 §1.3), but (i) it
is **not a PCS** — it consumes one; (ii) its value (eliminating embedding overhead) largely
evaporates at 31 bits: packing buys `ℓ → ℓ−2`, not `ℓ → ℓ−7`; (iii) `[L:K]` must be a **power of
2**, ruling out degree-5 extensions.

---

## 10. The rest of the BaseFold family — all four rejected, with reasons

| | regime | conjecture? | commit = ordinary RS/FRI root? | verdict |
|---|---|---|---|---|
| **DeepFold** 2024/1595 | capacity `1−ρ−ε` | ⚠ **YES, and it infects the COMMITMENT** | **NO** — root **+ a (α,c) DEEP triple** | reject |
| **UltraFold** 2026/266 | conjectured capacity, **in prose only** | yes | ZCF23 + leaf permutation | **not a distinct target** |
| **Galois-ring BaseFold** 2025/1767 | `δ ≲ Δ/3` | no, but **two unproved "Fact"s** | **NO** — no evaluation domain at all | reject |
| **SwitchFold** 2026/1489 | **`δ/3`, unique decoding, ZERO conjectures** | **no** | **NO** — interleaved matrix, row leaves | reject, but note the regime |

**DeepFold** is a *simpler protocol* than BaseFold — no sumcheck at all, a degree-1 "ladder" of
DEEP evaluations folded by the same `r_i`, and the FRI leg is bit-for-bit standard with
**our exact fold convention** `f^{(i)} = f_E + r_i·f_O`. But: **Conjecture 1** (RS list-decodability
to capacity, `L ≤ (|L|/ε)^{C_ρ}`) sits on the dependency chain *Theorem 4 → Lemma 7 → Theorem 2's
proof*, and Theorem 4 is the **binding** theorem — so **the conjecture infects the commitment
itself**, and the commitment is a three-message `⟨rt, α, c⟩` triple, not a root: *without `(α,c)` the
scheme is not binding at all* in that regime. Further: `poly(|L₀|)` in Theorem 2's bound is **never
instantiated anywhere**, so no bit-security is derivable for the non-query term; **no extractor is
ever constructed** ("extractor" occurs once, in a definition); and the proof invokes *"**the DEEP
theorem**"* with **no statement, no number, no citation** — its largest hidden dependency. Its
measured numbers are excellent (s=34 vs BaseFold's 120; 208 KB vs 619 KB) and irrelevant to
provability.

**UltraFold** *"contains no theorem"* — Definition 1 and Lemmas 1–8, and **every soundness lemma has
the form "the same bound as centralized BaseFold" with the bound never written down.** Lemma 5's
proof is a simulation wrapper. Its only quantitative content is a prose paragraph citing WHIR's
**conjectured** capacity MCA. Formalizing UltraFold = formalizing BaseFold plus an index-permutation
identity. ⚠ Two internal defects worth noting as a calibration on the paper: it uses Goldilocks
(`2^64`) while its own §2 requires `|F| = Ω(2^λ)` at λ=100 (the d-round sumcheck alone loses `2^{−58}`
at d=27), and its one quantitative citation attributes a bound to "DEEP-FRI [12]" where ref [12] is
**DeepFold**.

**Galois-ring BaseFold**: the headline finding is that **every soundness error is in terms of the
residue field `p^r`, never `|GR| = p^{rs}`** — *you get a ring of size `p^{rs}` and the security of a
field of size `p^r`; `s > 1` buys `Z_{p^s}` representation and **zero bits of soundness***. Good news
for a would-be formalizer: no exceptional set, no Lenstra machinery. Bad news: **Fact 2** (the
Schwartz–Zippel replacement over a finite chain ring, `Pr[f(x)=0] ≤ d/p^r`) is stated with **no proof
and no citation**; the ring analogue of `fold_preserves_code` is **used but never stated or proved**;
four field-only results (BKS'18 Johnson, twice) are applied to free modules with no ring-side proof;
**no knowledge-soundness theorem exists**; and **`p ≠ 2` is required** (the fold needs `2·diag(T)` to
be a unit) — ⚠ *in a paper motivated by lattice/FHE, which live over `Z_{2^k}`*.

**SwitchFold** deserves its own note because **its regime is the friendliest in the corpus**:
everything strictly inside `δ/3`, unique decoding, **zero conjectures anywhere**, on the strength of
one Ligero-style lemma (BKS'18 Thm 7) for an **arbitrary linear code**. But it has **no folding
operator and no braid** — so `FoldDistancePreserving` and `IsProximityGenerator` have *no counterpart*
— its commitment is an interleaved matrix with row leaves, it adds **Θ(log N) fresh roots plus three
point-oracle commitments per level**, its `κ_Hash` is never instantiated, and its **Lemma 7**
(RBR-knowledge-soundness ⇒ knowledge-soundness), load-bearing for Theorems 3/5/6, is stated with
**no proof and no citation**. Its measured cost is the tell: `33λ` queries **per level per opening**
at δ=1/16, giving 754 s at N=2^30 for BrakeFold. Reject — but keep the regime observation.

---

## 11. ⭐ RANKING — what to formalize first, with the composition path

### 11.0 Where I disagree with a lane, and why

The BaseFold lane's recommendation is **Haböck 2024/1571 in the unique-decoding regime**. Its
argument is strong and I accept its premises: Haböck's Theorem 1 *is* round-by-round (the shape our
pipeline consumes), concrete, conjecture-free, and three lemmas long, whereas ZCF23's published
proof is asymptotic with a `negl`-defined bad event and a second distance notion `Δ*`.

**But its ingredient is not one we hold, and WHIR's is.** Haböck needs two *new* correlated-agreement
results: **(G1)** the weighted variant (sub-probability measure with denominator `B_i = 2^i`), and
**(G2)** the *subcode* variant — whose short Vandermonde proof runs **on top of the BCIKS20 Prop-2
intermediate `P(X,Z)`, which Selvage's `IsProximityGenerator` does not expose** (it concludes only
the final `∃ S, … ∧ ∀ i, ∃ u ∈ C, AgreesOn S (f i) u`). The lane flagged this itself, conditionally.
I read the Lean; the condition is **not met**. Meanwhile WHIR Theorem 5.2's hypothesis — *"Gen is a
proximity generator with mutual correlated agreement … with bound `B*` and error `err*`"*, **at arity
2** — is `HasMutualCorrelatedAgreement G C Bstar errstar` on the nose, and Selvage's version of the
lemma that discharges it is **more general and more correct than the paper's** (§8.1).

**And the third option neither lane took is the right first one:** *take the protocol, not the
paper's proof.* Nothing forces us to formalize ZCF23's asymptotic argument. Selvage's `Rbr.lean`
exists; the deliverable is an `RbrKnowledgeSoundness` instance. We can state BaseFold's soundness
round-by-round — which is *Haböck's structural insight, applied in ZCF23's fold convention (already
ours) at the radius our ingredients already reach unconditionally.* That combination is in no paper
and is strictly the cheapest thing on the table.

### 11.1 The ranking

**Rank 0 — prerequisites, both small, both shared.** Do these regardless of what wins.

**(0a) The degree-2 honest sumcheck round family.** `adaptive_sumcheck_soundness`
(`SumcheckReduction.lean:296`) is *already* `d`-generic with bound `v·d/|F|` (§3.4, verified at
source). What is missing is the honest side at `d = 2`: a `roundPoly` through three interpolation
points and the "multiaffine × multiaffine is degree ≤ 2 per coordinate" lemma, discharging
`hHonestDeg` and `hHonest` for `g(b) = f̃(b)·eq(z,b)`. **Needed by BaseFold, WHIR (`d = 3` for
`ŵ = Z·eq`), and jagged (`2m/|𝔽|` *is* Lemma 2.3's degree-2 error).** *Not* needed on Haböck's route
— his `Λ_i` linearization absorbs the sumcheck into the relation, contributing exactly `1/|F|`,
which is worth knowing but is not a reason to take that route.

**(0b) `relDist_fold_le`.** `relDist (fold D f α) (fold D u α) ≤ 2 · relDist f u`, ~40 lines from
`card_sq_preimage`/`card_eq_two_mul_card`. This is what lets us reach ZCF23's `3δ` bound **without
importing the coset distance `Δ*`** that the paper threads through five results (§6.1).

**Rank 1 — ⭐ BaseFold at Reed–Solomon, unconditional band, as an `RbrKnowledgeSoundness` instance.**

*Why it wins on "provable soonest":* it has the **fewest machine parts** of any candidate that is
actually a multilinear PCS — binary folding (not k-ary), no domain shift, no out-of-domain sample,
no list-decoding-preservation theorem (at unique decoding the list is a singleton, so WHIR's
Theorem 4.20 collapses to §5.1's triangle), one oracle per round beyond the FRI tower, and a
tie-off that is the verifier **re-encoding one field element** (`Enc₀(h₁(r₀)/ẽq_z(r)) = π₀`).
And the commitment is `Selvage/Commitment.lean` **unchanged**.

*The composition path, theorem by theorem:*

| step | cite | status |
|---|---|---|
| commitment + binding | `Commitment.lean` `BindingCommitment`, `opened_eq_committed:154`, `commit_injective:161` | **held** |
| `t` columns → full word | `Erasure.lean:128` `recoverFromColumns_sound` | **held** |
| Möbius round-trip | `booleanMobiusPolynomial` + new `coeffsToTable` | **new**, §2.1 (C1) |
| tower fold = coefficient fold | `Proximity.lean:321` `fold_eval` | **new** induction, §2.1 (C2) |
| terminal word is the MLE | `MultiplicativeMleTerminal.lean:318` | **held**; §2.1 (C3) is a corollary |
| far ⟹ far, per round | `ProximityGapUD.lean:534` `foldDistancePreserving_UD` (unconditional at `δ < (1−ρ)/3`, `b = |κ|`) | **held** |
| far ⟹ far, whole tower | `Proximity.lean:706` `proximity_sound_prob` | **held** |
| adaptive + committed + queried | `HalfThresholdFriQuery.lean:415` `friAdaptive_sampled_sound` (`m·b/|F| + (1−τ)^q`) | **held** |
| **fold-chain consistency** | `CorrelatedAgreement.lean:165` `codeword_eq_of_close_of_close` + (0b) | **elementary**, §5.1 — and it is ZCF23's own Lemma 8 (§6.1) |
| sumcheck round | `SumcheckReduction.lean:296` at `d := 2` | **held** + (0a) |
| extension-field challenges | `SmallField.lean:270` `fold_liftWord_mem` | **held** |
| RBR packaging | `AccRbrInstance.lean` as template | **new**, §3.1 (S4) |
| RBR ⟹ state-restoration | `Depth.lean:1982` `OB2_depth_composition_nonneg_proved` | **held** |
| ⟹ non-interactive at the deployed alphabet | `FiatShamir.lean`, `AccRbrBcs.lean` | **held** |

*The theorem it produces*, in Selvage's vocabulary (§3.1), with a per-round bound
`n/|K| + 0 + 2/|K|` — **the chain-consistency term is zero** because
`codeword_eq_of_close_of_close` is deterministic (§5.5) — plus one `(1−τ)^q` query term.

*What is genuinely new work, stated without softening:* (C1), (C2), (0a), (0b), and (S4). Five items.
(S4) — building `Reduction`/`KStateFn`/`RbrKnowledgeSoundness` and proving `extract_sound` — is the
large one, and `AccRbrInstance.lean` is a worked precedent, not a guess.

**Rank 2 — WHIR-UD (Theorem 5.2), once Rank 1's scaffolding exists.**

Selvage holds *more* of WHIR than of BaseFold: `constrainedRS` **is** WHIR Def 4.5; `OutOfDomain.lean`
**is** WHIR §4.4 including the pinning bound; `reedSolomon_johnson_list_bound` **is** Theorem 4.3;
`close_of_correlatedAgreement` **is** the ⊇ algebra of Claim 4.23; and its MCA hypothesis at arity 2
**is** `HasMutualCorrelatedAgreement`. **You do not need STIR** — WHIR imports exactly one STIR lemma
(4.25, a two-line union bound) and discards the entire `Quotient`/`PolyQuotient`/`DegCor` stack
(§8.3). Theorem 5.6 (batching) is *"one polynomial-identity-lemma step plus a union bound"* and is the
cheapest real WHIR theorem to check.

The reason it is Rank 2 and not Rank 1 is honest: **k-ary folding and per-round domain shifting are
machinery BaseFold does not have**, and Theorem 4.20's list-decoding preservation, while trivial at
`ℓ = 1`, is stated in the general form. Do it second, on the scaffolding Rank 1 builds.

⚠ Two porting traps: **Theorem 7.5's `δ < B*` is a typo for `δ < 1 − B*`** — copying it literally
proves a different theorem — and **Lemma 4.10's printed `min` must be `max`** (§8.1).

**Rank 3 — ⭐ GKL / Khatam: elementary MCA at the 1.5-Johnson bound.**

This is the **highest-leverage item in the whole landscape**, it is independent of which PCS wins,
and it is in neither the brief nor any lane's top recommendation. Selvage's unconditional RS
proximity generator stops at `(1−ρ)/3`; the full UD band already costs a **named hypothesis**
(`PolishchukSpielman`); Johnson costs `HaboeckTheorem2`, whose core is Guruswami–Sudan over a
rational function field with a Hensel lift — the worst formalization target in this literature. GKL
Theorem 3/4 and Khatam Theorem 1 reach the **1.5-Johnson** radius for **arbitrary linear codes** by
agree-domain intersection counting, with **zero** hits for `function field|Hensel|Guruswami-Sudan`
(grep-verified). Khatam's bound `1/(ϵη)` is even **independent of `n`**. At `ρ ≲ 0.23` — rate 1/8 and
below, where these systems run — 1.5-Johnson beats unique decoding outright. **One elementary Lean
result that upgrades the radius of every theorem downstream of it.**

**Rank 4 — Jagged.** Cheap, self-contained, `multiAffine_eq_mle` applied six times plus (0a). But it
**commits to nothing on its own** (§7.2/§7.4): no extractor, no binding, no knowledge soundness, no
RBR — a claim transformer whose output claim needs a dense PCS that Ranks 1–2 supply. Do it *after*.
Formalize **Lemma 5.1's `(2m+1)/|𝔽|`**, not Theorem 1.5's `2m/|𝔽|`, and quantify `i` over
`Fin m → Bool` (Remark 3.1).

**Rank 5 — Diamond–Gruen 2024/1351**, if and when interleaved/tensor commitments become interesting.
Three elementary counting lemmas + pigeonhole + one induction, for an **arbitrary** linear code, and
it lands in `IsProximityGenerator` as an ordinary instance (the tensor generator is just another `G`).
It is the shared proximity input of Ligerito *and* Binius2. Two honest costs: presenting the tensor
generator as a `G.pr`, and a **column** distance on `Fin m → ι → F` that `relDist` does not provide.
Not on the critical path for Ranks 1–2; a good thing to hold.

### 11.2 Ruled out, with the reason in one line each

- **Gemini / multilinear-from-univariate** — the identity matches are exact and beautiful
  (`mleCoefficientFold` *is* `f^{(j)}`; `fold_eval` *is* Eq. 16; the completeness induction is already
  proved), and Lemma 5.4 is the **cheapest soundness statement in the corpus**. But Gemini compiles
  with **KZG** (11 KZG/pairing hits, **0** for FRI/Merkle/hash-based), and its `β, −β, β²` queries are
  **out-of-domain**, requiring a univariate *evaluation* PCS — quotienting/DEEP — that Selvage does not
  have assembled. **BaseFold's whole structural advantage is deleting exactly that requirement.** Two
  lanes and I reached this independently. Keep Lemma 5.4 as a lemma; do not take the route.
- **Ligero / Brakedown / Shockwave** — the SoK's own answer to "simplest to prove", and genuinely so
  for *binding*; but √N verifier, tens-of-MB proofs, and **knowledge soundness needs rewinding
  extractors in expected polynomial time**, harder in Lean than anything else here.
- **Blaze / Bolt / RAA / LDPC / expander codes** — the distance is a property of a *randomly sampled*
  code (Blaze: failure `2^−13` … `2^−42`, conditional on a **computer-checked transcendental
  optimization**; nothing below block length `2^21`; Bolt: Gallager ensemble). Replacing a 30-line
  Vandermonde theorem with a random-ensemble distance theorem is a research-scale formalization in
  combinatorics we hold none of. And **neither removes RS**: both end in a BaseFold/WHIR call.
- **2026/487 (RAA over prime fields)** — `o(1/N)` with unspecified constants, **proof sketches with no
  appendix**, soundness asserted as a Brakedown re-parameterization. Not buildable on.
- **Ligerito** — best recursion shape in the corpus (explicit induction on `ℓ`), no √N verifier; but an
  unrefereed note whose **stated error bound has two transcription defects**, both in the *favourable*
  direction, and an interleaved row-leaf commitment.
- **Hyrax** — Pedersen/dlog, *requires* an additively homomorphic commitment. **No hash-based
  instantiation exists.** Not post-quantum.
- **STIR as a target** — one lemma imported, `q_STIR = q_WHIR`, and an untight field-size hypothesis.
  Detour.
- **Binius ring-switching** — not a PCS (it consumes one); worth `ℓ → ℓ−2` at 31 bits rather than
  `ℓ → ℓ−7`; needs `[L:K]` a power of 2, ruling out degree-5 extensions.
- **Zinc / integer-mod / LigeSIS / Titan / Vela–Carina** — orthogonal (different ring, different
  assumption, or not hash-based).
- **DeepFold / UltraFold / Galois-ring / SwitchFold** — §10.
- **TensorSwitch (2025/2065)** — ⚠ **not ruled out; unassessed.** It is a *base* multilinear PCS, by
  jagged's own senior author, that both jagged (Remark 7.1) and 2026/347 reach for, that takes
  *"`C` has mutual correlated agreement up to `δ`"* as a **hypothesis** — our predicate as someone
  else's assumption — and that has the **round-by-round section nobody else has**. It was published
  the same month up-to-capacity MCA was refuted, and **nobody has read its §3.19 against
  Crites–Stewart 2025/2046.** That reading is the single cheapest open action in this note.

### 11.3 The honest statement of what remains genuinely new work

**For Rank 1 (BaseFold-UD), five items**: the Möbius round-trip (C1); the tower-fold induction (C2);
the degree-2 honest sumcheck family (0a); `relDist_fold_le` (0b); and the RBR instance with
`extract_sound` (S4). Nothing on that list requires a proximity result we do not hold, and nothing on
it requires a conjecture. **That is the verdict the brief asked whether we could reach: no, "all of
them need a new proximity result" is *not* the outcome — for BaseFold at the unconditional radius.**

**For Rank 2 (WHIR-UD), add**: Theorem 4.20's folding-preserves-list-decoding (trivial at `ℓ=1`,
stated generally), k-ary folding, and per-round domain shifting. Everything else is held.

**For any radius above `(1−ρ)/3`**: a real proximity result we do not hold — either
`PolishchukSpielman` (to `(1−ρ)/2`), or `HaboeckTheorem2` (to Johnson, and its core is the hardest
target in this literature), or **GKL/Khatam** (to 1.5-Johnson, and *elementary* — Rank 3). Above
Johnson: **refuted over prime fields with smooth domains**, which is our setting.

**Under-claiming deliberately**: (C1)–(C2), (0a)–(0b) and (S4) are shapes derived from reading the
Lean and the theorem statements. I have built none of them, and this repo's own record says my
effort estimates run long. Treat the *decomposition* as the deliverable and the *sizes* as untested.

---

## 12. Master table — the per-candidate deliverable

Columns: **Commit** = can we reuse `Selvage/Commitment.lean` unchanged (the criterion that
dominates cost, §0)? **RBR** = is the paper's soundness already in the round-by-round shape
`Selvage/Rbr.lean` consumes? **Ingredient** = does Selvage hold the proximity result it needs?

| Candidate | Lean-shaped soundness statement | Regime, and what discharges it | Commit reusable | RBR | Ingredient held | Verdict |
|---|---|---|---|---|---|---|
| **BaseFold @ RS** (ZCF23 protocol, RBR-shaped by us) | `basefoldRbr : RbrKnowledgeSoundness (basefoldReduction T deg δstar)`, per-round `err ≤ n/\|K\| + 0 + 2/\|K\|`, query `(1−τ)^q` | `δ < (1−ρ)/3`, from `foldDistancePreserving_UD` (**unconditional**) + `codeword_eq_of_close_of_close` (**deterministic**) | ✅ **unchanged** | ✅ (by us; ZCF23's own proof is asymptotic) | ✅ **all of it** | ⭐ **RANK 1** |
| **WHIR-UD** (Thm 5.2) | same shape; `ε^fold ≤ d·ℓ/\|F\| + err*(·,2,δ)`, `ε^out ≤ 2^m ℓ²/(2\|F\|)`, `ε^shift ≤ (1−δ)^t + ℓ(t+1)/\|F\|`, `ε^fin ≤ (1−δ)^t` | `δ < 1 − B*`, `B* = (1+ρ)/2`; discharged by Lemma 4.10/Cor 4.11 = **Selvage's `hasMutualCorrelatedAgreement_of_isProximityGenerator`** | ✅ unchanged (2^k-coset leaves) | ✅ **the paper is RBR** | ✅ **MCA at arity 2 is exactly ours** | **RANK 2** |
| **Haböck 2024/1571** (Thm 1) | `ε ≤ max{ε(C₀,M,1,θ), 1/\|F\| + ε(C_i,1,B_i,θ), (1−θ)^s}` | Johnson, *"carries over verbatim to unique decoding"* | ✅ unchanged | ✅ **the paper is RBR** | ⚠ **needs weighted CA (G1) + subcode CA (G2); (G2) does not go through from `IsProximityGenerator`'s conclusion** | strong structure, missing ingredient |
| **Jagged** (Thm 1.4) | `p̂(z) ≠ v ⟹ Pr[reject ∨ q̂(z′) ≠ v′] ≥ 1 − 2m/\|𝔽\|` | none — information-theoretic | n/a — **no commitment** | ❌ plain soundness only | n/a | **RANK 4** — adapter; commits to nothing alone |
| **GKL / Khatam MCA** | `\|Bad_δ(π₁,π₂)\| < 2/η + (n+6)/(η·(∛(1−Δ)+η − √(1−Δ+η)))`; Khatam `\|A_{π,ϵ,η}\| ≤ 1/(ϵη)` | **1.5-Johnson, arbitrary linear code, elementary** (grep: 0 hits for function field / Hensel / Guruswami-Sudan) | — | — | it *is* the ingredient | ⭐ **RANK 3** — radius upgrade for everything |
| **Diamond–Gruen** (Thm 3.1/3.6) | interleaved + tensor-style proximity gaps at `e ≤ ⌊(d−1)/2⌋`, `ε := n` | unique decoding, **arbitrary linear code** | — | — | lands as an `IsProximityGenerator` instance | **RANK 5** — hold |
| Gemini (Thm 5.2 / Lem 5.4) | `(N−1)/\|𝔽ˣ\|`, one Schwartz–Zippel, **no code/field/domain hypothesis** | n/a | ❌ — needs a **univariate evaluation PCS** (quotient/DEEP) we have not assembled; compiles with KZG | ❌ | — | cheapest *lemma*; **not a route** |
| Ligerito | eqs (17)/(18), per-level induction on `ℓ` | UD `d/2` (RS) / `d/3` (general) | ❌ interleaved, **row leaves** | partial (induction, not RBR) | needs Diamond–Gruen | ⚠ two error-bound typos, both favourable |
| Ligero / Brakedown | Ligero Thm 4.4 `(1−e/n)^t + (e+1)/\|F\|`; Brakedown binding (5)/(6) | `e < d/4` (any linear code) / `γ/3` | ❌ interleaved, column leaves | ❌ | ✅ (elementary) | √N verifier; **KS needs expected-PPT rewinding** |
| Blaze / Bolt / RAA / LDPC | Blaze Thm 7.1 `n/\|F\| + 2^{−λ} + O((1/δ+log n)/\|F\|)` | ⚠ distance is **probabilistic over code sampling**, `2^−13`…`2^−42`, + a computer-checked optimization | ❌ | ❌ | ❌ — the distance theorem is a research-scale formalization | **out** — and neither removes RS |
| 2026/487 (RAA over `F_p`) | Thm 9 `(1−δ/3)^ℓ + N/p^k`, **asserted, unproved** | `o(1/N)`, no concrete `N` | ❌ | ❌ | ❌ | **out** |
| DeepFold | Thm 2, existence-shaped; `poly(\|L₀\|)/\|F\| + (1−Δ)^s` with `poly` **never instantiated** | capacity; ⚠ **Conjecture 1 infects the COMMITMENT** | ❌ root **+ (α,c)** | ❌ | ❌ | **out** |
| UltraFold | **no theorem in the paper** | — | — | — | — | **not a distinct target** |
| Galois-ring BaseFold | Thm 3, errors in `p^r` (residue field) not `\|GR\|` | `δ ≲ Δ/3`; ⚠ `p ≠ 2`; **no knowledge soundness** | ❌ no evaluation domain | ❌ | ❌ (Fact 2 unproved) | **out** |
| SwitchFold | Thm 6 (Big-O); Thm 2 per switch | ⭐ `δ/3`, UD, **zero conjectures** | ❌ interleaved matrix | RBR chain, but **Lemma 7 unproved** | needs Lemma 1 for arbitrary code | **out**, regime noted |
| STIR | Thm 5.1 / Lemma 5.4 | Johnson; `\|F\| = Ω(λ2^λ d²\|L\|^{3.5})`, *"not tight"* | ❌ + `Fill` oracle | ✅ | ✅ | **detour** — WHIR imports one lemma from it |
| Hyrax | — | — | ❌ **Pedersen, needs homomorphic commitment** | — | — | **no hash-based instantiation exists** |
| **TensorSwitch** 2025/2065 | Thm 1.1 / **Thm 8.5**: *"`C` with **MCA** and list-decoding up to `δ`"* ⟹ soundness `2^{−λ}` | ⚠ **unassessed against Crites–Stewart 2025/2046** | ? interleaved tensor | ✅ **has §2.5 RBR** | ⭐ takes **our predicate** as its hypothesis | ⚠ **UNASSESSED — cheapest open action** |

### 12.1 Corpus corrections this note produced

- `tensorcommitments.pdf` is **arXiv 2602.12630, an ML proof-of-inference paper** — not
  Bootle–Chiesa–Groth, not a tensor-query PCS.
- `ring-fully-succinct-integer-mod-pcs-successor-to-zinc-2026-347.pdf` is **not a Zinc successor** —
  different authors, a competitor. The real successor is `zincplus.pdf`.
- `jagged-pcs-sp1.pdf` ≡ `grey-succinct-jagged-…pdf` is the **superseded v1** of 2025/917.
- **2026/1367 has six byte-identical copies**, and `sok-hash-based-pcs-fri-basefold-stir-whir-…txt`
  is **truncated** (78 597 B vs 90 086 B) — do not grep that one.
- `whir.pdf` ≡ `whir-proximity-generator-mca-2024-1586.pdf`; `habock-…-2110` duplicated likewise.
- **Fetched because absent**: STIR (2024/390), Khatam–Zeilberger (2024/1843), Brakedown (2021/1043),
  Ligero (2022/1608), Hyrax (2017/1132), Bolt (2026/310), LigeSIS (2026/751). **Orion** is still absent.
- **`tensorswitch-2025-2065.pdf` is on disk and was on no lane's list.**

### 12.2 Errata found in the source papers (do not transcribe as printed)

| paper | defect |
|---|---|
| WHIR Lemma 4.10 | `min{1 − δ_C/2, B}` should be **`max`** — Selvage has it right; Cor. 4.11's printed `(1+ρ)/2` confirms |
| WHIR Def 4.9 | `δ ∈ (0, 1 − B)` should be `1 − **B\***` |
| WHIR Thm 7.5 | `δ < B*` should be `δ < 1 − B*` |
| WHIR §2.1.4 | rate `ρ_i := (2/k)^i·ρ` should be `(2/2^k)^i·ρ` |
| Haböck 2024/1571 p.10 | both fold numerators print `f(x) + f(−x)`; the odd part must be the **difference** over `2x` |
| Gemini Construction 1 | prints `f_e + ρ·f_e`; correct is **`f_e + ρ·f_o`** (Lemma 5.3's text swaps them instead) |
| Jagged Thm 1.5 | `2m/\|𝔽\|` should be **`(2m+1)/\|𝔽\|`** (its own Lemma 5.1) |
| Ligerito eqs (4)/(15)/(17) | `(m − n − 1)/(2m)` should be `(m + n − 1)/(2m)` — the printed form is **more favourable** |
| Ligerito eq (18) | summand prints `(d_i/(3m_i))^{\|S_i\|}`, should be `(1 − d_i/(3m_i))^{\|S_i\|}` |
| UltraFold | attributes a query bound to "DEEP-FRI [12]"; ref [12] is **DeepFold** |
| WHIR Lemma 4.10 proof | applies the generator at `1 − \|T\|/n ≤ δ` while holding only `err(δ)` — **needs `err` monotone, never stated**; Selvage's `herr_mono` is the repair |
