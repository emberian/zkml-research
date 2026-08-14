# BaseFold on the additive tower — step 1 of the short path

2026-08-14. Landed: `minidregg/Selvage/AdditiveBaseFold.lean` (838 lines, 54
declarations, 0 `sorry`, 13 `#print axioms` pins, 0 bare `#guard`), commit
`b5da623`. Whole-tree `lake build` green (8992 jobs); import boundary green;
`scripts/check-char2-vacuity.sh` green (29 263 declarations, **0 vacuous**).

---

## 0. How the `two_ne` vacuity was avoided — the machine-checked answer

`Selvage/Proximity.lean:178`'s `FoldingData` carries `two_ne : (2 : F) ≠ 0` as a
**structure field**, so at characteristic two the carrier is empty and every
theorem over it is free. The brief said to coordinate with the repairing lane;
that lane landed **`Selvage/CharTwoWall.lean`** while this one was running.

Three things, in order of how much they are worth:

1. **Cited, not restated.** My first draft duplicated the emptiness theorem as
   `foldingData_isEmpty_of_charTwo`. That duplicate is **deleted**;
   `AdditiveBaseFold` imports `Selvage.CharTwoWall` and points at
   `foldingData_isEmpty_charTwo` / `foldingData_vacuous_of_charTwo`. Two shapes
   that agree today disagree later.
2. **Structural avoidance.** Not one declaration in the file takes a
   `FoldingData`, a `FoldingTower`, `fold`, `proximityTest` or `chalExt` as an
   argument. The descent operator is `Minidregg.Theory.friFold`, which has no
   characteristic-≠-2 side condition anywhere.
3. ⭐ **Independent whole-tree confirmation.** `scripts/check-char2-vacuity.sh`
   (also the sibling lane's) scans every declaration in the tree for
   quantification over a char-2-refuted carrier and gates on the finding, not on
   a count. With `AdditiveBaseFold` in the tree it reports **0**. This is the
   part that is evidence rather than intent.

⚠ **The residual honest limit.** Non-vacuity of a *cited* lemma is argued by
inspection (it names no `FoldingData` in its statement) plus the keystones,
which instantiate the whole chain at `binaryTower 2 = GF(16)`. Premise
inhabitation is discharged rather than assumed: `tableOfPoly_preA_ne_preB` proves
the hypothesis of `terminal_ne_of_tableOfPoly_ne` is satisfied at a concrete
binary field, so `keystone_basis_ambiguity_terminal` is a non-empty existential.
(The two terminal values are proved **distinct**, not **computed** — computing
through GF(16) `decide` was deliberately avoided; every keystone here is
algebraic, via `fpGen_ne_zero` / `fpGen_ne_one` / `binaryTower_two_eq_zero`.)

---

## 1. The classification the brief asked for

The prime template is `Selvage/BaseFoldCompleteness.lean` (39 named results).
Item by item:

| prime object | verdict | where |
|---|---|---|
| **Möbius round trip** — `booleanMobiusPolynomial` a bijection onto `degreeLT (2^m)`, inverse `tableOfPoly` | ⭐ **PORTS VERBATIM, cited not reproved** | it is a change of basis on coefficient **vectors**; no field characteristic enters. `AdditiveBaseFold` reuses `booleanMobiusPolynomial_tableOfPoly`, `degree_booleanMobiusPolynomial_lt`, `booleanMobiusPolynomial_injective` unchanged |
| **the coefficient fold** `mleCoefficientFold p α = evenPart p + C α * oddPart p` | ⭐ **PORTS VERBATIM** | the fold on *coefficients* is `a ↦ a₀ + λ·a₁` in either world; `foldMleVariables` and `foldMleVariables_succ_last` are reused as-is |
| **the terminal-coefficient identity** `coeff_zero_foldMleVariables_eq_mle` | ⭐ **PORTS VERBATIM** | mentions no `FoldingData`; this is the single most valuable reuse |
| **the fold operator** (`FoldingData`, `fold`, `foldEven`/`foldOdd` at `±x`) | ✖ **GENUINELY DIFFERENT** | not "inconvenient" — *uninhabited*. Squaring is Frobenius (injective) in char 2, so `{x,−x}` fibres are singletons. Replaced by `friFold` over the additive coset `{x, x+β}` |
| **`fold_eval`** (fold of a codeword = codeword of the folded polynomial) | **CHAR-2 ANALOGUE** | `friFold_eval_decomp`. `Theory`'s `friFold_eval_poly` only asserts *some* folded polynomial exists; a descent needs it **named**, so the sharp form is proved here from `friFold_eq_even_add_mul_odd` + coset invariance (both already in `Theory`) |
| **the monomial packing** `X^{Σ cᵢ2^i}` | **CHAR-2 ANALOGUE — this is the whole content of the port** | `novelPack`: the LCH novelpoly packing `∏ᵢ Ŵᵢ^{cᵢ}`. Its recursion is *literally* `parityInterleave` with `expand F 2` replaced by `.comp (foldPoly (β 0))` |
| **degree bookkeeping** → terminal is a constant | **CHAR-2 ANALOGUE** | `novelPack_natDegree_lt`, and **unconditional**: the packing is inside the window for *any* input, so the low-degree base check is met by construction at every level, exactly as in the prime case |
| **tower-fold induction** `FoldingTower.word_eval_foldMleVariables` | **CHAR-2 ANALOGUE — with a new moving part** | `lchLevelWord_succ`. The multiplicative tower has a fixed domain chain `x ↦ x²`; here **the ordered basis is state** and folds alongside the word (`lchTowerBasis`, `additiveFoldedBasis_lchTowerBasis`) |
| **`basefold_terminal_word_eq`** — the terminal is `mle (tableOfPoly m p) r` for ANY window codeword | ⭐ **LANDED** | `lchLevelWord_terminal` + `exists_unique_table_novelPack`; see §2 |
| **`mem_range_booleanMobiusPolynomial_iff`** (image = window) | **CHAR-2 COMPANION PROVED** | `novelPack_surjective_on_window` + `novelPack_injective_of_natDegree_lt`: the packing is a **bijection of** the window (the Möbius map is a bijection *onto* it) |
| **`relDist_fold_le` / the distance bound** | ✅ **ALREADY PROVED ADDITIVELY — nothing new needed** | `Selvage/AdditiveProximity.lean`'s `additiveFold_distance_UD`, unconditional on `δ < (1−ρ)/3`, with `additiveProximityGap_UD` under it. Cited, not restated |
| **`basefold_opening_complete`** | **CHAR-2 ANALOGUE** | `lch_opening_complete`: starts at the committed word, every round is one `friFold` at a genuine nonzero pivot, terminates at the constant |

### The one structural discovery of the port

**In the multiplicative world the packing basis is canonical; in the additive
world it is a parameter.** Everything else is bookkeeping. `evenPart`/`oddPart`
split by `X²`, which the domain has no say in; `foldPoly_decompose` splits by
`q_β = X² + βX`, which the domain's *ordered basis* chooses. That single fact
produces the analogue (`novelPack`), the extra moving part in the tower
(`lchTowerBasis`), and the new ambiguity (§3).

---

## 2. The terminal identity — landed, and in its strong form

```
lchLevelWord_terminal :
  p.degree < 2^m →
  lchLevelWord β p r m 0 y = mle (tableOfPoly m p) (fun j : Fin m => r j.val)
```

for **every** `p` in the degree window, not only an honest packing — which is
the prime cone's point and it survives, because `tableOfPoly` is *total*. The
strong form is

```
exists_unique_table_novelPack :
  P.natDegree < 2^m →
  ∃! table, novelPack β m (booleanMobiusPolynomial m table) = P
```

i.e. every level-`m` codeword is the LCH commitment of exactly one Boolean
table. Composed, that is the round-by-round knowledge state's clause (b) as a
theorem at characteristic two: *"the terminal constant is the multilinear of
nothing in particular" is impossible.*

Nothing blocked it. The two things that could have and did not:

- The Möbius layer was expected to need a char-2 analogue. It does not — the
  Boolean Möbius transform is a statement about coefficient vectors, and
  `1 − x = 1 + x` changes nothing about `mle` or `mle_injective`.
- The novelpoly change of basis was expected to need `[ANTT-transform]`.
  It does not: `Theory/AdditiveNTTTransform.lean` **already closed it**
  (`novelBasisTransform_closed`), and in any case `novelPack`'s bijectivity is
  proved here directly and constructively from `foldPoly_decompose`.

⚠ **Scope, stated plainly.** This is the **completeness/algebra** leg, at the
same resolution as `BaseFoldCompleteness`: whole-level words, no Merkle/query
layer, no sumcheck braid, and no soundness claim. The additive soundness leg it
must be braided with is `additiveFold_distance_UD` (proved) plus a degree-2
sumcheck and an RBR knowledge-soundness instance (not done additively).

---

## 3. The teeth — the prime one ports, and characteristic two adds a new one

### 3a. The ported ambiguity, and it resolves the same way

The prime cone exhibits two commitments of "the same" data both passing the
descent and terminating at different constants, later resolved as *two honest
claims about different tables*. That resolution ports, because the terminal is
`mle (tableOfPoly m p) r` for the **same total `tableOfPoly`** in both worlds:

```
terminal_ne_of_tableOfPoly_ne :
  tableOfPoly m p ≠ tableOfPoly m q →
  ∃ r, ∀ y y', lchLevelWord β p r m 0 y ≠ lchLevelWord β' q r m 0 y'
```

Two words that terminate differently are two different tables — never one word
with two values. **Resolved, not merely named.**

### 3b. ⚑ The char-2-specific ambiguity — ONE codeword, ONE domain, TWO tables

`keystone_basis_ambiguity` / `keystone_basis_ambiguity_terminal`, at
`binaryTower 2 = GF(16)`, on the four-point domain `W = span_{GF(2)}{1, x₁}`:

| | basis | coefficient vector | committed codeword |
|---|---|---|---|
| A | `(1, x₁)` | `X²`, i.e. `(0,0,1,0)` | `X² + X` |
| B | `(x₁, 1)` | `C(1+x₁)·X + X²`, i.e. `(0, 1+x₁, 1, 0)` | `X² + X` |

Proved: the two packings are **equal**; the two `additiveDomain`s are **equal**
(same span, hence the same evaluation points and the same Merkle leaves); both
orderings are GF(2)-**linearly independent** (so neither is a degenerate setup);
the two `tableOfPoly`s are **different**; and the descents terminate at
**different constants** on a common challenge stream.

**Why this has no multiplicative counterpart.** There the packing basis is the
monomial basis, and the evaluation domain does not get a vote. Here the LCH
basis `X̂_c = ∏ Ŵᵢ^{cᵢ}` is built from the *ordered* β, while the domain is only
its *span*. At `m = 1` the packing is basis-independent (`novelPack_one`), which
is why the smallest witness needs `m = 2`.

⚑ **The finding, stated at deployment resolution: an additive-FRI transcript
that binds the domain but not the ORDERED BASIS does not determine the committed
multilinear.**

*Measured, with the instrument named.* `Selvage/AdditiveFriTower.lean` takes
`beta : ℕ → F` as a bare parameter and never absorbs it. The **deployed**
additive-FRI controllers —
`Compiler/Tower256AdditiveFriController.lean` (428 lines) and
`Compiler/Tower256AdditiveFriRawController.lean` (484 lines) — carry a
`domainId : Digest` **sponge domain-separation tag**, and `grep -n
'beta|basis|Basis|absorb'` over them returns **no basis binding at all**: the
transcript separates *channels*, not *bases*. The BCS/Fiat–Shamir schedule
(`BaseFoldBcs*`) is written for the multiplicative side, where the question does
not arise. ⚠ The instrument here is a grep over the additive controller cone plus
reading `AdditiveFriTower`'s signature — it is not a proof of absence over the
whole tree, and anyone repairing this should re-measure at the controller they
actually deploy.

**Named, not repaired here.** The repair is a transcript-layer change — absorb
β, *in order*, before the first challenge — and it belongs with whoever owns the
additive Fiat–Shamir schedule; doing it blind from this lane would be authoring
a transcript format for a cone I did not read. It is cheap, it is greenfield,
and it should be next.

---

## 4. Corrections to the brief, measured at source

- **`AdditiveFriQuery.lean` and its `m·2^(ℓ−1)/|F| + (1−τ)^q` bound are real**,
  as stated — but they are the *query/coherence* leg, not the descent algebra,
  and this port did not need them. The descent's own distance leg is
  `AdditiveProximity.additiveFold_distance_UD`.
- **The additive cone is further along than the brief implies.**
  `Theory/AdditiveNTTTransform.lean` **closes `[ANTT-transform]`**
  (`novelBasisTransform_closed`) and already carries `foldEven`/`foldOdd`,
  `friFold_eq_even_add_mul_odd`, coset invariance and `agree_pair`. The brief's
  "port the additive-NTT machinery" was in part "discover it is there".
- **`HalfThresholdFriTower.lean` is not binary** — confirmed, not used.
- **`AdditiveFriTower.lean` folds the REVERSED basis** (`additiveReverseBasis`,
  highest generator first) while `foldMleVariables`/`mleCoefficientFold` peel the
  **lowest** challenge first. `AdditiveBaseFold` folds LSB-first to match the
  multilinear layer, so its `lchTowerBasis` is *not* `AdditiveFriTower`'s
  `additiveTowerMap`. ⚠ **These two additive tower conventions now coexist and
  will disagree.** They should be unified — the deployed additive FRI's index
  layout decides which survives, and that decision is not mine to make silently.

---

## 5. What step 3 (ring-switching) now has to consume

The brief's premise holds: Diamond–Posen name "a characteristic-2 adaptation of
BaseFold" as their compilation target, and this is one. Concretely, what a
ring-switching compiler can now take as input:

- a **commitment map** `table ↦ novelPack β m (booleanMobiusPolynomial m table)`
  that is a proved bijection onto the level-`m` degree window;
- an **opening protocol** whose every round is one `friFold` at a nonzero pivot
  (`lch_opening_complete`), with the base check discharged by construction;
- a **terminal** pinned to `mle table r` for every codeword in the window;
- a **proved one-round distance bound** on `δ < (1−ρ)/3` to hang the soundness
  leg from.

⚠ Still missing for step 3, unchanged from the brief's assessment: **no `Basis`
of an extension over a subfield** anywhere in the tree, and `liftWord` points the
wrong way. `Selvage/RingSwitching.lean` landed from a sibling lane during this
session (commit `f5b604f`, "the compiler stated, and `liftWord`'s direction
fixed") — that is the seam to check next, and it should be checked *against*
`novelPack` rather than against the multiplicative packing.
