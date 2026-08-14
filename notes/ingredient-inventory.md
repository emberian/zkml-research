# The ingredient inventory — what the bag actually holds, and how composable it really is

*Survey lane, 2026-08-14. Target: `~/dev/minidregg` at `323a7b3` (working tree, other
lanes live). Framing (ember): "Lean is a bag of formal composable ingredients that we
build as we chart them out. We're basically doing pure basic research — formalize and
evaluate the landscape, not build one thing that dominates."*

**This document is a map, not a system.** It produces: a role catalogue with theorem
names; a per-ingredient generality classification (real / cosmetic / trap); the twin
and island lists; a gap list aimed at instantiation; and one refactor verdict.

---

## 0. Instruments, and what each can and cannot see

Every number below is measured. The instrument is named beside it, because a census
that cannot go red is not a census.

| instrument | what it answers | blind to |
|---|---|---|
| `scripts/check-char2-vacuity.sh` → `scripts/CharTwoVacuityCensus.lean` | does any declaration quantify over a carrier that is EMPTY at char 2 | any *other* empty regime; carriers not in its registry |
| `scripts/CarrierCensus.lean` | which structures are used as hypotheses and produced NOWHERE outside their home module | ⚑ **`private` producers** — private names are mangled, so `ours` fails and a private witness reads as absent |
| text census (this lane, `census.py`) — 473 files, 16,097 declarations | declaration names, kinds, namespaces, imports | `open`/dot-notation aliasing; anything the regex misses |
| identical-body hash (this lane, `semtwins.py`) | cross-module byte-identical declaration text, name-blinded | twins that were *retyped*, not copied |
| token reverse-index (this lane, `islands.py`) | declarations never mentioned outside their own module | over-counts consumers on common short names |
| import DAG (this lane, `dag.py`) | shared core vs leaves, module-level | intra-module deadness |

**Measured, tree-wide, today:**

- **473 `.lean` files, 16,097 text-level declarations; 29,276 declarations in the
  environment** (the environment count includes generated satellites).
- **ZERO `sorry`. ZERO `axiom` declarations.** Verified by grep for `:= sorry`,
  `by sorry`, `^\s*sorry\s*$`, `^axiom `. The house law holds. Every gap in this tree
  is carried as a **named `def … : Prop`** supplied as a hypothesis, which is the
  reason a gap list is even possible.
- **`IsPrimitiveRoot`: 0. `rootsOfUnity`: 0. `primitiveRoot`: 0. `nthRoots`: 0.**
  Re-verified in this lane. See §3.1 — this is *not* the gap it looks like.
- **455 `omit` lines**, of which **63 are `omit [Field F]`** — the direct measurement
  of cosmetic field binders. Breakdown: `[Fintype F]` 137, `[DecidableEq ι]` 90,
  `[Field F]` 63, `[Fintype ι]` 61, `[DecidableEq F]` 32, `[CharP F 2]` 3.
- **char-2 vacuity: 0 vacuous declarations** out of 29,276 scanned, 2 dead carriers
  registered, 5 exempt in the wall itself. The census's own sentence:
  *"the multiplicative and additive cones are disjoint."*
- **carrier census: 1501 carriers declared, 663 produced outside home, 627 unwitnessed
  and load-bearing, 622 actionable.**

---

## 1. The role catalogue

Roles are the slots a proof system is assembled from. For each: what we have, at what
generality, with the theorem names.

### 1.1 Codes and proximity — **the deepest, most general layer we own**

Import-DAG rank (transitive dependents inside `Selvage`+`Theory`, 188 modules):
`CorrelatedAgreement` **121**, `ReedSolomon` **119**, `ConstrainedCode` **108**.
These three are the true foundation — deeper than `Proximity` (46).

| module | primitives | headline theorems |
|---|---|---|
| `Selvage/CorrelatedAgreement.lean` | `relDist`, `close`, `AgreesOn`, `comb`, `structure ProximityGenerator`, `CorrelatedAgreement`, `IsProximityGenerator`, `MutualCAFailure`, `HasMutualCorrelatedAgreement`, `affineGenerator` | ⭐ `hasMutualCorrelatedAgreement_of_isProximityGenerator` (WHIR Lem 4.10, **any linear code**), `codeword_eq_of_close_of_close`, `relDist_triangle`, `one_div_card_le_relDist` |
| `Selvage/ReedSolomon.lean` | `evalOnDomain`, `reedSolomonCode` | ⭐ `reedSolomonCode_minDist` (exact MDS, not rounded), ⭐ `reedSolomonCode_hasMutualCorrelatedAgreement` (WHIR Cor 4.11) + `_closed`/`_of_le`/`_sqrtRate`, `reedSolomonCode_card_eq_top`, `card_agreeSet_lt_of_ne` |
| `Selvage/ProximityGapUD.lean` | — | ⭐⭐ `reedSolomonCode_isProximityGenerator_UD` — **`hPG` PROVED hypothesis-free on `δ ∈ (0,(1−ρ)/3)`**; `rs_proximityGap_UD`, `hasMutualCorrelatedAgreement_UD`, `foldDistancePreserving_UD` |
| `Selvage/ProximityGapUDSharp.lean` | `rsUdSharpError` | `rs_proximityGap_UD_sharp`, ⭐ `reedSolomonCode_isProximityGenerator_UD_sharp` — strictly sharper, same band, **zero `omit`, no `FoldingData`** |
| `Selvage/ProximityGapUDTight.lean` | `ZDegLE`, `lineAt`, ⚑ `PolishchukSpielman` | `exists_bw_solution` (unconditional Berlekamp–Welch), `bw_quotient_at`, ⭐ `rs_proximityGap_UD_full`, `reedSolomonCode_isProximityGenerator_UD_full`, `hasMutualCorrelatedAgreement_UD_full` — the `(2+ρ)/3 → (1+ρ)/2` upgrade, **each carrying `hPS` in its signature** |
| `Selvage/JohnsonRegime.lean` | `johnsonRadius`, ⚑ `WHIRConjecture412` | ⭐ `johnson_list_bound` (**any linear code**, via Chebyshev), `reedSolomon_johnson_list_bound`, ⭐ `whirConjecture412_of_ud_bound` (the conjecture *is a theorem* where `B` dominates the UD cap), ⭐ `column_sampling_count` / `column_sampling_bridge` / `_pr` |
| `Selvage/JohnsonMcaBridge.lean` | `haboeckRadius`, `haboeckEll`, `haboeckBadCount`, ⚑ `HaboeckTheorem2`, ⚑ `HaboeckErrorEnvelope` | `hasMutualCorrelatedAgreement_of_haboeckMCAAt`, ⭐ `whirConjecture412_rs_of_haboeck` — discharges the WHIR conjecture from Haböck 2025/2110 |
| `Selvage/ConstrainedCode.lean` | `structure LinearConstraint`, `dotWt`, `Satisfies`, `constrainedRS`, `batchConstraint`, `defectPoly` | ⭐ `card_batch_satisfying_le` (Schwartz–Zippel batching; the exact-membership kernel of WHIR Constr 5.5), `exists_dotWt_eq` |
| `Selvage/ConstrainedMask{,Multi}.lean` | `constrainedMaskSpace`, `constrainedMaskSpaceMulti` | `exists_constrainedMask_open`, ⭐ `constrainedMask_hiding`, `exists_constrainedMaskMulti_open`, `constrainedMaskMulti_hiding` |
| `Selvage/Erasure.lean` | `recoverFromColumns` | ⭐ `recoverFromColumns_sound` (full word equality), ⭐ `committed_word_recovered` — `[ACC-extract-bind]`(b) closed at UD |
| `Selvage/SubUdSeam.lean` | ⭐ `foldFamily f₀ g ρ = f₀ + ρ • g`, `subUdRecover`, `subUdSeamCounterfactual` | ⭐ `foldFamily_eq_comb` (**the seam's correlation IS the CA machinery's input, by `rfl`-level bridge**), ⭐ `subUdRecover_of_foldFamily`, ⭐ `no_column_extractor` (an *impossibility*: column resolution cannot work sub-UD) |

### 1.2 Folding / descent operators — **two disjoint cones, and the disjointness is proved**

**Multiplicative** (`Selvage/Proximity.lean` and its tower):

- `structure FoldingData` — fields `neg`, `dom_neg`, `sq`, `domSq_sq`, `sec`, `sq_sec`,
  `dom_ne_zero`, ⚑ `two_ne : (2:F) ≠ 0`. `dom`/`domSq` are *parameters*, so consecutive
  tower levels share embeddings definitionally.
- `foldEven`, `foldOdd`, ⭐ `fold D f α` (affine in α), `structure FoldingTower`,
  `FoldingTower.word`, `proximityTest`, `FoldDistancePreserving`, `acceptSet`.
- ⭐ `fold_eval`, ⭐ `fold_preserves_code` (degree halving), `card_eq_two_mul_card`
  (domains halve *exactly*), ⭐ `proximity_far_covering`, ⭐ `proximity_sound(_prob)`,
  ⭐ `close_of_correlatedAgreement` — **the reduction arrow from proximity gaps to
  folding soundness; the most-reused theorem in the FRI stack.**
- Two realizers of `[PROX-fold-distance]`: `foldDistancePreserving_of_lt_inv_card`
  (**unconditional**, sub-quantization, `b=1`) and
  `foldDistancePreserving_of_isProximityGenerator`.

**Half-threshold** (`Selvage/HalfThresholdRegime.lean` → `…Fri` → `…FriTower` →
`…FriTranscript` → `…FriQuery` → `…FriCoherent`):

- ⭐⭐ `correlatedAgreement_of_two_half_close` — the Raghavendra–Wootters 2×2 solve in
  Chai–Fan half-threshold form. **Any finite linear code, any characteristic, zero
  `omit`, zero conjectures, no `FoldingData`.** With `halfThreshold_bad_card_le_one`
  and `halfThreshold_pr_le ≤ 1/|F|`.
- `FoldDistanceTransition` (the two-radius generalization `FoldDistancePreserving`
  cannot state), `fold_eq_foldFamily` (proof: `rfl`),
  ⭐⭐ `foldDistanceTransition_halfThreshold` (δ-far ⟹ δ/2-far outside ≤1 challenge),
  ⭐⭐ `proximity_sound_halfThen_UD` (unconditional), `proximity_sound_rateHalf_postJohnson`
  (rate 1/2, δ=3/10 — **strictly beyond Johnson, unconditionally**),
  ⭐⭐ `committedFri_sound_halfThen_UD`, ⭐⭐ `friAdaptive_sampled_sound`,
  ⭐⭐ `friAdaptive_coherent_sampled_sound`.

**Additive / char-2** (`Theory/AdditiveNTT*` → `Selvage/Additive*`):

- `foldMap β x = x² + βx`, `foldPoly`, `friFold`, `subspaceVanishing` (Ŵᵢ),
  `novelBasis`, `additiveDomain` (a `Submodule (ZMod 2) F`), `domainPoint`.
- ⭐ `foldPoly_decompose` — the LCH split `P = P₀∘q_β + X·(P₁∘q_β)`, **the additive
  replacement for the multiplicative even/odd split**. `friFold_coset_invariant`,
  `friFold_eval_poly`, `foldMap_add`, `foldMap_two_to_one`.
- `novelBasisTransform_closed : NovelBasisTransform` — the AdditiveNTT residual is
  **discharged** one import layer up in `AdditiveNTTTransform`.
- ⭐ `additiveProximityGap_UD` and `additiveFold_distance_UD` — proved
  **unconditionally** on `δ < (1−ρ)/3`. `additiveProximityGap_exact` at δ=0.
- `structure AdditiveFriTower` (fields `beta`, `offset`,
  `independent : LinearIndependent (ZMod 2) …`, `rounds_le`),
  ⭐ `additiveFriAdaptive_coherent_sampled_sound_UD`.
- **`Selvage/AdditiveBaseFold.lean` (landed today, `b5da623`)**: `novelPack` (LCH
  novelpoly packing), `lchTowerBasis`, `lchPivot`, `lchLevelWord`;
  ⭐ `novelPack_friFold`, `lchLevelWord_succ`, `lchLevelWord_terminal`,
  `exists_unique_table_novelPack`, ⭐ `lch_opening_complete`.
- ⭐ `Selvage/CharTwoWall.lean` — `foldingData_charTwo_False`,
  `foldingData_isEmpty_charTwo`, `foldingData_vacuous_of_charTwo`,
  `foldingTower_charTwo_False`, `foldingTower_vacuous_of_charTwo`, plus **two negative
  controls** (`charTwoHeightZeroTower`, `strippedCharTwoWitness`) proving the wall is
  at `two_ne` and at `0 < m`, not at char 2 as such.

### 1.3 Sumcheck at each degree — **generic engine, hand-written realizers**

⚑ **The central measured answer for this role:** the *protocol* layer is genuinely
degree-generic; the *realizer* layer is three hand-written copies.

| layer | degree binder | status |
|---|---|---|
| `Selvage/Sumcheck.lean` `sumcheck_soundness` | `{v d : ℕ}` | **REAL** degree-generic |
| `Selvage/SumcheckReduction.lean` `adaptive_sumcheck_soundness`, `adaptive_sumcheck_retires_constraint`, `sumcheck_retires_batch` | `{v d : ℕ}` | **REAL** degree-generic |
| `Selvage/SumcheckRbr.lean` `sumcheckReduction`, `sumcheckKState`, `sumcheckRbrKnowledgeSound` | `(k d : ℕ)` | **REAL** degree- *and* round-generic; per-round `d/|F|` by `rfl` |
| honest realizer | **d = 1, 2, 3 written three times** | three parallel copies |

The one induction (`lie_persists` → `sumcheck_reduction` → union bound) lives once, in
`Selvage/Sumcheck.lean`. Each degree file's soundness theorem is a literal one-liner
against it:

- `QuadraticSumcheck.lean:227` `quad_sumcheck_soundness` — `adaptive_sumcheck_soundness (v := m) (d := 2) … ; simpa`
- `AirSumcheckCubic.lean:366` `cubic_sumcheck_soundness` — `adaptive_sumcheck_soundness (v := m) (d := 3) … ; simpa`
- `MultilinearExtension.lean:587` `mle_retires_constraint` — `adaptive_sumcheck_retires_constraint (v := v) (d := 1) …`

What **is** triplicated (~100 lines each, structurally parallel, no shared abstraction):

| d=1 (`MultilinearExtension`) | d=2 (`QuadraticSumcheck`) | d=3 (`AirSumcheckCubic`) |
|---|---|---|
| `roundPoly` / `_eval` / `_degree` | `quadRoundPoly` / `_eval` / `_degree` | `cubicRoundPoly` / `_eval` / `_degree` |
| `mleHonest` | `quadHonest` | `cubicHonest` |
| `mleHonest_prefixMeasurable` | `quadHonest_prefixMeasurable` | `cubicHonest_prefixMeasurable` |
| `mleHonest_degree` | `quadHonest_degree` | `cubicHonest_degree` |
| `mleHonest_boolean_sum` | `quadHonest_boolean_sum` | `cubicHonest_boolean_sum` |
| `scChain_mleHonest_final` | `scChain_quadHonest_final` | `scChain_cubicHonest_final` |
| `mleHonest_complete` | `quadHonest_complete` | `cubicHonest_complete` |
| — | `prodDiff`, `quadCross`, `roundSum_prodDiff` | `cubicForm`, `innerC0..2`, `cubicC0..3`, `cubicRound0..3` |

All three share the arity-generic `roundSum` / `glue` / `suffixSplit` /
`roundSum_zero` / `_succ` / `_last` skeleton from `MultilinearExtension`, so the
*cube-folding* is written once. `AirSumcheckCubic` **does** import
`AirSumcheckQuadratic`, but the only cross-reference is `cubicForm_subsumes_prodDiff`
— a *denotational* subsumption (`funext; simp; ring`), **not** a derivation of cubic
soundness from quadratic. Both realizer stacks are live and both are consumed
independently (`SpartanR1CS` uses `cubicHonest` for phase 1 and
`quad_sumcheck_soundness` for phase 2).

**There is no degree-generic realizer** — no `dHonest : (d : ℕ) → …` anywhere. A d=4
rung means a fourth copy. See §6.1.

**MLE machinery — arity-generic, REAL.** `mle`, `chiEval`, `roundSum`, `SuffixCube`,
`glue`, `suffixSplit` are all `{m : ℕ}`-generic over `[CommRing F]`, universe-poly.
Two-block variants (`mle₂`, `rowHalf`/`colHalf`, `flatten₂` via `Fin.append`) are
`{μ κ ν : ℕ}`-generic. Headlines: `mle_agrees`, `mle_injective`, `mle_hypercube_sum`,
`mle_multilinear`, ⭐ `multiAffine_eq_mle` (uniqueness, `[Nontrivial F]`),
⭐ `mle_zero_uniform_bound` (multivariate Schwartz–Zippel, `≤ m/|F|`),
⭐ `eqMle_fold` (`∑_b eq(z,b)·f(b) = f̂(z)` — the zerocheck→sumcheck bridge),
`eqMle_eq_mle`, ⭐ `foldMleVariables_booleanMobiusPolynomial` (the MLE↔coefficient
bridge BaseFold runs on).

### 1.3b The relation layer — **four formats, no `CCS`, no trace-AIR**

**1. `LinearConstraint`** — `Selvage/ConstrainedCode.lean:98`. `{wt : ι → F, target : F}`,
`Satisfies f c := dotWt c.wt f = c.target`, with `exists_dotWt_eq` (every linear
functional *is* a `dotWt`). **The universal currency of the whole slice** — `AirSumcheck`,
both AIR sumcheck rungs, and Spartan's inner phase all reduce to it.

**2. `Gate` / `WireRef` / `GateOp` / `FlatOut` / `Flat`** — `Compiler/AirFlatten.lean`.
The degree-≤2 gate-list format. ⭐ `flatten_constraint_iff`,
`flatten_forces`, `flatten_sound`, `flatten_aux_unique`. `[AIR-flatten]` **CLOSED**.

**3. `AirSig` / `ConstraintSystem`** — `Compiler/Air.lean:55`. ⚠ **"AIR" here means an
arithmetic expression DSL as a free term algebra over a signature** — `AirOp` with
`const/var/add/mul`, `ConstraintSystem := List (Term (AirSig F Idx))`, two readings
proved equal by initiality (`eval_agrees_exec`, `accepts_iff_semHolds`). **It is not a
trace/transition AIR**: no columns, no row-shift, no transition constraint. Do not read
it as STARK-AIR.

**4. `R1CSMatrix`** — `Assurance/SpartanR1CS.lean:150`. A bare dense-table abbrev
`(Fin s → Bool) → (Fin t → Bool) → F`, with `R1CSSat` and `r1csDefect`. No `structure`,
no public/private input split, no `z = (1, io, w)` convention.

**`SpartanR1CS.lean` is fully parameterized**, not specialized: `{A B C : R1CSMatrix F s t}`,
`{z}`, `{s t : ℕ}`, adaptive prover families `outer`/`inner`. `SpartanExample` at
`ZMod 7, s = t = 1` is a separate teeth namespace. Its top-level theorem:

```lean
theorem spartan_sound {A B C : R1CSMatrix F s t} {z}
    (hunsat : ¬ R1CSSat A B C z) {vA vB vC : SpartanClaim F s} {outer} {inner}
    (houterPm) (houterDeg : … < 3+1) (hinnerPm) (hinnerDeg : … < 2+1) :
    uniformProb _ (SpartanAccepts A B C z vA vB vC outer inner)
      ≤ (s/|F| + s*(3/|F|)) + 2/|F| + t*(2/|F|)
```

Only adversary-side hypotheses; both honest sides are BUILT
(`spartanOuterHonest := cubicHonest (eqHead τ) …`, `spartanInnerHonest` = the d=2
realizer). **What commit `ef12ccf` actually did**: it replaced the idealized terminal
check with `SpartanOuterRealAccepts` (line 508) — a deployed predicate with *no honest
side in it*, terminating at
`spartanTerminal τ rx vA vB vC := eqMle τ rx * (vA*vB − vC)`, computable from the
verifier's own randomness plus prover-supplied values — plus
`outerReal_iff_sumcheckAccepts` and a case split. The file says so itself at line 600:
*"The composition moved the idealization from phase 1 to phase 2; it did not remove it
from the stack."* The survivor is `[SPARTAN-pcs]`.

⭐ **Two theorems worth pulling out as reusable relation-layer facts:**
`cubicForm_hadamard` (the Hadamard zerocheck `eq·(Â·B̂ − Ĉ)` **is** a `cubicForm`) and
`cubicForm_fraction_layer` (the **GKR fraction-tree layer** `eq(z,x)·(p_L·q_R + p_R·q_L)`
**is** a `cubicForm`). The second is the load-bearing one for §6: the degree-3 engine
already denotes a GKR layer.

### 1.4 Commitment and opening

- `Selvage/Commitment.lean`: `structure OpeningScheme (Root F ι Op)` — fields `commit`,
  `openAt`, `verifyOpen`, `verifyOpen_commit`; `OpeningScheme.PositionBinding`;
  `structure BindingCommitment extends OpeningScheme` (field `binding`);
  `idealCommitment` as the inhabitant; `OpeningScheme.PositionEquivocation`.
  Theorems: `BindingCommitment.word_binding`, `.opened_eq_committed`,
  `.commit_injective`, `.not_positionEquivocation`, `committed_extract_bind`,
  `committed_fold_bind`, `decider_open_sound`, `decider_open_complete`.
  Refutation witness: `equivocal_not_binding`, `equivocal_breaks_extract_bind`.
- `Selvage/BinaryMerkle.lean`: `structure HashSuite (Value Digest)`, `cubeRoot`,
  `cubePath`, `recompute`, `openingScheme`;
  ⭐ `positionBinding_of_collisionFree`. **Fully field-free** — `{Value Digest : Type*}`,
  no `Field`, no carrier. "Binary" = binary *tree* over `Fin k → Bool`, not GF(2).

### 1.5 Fiat–Shamir and the RO model

- `Selvage/Rbr.lean`: `structure Reduction : Type 1`, `structure Stmt`,
  `structure KStateFn`, `structure RbrKnowledgeSoundness`, plus the straightline layer
  `Salt`/`SrMove`/`SrOutput`/`SrProver`/`SrExtractor`/`StraightlineSrKnowledgeSoundness`,
  and the generic finite-probability kit `uniformProb` + `fracHamming` + `RelaxedMem`.
- `Selvage/Depth.lean` (2025 lines, **no codes, no folding — pure RBR depth
  composition**): ⭐ `OB2_depth_composition_false` — an **audit refutation** of the
  as-stated obligation (`Z = ∅`, `εrbr := fun _ => −1`, `t = 0`); then
  `gameSlotBound_proved : GameSlotBound` closing `[OB-2a]`, and
  ⭐⭐ `OB2_depth_composition_nonneg_proved` — the repaired obligation, no remaining seam.
  Its `uniformProb_*` kit (`_mono`, `_or_le`, `_exists_le`, `_equiv`, `_prod_le`,
  `_pushforward_le`) is the union-bound engine every soundness head runs on and has
  **zero algebraic dependencies**.

### 1.6 Field and extension machinery

| module | what it gives | reusable at a prime field? |
|---|---|---|
| `Theory/ExtensionBasis.lean` | `cubeBasis` (needs only `finrank K L = 2^κ`), `packOf`, `packEquiv`, `towerCubeBasis`, `biniusCubeBasis`; `no_cubeBasis_of_finrank_ne`, `packOf_bijective`, `towerExt_finrank` | ⭐ **YES** — `{K L}[Field][Field][Algebra]`, no characteristic, zero `omit` |
| `Selvage/BabyBearExt4.lean` | `BabyBear = ZMod 2013265921`, `extensionPolynomial = X⁴ − 11`, `Ext4 = AdjoinRoot`; `eleven_euler_witness`, `extensionPolynomial_irreducible`, `ext4_finrank = 4` | concrete carrier — and `finrank = 4 = 2²` **feeds `cubeBasis` at κ=2** |
| `Selvage/SmallField.lean` | `securityBits`, `algebraMapEmb`, ⭐ `extDomain = Embedding.trans` (**domain transport needs no root structure**), `liftWord`, `liftWordₗ`; `sumcheck_lambda_secure(_ext)`, `card_extension`; and the teeth `smallField_bound_vacuous`, `smallField_bound_allows_certainty`, `smallField_rescued_by_extension` | ⭐ **YES**, prime-field-native |
| `Selvage/ExtensionChallengeBridge.lean` | `liftConstraint`; `satisfies_liftConstraint_iff`, `card_lifted_batch_satisfying_le` | ⭐ **YES**, no characteristic |
| `Theory/CyclotomicInertia.lean` | ⚑ **the smooth-domain API**: `exists_unitsZMod_orderOf_eq {d} (hd : d ∣ p−1) : ∃ u, orderOf u = d`, `not_exists_subgroup_card_eq`, `goldilocks_domain_exists`, `p61_domain_exists`, `goldilocks_no_domain_two_pow_33`; plus `orderOf_koalaBear_three_pow`, `irreducible_cyclotomic_three_pow`, `KBCyc81_finrank = 54`, `p61_prime` | ⭐ **YES — this is what stands in for `IsPrimitiveRoot`** |
| `Theory/BinaryTower{,FanPaar,Trace,FanPaarCodec}.lean` | `binaryTower k = GaloisField 2 (2^k)`, `fpGen` (**built**, not assumed), `towerMul`, `Tower256 = binaryTower 8`, `codec` | char-2 only, correctly |
| `Theory/Bignum.lean`, `Theory/CrossModulus.lean`, `Theory/IntegerFingerprint.lean` | radix limbs (`Limbs`, `equivFin`), modular views + CRT (`value_unique_below_product`), integer fingerprinting (`Row`, `fingerprint_complete`, ⭐ `adaptive_quotient_defeats_fingerprint`) | **YES**, no field at all |

### 1.7 Lookup / permutation — **one general primitive, no product layer**

- ⭐ `Selvage/LogupStar.lean` is **fully general**: `{F : Type*} [Field F]`,
  `{κ ι} [Fintype κ] [Fintype ι] [DecidableEq ι]`, arbitrary table `J : ι → F`,
  arbitrary index map `I : κ → ι`, arbitrary weights `X : κ → F`, **no characteristic
  hypothesis**. Primitives `logupPushforward`, `logupDot`, `logupLogDerivative`,
  `logupDenominator`, `logupCofactor`, `logupDefect`. Headlines
  `logup_pullback_pushforward`, `logup_logDerivative_complete`,
  `logupDefect_ne_zero_of_ne`, `logupDefect_natDegree_le`,
  ⭐ `logup_wrong_rational_accept_prob_le` (≤ `(|ι|−1)/|F|`),
  ⭐ `logup_wrong_or_pole_prob_le` — **poles are counted, not excluded from the sample
  space**, which is unusually honest. Scope disclaimed in-file: it is *"a
  committed-pushforward integrity kernel, not a complete lookup-soundness theorem"*;
  `[LOGUP-PULLBACK-SOUND]` and `[LOGUP-ADDRESS-LINK]` are named and external.
- `Selvage/BinaryLookup.lean` + `Selvage/LogupIndexLink.lean` are the address bridge:
  `binaryTableDot_lookupEq_eq_mle`, `canonicalIncidencePushforward_eq_logupPushforward`,
  `canonical_indexed_lookup_pullback`.
- Everything under `Compiler/Tower256Logup*` and `Assurance/Tower256Logup*` is a
  **deployment profile** around LogupStar, not a second primitive.

⚑ **There is NO permutation/multiset argument, and NO product layer.** Measured:
`grandProduct` 0 files, `fractionalSum` 0, `productTree`/`fracTree`/`fractionTree` 0.
`GKR` appears in 4 files and the *only* artifact is
`Assurance/AirSumcheckCubic.cubicForm_fraction_layer` — a single algebraic identity
showing that a GKR fraction-tree layer's summand `eq(z,x)·(p_L·q_R + p_R·q_L)` **is an
instance of the landed degree-3 round form**. No layer object, no tree, no recursion,
no soundness theorem. The tree offers only *indexed* lookup; the docblock explicitly
declines the unindexed-multiset primitive, flagging that it would need noncancelling
multiplicities in char 2.

### 1.8 Soundness accounting — **two shapes, and the better one is not the one in use**

| object | where | shape | composable? |
|---|---|---|---|
| `structure SoundnessParams` | `Assurance/ErrorBudget.lean` | a flat **parameter** record (11 ℕ/ℝ knobs), with legs as separate `def`s: `errStarUD`, `grindingTerm`, `sumcheckTerm`, `crTerm`, `proximityTerm`, summed by `soundnessError` | **by inheritance, not by leg-addition** — no `legs : List ℝ`, no fold, no `Budget × Budget → Budget`. Adding a leg means editing `soundnessError` and re-proving `soundnessError_bound`. |
| ⭐ `structure AuditParams` | `Selvage/AuditSampling.lean` | a genuine **error-leg record with proof-carrying fields** (`p, εchk, εbind, εbeacon` + their nonneg/le-one proofs), derived `q := p(1−εchk) − εbind − εbeacon`, legs as `def … : Prop` (`BeaconLeg`, `ChkLeg`, `BindLeg`) bundled in `structure DetectionLegs` | ⭐ **YES** — this is the "named legs, add a leg" pattern |

`soundnessError_bound` is a **real theorem** over one explicit product coin space, via
`uniformProb_four_prod_le`, citing `lightClientGrinding_sound`, `sumcheck_soundness`,
`commitCR_of_RO_pow`, `hasMutualCorrelatedAgreement_UD` — **mutual CA is discharged by
the proved UD realizer, not left as a free hypothesis.** Extension *is* first-class and
done twice (`PoWSoundnessParams extends SoundnessParams`, `ChallengeFieldProfile`), with
backward compatibility **proved** (`pow_zero_recovers`, `uniform_one_gate_recovers`).
Two-sided numbers throughout (`deployedBudget_secure ≤ 2⁻⁵⁵` **and**
`deployedBudget_ceiling > 2⁻⁵⁶`), plus the vacuity control
`budgetF₅_value : soundnessError budgetF₅ = 133/10` — an "error" of 13.3, exhibited on
purpose.

Residuals: `[BUDGET-compose]` (the bound is at the **product measure** — four
independent coin blocks — while the deployed system runs **one** oracle; the four
adversaries are quantified separately and are never identified as one prover's single
execution) and `[BUDGET-PoW-compose]` (arithmetic core closed in
`Assurance/PowGrinding.lean` via `powGrindingWin_le`; the deployed nonce protocol and
domain separation are not).

⚑ **`Assurance/TwoRegimeQueryBudget.lean` carries the best design idea in the tree.**
`structure QErr (r : Regime)` — **the regime is carried IN THE TYPE**, so `QErr .UDR`
and `QErr .JBR` are different types and a UDR number cannot be summed or `min`'d with a
JBR number without a visible regime change. Plus `Regime.status`
(`proven`/`idealised`/`withdrawn`), `Regime.Reportable`, and
**`theorem cbr_not_reportable`** — the capacity regime is *mechanically barred*
(Crites–Stewart 2025/2046). Teeth include
`ir2_the_conjectured_130_is_the_withdrawn_regime` and
`ir2_only_the_withdrawn_regime_clears_128`. The same pattern appears in
`Selvage/RateRegimeSelector.lean` as `inductive RateRegimeRequest`, where the Johnson
branch **cannot be constructed** without `HaboeckTheorem2`.

### 1.9 Zero knowledge — the deepest single ladder

`ZK` → `ZKHiding` → `ConstrainedMask(Multi)` → `ZkArgument` → `RbrZeroKnowledge` →
`ZkTriangular` → `ZkExtraction` → `ZkRbrGame`. Every file's headline is a
`structure … : Prop` whose *field types are the conclusions of cited theorems*,
discharged by a `_of_*` composition theorem, plus refutation teeth.

⚑ **The design point, and it is reusable far outside ZK: the quantifier position IS the
separation.** `ZkArgument`'s `knowledge_sound` quantifies a second challenge `γ'`;
`zero_knowledge : MaskedOpeningHiding M q γ` contains no `γ'` at all. `ZkRbrGame` scales
this to nine fields on one parameter tuple, where `γalt` appears only in the knowledge
fields and `ηalt` only in `pair_extraction`.

Headlines: `mask_bijOn`, `zkAccScheme_iff_bijOn` (audit transparency — no hidden
strength), ⭐ `maskedOpeningHiding_of_surj` (hiding follows from **one** property:
surjectivity of the opening map on the mask space — the reusable interface),
`rs_maskedOpeningHiding`, `constrainedMask_hiding`, `constrainedMaskMulti_hiding`,
`zkArgument_of_hiding`, `rbrZeroKnowledge_of_rounds`,
⭐ `zkRbrError_eq_accRbrError_exact` (ZK round price and soundness round price on one
scale), ⭐ `triangularHiding_of_rounds`, ⭐ `partialFold_eq_triFold`,
`zkRbrGame_holds`, `selvage_zk_argument`.

**Proved negatives** (not conjectured): `not_maskedOpeningHiding_of_gt` (beyond the
degree bound, hiding *fails*), `masked_pair_ambiguous`,
`not_constrainedMask_hiding_of_recoverable` (the `t ≥ d` recovery regime is
*incompatible* with constrained-mask hiding), `tri_dependence` vs `product_model_blind`.

**Generality: REAL, and the least cosmetic slice in the tree — exactly ONE `omit`
across nine files** (`ZkExtraction:762`). Unlike the metric layer, the ZK development
genuinely consumes its field/module structure. Every hiding result needs `γ ≠ 0`, and
every file proves that hypothesis load-bearing by refutation.

### 1.10 Ligerito-family interleaved codes — `Selvage/LigeritoInterleaved.lean`

Landed today (`0c08c93`), 567 lines. Imports **only** `Selvage.CorrelatedAgreement` +
two Mathlib files — deliberately not `Selvage.Proximity`, and that abstinence is the
file's char-2 claim.

**Defs** (all at an arbitrary module alphabet `{V} [AddCommGroup V] [Module F V]`):
`relDistV`, `closeV`, `AgreesOnV`, `combV`, `CorrelatedAgreementV`,
`IsProximityGeneratorV`, `interleavedCode m C` (DG24 `Cᵐ`, column-major, all four
submodule fields proved inline), `tensorCoeff` (the Kronecker vector `⨂ᵢ(1−rᵢ, rᵢ)`
**materialized**, where the tree previously had only the evaluated product form).

**The headline, verbatim:**

```lean
theorem correlatedAgreement_iff_closeV_interleaved [Nonempty ι]
    {C : Submodule F (ι → F)} {δ : ℝ} {f : Fin m → ι → F} :
    CorrelatedAgreement C δ f ↔ closeV δ (interleavedCode m C) (Function.swap f)
```

Arbitrary `ι`, arbitrary `F`, arbitrary `m`, arbitrary submodule `C`, arbitrary `δ`, no
characteristic, and it is an **`↔`**. Guarded against vacuity by `interleavedCode_top`.
**REAL**, and the file's thesis is precisely that the interleaved-code metric *is* our
metric transposed — so the five `rfl` bridges (`relDistV_eq_relDist`,
`closeV_eq_close`, `correlatedAgreementV_eq_correlatedAgreement`, …) are
**cosmetic by construction and that is the deliverable**, not a defect. Also genuinely
new: `agreeSet_card_ge_of_relDistV_le`, the converse `CorrelatedAgreement.lean` lacks.

**Both errata named and proved**: `printed_rs_bound_is_optimistic`,
`printed_generic_bound_is_optimistic` (with `correctedBase_sub_printedBase`).

⚠ **`LigeritoSound` as stated is near-vacuous** — `0 < rounds → accepts → (¬guarantee →
err > 0)` carries quantifier structure only. The docblock says so ("left deliberately
abstract in the acceptance predicate; this file has no transcript object"), which makes
it honest, but it should not be cited as an obligation with content.

**⚑ The 12 named missing lemmas are NOT in the `.lean`** — they are in
`~/dev/zkml-research/notes/ligerito-exploration.md` §4 (lines 331–375). The four
in-file obligation `Prop`s (`InterleavingPreservesProximityGap`,
`TensorStyleProximityGap`, `MatVecProductSound`, `LigeritoSound`, tag
`[LIGERITO-interleaved]`) are the *targets*; the 12 are the route:

| tier | lemma | note |
|---|---|---|
| A1 | `interleavedCode_minDist` | cheap, days |
| A2 | `interleavedCode_uniqueDecoding` | immediate from A1 + the **existing** `codeword_eq_of_close_of_close` |
| **A3** | `interleavingPreservesProximityGap` (DG24 Thm 3.1) | ⚑ **the only substantial mathematics** |
| A4 | `tensorCoeff_succ` | nothing is currently proved about `tensorCoeff` — it is a bare `def` |
| A5 | `tensorStyleProximityGap_of_affineLineGap` (DG24 Thm 3.6 / AER24) | induction on `ϑ` |
| **A6** | `openingSchemeV` | ⚑ `OpeningScheme` with its value type generalized `F → V`. Mechanical but **wide** — every consumer of `verifyOpen` re-types |
| A7 | `positionBinding_columns` | `BinaryMerkle` binding at **column** leaves; likely direct from `positionBinding_of_collisionFree`. *Verify, do not assume.* |
| A8 | `matVecProductSound_of_*` | assembly of A1–A7 |
| B1 | `partialSumcheck_sound` | ⚑ sumcheck reducing `k → k'` variables, **not `k → 0`** |
| B2 | `batchedSumcheck_sound` | the `+1/|F|` batching term |
| B3 | `gluedSumcheck_sound` | the round-to-round hand-off |
| B4 | `ligeritoSound_induction` | induction on `ℓ` tallying the **corrected** `ligeritoErrRS` |

Tier C is a wall, not a lemma list: (i) knowledge soundness needs expected-PPT rewinding
extractors — a framework we do not have, inherited from the Ligero family since Ligerito
proves soundness only; (ii) BCIKS Thm 4.1 at `d/2`, already carried behind
`PolishchukSpielman`, and **avoidable** by targeting the general-linear-code bound at
1.63× proof size.

---

## 2. ⚑ Generality, measured — real / cosmetic / trap

This is the deliverable. For each ingredient: **what does it actually quantify over?**

### 2.1 The one-line verdict

**Generality in this tree is mostly REAL, occasionally COSMETIC in a way that is
*honestly annotated by the `omit` lines themselves*, and TRAP in exactly one place —
which is already detected, gated, and proved.**

That is a better answer than I expected to be able to write, and it is the reason §5's
verdict is a refusal rather than a refactor.

### 2.2 COSMETIC — measured by `omit`, 455 lines

An `omit [C]` line is a *confession in the source* that the binder was not used. The
distribution says what is decorative:

| omitted | count | reading |
|---|---|---|
| `[Fintype F]` | 137 | field finiteness matters only inside the `uniformProb` bounds |
| `[DecidableEq ι]` | 90 | index decidability is a `Finset` convenience, not content |
| **`[Field F]`** | **63** | ⚑ **the metric, probability, counting, and syntactic layers need no field at all** |
| `[Fintype ι]` | 61 | — |
| `[DecidableEq F]` | 32 | — |
| `[CharP F 2]` | 3 | only in `AdditiveFriTower`/`AdditiveFriQuery` |

Densest `omit` files (i.e. most-decorative binders): `ConstrainedCode` 22,
`OutOfDomain` 21, `SumcheckReduction` 20, `ProximityGapUDTight` 20, `AirSumcheckCubic` 20,
`AirSumcheckQuadratic` 16, `CorrelatedAgreement` 15, `AirFlatten` 14, `SpartanR1CS` 14.

**Four genuinely field-free sublayers** fall out of this, and they are the most
transplantable things in the tree:

1. **The union-bound / counting engine** — `Selvage/Depth.lean`'s `uniformProb_*` kit
   (`_mono`, `_or_le`, `_exists_le`, `_equiv`, `_prod_le`, `_pushforward_le`) plus
   `Proximity.card_filter_exists_coord_mem_le`. `{C : Type} [Fintype C]`, **no algebra
   whatsoever**. Every soundness head in the tree runs on it.
2. **The metric layer** — `relDist`, `close`, `AgreesOn`, `relDist_triangle`,
   `one_div_card_le_relDist` all carry `omit [Field F]`.
3. **The column-sampling bridge** — `JohnsonRegime.column_sampling_count` /
   `column_sampling_bridge` / `_pr` carry `omit [DecidableEq ι] [Field F]`: pure
   counting over any `Fintype ι` and any type `F`.
4. **The AIR flattener** — `Compiler/AirFlatten.lean` has 12 `omit [Field F]`; the whole
   syntactic gate-flattening pipeline is field-free.

⚠ Cosmetic here is **not** a defect. It is the tree telling you, in machine-checked
form, which lemmas you can lift into a different algebraic setting for free. It is
actionable *generality*, not decoration.

### 2.3 TRAP — exactly one carrier, and it is gated

`Selvage.Proximity.FoldingData` carries `two_ne : (2:F) ≠ 0` as a **structure field**,
so it is an **empty type at characteristic two** and every theorem quantified over it
is silently vacuously true there — on a green build, passing its axiom pin.

**Blast radius, measured by the carrier census: 58 declarations quantify over
`FoldingData`.** Files in the cone: `Proximity`, `ProximityGapUD` (one theorem),
`ProximityGapUDTight` (one theorem), `HalfThresholdFri`, `HalfThresholdFriTower`,
`HalfThresholdFriTranscript`, `HalfThresholdFriQuery`, `HalfThresholdFriCoherent`,
`DeciderProximity` (deployed section), `RateRegimeSelector`,
`BaseFoldRawCommittedIor`, `BaseFoldBinaryMerkle`, `BaseFoldCompleteness`.

**The trap is DETECTED, not merely documented.** `Selvage/CharTwoWall.lean` names it as
theorems (`foldingData_charTwo_False`, `foldingData_vacuous_of_charTwo`,
`foldingTower_charTwo_False`), proves the wall is at `two_ne` and at `0 < m` rather
than at char 2 as such (`charTwoHeightZeroTower`, `strippedCharTwoWitness`), and
`scripts/check-char2-vacuity.sh` gates **on the finding** — the honest number is zero
and the tree is at zero. Re-measured this lane: **29,276 declarations scanned, 0
vacuous.**

⚑ **One thing the census cannot see, and I flag it as a live hazard:**
`Selvage/HalfThresholdFri.lean`'s docstring on `foldDistanceTransition_halfThreshold`
says *"No Johnson bound, rate inequality, characteristic assumption, or proximity gap
theorem is used."* That is **true of the proof and false of the carrier** — the
theorem takes `D : FoldingData F dom domSq`, so it is vacuous at char 2. The
characteristic-free content genuinely lives one level up, in
`HalfThresholdRegime.correlatedAgreement_of_two_half_close`, which quantifies over an
arbitrary `Submodule F (ι → F)` and has no `FoldingData` at all. **This is exactly the
"honest label hides mediocrity" shape read in reverse: an accurate sentence about the
proof, sitting on a carrier that makes the theorem say nothing in the regime the
sentence invites you into.** Cheap fix in §5.2.

### 2.4 Universe pinning — a third category the brief did not name

Measured in `Selvage/`+`Theory/` `variable` lines: **321 monomorphic binders
(`: Type)` 60 + `: Type}` 261) against 357 `Type*`.** Monomorphic sections include
`SumcheckRbr`, `QuadraticSumcheck`, `MultilinearExtension` (§Realizer),
`MultilinearZeroTest` §2, `SubUdSeam` (the Seam section, line 462), `AccSound`,
`AccSoundRbr`, `LightClientSound`, `LightClientFS`, `LogupStar`, the whole
`OracleLogLinked*` family, `AdditiveFriQuery`, `HalfThresholdFriQuery` (two sections),
`HalfThresholdFriCoherent`, and `SpartanR1CS`.

**Classify this as REAL-but-benign.** `Rbr.Reduction : Type 1` bundles its `Chal`/`PMsg`
at `Type`, so universe 0 is forced at the protocol boundary anyway, and every carrier
we care about (`ZMod p`, `AdjoinRoot`, `GaloisField 2 (2^k)`) lives in `Type 0`. It
costs nothing today. It would cost a re-proof or a `ULift` the day someone wants a
`Type 1` field, which is not a thing we want.

### 2.5 The domain question — **not a gap, a different API**

The prior census's finding is re-confirmed: **`IsPrimitiveRoot` 0, `rootsOfUnity` 0,
`primitiveRoot` 0, `nthRoots` 0.** What stands in their place is *four* domain
constructions, and none of them needs a root of unity:

| construction | where | shape |
|---|---|---|
| abstract embedding + algebraic coherence | `Selvage/Proximity.lean` | `dom : ι ↪ F` with `neg`/`sq`/`sec` and their laws as **structure fields**. The domain is axiomatized, not built. |
| GF(2)-span as a `Submodule` | `Theory/AdditiveNTT.lean:118` | `additiveDomain β k := Submodule.span (ZMod 2) (range β)`, points `∑ j, c j • β j`; injective **iff** `LinearIndependent (ZMod 2) β` |
| `Finset F` + transversality | `Theory/AdditiveNTTTransform.lean:403` | `R : Finset F` with `hR : ∀ r ∈ R, r + β ∉ R`; `pairDomain R β = R ∪ R.image (·+β)` |
| ⚑ **multiplicative subgroup by order** | `Theory/CyclotomicInertia.lean` | `exists_unitsZMod_orderOf_eq {d} (hd : d ∣ p−1) : ∃ u, orderOf u = d`, with the refusals `not_exists_subgroup_card_eq`, `goldilocks_no_domain_two_pow_33`, `p61_no_domain_two_pow_55` |

**So the smooth-domain reasoning exists** — it is keyed on `2^ν ∣ p−1` via `orderOf`,
not on `IsPrimitiveRoot`. `goldilocks_domain_exists {ν} (h : ν+1 ≤ 32)` and
`p61_domain_exists {ν} (h : ν+1 ≤ 54)` are the constructors.

⚑ **But the two halves have never been joined.** `CyclotomicInertia` is an island
(110 declarations, **1** consumed outside its own file). Nothing constructs a
`FoldingData` whose `dom` is a smooth multiplicative coset. The only `FoldingData`
inhabitants in the tree are:

- `Selvage/Proximity.lean:1187` `ProximityExample.data0 : FoldingData (ZMod 5) dom0 dom1` (home module), and
- `Assurance/ReceiptClaim.lean:696` `private def data₄ : FoldingData (ZMod 5) dom₄ …`.

Both at **F₅**, a five-element toy field, with `dom : Fin 4 ↪ ZMod 5` an arbitrary
embedding. The BabyBear machinery (`Selvage/BabyBearExt4.lean`) is real and proved
(`extensionPolynomial_irreducible`, `ext4_finrank = 4`) but is used **only** in the
transcript/hash/codec layer (`BaseFoldPoseidon2`, `BaseFoldBcsFiatShamir`,
`ExtensionChallengeBridge`), never as the `F` of a proximity or folding theorem.

⚠ **Detector limitation, recorded:** the carrier census reports `FoldingData` as
UNWITNESSED. That is because `Assurance/ReceiptClaim.data₄` is `private`, and a private
name is mangled to `_private.Assurance.ReceiptClaim.0.…`, so the census's
`ours name := (`Minidregg).isPrefixOf name` test fails. **The census cannot see private
producers.** Worth a two-line fix; it inflates the unwitnessed count by an unknown
amount.

**Verdict on the domain layer: REAL generality, unpaid instantiation.** The theorems
genuinely hold for any structure satisfying the fields; nobody has ever exhibited one
at a deployment-sized field. That is the single cheapest high-value gap in §6.

---

## 3. Twins

**Instrument:** name-blinded SHA-1 over each declaration's full text (`semtwins.py`),
plus exact full-name collision across non-importing modules. ⚑ **A per-file
`lake build` cannot see a twin by construction** — the `matVec` twin (`b3fbde8`) was
green in `lake build Assurance.SpartanR1CS` and only died under the umbrella build.
Text is the right instrument, not the compiler.

**Measured: 111 cross-module groups of byte-identical declaration text.**

### 3.1 Substrate twins (Selvage / Theory) — the ones that matter here

| twin | modules | note |
|---|---|---|
| `eq_of_relDist_le_of_lt_inv_card` | `LightClientSound:559`, `LightClientFS:340`, `LightClientGrinding:529` | **×3, verbatim**, in modules that import each other in a chain |
| `uniformProb_eq_card_filter` | `AccSound:125`, `BaseFoldIor:174` | ×2, both `private` (which is why they do not collide) |
| `bytesOfDigits`, `bytesOfDigits_length`, `bytesOfDigits_toNats` | `Selvage.BaseFoldBcsByteCodec:40,45,50` and `Theory.BinaryTowerFanPaarCodec:222,227,232` | ⚑ **the byte codec is duplicated once per cone** — prime-field BCS vs binary tower |
| `AccClaim.Satisfies` ≡ `decider` | `Selvage.Accumulator:141`, `Selvage.Decider:73` | 120 chars identical; *deliberate*, bridged by `decider_sound := Iff.rfl`. Honest, but still two definitions of one object |
| `stagedR` | `OracleLogLinkedTwoPhaseHorns:32`, `OracleLogLinkedTwoPhaseSoundness:30` | ×2 abbrev |
| `xWord_sat_evalA` | `ZK:388`, `ZkArgument:246` | ×2 |
| `LazyHybridState` / `PrefixHybridState` | `SpongeIndiffLazyHybrid:33`, `SpongeIndiffPrefixHybrid:34` | same structure, two names — a **near**-twin |
| `fstSubtypeEquiv` / `prodFstSubtype` | `Assurance.ErrorBudget:162`, `Selvage.LightClientGrinding:96` | same equiv, two names, two cones |
| `tower256_card` / `cardinality` | `Assurance.BinaryTowerHeaderCodec:91`, `Theory.BinaryTowerFanPaarCodec:318` | same fact, two names |
| `close_of_correlatedAgreement` | `Selvage.Proximity:1059`, `Theory.AdditiveNTTTransform:470` | ⚠ **NOT a twin — a name collision.** Genuinely different theorems (multiplicative vs additive). This is the "a display name is not a key" hazard: resolve by full name. |

### 3.2 Application-layer twins (outside my remit, reported because the detector found them)

The largest twin mass is in `Kernel`/`Compiler`/`Assurance`, not the substrate:

- ⚑ **`Assurance.SemanticHistoryFamily` re-declares the ENTIRE `VerifiedHistoryHead` API
  of `Assurance.SemanticHistoryAccumulator`** — `VerifiedHistoryHead`, `.AppendLink`,
  `.FoldRecommitment`, `.append`, `.depth`, `.latestReceiptRoot`, `.start`,
  `.append_depth`, `.append_latest`, `.start_depth`, `.decider_complete_at_head`,
  `.opened_decider_extracts_head`, `.opening_decider_complete` — **13 declarations,
  several byte-identical**, in a module that *imports* the original. They do not
  collide only because they sit in sibling namespaces.
- `Kernel.HyperdocumentMerge` vs `Theory.HyperdocumentOperations`: `Declaration.toRequest`
  (713 chars), `.patch`, `.patch_namedFields`, `.patch_namedResources`, `.effectDigest`,
  `.requestId`, `.operationId`, `sealedOnly`.
- `Assurance.DreggNetProviderConsumer` vs `Kernel.ProviderExecutionLease`:
  `authorization`, `refundAuthorization`, `terminalBeforeBytes`, `terminalBeforeModel`,
  and `prepay_exact_retry_is_free` ≡ `exact_prepay_retry_replays` (renamed twin).
- The five page materializers (`CredentialAuthority`, `DeclaredEffect`,
  `HyperdocumentContent`, `HyperdocumentEvent`, `HyperdocumentIndex`) share
  `state_ext` ×5, `stateCodec` ×4, `Page.insert?` ×3, `collision_of_root_eq_of_ne` ×3,
  `state_eq_of_root_eq` ×3, `pageTupleStream` ×2 — a materializer *pattern* that was
  never abstracted.
- `Compiler.BfvProofController` vs `Compiler.NoteSpendProofController`: `run` (529),
  `run_success_integrity` (708).
- `unitCodec` ×6 across `Theory` and `Kernel`.
- ⚠ `Assurance.Tower256RawHistoryCshakeTrace:67` vs
  `Assurance.Tower256RawHistoryFsExecution:50`: **`TowerField`, 1294 chars identical** —
  the largest single twin in the tree, and it is a *field definition*.

**Reading:** the substrate (Selvage/Theory) is nearly twin-free; the application layer
is not. That is the correct place for the duplication to be, but the
`SemanticHistoryFamily` and `TowerField` cases are worth naming as debt.

---

## 4. Islands

**Instrument:** token reverse-index over all 473 files; a declaration is an island if
its short name appears in no module but its own (umbrellas excluded, since the
umbrella's per-import annotations are documentation, not consumption).

**Measured:** of 16,044 non-instance declarations, **9,318 (58%) are never mentioned
outside their defining file.** That headline number is *not* alarming on its own —
most are `private` helpers and `decide`d keystone teeth, which are meant to be
terminal. The signal is at two finer resolutions.

### 4.1 Island MODULES — 17 with **zero** declarations consumed anywhere else

| module | decls | note |
|---|---|---|
| `Selvage.BaseFoldBcsRunSchedule` | 69 | the largest island in the tree (2003 lines) |
| `Selvage.LigeritoInterleaved` | 38 | landed today (`0c08c93`) — expected |
| `Selvage.RingSwitching` | 27 | landed today (`f5b604f`) — expected |
| `Theory.DeployedTotalCarrierAudit` | 27 | |
| `Selvage.SpongeIndiffOracleReordering` | 25 | |
| `Selvage.AdditiveOodOpening` | 23 | ⚑ the additive OOD channel has no consumer |
| `Selvage.ConstrainedMaskMulti` | 21 | closes `[CMASK-multi]`, consumed by nothing |
| `Selvage.BaseFoldRbr` | 14 | ⚑ see §4.3 — this is the *repaired* island, and it moved |
| `Selvage.SpongeIndiffOffBadRun` | 13 | |
| `Selvage.RateRegimeSelector` | 11 | the regime dispatcher nothing dispatches through |
| `Theory.StoreFiniteSupport` | 10 | |
| `Selvage.ProximityGapUDSharp` | 9 | ⚑ the **strictly sharper** `hPG`, consumed by nothing |
| `Selvage.ExtensionChallengeBridge` | 8 | (imported by `Compiler.GateMleExt6`, but no *declaration* is used) |
| `Selvage.BaseFoldBcsStrictRomLedger` | 6 | |
| `Selvage.SpongeIndiffPrefixWalk` | 4 | |
| `Selvage.OracleLogSatisfiable` | 3 | |
| `Selvage.SpongeIndiffPrefixFailure` | 3 | |

Near-islands (≥1 but ≤6% consumed): `Theory.CyclotomicInertia` **110 decls / 1
consumed**, `Selvage.ProximityGapUDTight` 37/2, `Selvage.AdditiveBaseFold` 59/3,
`Theory.ZkmlMatmulSum` 35/2, `Selvage.OracleLogLinkedAttributed` 26/1,
`Theory.BinaryTowerTrace` 19/1, `Selvage.HalfThresholdFriTower` 11/1,
`Selvage.HalfThresholdRegime` 8/2.

⚑ **The last one is the sharpest finding in this section.**
`HalfThresholdRegime.correlatedAgreement_of_two_half_close` and `halfThreshold_pr_le`
are the tree's *best* primitive by every measure — any finite linear code, any
characteristic, zero `omit`, zero conjectures, and they beat Johnson unconditionally —
and **2 of its 8 declarations are consumed.**

### 4.2 Module-level leaves — 44 of 188 `Selvage`/`Theory` modules

Nothing in `Selvage`/`Theory` imports these. Of those, the ones **nothing at all**
imports (not even `Assurance`/`Compiler`/`Kernel`) are:

`Selvage.AdditiveBaseFold` · `Selvage.AdditiveOodOpening` · `Selvage.AuditSampling` ·
`Selvage.BaseFoldBcsByteCodec` · `Selvage.BaseFoldBcsRunSchedule` ·
`Selvage.BaseFoldBcsStrictRomLedger` · `Selvage.ConstrainedMaskMulti` ·
`Selvage.LigeritoInterleaved` · `Selvage.OracleLogSatisfiable` ·
`Selvage.ProximityGapUDSharp` · `Selvage.ProximityGapUDTight` ·
`Selvage.RateRegimeSelector` · `Selvage.RingSwitching` · `Selvage.Statements` ·
`Selvage.ZkmlSuiteRegistry` · `Theory.CyclotomicInertia` · `Theory.IntegerFingerprint`

⚑ **The entire additive/char-2 cone terminates in a leaf.** `AdditiveBaseFold` and
`AdditiveOodOpening` are imported by nothing; `AdditiveFriQuery` reaches only
`Compiler.AdditiveFriReceiptClause`. The char-2 lane is built and unwired.

### 4.3 ⚑ The island that MOVED — the pattern to name

`basefoldSumcheckRbr` was the recorded island: a landed WARP-Def-4.2 object with zero
consumers while the ledger path ran through `BaseFoldIor`'s operational bound. It was
repaired by giving it a consumer — `basefoldSumcheck_fs_sound`, in the **same file**.

Measured today: `basefoldSumcheck_fs_sound` appears in exactly two places,
`Selvage/BaseFoldRbr.lean` and the `Selvage.lean` umbrella annotation. **The island did
not close; it moved up one level.** `Selvage.BaseFoldRbr` is now a zero-consumption
island module (14 declarations, 0 consumed).

**The lesson generalizes and I state it as a rule:** *an island is closed by a
consumer in a DIFFERENT module, on the path that actually reaches the top. A consumer
inside the same file relocates the island, and the relocation is invisible to the same
instrument that found the original.* Same-file consumption is what a per-file build
can see, which is precisely why it is the fix that suggests itself and precisely why
it does not work.

### 4.4 The deliberate island — read before calling it debt

`Selvage/BinaryMerkle.positionBinding_of_collisionFree` is the only theorem in the tree
that would let the **deployed** Merkle path be a `BindingCommitment`. As of the survey
snapshot (`323a7b3`) it had **zero consumers**, and the deployed BaseFold BCS path
consumes `BinaryMerkle.openingScheme` as a bare `OpeningScheme` with the binding
forgotten (`BaseFoldBcsFiatShamir`, `BaseFoldBcsQuerySampling{,Joint}`,
`BaseFoldBcsStrictRomLedger`), routing through `RawFriAdaptiveTranscript` — whose
docstring says outright *"no perfect-binding field is present"* — and pricing
equivocation as a **hash collision** (`friRawAdaptiveEquivocates_flatHash_collision` →
`friRawAdaptiveEquivocates_implies_poseidon2_collision`). The bridge
`RawFriAdaptiveTranscript.ofBinding` goes one way only: it takes a `BindingCommitment`
and *forgets* binding. There is no lift back.

⚑ **This island is a design choice, not debt.** Assuming `¬ Collision H` is weaker
evidence than *reducing to* a collision. Do not "fix" it by wiring
`positionBinding_of_collisionFree` into the deployed path — that would replace a
reduction with an assumption. It belongs on the island list because the instrument
found it, and it belongs in this paragraph because the instrument cannot tell the
difference.

*(Postscript: it acquired three consumers during this survey — see §7.1.)*

Other advertised-in-the-umbrella-consumed-by-nothing headliners (216 total; these are
the ones a consumer would plausibly want): `rs_proximityGap_UD_full`,
`hasMutualCorrelatedAgreement_UD_full`, `reedSolomonCode_isProximityGenerator_UD_full`,
`sponge_realizes_handler_step`, `SpongeIndifferentiable`, `ledger_paid_in_full`,
`deciderProx_sound_subquant`, `emulator_unpack_unique`, `ringSwitch_batching_bound`,
`rank1_sound`, `rank1_complete`, `mle_sgdStep`, `constrainedMaskMulti_hiding`,
`friFold_eval_decomp`, `basefoldExactClaim_value_unique`, `commitCR_of_RO`,
`committed_fold_bind`, and the whole of `Assurance.SpartanR1CS` (24 items, landed today).

---

## 5. The gap list, aimed at instantiation

The five systems to compare, and what each needs from the bag.

### 5.1 Shared vs per-system

**SHARED — every one of the five runs on these, and they are already role-shaped:**

| ingredient | why it is shared |
|---|---|
| `CorrelatedAgreement` metric + CA vocabulary | 121 transitive dependents; `relDist`/`close`/`AgreesOn` carry `omit [Field F]` |
| `Depth`'s `uniformProb_*` kit | the union-bound engine; `{C : Type} [Fintype C]`, **no algebra** |
| `Sumcheck` + `SumcheckReduction` | degree-generic `{v d : ℕ}`; the one induction |
| `MultilinearExtension` §1–3 | arity-generic over `[CommRing F]`, universe-poly |
| `Commitment.OpeningScheme` / `BindingCommitment` | ⚑ **alphabet-generic — see 5.2** |
| `BinaryMerkle.HashSuite` / `openingScheme` | `{Value Digest : Type*}`, **no field at all** |
| `Rbr.Reduction` / `KStateFn` / `RbrKnowledgeSoundness` | 4 genuine inhabitants |
| `FiatShamir.Oracle` + `fsKeystone_proved` | unconditional; shared with the CR layer |
| `ConstrainedCode.LinearConstraint` | the universal relation currency |
| `ErrorBudget` / `SmallField.securityBits` | the accounting |

**PER-SYSTEM:**

| system | its own ingredients | status |
|---|---|---|
| (a) prime-field FRI-BaseFold | `Proximity.FoldingData`+tower, `ProximityGapUD{,Sharp,Tight}`, `HalfThresholdFri*`, `BaseFold*`, `BaseFoldPoseidon2`, `BaseFoldBcs*` | **have**, instantiated only at F₅ |
| (b) additive/binary BaseFold | `AdditiveNTT{,Transform}`, `Additive{Proximity,FriTower,FriQuery,OodOpening,BaseFold}`, `BinaryTower{,FanPaar,Trace,Codec}`, `RingSwitching` | **just landed**, entirely unwired (leaf) |
| (c) Ligerito interleaved | `LigeritoInterleaved` (V-alphabet metric layer) | **exploratory**, 4 obligation `Prop`s + 12 named lemmas |
| (d) Spartan over R1CS | `SpartanR1CS`, `AirSumcheckCubic`, `QuadraticSumcheck` | **just landed, composes** |
| (e) GKR / lookup layer | `LogupStar` (general) + `cubicForm_fraction_layer` (one identity) | **absent as a protocol** |

### 5.2 ⚑ Two gaps that are already closed and were priced as open

**Ligerito A6 `openingSchemeV` — priced as "mechanical but wide; every consumer of
`verifyOpen` re-types". Measured: it requires ZERO new Lean.**

```lean
structure OpeningScheme (Root : Type*) (F : Type*) (ι : Type*) (Op : Type*) where
  commit : (ι → F) → Root ;  openAt : (ι → F) → ι → Op
  verifyOpen : Root → ι → F → Op → Prop
  verifyOpen_commit : ∀ f i, verifyOpen (commit f) i (f i) (openAt f i)
```

`F` is a **bare `Type*` with no instance binder**. `[Field F]` first appears at
`Selvage/Commitment.lean:238`, in a later section. So `PositionBinding`,
`BindingCommitment`, `word_binding`, `opened_eq_committed`, `commit_injective`,
`verifyOpen_of_commit_eq`, `PositionEquivocation`, `not_positionEquivocation` are all
already alphabet-generic. Instantiate `OpeningScheme Root (Fin m → F) ι Op` and you
have a column commitment with its binding theory, verbatim.

**Ligerito A7 `positionBinding_columns` — the note said "likely gives it directly if you
commit column-wise — *Verify, do not assume.*" Verified. It does.**

```lean
def openingScheme (H : HashSuite Value Digest) (k : Nat) :
    OpeningScheme Digest Value (Fin (2 ^ k)) (List Digest)
theorem positionBinding_of_collisionFree (k : Nat) (hfree : ¬ Collision H) :
    (openingScheme H k).PositionBinding
```

`Value` is a bare `Type*`. Take `Value := Fin m → F` and both are yours.

⚑ **Both were priced as work because the *prose* said "the commitment layer" without
anyone re-reading the binder.** That is the read-the-blocker-at-source failure in
miniature, and it is why this survey exists: **the binders are the interface, and the
docblocks are dated commentary.** (`AirSumcheckQuadratic.lean:105` documents the same
class against itself: its own residual paragraph was stale from the day the fix landed,
and a sibling lane quoted it as a live gap on 2026-08-14.)

Ligerito Tier A therefore reduces from 8 lemmas to **5**: A1, A2, **A3**, A4, A5, plus
the assembly A8. A3 (`interleavingPreservesProximityGap`, DG24 Thm 3.1) remains the
only substantial mathematics.

### 5.3 ⚑ The single missing ingredient that unblocks the most

**The partial-round honest terminal: `scChain_*Honest_partial` at `k ≤ m`.**

The measurement that makes this the answer — `Selvage/Sumcheck.lean`:

```lean
def AcceptsFalse {v : ℕ} (prover honest : ℕ → Polynomial F) (H S : F) (r : Fin v → F) : Prop :=
  (∀ i, i < v → (prover i).eval 0 + (prover i).eval 1 = scChain H prover (chalOf r) i)
    ∧ scChain H prover (chalOf r) v = scChain S honest (chalOf r) v
    ∧ H ≠ S
```

**Nothing in `AcceptsFalse` mentions a cube, a variable count, or a final oracle
evaluation.** The "terminal" clause compares the *two chains at round `v`*. So
`sumcheck_soundness` and `adaptive_sumcheck_soundness` — already `{v d : ℕ}` — are
**already partial-sumcheck soundness at every `v`.** The soundness half of Ligerito B1
is landed and nobody noticed, for the same reason A6 was: the statement is more general
than the prose around it.

What is genuinely missing is the **realizer** half. `scChain_mleHonest_final` is stated
only at the full round count `m`:

```lean
theorem scChain_mleHonest_final (f) (r : Fin m → F) :
    scChain (∑ b, f b) (mleHonest f (chalOf r)) (chalOf r) m = mle f r
```

and `roundSum g r i t` already sums over `SuffixCube m (i.val + 1)` — **the partially
folded object is already the primitive.** The missing lemma is that theorem with `m`
generalized to `k ≤ m`, landing not on `mle f r` but on the residual
`∑ b : SuffixCube m k, f (glue r k b)` — a well-formed claim of the same shape as the
original, which is exactly what "hand the residual to another reduction" needs.

*(Derived, not measured: I have not attempted the proof. The induction inside
`scChain_mleHonest_final` proceeds round-by-round, so the generalization is plausibly
a restatement of what it already establishes internally. Treat the cost as unpriced.)*

**What this one ingredient unblocks — five of five:**

| system | what it buys |
|---|---|
| (c) Ligerito | **B1 directly**, and B2/B3 are its batched/glued variants — 3 of 4 Tier-B lemmas |
| (b) additive | `RingSwitchSecure`'s only undischarged leg is *"the `ℓ′`-round degree-2 sumcheck transfer contributing `2ℓ′/|L|`"* — literally a partial sumcheck |
| (e) GKR | the layer-to-layer hand-off; `cubicForm_fraction_layer` already gives the round polynomial, the hand-off is what is absent |
| (d) Spartan | the phase-1→phase-2 join, currently a hand-written case split in `spartan_sound` |
| (a) prime BaseFold | descend `k` rounds, then switch code — which *is* Ligerito's recursion, and is what would let (a) and (c) be compared on one trunk |

⚑ **It is the composition operator the bag is missing.** Everything else in the bag is a
complete protocol; this is the glue that lets one protocol stop early and hand off.

**Runner-up, and the reason it is only runner-up:** a `FoldingData` at a smooth
BabyBear domain. The machinery exists on both sides —
`CyclotomicInertia.exists_unitsZMod_orderOf_eq` builds the subgroup,
`BabyBearExt4.ext4_finrank` builds the extension — and they have never been joined.
But (a) is already "have" at the theorem level; this buys deployment realism, not a
system. Do it second, and note it also closes the `CyclotomicInertia` island
(110 declarations, 1 consumed).

### 5.4 The rest of the gap list, by owner

| gap | owner | one line |
|---|---|---|
| `[COMMIT-CR]` (93 citations — the most-owed in the tree) | `Commitment.lean` | tree-shaped `commit` + log-size `openAt` + the path-collision reduction; the CR of the deployed compression function |
| `[FS-ROM]` (55) | `FiatShamir.lean:70` | "the deployed sponge realizes this lazy-sampling `Oracle`" — named, not axiomatized |
| `[ACC-extract-bind]` (62) | `AccExtract.lean:333` | the `t`-opened-column erasure lift beyond UD |
| `[SPONGE-indiff-game]` | `SpongeIndiff.lean:1247` | only `q = 0` is proved; the RP/RF switch and identical-until-bad coupling await mass |
| `[SPARTAN-pcs]` | `SpartanR1CS.lean:703` | the two terminal openings are still compared against the honest chain |
| `[SPARTAN-sparse]` | `SpartanR1CS.lean:729` | **cost, not soundness** — everything computes from the dense `2^(s+t)` table; no SPARK machinery exists in the tree at all |
| `[RECURSE-sumcheck-bridge]`, `[RECURSE-fri-bridge]` | `SumcheckVerifierAir.lean:36`, `FriQueryVerifierAir.lean:40` | ⚑ the AIRs are **proved correct against their own specs**; no theorem identifies their accept predicate with Selvage's. Owed Assurance-side, prose only. |
| `[BUDGET-compose]` | `ErrorBudget.lean:595` | the bound is at the **product measure**; the deployed system runs one oracle and one prover |
| `[ACC-sound-list]` | `AccSound.lean:92` | Johnson/Guruswami–Sudan list counts **are not in this tree** |
| `PolishchukSpielman` | `ProximityGapUDTight.lean:565` | the one unproved rung of BCIKS Thm 4.1; premises proved inhabited |
| `WHIRConjecture412`, `HaboeckTheorem2`, `HaboeckErrorEnvelope` | `JohnsonRegime`, `JohnsonMcaBridge` | the Johnson-regime inputs, carried as hypotheses |
| `TowerRSDistance` | `Theory/BinaryTower.lean` | the only surviving `[BTOWER-*]` residual — the others were discharged by `BinaryTowerTrace` |
| ordered-basis binding | `AdditiveBaseFold.keystone_basis_ambiguity_terminal` | ⚑ a **proved negative**: an additive-FRI transcript that binds the domain but not the ORDERED basis does not determine the committed multilinear, and **nothing in this tree binds it** |
| GKR / product layer | — | absent: 0 `grandProduct`, 0 `fractionalSum`, 0 product tree, no multiset/permutation argument |
| degree-generic realizer | — | no `dHonest : (d : ℕ) → …`; a d=4 rung is a fourth copy |

---

## 6. ⚑ The refactor verdict — mostly a refusal, with three narrow exceptions

**The brief asks for a role-level typeclass or structure that several ingredients could
instantiate, and explicitly permits "it is already composable enough and a refactor
would be churn." That is close to the honest answer, and here is the evidence.**

### 6.1 Why a role-typeclass sweep would be churn

The tree **already has** role-level interfaces, in the three places where a second
instance existed to justify one, and they are good by the standard that matters
(inhabited, parametric, and *refutable*):

| interface | inhabitants | the refutation that proves the parameter is load-bearing |
|---|---|---|
| `Commitment.OpeningScheme` / `BindingCommitment` | `idealCommitment`, `roBinding`, `HistoryHeadInhabitation.scheme`, `towerBindingCommitment`, + a reindexing combinator | `equivocal` + `equivocal_no_binding_extension` + `equivocal_breaks_extract_bind` — the conclusion **fails** without binding |
| `Rbr.Reduction` / `KStateFn` / `RbrKnowledgeSoundness` | `sumcheckRbrKnowledgeSound`, `basefoldSumcheckRbr`, `accRbrKnowledgeSound`, `accRbrKnowledgeSoundBcs` (+ derived `SemanticHistoryBcsGame.knowledgeSoundness`) | `trivialRbr` powering `OB2_depth_composition_false` |
| `ConstrainedCode.LinearConstraint` | every AIR rung + Spartan's inner phase | `exists_dotWt_eq` (completeness: *every* linear functional is one) |

And the pattern **reproduced itself during this survey**: a concurrent lane landed
`Selvage/HashFamily.lean` (`bf0b311`) — `structure HashFamily (Block Value Digest)` with
`suite : HashSuite Value Digest` and `absorb : List Block → Digest`, joining the Merkle
and transcript roles; two construction routes (`ofSponge`, `ofChain`); instances on
**two different characteristics** (`poseidon2Family`, `spongeFamilyCharTwo`); the
obligations as named `Prop`s (`MerkleObligation`, `TranscriptCollisionObligation`); a
separating refutation (`collapsingFamily`, `collapsing_not_merkleObligation`,
`merkleObligation_separates`); and — the good part —
`merkleObligation_not_provable [Fintype Digest]`, a **proved impossibility** that the
obligation cannot be discharged for a finite digest.

**That is how interfaces should arrive here: from the lane that needs the second
instance, with a refutation attached.** A survey lane adding a fourth abstraction layer
over three working ones would be exactly the churn the brief warns about, and it would
add an indirection that every existing consumer would have to be re-typed through — for
zero new capability.

**So: no role-typeclass sweep. The bag is already a bag.**

⚑ And note *why* it is already a bag, because it is not an accident and it is worth
copying: **the binders were kept minimal from the start.** `OpeningScheme` has no
`[Field F]`. `HashSuite` has no carrier at all. `Depth`'s counting kit has no algebra.
`LinearConstraint` is `{wt, target}` over any `ι`, `F`. The 455 `omit` lines are the
tree continuously re-checking that claim against itself. Composability here was bought
by *not adding* structure, and the instrument that keeps it honest is `omit`, not a
typeclass hierarchy.

### 6.2 Exception 1 — the one structure that would earn its keep, **and only on a trigger**

The honest sumcheck realizer is written three times (d=1, 2, 3), seven parallel lemma
names each, with no shared abstraction. §5.3's partial-round generalization would make
it **twenty-one**. That is the one place where the triplication is about to compound.

But the right first move is **not** a structure. It is:

1. Add `scChain_mleHonest_partial`, `scChain_quadHonest_partial`,
   `scChain_cubicHonest_partial` — 3 mechanical lemmas. This unblocks five systems
   (§5.3) at the smallest possible diff.
2. **Then consider deleting the d=2 realizer.** `cubicForm_subsumes_prodDiff` already
   proves `prodDiff = cubicForm (fun _ => 1) A B (fun b => -(C b)) (fun _ => 1)`
   *denotationally*. Deriving `quadHonest`'s stack from `cubicHonest`'s removes code
   instead of adding a layer — strictly better than abstracting over both.
3. **Only if a d=4 rung is actually wanted** does a `structure HonestRound (F) (m d)`
   with fields `poly` / `degree` / `prefixMeas` / `boolean_sum` / `partial_terminal`
   earn its keep — and it should be a `structure` in the tree's statement-first idiom,
   never a `class`.

**Trigger, stated so it can fire without me:** *write the structure when a fourth degree
rung is requested, not before.* Today it would abstract over two objects that one
theorem already proves are one object.

### 6.3 Exception 2 — lift `QErr`'s regime-in-the-type into `SoundnessParams`

`Assurance/TwoRegimeQueryBudget.lean` carries the best structural idea in the tree:

```lean
structure QErr (r : Regime) where ...
```

The regime is in the **type**, so `QErr .UDR` and `QErr .JBR` cannot be summed or
`min`'d without a visible regime change, and `cbr_not_reportable` mechanically bars the
withdrawn capacity regime. `RateRegimeSelector`'s `inductive RateRegimeRequest` does the
same by constructor — the Johnson branch **cannot be built** without `HaboeckTheorem2`.

`ErrorBudget.soundnessError` sums five legs whose regimes are tracked **only in prose**
(`errStarUD` is UD-only; the Johnson-regime variant would be a different number). This
is the shape that lets a proven leg and an idealised leg be added together with nothing
in the type objecting. Cost: index the leg `def`s by `Regime` and let `soundnessError`
require agreement. Cheap, and it converts a prose discipline into a checked one.

### 6.4 Exception 3 — two mechanical fixes to the instruments themselves

1. ⚑ **`scripts/CarrierCensus.lean` cannot see `private` producers.** Its
   `ours name := (`Minidregg).isPrefixOf name` test fails on
   `_private.Assurance.ReceiptClaim.0.Minidregg.…`, so `Assurance/ReceiptClaim.data₄`
   — a real `FoldingData` witness — reads as absent, and `FoldingData` is reported
   UNWITNESSED with 58 dependents. The 622 "actionable" count is inflated by an unknown
   amount. Two-line fix: strip the `_private.<Module>.<n>.` prefix before the test.
2. **`Selvage/HalfThresholdFri.lean`'s docstring on
   `foldDistanceTransition_halfThreshold`** says *"no characteristic assumption"* — true
   of the proof, false of the carrier (it takes a `FoldingData`, empty at char 2). One
   sentence, pointing at `HalfThresholdRegime` where the characteristic-free content
   actually lives.

### 6.5 What I am NOT proposing, and why

- **No `V`-alphabet refactor of the commitment layer.** §5.2: it is already generic.
- **No unification of the multiplicative and additive cones.** They are *proved*
  disjoint (`CharTwoWall`), the char-2 census gates on that disjointness at zero, and
  `foldMap_add` is false outside char 2. A common `Fold` interface would have exactly
  two instances that share no laws.
- **No abstraction over the three relation formats.** `LinearConstraint` is already the
  currency all of them reduce to; `AirSig`, `Gate`, and `R1CSMatrix` are *source*
  formats with genuinely different denotations.
- **No island sweep.** Most of the 9,318 are `private` helpers and `decide`d teeth that
  are *meant* to be terminal. The islands worth closing are named individually in §4.1
  and §5.3, and closing them means **wiring them into a consuming module**, not
  refactoring them — see §4.3 for why a same-file consumer does not count.

---

## 7. Status, provenance, and what to distrust

### 7.1 The tree moved during the survey

Snapshot: `323a7b3`. During the run, `bf0b311` (`Selvage/HashFamily.lean`) landed. All
counts in §0–§4 are as of `323a7b3` and are now one commit stale:
`positionBinding_of_collisionFree` acquired three consumers in `HashFamily.lean`, so
§4.4's "zero consumers" is true of the snapshot and false of `HEAD`. This is a shared
tree with many live lanes.

**Before quoting any number here in a brief, re-derive it.** The four instruments are
cheap to rebuild and each is a few dozen lines: (i) a declaration scrape — regex
`^(@\[…\])?(private|noncomputable|…)*(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+<ident>`
with a namespace stack, ⚠ **the identifier class must include Unicode subscripts** or
`flatten₂` reads as `flatten` and you get phantom twins (it did, on my first pass);
(ii) twins — name-blinded SHA-1 over each declaration's text, grouped across modules;
(iii) islands — a token reverse-index, umbrella files excluded from the consumer set;
(iv) the import DAG for transitive-dependent counts. Plus the two in-tree censuses,
`scripts/check-char2-vacuity.sh` and `scripts/CarrierCensus.lean`.

### 7.2 What each claim rests on

| claim | status |
|---|---|
| 0 `sorry`, 0 `axiom`; 0 `IsPrimitiveRoot`/`rootsOfUnity`/`primitiveRoot`; 455 `omit`; 63 `omit [Field F]` | **measured** (grep, this lane) |
| 0 char-2-vacuous declarations of 29,276 | **measured** (`CharTwoVacuityCensus.lean`, run this lane) |
| 1501 carriers, 627 unwitnessed, 622 actionable | **measured** (`CarrierCensus.lean`, run this lane) — ⚠ inflated, see §6.4 |
| 111 cross-module identical-text twin groups; 17 island modules; 44 leaves; import-DAG ranks | **measured** (this lane's scripts) |
| `OpeningScheme`/`HashSuite` are alphabet-generic ⇒ Ligerito A6/A7 need no new Lean | **measured** (read the binders) |
| `AcceptsFalse` is already the partial-sumcheck predicate ⇒ B1's soundness half is landed | **measured** (read the definition) |
| the partial-round *realizer* is the missing lemma, and it is cheap | ⚠ **derived, unpriced** — I did not attempt the proof |
| "unblocks five of five systems" | **derived** from the residual texts named in §5.3; each link is checkable, the aggregate is my judgement |
| per-file theorem names and generality classifications in §1 | **measured** by five parallel read-only lanes; I spot-verified the load-bearing ones |

### 7.3 Two instrument warnings worth carrying out of this lane

1. ⚑ **Docblocks in this tree are dated commentary; binders and `Prop`s are current
   status.** Three separate gaps in this survey were priced as open work by prose that
   the code had already overtaken (Ligerito A6, Ligerito A7, and `AirSumcheckQuadratic`
   residual (ii), which documents the failure against itself). **Read the binder before
   pricing the lemma.**
2. ⚑ **An island is closed by a consumer in a DIFFERENT module, on the path that
   reaches the top.** `basefoldSumcheckRbr` was repaired with a same-file consumer and
   the island simply moved up one level to `basefoldSumcheck_fs_sound` — invisible to
   the same instrument that found the original, and for the same reason a per-file
   `lake build` cannot see a twin.
