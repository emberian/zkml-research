# The Lean-authored multilinear/GKR substrate — design memo

2026-08-13. Design lane + a ground-truth spike. This is the artifact four
independent lanes converged on needing and that has never had a design pass.

**Substrate law, restated so it is in the file and not only in the brief:** we
are abandoning Plonky3 and every third-party prover stack as fast as we can.
Everything below is **ours, authored in Lean, in Selvage/Assurance/Compiler**.
Upstream was read for API shapes and pitfalls and appears here only as measured
facts about code we will not depend on.

**Claim tags** are on every load-bearing sentence: [MEASURED] = I read it at
source this session and cite file:line; [SOURCED] = from a note in this repo
that cites a source; [INFERRED-BY-ME] = my reasoning, not checked; [OPEN] = a
decision I am deliberately not making.

---

## 0. The one-paragraph verdict

The substrate is **much closer than the convergence note implies, and closer in
the right places.** Selvage's sumcheck protocol layer is *already degree-generic*
— `{d : ℕ}` runs through `sumcheckRound_prob`, `launderSet_card_le`,
`adaptive_sumcheck_soundness`, `AdaptiveUnionBound` — and the whole round-chain
skeleton in `MultilinearExtension.lean` (`roundSum_fold/_zero/_succ/_last/
_congr_prefix`) is proved for an **arbitrary** `g : (Fin m → F) → F` with no
multilinearity hypothesis [MEASURED]. Degree 1 is pinned only at the *realizer*
layer, and `Assurance/AirSumcheckQuadratic.lean` has already done the degree-2
port once, end to end, giving a line-for-line template [MEASURED]. What is
genuinely missing is small and nameable: a **two-vector `eq` polynomial**
(absent in Lean, verified by grep; present in Rust only in characteristic two),
a **multilinear Schwartz–Zippel bound** (the zerocheck's soundness), a
**layer/claim datatype** (GKR absent everywhere, verified), and a **multilinear
PCS** (absent; what we hold is univariate RS/FRI proximity). The design below
makes the fail-open seam structurally impossible, fixes degree at ≤ 5 with 3 as
the landed rung, states the PCS as an abstract interface rather than solving it,
and names the two places where I think the tree currently disagrees with itself.

---

## 1. The interface

### 1.1 What a layer is

A **layer** is a claim-transformer, not a circuit slice. Concretely:

```
structure LayerSpec (F : Type) (m : ℕ) where
  arity    : ℕ                                   -- number of multilinear factors
  degree   : ℕ                                   -- per-coordinate degree of the summand
  combine  : (Fin arity → F) → F                 -- the low-degree combining map
  -- the summand is  fun x => combine (fun j => mle (factor j) x)
```

A **claim** is `⟨point : Fin m → F, value : F⟩` — "this committed multilinear
evaluates to `value` at `point`". A layer consumes *output* claims and produces
*input* claims, and the sumcheck is what carries one to the other.

The reduction, in the shape our Lean already speaks:

1. Verifier holds output claims. Batch them with one challenge `γ` into a single
   claim (`SumcheckReduction.list_as_single_sumcheck` / `batch_survives_prob_le`
   already do exactly this at the constraint level [MEASURED]).
2. Verifier draws `ρ ∈ F^m`, and the claim becomes the **eq-weighted sum**
   `Σ_b eq(ρ, b) · [layer relation at b] = 0`. This is the zerocheck step, and
   it is the piece that does not exist yet.
3. Run `degree`-bounded sumcheck over `m` rounds. Out comes a challenge point
   `r` and a folded value.
4. The terminal comparison is `folded == combine(v₁,…,v_arity)` where the `vⱼ`
   are the input claims at `r`. Those become the next layer's output claims.
5. The last layer's input claims are discharged by the PCS.

Selvage already names step 4's shape: `scChain_quadHonest_final` states the
final check **factored** as `Â(r)·B̂(r) − Ĉ(r)` rather than as a single opaque
oracle value [MEASURED, `Assurance/AirSumcheckQuadratic.lean`]. That factoring is
exactly what makes a layer *composable* — the factors are the next claims.

### 1.2 The round message shape, and why it is not the obvious one

**A round message is `d+1` field elements: the round polynomial evaluated at the
fixed nodes `0, 1, …, d`.** Not coefficients, not `[h(0), h(∞)]`.

This is a deliberate refusal of what p3-sumcheck does, and the reason is sharper
than "their verifier checks nothing final". At our pin (Plonky3 `82cfad73`), the
round message is `[c0, c_inf]` and **`h(1)` is *derived* by the verifier as
`claimed_sum − c0`** [MEASURED, `sumcheck/src/data.rs:14-26,118-131`]:

> `Each entry is [h(0), h(inf)] … h(1) is derived as claimed_sum - h(0) by the verifier.`

The consequence is not that the round check is skipped — **it is that the round
check has been made a tautology.** `h(0) + h(1) = claimed_sum` holds by
construction for every transcript, honest or not. `verify_rounds` therefore
contains no per-round rejection at all; it observes, grinds, samples, folds via
`extrapolate_01inf`, and returns `Ok(Point)` [MEASURED, same file]. 100% of the
soundness is displaced into the single terminal comparison, which lives in the
**caller** — the only real caller at our pin is WHIR's PCS verifier, at
`whir/src/pcs/verifier/mod.rs:233-245`:

```rust
// Final consistency check: claimed_eval == weight * f(r).
if claimed_eval != evaluation_of_weights * final_value { return Err(...) }
```

[MEASURED]. So the seam is real and it is *structural*, not an oversight: a
compression chosen for prover speed (the `{0,1,∞}` basis, cited in-file to
eprint 2026/587 Lemma 2 [MEASURED]) deleted the round check as a side effect.

**Our two laws.**

> **LAW-1 — no partial verifier.** The substrate exposes no function that
> consumes a sumcheck transcript and returns folding randomness without also
> consuming the terminal value. Where a protocol genuinely needs the randomness
> before the terminal value exists (WHIR does — the randomness selects the
> queries), the substrate returns a `PendingClaim`: an opaque `#[must_use]` value
> with no public constructor and exactly one consuming method
> `fn settle(self, terminal: Fp) -> bool`. On the Lean side the rule is stated as
> a *proof-shape* rule: there is no lemma of the form "if every round check
> passes then …". Only the composed form exists. Selvage's `SumcheckAccepts` is
> already a conjunction of the round checks **and** the final check, and
> `acceptsFalse_iff_accepts` links them [MEASURED,
> `Selvage/SumcheckReduction.lean:145,152`] — this law is a promise not to
> weaken what is already there.

> **LAW-2 — never compress `h(1)` out of the message.** Send `d+1` evaluations
> including `h(1)`. The `{0,1,∞}` trick may be used *inside the prover* to
> compute the message cheaply; it must not reach the wire. Cost of the law: one
> extension-field element per round. At `m = 20` over BabyBear⁶ (24 bytes) that
> is **480 bytes**, against a proof measured elsewhere in hundreds of KiB
> [SOURCED: leanVM 327 KiB proven-regime, grey-lit §4]. This is the cheapest
> soundness we will ever buy.

`prover/src/sumcheck.rs::verify_sumcheck` already obeys both laws: it takes the
oracle as an argument, rejects `g.len() != 2`, checks `g[0]+g[1] == running`
per round, and ends with `running == f_oracle(&proof.challenges)` [MEASURED].
The degree-3 rung must not regress it.

### 1.3 Where the final check lives

**Inside the verifier, always.** And one refinement that matters for GKR: the
terminal check is *factored* (`folded == combine(v₁..v_k)`), so the verifier
never receives one opaque "the oracle says X". It receives the individual input
claims, checks the combination itself, and hands the claims onward. A prover
that supplies `combine(...)` directly instead of the factors is the **Class 3
industry bug** — "verifier accepts a prover-supplied value it should recompute",
which grey-lit §7 records as our own E10 wound and as Jolt/Dusk/OpenVM's
[SOURCED]. Design rule: **the verifier recomputes `combine`; the prover supplies
only the `k` factor values.**

---

## 2. Degree

### 2.1 What is already generic (the good news)

[MEASURED, `Selvage/Sumcheck.lean`] — every one of these carries `{d : ℕ}`:
`sumcheckRound_sound`, `sumcheckRound_prob` (`≤ d/|F|`), `lie_persists`,
`sumcheck_reduction`, `sumcheck_soundness`, `unionBound_fixed`,
`uniformProb_coord_mem_prefix`, `AdaptiveUnionBound F v d`,
`adaptiveUnionBound_holds`. And `Selvage/SumcheckReduction.lean`:
`launderSet_card_le {v d}`, `adaptive_sumcheck_soundness {v d}` (→ `v·d/|F|`),
`sumcheck_retires_batch {v d}`.

[MEASURED, `Selvage/MultilinearExtension.lean`] — proved for an **arbitrary**
`g : (Fin m → F) → F`, no degree hypothesis: `roundSum`, `roundSum_fold`,
`roundSum_zero`, `roundSum_succ`, `roundSum_last`, `roundSum_congr_prefix`,
`glue`, `glue_update`, `suffixSplit`.

**The chain skeleton is already degree-generic. Only the realizer is pinned.**

### 2.2 What is pinned at degree 1

`AffineInCoord` (line 161), `roundSum_affine` (405), `roundPoly` (450 — the
two-point interpolant `C(g(1)−g(0))·X + C(g(0))`), `roundPoly_degree`,
`mleHonest`, `mleHonest_degree`, `mle_sumcheck_soundness`,
`mle_retires_constraint`. Rust: `round_poly` returns 2 evals, `eval_affine`
asserts length 2, `verify_sumcheck` rejects length ≠ 2 [MEASURED].

### 2.3 What is pinned at degree 2 — and it is a whole worked example

`Assurance/AirSumcheckQuadratic.lean`, 916 lines, `[AIR-sumcheck-quadratic]`,
CLOSED [MEASURED]. It carries the entire realizer port at `d = 2`:

```lean
theorem prodDiff_line (A B C : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) (t : F) :
    prodDiff A B C (Function.update x i t)
      = (1 - t) * prodDiff A B C (Function.update x i 0)
        + t * prodDiff A B C (Function.update x i 1)
        + (t * t - t) *
          ((mle A (Function.update x i 1) - mle A (Function.update x i 0))
            * (mle B (Function.update x i 1) - mle B (Function.update x i 0)))
```

with proof `have hA := mle_multilinear A i x t; … ; rw [hA,hB,hC]; ring` — **six
lines** [MEASURED]. Then `quadCross`, `quadRoundPoly` (a real `Polynomial F`,
`C(cross)·X² + C(...)·X + C(...)`), `quadRoundPoly_eval` (with *no* affineness
hypothesis — the quadratic identity carries it), `quadHonest*`,
`scChain_quadHonest_final`, and

```lean
theorem quad_sumcheck_soundness … (hProverDeg : … (prover χ i).degree < ((2+1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → F) (AdaptiveAcceptsFalse prover (quadHonest A B C) H (∑ b, (A b * B b - C b)))
      ≤ (m : ℝ) * (2 / Fintype.card F)
```

**The repo has already chosen the per-shape route** (a closed-form line lemma per
summand shape) over a general MvPolynomial-degree theory. That is the cheaper
route and the degree-3 rung should follow it.

### 2.4 The decision

> **The substrate supports per-coordinate degree `d ≤ 5`, with `d = 3` as the
> landed rung and `d = 2` already landed.**

Why 3: GKR fraction-tree layers want `eq(ρ,·) · (p_L·q_R + p_R·q_L)` and
`eq(ρ,·) · (q_out − q_L·q_R)` — one eq factor (per-coordinate degree 1) times a
product of two multilinears (degree 2) = **degree 3 per coordinate, with 5
multilinear tables resident** (eq, p_L, p_R, q_L, q_R). zkML matmul is
`eq(ρ,·)·(Â·B̂ − Ĉ)` — also degree 3, 4 tables. Both consumers land on the same
rung [INFERRED-BY-ME from the relation shapes; the fraction-tree relation is
standard].

Why a ceiling of 5: batching a fraction-tree layer with a selector or fusing two
layers reaches 5; nothing among our four consumers reaches higher, and each extra
degree costs a table pass in the prover and a wire element per round.

**What degree costs, stated in the three currencies:**

- *Soundness*: `m·d/|F_challenge|`. At `m = 20`, `d = 3`, BabyBear⁶ (|F| ≈ 2^186):
  `60/2^186`. **Degree is not, and will not become, the soundness problem.** The
  field is (§3.4 / §7).
- *Proof size*: `m·(d+1)` extension elements. `m=20, d=3`, BabyBear⁶ = 80 × 24 B
  = **1.9 KB**. Under LAW-2 the honest accounting includes the `h(1)` we refuse
  to compress out: `m` elements = 480 B of that.
- *Prover time*: for `k` multilinear factors at degree `d`, the folding prover
  costs roughly `2·k·(d+1)·2^m` base multiplications total across all rounds,
  versus `2·2^m` for the current `k=1, d=1` engine — so **degree-3/5-factor is
  ~10–20× the field work of the degree-1 single-table engine, per sumcheck**
  [INFERRED-BY-ME, standard count, not measured]. This number should be replaced
  by a measurement in card G3.

⚠ And the *current* Rust engine is not the folding prover: `round_sum` is the
literal `O(2^m)`-MLE-evals-per-point mirror, so a round costs `O(4^m)` [MEASURED,
`prover/src/sumcheck.rs:98-123` and its own docstring saying so]. **The degree-3
rung must land table folding at the same time or the demo caps around m≈12.**
The kernel exists — `mle_kernels::fold_mle_table` [MEASURED] — but is generic
over `trait NativeMleScalar`, implemented for `Ext6`/`TowerElem`/`Tower256` and
**not for the prime `Fp = u64` the sumcheck engine uses**, and is wired to no
Lean-owned dispatch adapter.

---

## 3. The commitment seam

### 3.1 What the substrate assumes, stated abstractly

The substrate must be stated against an interface and married to nothing. Four
requirements, and they are not what our existing commitment abstraction provides:

1. **Evaluation at an arbitrary point of `F^m`** — not opening at an index.
   ⚠ `Selvage/Commitment.lean`'s `OpeningScheme Root F ι Op` has
   `openAt : (ι → F) → ι → Op` and `verifyOpen : Root → ι → F → Op → Prop`
   [MEASURED] — that is a **positional vector commitment**. It is the right shape
   for Merkle leaves and the wrong shape for a multilinear claim. The substrate
   needs a sibling structure, not a reuse:

   ```lean
   structure MultilinearOpeningScheme (Root F : Type*) (m : ℕ) (Op : Type*) where
     commit     : ((Fin m → Bool) → F) → Root
     openAt     : ((Fin m → Bool) → F) → (Fin m → F) → Op
     verifyOpen : Root → (Fin m → F) → F → Op → Prop
     verifyOpen_commit : ∀ f pt, verifyOpen (commit f) pt (mle f pt) (openAt f pt)
   def EvaluationBinding (S) : Prop :=
     ∀ rt pt v v' o o', S.verifyOpen rt pt v o → S.verifyOpen rt pt v' o' → v = v'
   ```

   `Commitment.lean`'s discipline should be copied wholesale: binding as a
   separate `Prop`, an axiom-free ideal inhabitant, **and an equivocator with a
   refutation theorem** — `equivocal_not_binding` / `equivocal_breaks_extract_bind`
   exist for the positional scheme [MEASURED] and are why binding is load-bearing
   there rather than decorative.

2. **Batched opening of `k` committed multilinears at ONE point.** Sumcheck always
   terminates at a single shared `r`. The interface must express "one opening
   proof for `k` polynomials at one point" or the GKR cost model is wrong by a
   factor of `k` at every layer.

3. **At most ONE post-challenge commitment round.** See §4.3.

4. **Nothing about hiding**, in v1. Selvage has `ZK.lean`, `ZKHiding.lean`,
   `RbrZeroKnowledge.lean`, `ZkTriangular.lean`; the substrate v1 is **not
   zero-knowledge** and should say so rather than gesture at them.

### 3.2 The flag, not solved here

**We hold univariate Reed–Solomon/FRI proximity. We do not hold a multilinear
PCS.** [MEASURED via census]: `Selvage/ReedSolomon.lean` is RS-as-a-`Submodule`
= image of `Polynomial.degreeLT` under evaluation; `Proximity.lean` is
BS08 multiplicative folding `Fold(f,α)(x²)`; `AdditiveFriTower/Query.lean` is the
char-2 affine-subspace counterpart; `SubUdSeam.lean`, `CorrelatedAgreement.lean`,
`OutOfDomain.lean` all sit on that univariate object. Grep for
`basefold|ligero|brakedown|hyrax|zeromorph|gemini|dory` across `.lean`/`.rs`
returns only prose in two docs — and `docs/SELVAGE-RECOMPOSITION.md` explicitly
*withdraws* the Basefold staging.

The bridge from univariate FRI to a multilinear evaluation claim — the thing
BaseFold/WHIR *is* — is not in the tree. **The one seed we hold is
`Selvage/MultiplicativeMleTerminal.lean`**: Boolean Möbius → LSB coefficients →
univariate `evenPart p + C r · oddPart p` folds, with
`foldMleVariables_booleanMobiusPolynomial` proving the terminal constant IS the
MLE [MEASURED]. That is the *algebraic half* of a BaseFold opening with no
commitment, query, or soundness layer attached.

> **This is the single largest missing piece of the trust path, and it is a
> campaign, not a section of this memo.** The substrate is designed so that
> plugging it in later changes no sumcheck theorem: everything above is stated
> against `MultilinearOpeningScheme` + `EvaluationBinding`.

### 3.3 What the PCS gap does *not* block

The layered-sumcheck substrate, the eq/zerocheck reduction, logUp-GKR's fraction
trees, and the degree-3 rung are all **claim-to-claim** machinery. They can be
built, proved, and conformance-bound against an *ideal* (identity) multilinear
opening scheme exactly the way `Commitment.lean` uses `idealCommitment`
[MEASURED]. The PCS is the last mile, not the first.

### 3.4 ⚠ A field-choice tension I found and am not resolving

`Assurance/MixedFieldBudget.lean` carries a `ChallengeFieldProfile` with four
separate challenge cardinalities and **named theorems** (not `#guard`s) computing
the composed bound: `baseGateExt4Fri_secure_16`, `ext6GateExt4Fri_secure_75`,
`unifiedExt6_secure_137` [MEASURED]. Its own header: *"using BabyBear^6 for every
algebraic challenge recovers the 137-bit point."* And `Ext6` is real in both
languages — `prover/src/field6.rs` (`BabyBear[u]/(u⁶−31)`) and
`Compiler/Ext6Conformance.lean`, where **fieldness is proved via a Kummer tower,
no `native_decide`** [MEASURED]. **Ext4 and Ext5 do not exist as types anywhere
in the tree** (grep verified).

Two things follow, and they point opposite ways:

- The convergence note's *"Ext5, not Ext6"* pin was derived from zkVMs that live
  on Ext4/Ext5. **We already have Ext6, built and proved a field, and a budget
  model that prefers it.** [INFERRED-BY-ME] the substrate should draw sumcheck
  and batching challenges in **Ext6**, and the OPEN-QUEUE §D "Ext5 decision"
  should be re-scoped to "which extension for algebraic draws, given Ext6 is the
  one we have."
- ⚠ But `mixedFieldSoundness` is `grinding + gateBatch + sumcheck + cr +
  proximity`, and its proximity leg is `mixedProximityTerm = codeLen /
  proximityCard` — **a field-size-bound term** [MEASURED, lines 62-66]. Grey-lit
  §3 records that the FRI/WHIR **query phase is query-count-bound and extension
  degree does nothing there**, with OpenVM2 itemizing `whir_query 100`
  [SOURCED]. **The 100-bit wall is not a term in this model.** So
  `unifiedExt6_secure_137` is a theorem *of a model that cannot see the leg
  grey-lit says binds.* I did not read `ErrorBudget120`/`PoWSoundnessParams` in
  full and the query leg may be composed elsewhere; but it is not in the
  expression the three `_secure_N` theorems bound.

**[OPEN — and it is a §2-of-the-pause-list item (it touches a check), so it is
ember's]:** the substrate's challenge field. Alternatives: (a) Ext6 everywhere
for algebraic draws, accepting that the budget model does not price the query
leg; (b) Ext6 for algebraic draws **plus** adding a query-count leg to
`MixedFieldBudget` first, so the number we quote is the realized one; (c) the
grey-lit Ext5 recommendation, which costs building a type we do not have. I
lean (b)-then-(a) and I am not doing it silently.

---

## 4. Pitfalls designed around

### 4.1 Binius64: *"the large field infects what ought to be a bit-level computation"*

[SOURCED, grey-lit §2 quoting Binius64 §1.2 — they abandoned bit-granularity for
64-bit words.]

**Our answer: the substrate's native unit is a base-prime field element. Bit-level
facts go through lookups, never per-bit columns.** And the good news is that this
is already the shape we hold: `Selvage/BinaryLookup.lean` proves
`binaryTableDot_lookupEq_eq_mle` — *a table dot-product at a Boolean address IS
the table's MLE* — so a 2^16 table is **an MLE evaluation, not 65,536 emitted
rows** [MEASURED via census]. `LogupIndexLink.canonicalIncidence_eq_unitVector`
proves the reconstructed incidence row is a **literal unit vector**, not merely
boolean-with-sum-one, and `BinaryLookupExample.boolean_sum_one_not_oneHot_charTwo`
(`![1,1,1,0] : Fin 4 → ZMod 2`) is the refuter showing why that distinction is
load-bearing [MEASURED]. This is the Binius pitfall's remedy, already proved, in
our tree.

⚠ **But the tree currently runs two lanes and the design must say so.** The
prime line is BabyBear/Ext6 + `Selvage/Sumcheck` + `AirSumcheckQuadratic`. The
binary-tower line is `Tower256` (GF(2^256)), the `Tower256Logup*` controller/
admission family (5 modules in `Compiler/`, 2 in `Assurance/`), the char-2
`AdditiveFri*` proximity stack, and — importantly —
`prover/src/tower256_kernels.rs`, which already holds
`equality_weight(left, right) = ∏ᵢ (1 + lᵢ + rᵢ)` (**a two-vector `eq`, valid
only in characteristic two**) and `fraction_add_layer(numerators, denominators)`
(**one inversion-free fraction-tree layer — the LogUp/Binius step — with no
protocol driver above it**) [MEASURED via census].

So: *the GKR fraction tree's kernel already exists in our Rust, in the binary
line; the driver is missing; and the sumcheck engine is in the prime line.* That
is the Binius64 tension reproduced inside our own repo.

**[OPEN — genuine design fork, pause-list item 4]:** does the GKR substrate serve
the Tower256 line, or supersede it? (a) *Prime-only substrate*: `eq` and the
fraction tree are re-authored over the prime/Ext6 field; the Tower256 kernels
become dead and the Tower256Logup controller family is debt to delete. (b) *Two
instantiations of one Lean interface*: the layer/claim/sumcheck theory is
field-generic (it already is — `variable {F : Type*} [Field F]`), instantiated at
both Ext6 and Tower256, with `eq` given once as `∏(rᵢxᵢ + (1−rᵢ)(1−xᵢ))` which
**specializes to the existing char-2 kernel by `ring`**. (b) is cheap because our
Lean is already generic and the char-2 kernel is literally the char-2 case of the
general formula. I lean (b) and flag that it must not become an excuse to keep
two unrelated stacks alive.

### 4.2 Expander: 63 GB for 4000 Keccaks — memory is the sharp edge

[SOURCED, grey-lit §2.]

Four design rules, and a budget object rather than a hope:

1. **At most two adjacent layers resident.** GKR consumes layers in order; a
   layer's tables are droppable once its input claims are produced.
2. **Regenerate, don't store.** Where a layer is a pure function of the layer
   below, the prover recomputes it from a seed/trace rather than holding it.
3. **The engine takes tables it can fold in place**, so a caller may stream:
   `fold_mle_table` already halves in place [MEASURED], which is the right
   primitive; the engine must not require a materialized `2^m`-per-round history.
4. **The memory budget is part of the emitted plan.** Lean computes peak resident
   bytes at emit time from `(arity, degree, m, |F|)` and the runtime **refuses**
   rather than OOMs. This is the "documented ≠ detected" law applied to memory: a
   budget that cannot go red is not a budget.

The naive peak, stated so it can be falsified: `arity × 2^m × |F_elem|` bytes.
At `arity=5`, `m=26`, Ext6/BabyBear (24 B) that is **8.1 GB**; Expander's 63 GB
says the realized constant is roughly an order of magnitude above the naive one
[INFERRED-BY-ME comparing their figure to this count — their circuit shape is not
ours and this is a sanity anchor, not a prediction].

### 4.3 powdr's logup\* route needs a post-challenge commitment round

[SOURCED, brief + lookup-ram-verdicts §"Status changes".]

`LogupStar.lean`'s own header already fixes the protocol order that makes the
challenges load-bearing [MEASURED]: bind trace and addresses → sample `r` →
sample `γ` to batch → **commit the pushforward `Y`** → *only then* sample `c`.
Step 4 is a commitment *after* a verifier challenge.

On a curve that is one group element. **On a hash PCS it is a whole additional
commitment: another Merkle tree, another opening, another set of queries — and
its cost is floor-dominated, not proportional to `|Y|`.** A small post-challenge
polynomial pays a large fraction of a full opening's fixed cost.

> **Design rule: exactly ONE post-challenge commitment round, carrying every
> post-challenge polynomial batched into a single commitment and a single batched
> opening.** A protocol that wants two rounds gets restructured, not accommodated.

And the consequence for the A/B the convergence note wants: **the logUp-GKR vs
logup\* comparison on our stack is decided by this floor, not by field-op
counts.** logUp-GKR needs no post-challenge commitment (the fraction tree is
recomputed, not committed); logup* needs one. [INFERRED-BY-ME — this is the
measurement card G4 should produce, and it is exactly the convergence note's
"price the substrate once and the four contenders become cheap A/Bs".]

### 4.4 Our own instrument classes, applied

- **`#guard` is a unit test in Lean clothes.** Every round identity, every
  degree bound, every eq fact gets a **named theorem** plus an axiom pin.
  ⚠ The pin idiom in *this* repo is `#guard_msgs (whitespace := lax) in
  #print axioms <name>` — 308 files use it — and **`#assert_axioms` does not
  exist in minidregg**; `Kernel/Camera.lean:30` says so in as many words
  ("minidregg has no `#assert_axioms` yet — that tool is Assurance-lane
  territory") [MEASURED]. Do not brief a lane to use the breadstuffs tool.
  `SumcheckConformance.lean` currently uses `example : … := by decide` for its
  reference values [MEASURED] — anonymous, so nothing can cite them. The degree-3
  conformance file should **name** them.
- **A falsifier that stopped falsifying.** The conformance mutations must be
  built **constructively** (mutate by index, assert the mutation changed the
  value, *then* assert rejection). `tampered_round_poly_fails` already does the
  `(x+1) % P` construction [MEASURED] — keep that discipline and add the
  assert-the-mutation-happened step.
- **Prove the floor false.** The degree bound must be **refutable**: a tooth in
  which a degree-4 prover message is REJECTED by the `d=3` verifier. A degree
  bound nothing can violate is not a bound.
- **Class 3 — verifier accepts what it should recompute.** §1.3's factored
  terminal check is the structural answer; it must be a *stated law* in the
  layer interface, because grey-lit §7 records this class as breaking Jolt,
  Dusk PLONK and OpenVM in 2025–26 [SOURCED].
- **The Rust verifier is a twin.** `verify_sumcheck` is a hand-written Rust
  mirror of `SumcheckAccepts` with no `@[export]` behind it. By the census law
  ("a `def` with no `@[export]` is the best predictor there IS a twin") this is
  debt. See §5.3.

---

## 5. The Lean-authoring plan

### 5.1 The split, per house law

| Object | Where it lives | Why |
|---|---|---|
| Layer/claim/plan **descriptor** (which factors, which `combine`, which degree, which nodes, how claims wire between layers) | **Lean-authored, Lean-emitted** via `Compiler/Emit.lean` + `EmitShare.lean` CSE | This is the constraint system. Rust never authors a layer. `emit_faithful` is unconditional and bidirectional in minidregg — a stronger emission theorem than anything in breadstuffs. |
| **Verifier semantics** | **Lean, proved** — `LayeredAccepts` extending `SumcheckAccepts`; soundness = `adaptive_sumcheck_soundness` at `d`, composed across layers by a union bound | The trust path. |
| **Prover** (round messages, table folding, fraction-tree kernels) | **Rust, executed under a Lean spec**, bound by conformance vectors emitted from the REAL Lean `roundSum` | Unverified compute. It authors nothing. |
| Field arithmetic kernels | Rust, conformance-bound (`Ext6Conformance.lean` is the existing pattern) | Same. |

### 5.2 How the verifier semantics bind

Today the binding is a **conformance vector**: `Compiler/SumcheckConformance.lean`
instantiates the real `mle`/`roundSum` at `m=3` over BabyBear, kernel-decides the
values, and writes `prover/testdata/sumcheck_conformance.json`; the Rust test
reproduces them [MEASURED]. Its own docstring carries the correct label —
*"Agreement on the vector is the whole claim — never refinement"* — and that
label must be carried forward verbatim. Rust has no formal semantics; agreement
on vectors is the entire seam.

Two teeth in the existing vector worth preserving in the degree-3 one [MEASURED]:
`m=3` has an **interior round** (non-boolean prefix *and* boolean suffix at once,
which `m=2` never exercises), and all 8 table values are distinct so an
**MSB/LSB flip permutes the table and fails the vector**.

### 5.3 ⚠ The verifier twin, and why the rung is the moment to decide

`verify_sumcheck` is Rust that *re-states* `SumcheckAccepts` rather than calling
it. Extending it from degree 1 to degree 3 is precisely the "just add the case to
the existing Rust" move the house law forbids for AIRs, one level up.

**[OPEN, and I have a recommendation]:** land the degree-`d` verifier as an
`@[export]`ed Lean function that Rust *calls*, and delete the Rust mirror — the
"closed = the node INVOKES the Lean" law.

Cost, measured rather than guessed: minidregg contains **exactly one `@[export]`
in the whole tree** — `@[export minidregg_gate_ok] def gateOKExport` at
`Kernel/Gate.lean:615`, whose own section header reads *"the FIRST `@[export]` in
`Kernel/` — it proves the export path EXISTS … a compiled symbol
(`minidregg_gate_ok`) a Rust caller links against (rust/ authors nothing; every
decision point is a Lean export)"* [MEASURED]. **Zero exports in
`Selvage/`/`Assurance/`/`Compiler/`.** So this is *extending a demonstrated
seam*, not building one — cheaper than I first wrote, and the file's own stated
doctrine ("every decision point is a Lean export") is an argument for doing it.

Alternative: keep the Rust mirror for the rung, tag it explicitly as a twin with
a named debt item, and do the FFI as its own card. I lean toward doing the rung
with the mirror **and dispatching the FFI card in the same wave**, because a
degree-3 mirror is a bigger twin than a degree-1 one and the debt compounds.

---

## 6. What this design serves, and what it drops

### Serves all four consumers

1. **Lookup arguments** — logUp-GKR is a fraction tree = degree-3 layers with an
   eq factor. `LogupStar.lean` supplies the algebraic core (`logupPushforward`,
   `logupDefect`, the root-counting bound `(|ι|−1)/|F|`, poles priced
   separately), and `LogupIndexLink.lean` **closes `[LOGUP-ADDRESS-LINK]`** —
   `canonicalIncidencePushforward_eq_logupPushforward` proves the runtime's
   incidence-MLE scatter IS LogUp*'s semantic pushforward [MEASURED]. What is
   missing is the *tree driver*, which is this substrate.
2. **zkML vector relations** — `eq(ρ,·)·(Â·B̂ − Ĉ)` is one degree-3 sumcheck.
   The measured MNIST trace is 158,800 MACs of which 156,800 (98.7%) are one
   784-contraction [SOURCED]; as a vector relation that is **one claim**, not
   158,800 rows. `AirSumcheckQuadratic` already carries the unweighted face; the
   eq factor is the delta.
3. **vFHE M1** — the 98,304-equation BFV family is a vector relation currently
   arithmetized as AIR rows, which is why coverage sat at 1 of 98,304 [SOURCED].
   ⚠ This is the consumer that exercises the **whole** substrate, not just the
   sumcheck face: RNS limb products are degree-2-to-3 relations, but the carry
   and range obligations are **lookups**, so vFHE M1 needs the sumcheck face and
   the logUp face composed [INFERRED-BY-ME from the RNS shape; I did not read the
   98,304-equation family].
4. **Selvage's own consumers** — `LogupStar`, `BinaryLookup`, `LogupIndexLink`,
   `Tower256Logup*`, `AuthenticatedColumnLogupBridge`,
   `SparseAuthenticatedStateLogupBridge`, `AirRange`. The first three are served
   directly. `AirRange` (which owns `ConstraintSystem F Idx := List (Term (AirSig
   F Idx))` and the `rangeGadget`) is served by the lookup face. The Tower256
   family's service depends on §4.1's open fork. ⚠ **"umem" does not exist** —
   grep for `umem`/`u_mem`/`unified memory` returns zero hits; the memory model
   is `Kernel/SparseAuthenticatedState.lean` (`Layout`/`Store`/`Address`/`BusRow`,
   disciplines `rom`/`appendOnly`/`ram`) plus `Kernel/State.lean`, and the proof
   side is `TwistContinuity` — **the statement a Twist-style argument must prove,
   named but not proved**, with mutable-RAM consistency an explicit admission
   residual [MEASURED via census]. The brief's consumer list should be corrected.

### Drops, explicitly

- **Zero-knowledge in v1.** Masking is a later rung. Saying it beats gesturing at
  `ZKHiding.lean`.
- **Bit-granular arithmetization.** Per §4.1: field elements + lookups.
- **Native one-hot addressing (Twist/Shout).** Our commitment stack has none of
  the three members of the one-hot law [SOURCED]; logup*'s pushforward is our
  route and Shout-via-logup* stays claim-level.
- **Everything curve/group-based**: Celer (group-based via Dory — it does not
  transfer to a hash setting at all [SOURCED, grey-lit §5]), Nebula's folding.
- **The multilinear PCS.** §3.2 — flagged, its own campaign.
- **Degree > 5.** No consumer.
- **A general MvPolynomial per-coordinate-degree theory.** The repo already chose
  per-shape line lemmas at `d=2` and that choice is right; a general theory is a
  research project the rung does not need.

---

## 7. Open decisions, stated rather than picked

1. **Challenge field** — §3.4. Ext6 (built, proved, preferred by our own budget
   model) vs the grey-lit Ext5 pin (derived elsewhere, no type exists here),
   **and** whether `MixedFieldBudget` must grow a query-count leg first. Touches
   a check ⇒ ember's.
2. **Prime-only substrate vs two instantiations of one field-generic Lean
   interface** — §4.1. Genuine design fork.
3. **Line-lemma form at `d=3`**: closed-form coefficients (follows `prodDiff_line`,
   cheaper prover, per-shape) vs a Lagrange identity on nodes `{0,1,2,3}`
   (general, reusable at any `d`, one extra evaluation pass). I lean Lagrange for
   the substrate with the closed form landed later as a *proved-equal* prover
   optimization.
4. **Rust verifier: `@[export]` FFI now, or mirror-plus-named-debt** — §5.3.
5. **logUp-GKR vs logup\*** — do not pick from field-op counts. §4.3 says the
   post-challenge-commitment floor decides it; card G4 measures it.

---

## 8. THE DEGREE-3 RUNG — the concrete next rung

The spike question was: *what exactly would it take to reach degree 3 with an
eq-factor?* Answer, in module counts and dominant terms rather than days
(estimates here run long by ~10× historically).

### 8.1 New Lean module A — `Selvage/EqPoly.lean` (~150 lines)

```lean
def eqMle (r x : Fin m → F) : F := ∏ i, (r i * x i + (1 - r i) * (1 - x i))

theorem eqMle_cubePt (r : Fin m → F) (b : Fin m → Bool) :
    eqMle r (cubePt b) = chiEval b r                       -- unfold + split + ring, short

theorem eqMle_multiAffine_right (r) : MultiAffine (eqMle r)  -- mirrors chiEval_update

theorem eqMle_fold (f : (Fin m → Bool) → F) (r) :
    ∑ b, eqMle r (cubePt b) * f b = mle f r                -- eqMle_cubePt + `mle`'s definition
```

`eqMle_fold` is **the zerocheck reduction**: "the relation vanishes on the whole
cube" becomes "one sumcheck claim at a random `ρ`". It should be short, because
`chiEval b x = ∏ if b i then x i else 1 − x i` and `eqMle r (cubePt b)` reduces
to exactly that by `cubePt`/`ofBool` case-split [MEASURED definitions].

Then the **one genuinely new soundness lemma**:

```lean
theorem mle_ne_zero_uniform_bound {f : (Fin m → Bool) → F} (hf : f ≠ 0) :
    uniformProb (Fin m → F) (fun r => mle f r = 0) ≤ (m : ℝ) / Fintype.card F
```

— multilinear Schwartz–Zippel. Induction on `m` splitting
`mle f x = (1−x₀)·mle f₀ x' + x₀·mle f₁ x'` via `AffineInCoord`, with the
`uniformProb` toolkit (`uniformProb_coord_mem_prefix`, `unionBound_fixed`,
`card_agreeFinset_lt`) already present [MEASURED]. **This is the rung's dominant
new proof term** — ~80–120 lines, no new mathematics, but real induction work,
and everything downstream cites it. It does not exist today (Selvage's SZ is
univariate: `card_agreeFinset_lt`).

Zerocheck soundness then follows as a corollary via `mle_injective` (already
proved) + `eqMle_fold`.

### 8.2 New Lean module B — `Assurance/AirSumcheckCubic.lean` (~900–1100 lines)

A line-for-line port of `AirSumcheckQuadratic.lean`'s 916 lines with `2 → 3` and
an eq factor. The template exists, so the shape is not in doubt:

| Quadratic (exists) | Cubic (to build) |
|---|---|
| `prodDiff A B C` | `eqProdDiff ρ A B C := fun x => eqMle ρ x * (mle A x * mle B x - mle C x)` |
| `prodDiff_line` (6-line proof) | `eqProdDiff_line` — a **4-node** identity; proof = `mle_multilinear` on A,B,C + `eqMle_multiAffine_right` on eq + `ring` |
| `quadCross`, `quadRoundPoly` (deg ≤ 2) | `cubicRoundPoly` via `Lagrange.interpolate` on `{0,1,2,3}`; degree bound free from `Lagrange.degree_interpolate_lt` (Mathlib, and Selvage may import Mathlib freely per `check-import-boundary.sh`) [MEASURED] |
| `quadRoundPoly_eval` | `cubicRoundPoly_eval` |
| `quadHonest*` (4 lemmas) | `cubicHonest*` — identical proofs; they ride `roundSum_zero`/`roundSum_succ`, **already degree-generic** |
| `scChain_quadHonest_final` factored `Â(r)B̂(r) − Ĉ(r)` | factored `eq(ρ,r)·(Â(r)B̂(r) − Ĉ(r))` — the 4 input claims |
| `quad_sumcheck_soundness ≤ m·2/\|F\|` | `cubic_sumcheck_soundness ≤ m·3/\|F\|` — `adaptive_sumcheck_soundness (d := 3)`, one `simpa` |

Side condition to state honestly: the node set `{0,1,2,3}` must be injective in
`F`, i.e. `ringChar F > 3`. True for BabyBear/Ext6, **false in characteristic 2**
— which is a second, concrete reason §4.1's fork matters. In char 2 the node set
must be `{0,1,β,β+1}` for a subfield element β, or the message must be sent in
coefficient form.

### 8.3 Rust — `prover/src/sumcheck.rs` (~+120 lines, −0)

1. `SumcheckProof` gains `degree: usize`; `rounds[i].len() == degree + 1`.
2. `round_poly(..., degree)` evaluates at nodes `0..=degree`.
3. `eval_affine` → `eval_lagrange(evals, t, p)`. **Needs a new primitive:
   `inv_mod`** — the engine currently has only `add_mod`/`sub_mod`/`mul_mod`
   [MEASURED]. Cheapest correct form: Fermat `pow_mod(x, p−2)`, ~10 lines. And
   note the barycentric weights for nodes `0..=d` are **constants**
   (`d=3`: `1/(−6), 1/2, 1/(−2), 1/6`), so one table of `d+1` inverses per prime
   keeps the hot path multiplication-only.
4. `verify_sumcheck`: `g.len() != degree+1 → false`; **keep** `g[0]+g[1] ==
   running` (LAW-2 is what makes this a real check); fold with `eval_lagrange`.
5. The summand is `k` tables + a combining shape, driven by the **emitted plan**,
   not by a Rust-side enum of relation kinds.
6. **`impl NativeMleScalar` for the prime scalar**, so `mle_kernels::fold_mle_table`
   applies and `round_sum` drops from `O(4^m)` to `O(2^{m−i})` per round. Without
   this the rung demos at `m≈12` and no further.

### 8.4 Conformance — `Compiler/SumcheckCubicConformance.lean`

Four tables + the eq point `ρ`, `m = 3` (keep the interior-round tooth), nodes
`{0,1,2,3}`, values kernel-decided by `decide` at BabyBear — feasible, as the
existing file proves; the Poseidon2 reduction bomb does not apply to plain field
arithmetic. **Name the decided values as theorems**, not `example`s. Add the
constructive mutation and the **degree-4-message-rejected** tooth (§4.4).

### 8.5 The cheapest spike inside the rung

`eqMle` + `eqMle_cubePt` + `eqMle_fold` alone — **~40 lines, no protocol change,
no Rust change.** It proves the eq factor is expressible in our `chiEval` world
and gives the zerocheck reduction its exact statement. If that is not short, the
whole rung's cost estimate is wrong and we find out for the price of an hour.

### 8.6 Dominant terms, honestly

Two: **multilinear Schwartz–Zippel** (§8.1, new, cited by everything) and the
**`AirSumcheckQuadratic` port** (§8.2, ~900 lines of mechanical-but-real work
where the only new content is one line lemma). Everything else is small. The
wildcard is §8.3 item 6 — the `NativeMleScalar` impl for the prime path — because
the trait is implemented today only for `Ext6`/`TowerElem`/`Tower256` and none of
the MLE kernels are wired to a Lean-owned dispatch adapter [MEASURED].

---

## 9. Dispatch-ready workstream cards

### G1 — `eq` + zerocheck + multilinear Schwartz–Zippel *(dispatch first; G2/G4 wait on it)*
**Spec:** §8.1 of this file. **Repo:** `~/dev/minidregg`, new file
`Selvage/EqPoly.lean`. **Build:** `lake build Selvage.EqPoly` then full
`lake build` (per-file green hides a red umbrella).
**Real signatures to build against** (do not reconstruct):
`Selvage/MultilinearExtension.lean:103 cubePt`, `:111 chiEval`, `:116 mle`,
`:142 mle_injective`, `:161 AffineInCoord`, `:192 mle_multilinear`;
`Selvage/Sumcheck.lean:77 card_agreeFinset_lt`, `:92 uniformProb_mem_finset`,
`:306 unionBound_fixed`, `:343 uniformProb_coord_mem_prefix`.
**Gate:** `eqMle_fold` and `mle_ne_zero_uniform_bound` are **named theorems**,
each pinned with `#guard_msgs (whitespace := lax) in #print axioms <name>` —
**not** `#assert_axioms`, which does not exist in this repo; a refutation tooth
(a nonzero `f` whose `mle` vanishes at a *specific* point, showing the bound is
not vacuous); `scripts/check-import-boundary.sh` green.
**Forbidden:** `#guard`; a vacuous or tautological statement; `sorry`.

### G2 — the degree-3 cubic realizer with an eq factor
**Spec:** §8.2. **Blocked on:** G1. **Repo:** `~/dev/minidregg`, new
`Assurance/AirSumcheckCubic.lean`, template `Assurance/AirSumcheckQuadratic.lean`
(916 lines, read it first — the port is line-for-line).
**Gate:** `cubic_sumcheck_soundness ≤ m·3/|F|` derived from
`adaptive_sumcheck_soundness (d := 3)`, not re-proved; `scChain_cubicHonest_final`
**factored** into the 4 input claims (§1.3 — a single opaque oracle value is a
Class-3 bug); the `ringChar F > 3` node-injectivity side condition **stated, not
assumed silently**; full `lake build`; detached-clone verification at the
committed SHA.
**Must not assume:** that `roundSum_*` needs re-proving — it is already
degree-generic; that `d=3` changes any protocol-layer theorem — it does not.

### G3 — the degree-`d` Rust engine + the folding prover, conformance-bound
**Spec:** §8.3–8.4. **Blocked on:** G2 (needs the Lean `roundSum` at the cubic
shape to emit the vector). **Repo:** `~/dev/minidregg`, edit
`prover/src/sumcheck.rs`, new `Compiler/SumcheckCubicConformance.lean`.
**Gate:** prover+verifier roundtrip where the verifier semantics are Selvage's;
LAW-1 and LAW-2 verifiable by reading the diff (`h(1)` on the wire; no function
returning randomness without the terminal value); the constructive mutation test
and the **degree-4-message-rejected** tooth both present and both red when
disarmed; the label on the result is **"vector agreement"**, never refinement or
verification. **Measure and report:** wall-clock and peak RSS at `m ∈ {10,16,20}`
with and without `fold_mle_table` — this replaces §2.4's inferred 10–20×.
**Tripwire, verbatim in the brief:** no `assert_zero`, no builder, no gate, no
AIR constraint in Rust. The relation shape comes from the emitted plan.

### G4 — logUp-GKR vs logup\*, priced on the substrate
**Spec:** §4.3 + `Selvage/LogupStar.lean`'s protocol-order header +
`Selvage/LogupIndexLink.lean`. **Blocked on:** G1, G2. **Deliverable:** the
fraction-tree layer driver over the substrate (logUp-GKR), and a measured
comparison against the logup\* route whose deciding term is the
**post-challenge commitment floor**, not field-op counts.
**Corrections baked in:** the Celer comparison is dead (group-based via Dory,
does not transfer to a hash setting); all field-op constants in the published
tables are denominated in a unit eprint 2026/587 moves by >10×, so **do not lock
the A/B on borrowed constants** — measure on our engine.
**Note the asset:** `prover/src/tower256_kernels.rs::fraction_add_layer` is an
inversion-free fraction-tree layer that already exists in char 2 — read it for
the kernel shape; it is not the driver and it is not in the trust path.

### G5 — the multilinear PCS seam: interface + ideal inhabitant + equivocator
**Spec:** §3.1–3.2. **Parallel** (blocks on nothing). **Repo:** `~/dev/minidregg`,
new `Selvage/MultilinearCommitment.lean`.
**Template to copy wholesale:** `Selvage/Commitment.lean` — `OpeningScheme` /
`PositionBinding` / `BindingCommitment` / `idealCommitment` / and crucially the
**`equivocal` counter-scheme with `equivocal_not_binding` and
`equivocal_breaks_extract_bind`**, which is what makes binding load-bearing there.
**Gate:** an axiom-free ideal inhabitant; an equivocator with a refutation
theorem; the sumcheck/GKR theorems from G2 restated against the interface with
**no mention of FRI, Merkle, Reed–Solomon, or a rate**.
**Must not:** attempt the BaseFold/WHIR bridge. That is a campaign. Point at
`Selvage/MultiplicativeMleTerminal.lean` as its seed and stop.

---

## 10. What I did NOT do

- **I did not build or compile anything.** No `lake build` was run; every Lean
  claim here is from reading source, and the line counts for new modules are
  estimates.
- **I did not read `Assurance/AirSumcheckQuadratic.lean` in full** (916 lines) —
  I read its header, `prodDiff_line`, `quadRoundPoly`, `quad_sumcheck_soundness`
  verbatim, and took the rest of its inventory from the census sweep.
- **I did not read `ErrorBudget120` / `PoWSoundnessParams`.** §3.4's finding is
  that the query-count leg is not in `mixedFieldSoundness`; whether it is composed
  elsewhere is unchecked, and that is exactly the thing to check before quoting
  137.
- **I did not verify the GKR fraction-tree relation shape against a source.** The
  degree-3/5-factor figure is standard and matches the brief, but I derived the
  per-coordinate degree myself from `eq·(p_L·q_R + p_R·q_L)`.
- **I did not read the 98,304-equation BFV family**, so consumer 3's degree claim
  is inference from the RNS shape.
- **I did not price the multilinear PCS** — deliberately, per the brief.
- **No absence claim here rests on the eprint mirror.** The absences I assert
  (GKR, layered circuits, zerocheck, two-vector `eq` in Lean, Ext4/Ext5 types,
  `umem`, multilinear PCS, `#assert_axioms`) are **grep results over our own
  trees**, which is a complete instrument for that question.
- ⚠ **Two of my own first-draft claims were wrong and are corrected in place**,
  recorded here because the class matters more than the facts: I wrote "zero
  `@[export]` in minidregg" (there is exactly one, `Kernel/Gate.lean:615`) and I
  briefed `#assert_axioms` as the axiom-pin idiom (that is breadstuffs'; this
  repo uses `#guard_msgs in #print axioms`). Both came from carrying a
  neighbouring repo's convention across a boundary — the same move that makes a
  lane build a mirror. Both were caught by grepping my own assertions.
