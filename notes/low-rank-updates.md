# Low-rank updates — the commitment is the step, so stop committing the step

Lane: LEAN + RUST BUILD, 2026-08-14. Repo: **`~/dev/minidregg`**
(`Assurance/ZkmlLowRankUpdate.lean`, `prover/src/bin/low_rank_commit_cost.rs`).
Landed as `c060efa` (Lean, 759 insertions, 0 deletions) and `3ffa609` (Rust, 276
insertions, 0 deletions).

**Substrate, said out loud: the constraint semantics are Lean-authored.** Rust is
prover and harness only — and here it is not even a prover, it is a COST COUNTER
that makes no soundness claim at all.

---

## THE RESULT IN ONE LINE

`W' = W + A·B` at rank `r` commits **`2rd` felts instead of `d²`** — **128× fewer
committed felts and 128× fewer Poseidon2 permutations at `d = 4096, r = 16`** —
and the base is committed **once**, so a training run's committed object is `W₀`
plus a list of factor pairs, with **no intermediate `W_t` ever committed at all**
(`chainUpdate_eq_base_plus_deltas`). Serving that chain is **one base matvec plus
`T` thin pairs**, because `(W + A·B)v = Wv + A(Bv)` and the `d²` term appears
exactly once for a list of any length (`matVec_chainUpdate`).

**Break-even rank is `d/2` — 2048 at `d = 4096` — in BOTH units.** No rank anyone
would use is anywhere near it, so **the commitment is never the reason to stop.**
The break-even that *does* bind is in **steps, not rank**: merging the deltas back
into `W` costs one full recommit and pays for itself once `T·2rd > d²`, i.e. **`T
= 128` steps at `d = 4096, r = 16`.**

---

## 0. WHY THIS LANE EXISTS — the prior rung's honest half

`notes/rank1-gradient-check.md` proved the gradient PROOF for a linear layer
~7·10⁴× cheaper (`O(2^{m/2})` against `O(2^m)`), with `sgd_step_sound` certifying
a whole SGD step in three openings at one common point and zero rounds. It then
said its own limit out loud:

> the check removes the `n²` PROOF, not the `n²` COMMITMENT. The step still
> commits `2^24` felts for `W'`.

`notes/field-op-counts.md` sharpened that afterwards: the prover is **hash-bound
by 5.0–7.2× at every feasible blowup**, count-vs-count with one measured
constant. So a committed felt is precisely the expensive thing, and once the
gradient proof is 10⁴× cheaper the commitment IS the step. This lane removes the
commitment.

---

## 1. WHAT LANDED IN LEAN

`Assurance/ZkmlLowRankUpdate.lean`, ~750 lines, no `sorry`, 21 headline axiom
pins all `[propext, Classical.choice, Quot.sound]`, wired into `Assurance.lean`.
It lives in `Assurance/` rather than `Selvage/` because it needs both
`Selvage.Rank1GradientCheck` and `Assurance.ZkmlMatmulSumcheck`, and
`scripts/check-import-boundary.sh` forbids the reverse.

### The relation, and why it cost almost nothing

For committed `W`, `A` (`d×r`), `B` (`r×d`) and a claimed `W'`, at `r = 2^κ`:

```
mle₂_lowRankUpdate :
  Ŵ'(x,y) = Ŵ(x,y) + Σ_{p ∈ {0,1}^κ} Â(x,p)·B̂(p,y)      at EVERY (x,y)
```

It is an identity of the extensions — no probability, no `eq` factor, no appeal
to multilinear uniqueness — and it is three lines, because of one observation:

```
lowRank_delta_is_the_matmul_output :  (fun a b => W'(a,b) − W(a,b)) = matmulTable A B
```

**The delta table IS the matmul's output table.** So the entire landed
contraction argument — `mle₂_contraction`, the honest prover `matmulHonest`, the
composed soundness — transfers to the update relation with nothing reproved. The
hard object already existed, which is the third time in three rungs that this has
been the reason a piece was cheap.

And the verifier never materializes the delta:

```
lowRank_target_from_two_openings :  mle₂ (W' − W) x y = mle₂ W' x y − mle₂ W x y
```

Its target is the difference of two openings it already holds. That is what makes
`W` and `W'` separate commitments rather than a materialized difference, and it is
a named theorem rather than a remark because the soundness statement below is
phrased over the delta table and this is the bridge.

### ⚑ THE CORRECTION — the brief asked, and the answer is "for one of two designs"

The brief flagged that `rankK_sound` already exists and **its bound does not grow
with `K`**, and asked whether the rank-`r` case is literally that theorem. It is —
**for one of two designs, and they are not the same protocol.**

| | `r`-openings design | **one-commitment design** |
|---|---|---|
| what is committed | `2r` separate vectors | **`A` and `B`, one matrix each** |
| openings | `2r` | **2** |
| verifier evaluates the inner sum | yes, `r` multiplications | **no — it cannot** |
| rounds | 0 | `κ = log₂ r` sumcheck rounds |
| bound | `(μ+ν)/\|F\|`, **no `κ`** | **`(μ+ν)/\|F\| + κ·3/\|F\|`** |
| saves the commitment | **no** | **yes — this is the whole point** |

* `lowRank_summand_is_rankK_summand` proves the summand is `rankK`'s summand **by
  `rfl`**: `rowPartial A x p` IS the one-block MLE of `A`'s `p`-th column and
  `colPartial B y p` IS the one-block MLE of `B`'s `p`-th row. So `lowRank_sound`
  is `rankK_sound`'s statement in the block representation, reindexed from `Fin K`
  to the cube `{0,1}^κ`, and it is **not reproved** — as the brief asked.
* `lowRank_sumcheck_soundness` is the one-commitment bound, obtained by
  instantiating the landed `matmul_sumcheck_soundness` at the delta table.

**So "the bound does not grow with `K`" is a fact about the design that does not
save the felts.** Quoting it for the design that does would be quoting the
flattering number of a pair — the failure mode this repo has a memory for.

⚑ **And the full honest picture, which cuts the other way**: the sumcheck the
one-commitment design adds runs over `κ` variables on tables of `r` entries.
**At `r = 64` that is 128 field operations.** Its *work* is nothing. Its *error*
is, at `d = 4096` over BabyBear:

| design | bound | bits |
|---|---|---|
| `r`-openings, any `r` | `24/2^31` | **2^−26.42** |
| one-commitment, `r = 16` (`κ=4`) | `36/2^31` | 2^−25.83 |
| one-commitment, `r = 256` (`κ=8`) | `48/2^31` | 2^−25.42 |

**The correction costs at most ~1 bit at every usable rank.** It matters because
it is the difference between *does not grow* and *grows*, not because the
magnitude is large, and reading it as "the one-commitment design is expensive"
would be the opposite error.

⚠ **Neither figure is a security level**, for exactly the reason the rank-1 rung
recorded: one point of the BASE field buys ~26 bits. The fix is the FIELD
(`Selvage/SmallField.lean` puts a degree-4 BabyBear extension at ~116 bits), not
the rank. ⚠ Small correction to the prior note in passing: it wrote `24/2^31 ≈
2^-26.1`; the value is `2^-26.42` (`2^-26.1` would need 30, not 24). Direction and
verdict unchanged.

### The rank-1 rung is the `r = 1` INSTANCE, not a sibling

```
matmulTable_rank_one :  at κ = 0,  matmulTable A B a b = A(a)·B(b)
```

The inner cube is a single point and the delta collapses to the outer product —
the object `Selvage/Rank1GradientCheck.lean`'s `outerTable` names in the flat
index convention. This was written deliberately: a new file beside the old one,
restating the same MLE machinery, would be a twin, and this repo has a campaign
about those. (`mle₂` is likewise not a parallel extension — the landed
`mle₂_row` proves it IS a composition of the one-block `mle`.)

### §2 — the chain, where the accumulator state IS the model

```
chainUpdate W [] = W
chainUpdate W ((A,B) :: rest) = chainUpdate (lowRankUpdate W A B) rest

chainUpdate_eq_base_plus_deltas :
  chainUpdate W L = fun a b => W a b + (L.map (fun AB => matmulTable AB.1 AB.2 a b)).sum
```

**Applying the deltas one at a time equals adding all of them to the base at
once.** That is the whole licence for never recommitting: no intermediate `W_t`
is ever a committed object, the history is `W₀` plus a list of factor pairs, and
`mle₂_chainUpdate` opens the whole history at ONE point,
`Ŵ_T(x,y) = Ŵ₀(x,y) + Σ_t Σ_p Â_t(x,p)·B̂_t(p,y)`.

### ⚑ §3 — the inference-side identity, the part the brief called actually new

The load-bearing fact is associativity:

```
matVec_matmulTable :  (A·B)·v = A·(B·v)
```

i.e. **the cheap evaluation order is LEGAL** — `2rd` multiplies rather than the
`d²r + d²` of forming `A·B` first. Cost is not in this model; the *availability*
of the cheap order is, and it is the entire content of the claim. On top of it:

```
matVec_lowRankUpdate :  (W + A·B)·v = W·v + A·(B·v)
matVec_chainUpdate   :  (chainUpdate W L)·v
                          = W·v + Σ_{(A,B) ∈ L} A·(B·v)
mle_matVec_lowRankUpdate : the same split in the unit a verifier consumes
```

`matVec_chainUpdate` is **what makes the CHAIN cheap rather than just the step**:
the `d²` term appears **once** on the right-hand side for a list of any length.

⚑ **Deliberately NOT a theorem.** "The base evaluation `W·v` does not depend on
`A` or `B`, so it is shared across every adapter" is `Iff.rfl` — a vacuous
statement of exactly the class this repo keeps finding, and a reader seeing it in
the theorem list would credit the file with a check it does not perform. The
non-vacuous form of that claim is `matVec_chainUpdate`, and it is proved. (The
prior rung made the same call about "the check never reads the forward pass"; the
discipline continues.)

### §4 — scope AS THEOREMS

* ⚑ **`lowRankUpdate_gauge`** — for ANY invertible `r×r` change of basis `S` (with
  inverse `T`), the pair `(A·S, T·B)` is the **same update** and is accepted
  identically. **The proof binds the `d×d` delta; the factorization is gauge.**
  Nothing downstream may read `A` as "the adapter", quote a norm of `A`, or treat
  `(A,B)` as identifying. `lowRankUpdate_rescale` is the scalar case — the exact
  analogue of the rank-1 rung's `outerTable_rescale`, and this is its correct
  generalization (that one pinned the matrix up to a scalar; this one is up to
  `GL_r`).
* **`lowRank_blind_to_the_projection`** — for ANY factor pair the relation holds
  at every challenge. **Whether `A,B` is the correct — or even a good — low-rank
  projection of the true gradient is a SEPARATE obligation**, and nothing here
  touches it.

---

## 2. TEETH — and the one the brief named

The vacuity to fear here is **not** the rank-1 file's. It is that the relation
might certify *"the delta is low rank"* rather than *"the delta is THIS low-rank
delta"* — a check with the weaker meaning accepts every `A'·B` and is worthless
for a training log. Point teeth at `μ = ν = 2, κ = 1` over F₅ (a 4×4 weight
matrix with a genuinely low-rank, rank-≤2 update); counting teeth at `μ = ν = 1,
κ = 0` (2×2 with a rank-1 update) where the whole 25-point challenge space is
kernel-checked by `decide`.

| tooth | what it excludes |
|---|---|
| ⚑ `lowRank_refuses_another_low_rank_update` | **a genuinely different rank-2 delta `A'·B` is REFUSED** — the brief's question, answered |
| `the_other_update_is_different` | …and it is a different matrix, so that is not refusing a spelling |
| `lowRank_refuses_a_tampered_base` | the BASE is bound, not just the delta — what makes a chain auditable |
| `lowRank_refuses_the_transposed_update` | an index-order bug in `rowPartial`/`colPartial` survives every symmetric test; this catches it |
| ⚑ `gauge_changes_the_factor` + `gauge_leaves_the_update_fixed` | a NONIDENTITY `S` the check genuinely cannot see — the gauge scope item bounds a **real** freedom, not an empty set |
| `inference_identity_fires` | `(W + A·B)v = Wv + A(Bv)` computed |
| `the_adapter_moves_the_output` | …and the identity is not trivially true because the delta does nothing |
| `the_two_evaluation_orders_agree` | the `d²r` association and the `2rd` one give the same vector |
| `chain_of_two_computed` | two deltas in sequence = both added to the base |
| `count_false_accepts = 9` | **9 of 25 against the theorem's 10/25 — the bound is nearly ATTAINED, not loose slack** |
| `count_false_accept_witness` | ⚠ the false-accept event is NONEMPTY, so the bound constrains a real event |
| `count_tampered_base_never_accepted` | 0 of 25 accept a shifted `W'` |
| `count_sound_fires` | the soundness theorem itself fires on the wrong update |

**Falsifier check.** Three mutations on scratch copies, all **exit 1**:

1. `count_false_accepts` mutated `= 9 → = 8` — `decide` proves it false.
2. the `¬` dropped from `lowRank_refuses_another_low_rank_update` — so the check
   genuinely refuses the other low-rank update; if it accepted, this would build.
3. the inference identity's second term swapped to a different adapter
   (`eA → eA2`) — so the identity pins *which* adapter, not merely *some*.

Each mutation was asserted to have applied (`assert s.count(old)==1`) before the
verdict was read, per the recorded class where a mutation quietly became a no-op
and the adversary died while the gate stayed green.

---

## 3. THE PRICE, IN THE UNIT THAT BILLS

`prover/src/bin/low_rank_commit_cost.rs`. **There is no clock in the file.** Every
number is a COUNT derived from what the code decides, hence contention-immune by
construction — this box runs at load 30–95 and its wall-clock is not evidence.
One measured constant enters at the very end, labelled, only to convert counts
into milliseconds.

### The model, and which half is measured

Committing a `w`-column × `h`-row matrix at `log_blowup = lb`:

```
n     = h · 2^lb          leaves (rows of the low-degree extension)
leaf  = ⌈w/8⌉ · n         PaddingFreeSponge over each row, rate 8
tree  = n − 1             binary Merkle compressions
```

* The `⌈w/8⌉`-per-row leaf term is the **mechanism stated** in
  `phase-profile.md` §6. It is not separately calibrated by that table.
* The tree law is **CALIBRATED, not asserted**. `phase-profile.md` §7's measured
  Merkle-commit column fits `2n − 3` exactly at `n = 1656·2^b`; this model gives
  `2n − 1` for a narrow commit, so the two must agree to a constant 2 at every
  rung. **They do, at all five rungs**, and the binary refuses to print if they
  stop. `the_calibration_is_refutable` checks the check can go red.

```
     b      measured         model   delta
     3         26493         26495       2
     4         52989         52991       2
     5        105981        105983       2
     6        211965        211967       2
     7        423933        423935       2
```

Rearranged, for `w ≥ 8`:

```
perms ≈ (2^lb / 8) · N · (1 + 8/w),        N = w·h committed felts
```

**So committed felts IS the right currency**, at `2^lb/8` permutations each — with
one correction, the aspect-ratio penalty `(1 + 8/w)`.

### ⚑ The finding that penalty produces: commit `A` WIDE

The penalty is under 7% for a wide matrix and it **bites exactly in the low-rank
regime**, because the natural `d×r` layout of `A` has `w = r ∈ {8,16,64}`. At
`d = 4096`, for identical felts:

| `r` | `A` as `d×r` | `A` transposed | penalty on `A` | penalty on the step |
|---:|---:|---:|---:|---:|
| 8 | 32,767 | 16,415 | **2.00×** | 1.50× |
| 16 | 49,151 | 32,831 | 1.50× | 1.25× |
| 64 | 147,455 | 131,327 | 1.12× | 1.06× |

**Only the transposed layout reaches the felt-count ratio `d/(2r)`.** This is
invisible in a felt count and is the sort of thing that would have been shipped as
a 1.5× loss without noticing.

### The table (at `log_blowup = 2`, `A` committed wide)

| `d` | full `W'` recommit | `r = 8` | `r = 16` | `r = 64` | `r = 256` |
|---:|---:|---:|---:|---:|---:|
| **felts** 4096 | 16,777,216 | 65,536 | 131,072 | 524,288 | 2,097,152 |
| **perms** 4096 | 8,404,991 | 32,830 | 65,662 | 262,654 | 1,050,622 |
| **ratio** | 1× | **256×** | **128×** | **32×** | **8×** |
| **perms** 1024 | 528,383 | 8,254 | 16,510 | 66,046 | 264,190 |
| **perms** 16384 | 134,283,263 | 131,134 | 262,270 | 1,049,086 | 4,196,350 |

⚑ **Every ratio here is blowup-independent** — the blowup is a common factor — so
the verdict does not rest on which `log_blowup` is deployed. Only the absolute
counts and the ms conversion do. (`2` is the post-`blowup-drop.md` figure,
demonstrated there rather than confirmed-deployed by this lane.)

### The break-even rank, and the one that actually binds

**Break-even rank: `r = d/2`, in BOTH units** — `2048` at `d = 4096`, `512` at
`d = 1024`, `8192` at `d = 16384`. Since `2rd = d² ⟺ r = d/2`, and permutations
track felts for wide commits, the two units agree to within 1 permutation.

> **Nobody uses a rank near `d/2`.** LoRA ranks run 8–256. **The commitment is
> never the reason to stop**, at any rank, at any of these dimensions.

**So what does stop it? Not the rank — the CHAIN LENGTH.** Serving `T` stacked
deltas costs `d² + T·2rd`, and merging them back into `W` costs one full recommit.
Merging pays once `T·2rd > d²`:

| `d` | `r = 8` | `r = 16` | `r = 64` |
|---:|---:|---:|---:|
| 1024 | T = 64 | T = 32 | T = 8 |
| **4096** | **T = 256** | **T = 128** | **T = 32** |
| 16384 | T = 1024 | T = 512 | T = 128 |

**That is the real break-even and it is in STEPS, not rank.** A run longer than
`T = d/(2r)` steps should periodically merge and eat one `d²` recommit; below it,
never merge.

### The conversion, isolated

Using `phase-profile.md` §7's measured rate (packed 189.5 ns/perm, prover side):

```
d = 4096, full W' recommit :  8,404,991 perms  =  1.59 s
d = 4096, low-rank r = 16  :     65,662 perms  =  12.4 ms
```

⚠ **This is not in contradiction with the prior lane's "263 ms for `W'`."** That
figure was a **cshake256 proxy over LE felts with no Merkle tree and no LDE
blowup**; this one is the deployed-shape Poseidon2 Merkle commit at blowup 4,
which is a strictly larger object. Different objects, ~6× apart for exactly that
reason.

### The per-step accounting, updated

```
  gradient PROOF      8.9–25 s      →  0.16–2 ms       (rank-1 rung)
  weight COMMITMENT   8,404,991 p   →  65,662 p        (THIS lane, r = 16)
  added sumcheck      —             →  ~32 field ops   (one-commitment design)
  added error         —             →  +0.6 bits
```

---

## 4. WHAT THIS DOES NOT COVER — precisely

Each item marked **[terminal]** (a theorem of the model — it will still be true
when everything else is done) or **[undone]** (real work wearing a caveat's
clothes).

1. **[undone] `A,B` is not verified to be the correct low-rank projection of the
   true gradient.** `lowRank_blind_to_the_projection` is a theorem: any pair is
   accepted. Whether the pair is a good approximation of `∇W`, or of *anything*,
   is untouched. This is the direct successor of the rank-1 rung's
   `rank1_blind_to_the_error` and it is the same gap one level up.
2. **[terminal] The factorization is gauge.** `lowRankUpdate_gauge` — `(A·S,
   S⁻¹·B)` is the same update for every invertible `S`. Correct (the delta *is*
   the object), but it means no downstream consumer may read `A` as identifying,
   nor bound anything by a norm of `A` alone.
3. **[undone] Nothing about the nonlinearity.** DARK-TRAINING §1's claim that `σ'`
   is virtualizable off the forward table is as unbuilt as it was.
4. **[undone] Nothing about accumulated exactness.** `chainUpdate` is exact over
   the field. Real deltas are bf16/fp32, and whether the field encoding's
   exactness argument survives `T` accumulating steps is DARK-TRAINING §7, still
   open. **The chain theorem makes this MORE urgent, not less** — it is precisely
   the construction that lets `T` grow without a recommit.
5. **[undone] The openings are assumed.** Both designs take `Ŵ`, `Ŵ'`, `Â`, `B̂`
   from a PCS, and `Selvage/Commitment.lean`'s `OpeningScheme` is still
   POSITIONAL — the wrong shape for a multilinear claim. Standing residual
   `[MATMUL-pcs]`, `gkr-substrate-findings.md`.
6. **[undone] Fiat–Shamir.** Both bounds are over a UNIFORM challenge; the
   deployed protocol draws from a transcript. Residual `[MATMUL-fs]`.
7. **[undone] `r` must be a power of two** (`r = 2^κ`). A rank of 12 or 48 needs
   padding; `padded_contraction` is cited as licensing it in
   `ZkmlMatmulSumcheck`'s docstring but this file does not use it.
8. **[undone] The field.** `(μ+ν)/|F| + κ·3/|F|` at BabyBear is `2^-25.8` at
   `d=4096, r=16`. Not a security level. The deployment fix is an extension field
   plus repetition — same conclusion as the rank-1 rung, and unchanged by rank.
9. **[terminal] Only a linear layer.** No bias, no convolution, no attention, no
   normalization. A conv delta is a correlation, not a matmul, and whether it has
   an analogous cheap factorization is open and unexamined.
10. **[undone] The `2rd` accounting prices the COMMITMENT only.** Producing `A,B`
    (the projection itself) is real prover work that nothing here counts.
11. **[terminal] The Rust is a COUNTER, not a checker.** It computes a cost model
    and asserts it against measured data. It makes no soundness claim, is never
    called refinement, and cannot be — there is no semantics of Rust.
12. **[undone] The serving cost grows linearly in `T` until a merge.** Priced
    above (`T = d/(2r)`), but the merge itself is not implemented or proved.

---

## 5. BUILD EVIDENCE

Exit codes captured directly, never through a pipe.

| gate | result |
|---|---|
| `lake env lean Assurance/ZkmlLowRankUpdate.lean` | **exit 0**, no output, ~4.7 s |
| `lake build Assurance` | **8,832 jobs, exit 0** |
| `cargo test --release` (whole prover crate) | **exit 0**, all suites + 5 new |
| `cargo run --release --bin low_rank_commit_cost` | **exit 0**, calibration holds at all 5 rungs |
| falsifier: count `9 → 8` | **exit 1** |
| falsifier: `¬` dropped from the sharp refusal tooth | **exit 1** |
| falsifier: inference identity's adapter swapped | **exit 1** |
| `grep sorry` on the new Lean | none |
| axiom pins | 21, all `[propext, Classical.choice, Quot.sound]` |
| `scripts/check-import-boundary.sh` | **exit 0** |
| `scripts/check-proof-hygiene.sh` | ⚠ **exit 1 — NOT this lane** (see below) |

⚠ **`check-proof-hygiene.sh` is RED on the tree, and it is not this lane's.** It
reports two bare `#print axioms` at `Selvage/BaseFoldBcsPadding.lean:238–239`,
introduced by a concurrent lane in `a696378 disambiguate padded BaseFold profile
types`. This file has **zero** bare footprints — all 21 pins use the repo's inline
`#guard_msgs (whitespace := lax) in #print axioms` idiom. Recorded rather than
silently absorbed, because "red as steady state hides everything" and the next
lane to run this gate should know which two lines to look at.

Two commits, both `--only` on named paths with the index re-added afterwards (the
2026-08-14 PREFLIGHT entry): `c060efa` (Lean, 2 files, 759 insertions, **0
deletions**) and `3ffa609` (Rust, 1 file, 276 insertions, **0 deletions**). Zero
deletions in both means no foreign hunks were swept from a tree carrying three
other lanes' uncommitted work. `prover/src/lib.rs` was **not touched** — cargo
auto-discovers `src/bin/`, so the new binary needed no edit to the file another
lane holds dirty.

⚠ **The Lean side was NOT verified from a detached extraction.** A detached Lean
build needs a cold `.lake` (mathlib fetch), not worth the wall-clock here. What
was checked instead: `lake build Assurance` (the WHOLE tree, 8,832 jobs, not just
the changed file) ran green *after* the module was registered, so the shared-
`Assurance.lean` consumer path is covered — which is the specific failure the
"per-file green hides a red umbrella" memory names. That is weaker than a detached
build and is stated as such.

⚠ **`git status` was re-checked immediately before the commit.** Between the
first check and the build, three `Selvage/BaseFold*.lean` files appeared modified
and then vanished (another lane committing). `Assurance.lean` carried exactly one
changed line — mine — verified by diff count before committing it.

---

## 6. THE ESTIMATE, MEASURED

The brief predicted the rank-`r` relation might be literally `rankK_sound`. **It
half was, and the half that wasn't is the finding.** The relation and the
`κ`-free bound really are that theorem — proved by exhibiting the summand
correspondence as `rfl` rather than by reproving anything — and the *other*
design, the one that actually saves the felts, needed a second bound that the
first does not imply.

⚑ The reason the whole file was one build cycle is the same reason as the last
two rungs: **the hard object already existed.** `mle₂_contraction`,
`mle₂_zero_uniform_bound` and `matmul_sumcheck_soundness` were built for the
matmul face, and `lowRank_delta_is_the_matmul_output` is the one line that makes
the update relation an instance of them. Four errors on the first compile, all
mechanical: a `Finset.sum_eq_single` goal order, a nonexistent
`Finset.mul_sum.symm`, and a missing `Decidable` instance for the accept predicate
(the rank-1 file avoided it by stating its teeth as raw equations — naming the
predicate instead is better, and costs one instance).

The genuinely new work was **§3, the inference side**, which the brief correctly
identified: there was no `matVec` anywhere in the tree, and `matVec_chainUpdate`
— the `d²` term appearing once for a list of any length — is the statement that
makes a *chain* cheap rather than a *step*.
