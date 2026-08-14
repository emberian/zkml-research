# The rank-1 gradient check — build log

Lane: LEAN + RUST BUILD, 2026-08-13. The first concrete piece of verifiable
training, unblocked by the degree-3 rung. Repo: **`~/dev/minidregg`** (Selvage
lives there, not in breadstuffs).

**Substrate, said out loud: the constraint semantics are Lean-authored**
(`Selvage/Rank1GradientCheck.lean`); Rust is prover and harness only
(`prover/src/rank1.rs`, bound by conformance vectors, never called refinement).

---

## THE RESULT IN ONE LINE

For a linear layer, `∇W = δ·xᵀ` is a rank-1 outer product, its multilinear
extension **FACTORS** — `(δ⊗x)^(r) = δ̂(r_row)·x̂(r_col)` — so the gradient is
checked by ONE multiplication of TWO single-variable openings, with **no sum over
an inner index and therefore no sumcheck round at all.** A wrong gradient survives
with probability at most `(mi + mj)/|F|`, i.e. `2·log₂ n/|F|`, which is `24/2^31`
at `n = 4096` over BabyBear.

That is strictly better than the matmul boundary, which needs a sumcheck over the
contracted index `k`. The rank-1 case needs none — that asymmetry is the whole
point, and it is now a theorem rather than an observation.

---

## 1. WHAT LANDED IN LEAN

`Selvage/Rank1GradientCheck.lean`, ~500 lines, no `sorry`, every headline
axiom-pinned (`#guard_msgs … #print axioms`, all
`[propext, Classical.choice, Quot.sound]`), wired into `Selvage.lean`.

### The factorization, and why it was cheap

`mle_outerTable : mle (outerTable d x) r = mle d (rowHalf r) * mle x (colHalf r)`
over any `CommRing` — no field, no finiteness, no randomness. The proof is two
mathlib facts and nothing else: reindex the `mi+mj`-bit hypercube along
`Fin.appendEquiv`, split the chi product with `Fin.prod_univ_add`, and the double
sum separates by `Finset.sum_mul_sum`. **The entire cost argument for verifiable
backprop of a linear layer rests on this one identity.**

### The check and its bound

```
Rank1Accepts G δ x r  :=  mle G r = mle δ (rowHalf r) * mle x (colHalf r)

rank1_complete : ∀ r, Rank1Accepts (outerTable δ x) δ x r
rank1_sound    : G ≠ outerTable δ x →
                   uniformProb (Fin (mi+mj) → F) (Rank1Accepts G δ x)
                     ≤ (mi + mj)/|F|
```

The soundness proof is **the defect argument**: `rank1_iff_defect_zero` shows the
check is exactly the vanishing of `G − δ⊗x` at `r`, and the landed
`mle_zero_uniform_bound` (the degree-3 rung's multivariate Schwartz–Zippel) prices
that at `m/|F|`. **No new probability toolkit appears** — the row/column split is
a fact about the CHECK, not about the measure, which is why "the bound should fall
out of the existing lemma" was correct.

### Three things that came free and are worth more than the headline

* **`rank1_refuses_other_outer_products`** — the sharp corollary. `rank1_sound`
  has no rank hypothesis on `G`, so it already covers `G = δ'⊗x'`: any OTHER
  rank-1 matrix is refused at the same bound. A check meaning "the claim is rank
  1" would accept every one of them; this one accepts exactly `δ⊗x`.
* **`rankK_sound`** — the BATCH shape, `∇W = Σ_k δ_k·x_kᵀ` at rank ≤ K. The check
  becomes `Σ_k δ̂_k(r_row)·x̂_k(r_col)`: `K` multiplications the verifier does
  itself, **and the soundness bound does not grow with `K`** (no round is added).
* **`sgd_step_sound`** — the second piece the brief asked for, and it fell out in
  five lines. `W' = W − η·∇W` is linear, so
  `mle_sgdStep : Ŵ'(r) = Ŵ(r) − η·δ̂(r_row)·x̂(r_col)`. **The whole SGD step for a
  linear layer is certified by three openings at one common point and zero
  rounds**, and the gradient is never committed or materialized at all. A wrong
  gradient, a wrong learning rate, and a tampered weight are all the same defect
  and all caught by the same bound.

### Scope AS THEOREMS

* `outerTable_rescale` — the check pins the MATRIX, not the pair: `(c·δ, c⁻¹·x)`
  is the same gradient and is accepted identically. That is the correct
  equivalence class (`∇W` *is* the matrix), but it must be said out loud.
* `rank1_blind_to_the_error` — for ANY `δ'`, the claim built from `δ'` is accepted
  at every challenge. Whether `δ` is the correct backpropagated error is a
  SEPARATE obligation.

⚑ One scope item was deliberately NOT made a theorem. "The check never reads the
forward pass" would be `Iff.rfl` — a vacuous statement of exactly the class this
project keeps finding, and a reader seeing it in the theorem list would credit the
file with a check it does not perform. It is stated as prose in the module
docstring and here, where it belongs.

---

## 2. TEETH — and the one that matters

Over F₅ at a 2×2 layer (`δ = (1,2)`, `x = (3,4)`, `∇W = δ⊗x = [3,1,4,3]`
LSB-first). All by `decide`, so they are kernel-checked over the whole 25-point
challenge space, not sampled.

| tooth | what it excludes |
|---|---|
| `rank1_complete_fires` | completeness at ALL 25 challenges, computed |
| `rank1_refuses_a_wrong_gradient` | a one-entry lie is refused at `(2,3)` |
| `rank1_wrong_accept_witness` | ⚠ the false-accept event is NONEMPTY — the bound constrains a real event |
| `rank1_wrong_accept_count = 9` | **9 of 25 against the theorem's 10/25 — the bound is nearly ATTAINED, not loose slack** |
| ⚑ `rank1_refuses_another_rank_one` | **a genuinely different rank-1 matrix `δ'⊗x` is REFUSED** |
| `rank1_other_accept_witness` | its false-accept event is nonempty too (9/25 again) |
| `rank1_refuses_the_transpose` | `x⊗δ` is refused — an index-order bug |
| `sgd_step_refuses_wrong_eta` | the learning rate is bound, not just the gradient |
| `sgd_step_refuses_tampered_weights` | 0 of 25 accept a shifted `W'` |

**The brief's sharper question — "does the check accept an arbitrary rank-1
matrix?" — is answered NO twice**: generally by `rank1_refuses_other_outer_products`
(no rank hypothesis in `rank1_sound`, so every `δ'⊗x' ≠ δ⊗x` is priced at the same
bound) and concretely by the F₅ tooth. That was the vacuity to fear here and it is
excluded by theorem, not by testing.

⚑ **The counting teeth cannot see a transposed row/column convention** — the wrong
gradient's accepting set `{r₀r₁ = 0}` is symmetric, so both counts stay 9 under a
swap. The rank-1 lie's accepting set is `{r₀ = 0} ∪ {r₁ = 2}`, which is NOT, so
the pair *accept at `(1,2)` / refuse at `(2,1)`* is the actual index-order
detector: `rank1_other_refused_at_the_swapped_point` in Lean and the same pair in
`prover/tests/rank1_gradient.rs`. Found by asking what a symmetric bug would
survive, not by it failing.

**Falsifier check on the counts.** A `decide` that "passes" proves nothing if the
statement is not what you think. Mutating `= 9` to `= 8` in a scratch copy fails
with `Tactic 'decide' proved that the proposition … is false` — the teeth are
live, not decorative.

---

## 3. WHAT LANDED IN RUST

`prover/src/rank1.rs` (+11 unit tests), `prover/tests/rank1_gradient.rs` (6
conformance tests against the Lean F₅ numerals), `prover/src/bin/rank1_gradient_bench.rs`.

* `mle_eval_folded` — `O(2^m)` MLE evaluation by table folding, **pinned to the
  crate's literal chi-basis `mle_eval` at every dimension up to 10**, so the fast
  path accelerates the Lean-mirroring path rather than replacing it (the same
  discipline the degree-3 rung used for `fold_table`).
* `outer_table` / `outer_sum_table` / `sgd_step_table` — the tables, LSB-first with
  the ROW index in the LOW bits, matching Lean's `rowHalf = coords 0…mi−1`.
* `rank1_accepts` / `rank_k_accepts` / `sgd_step_accepts` — the verifier's whole
  arithmetic.
* `zerocheck_tables` — the SAME claim as a circuit, in the landed degree-3 engine's
  five-table shape `Ê·(Â·B̂ + Ĉ·D̂)` at `A = δ` broadcast over rows, `B = x`
  broadcast over columns, `C = G`, `D = −1`. The baseline is the repo's own engine,
  not an invented gate count, and
  `the_zerocheck_baseline_states_the_same_thing` checks the claim is `0` exactly
  when the gradient is right — **so the two sides state the same thing before
  either is timed.**

---

## 4. THE MEASUREMENT, at 4096 × 4096

`cargo run --release --bin rank1_gradient_bench`. `mi = mj = 12`, `m = 24`,
16 777 216 gradient entries, BabyBear.

### DERIVED (what the code decides — stable)

| path | modular ops |
|---|---|
| rank-1 check, prover | 2 × `mle_eval_folded` on 2^12 ⇒ ≈ **2.5 × 10⁴** |
| circuit, prover | `claim` 5·2^24 + rounds Σ_r 40·2^{24−r} + folds 7.5·2^25 ⇒ ≈ **1.7 × 10⁹** |
| **ratio** | **≈ 7 × 10⁴** |

The asymptotics are the honest statement: **`O(2^{m/2})` against `O(2^m)`**, so the
advantage grows with the layer — `4096×` in touched elements at `n = 4096`, and
the constant factor (five tables, four nodes, 24 rounds) puts the operation-count
ratio an order above that.

Verifier: **one multiplication** against 24 rounds of 4-node Lagrange
interpolation, each with a Fermat inversion — ≈ 2.4 × 10³ ops. Proof: **3
openings** against 96 round felts + 5 openings.

### MEASURED (three runs, and why they are only an order of magnitude)

⚠ **The box was at load average 59 with 39 users** — this laptop was shared with
concurrent lanes throughout. Wall-clocks here confirm the order of magnitude and
nothing finer; the derived counts above are what should be quoted.

| quantity | run 1 | run 2 | run 3 |
|---|---|---|---|
| circuit prover, m = 24 (measured, not extrapolated) | 8.92 s | 16.42 s | 25.10 s |
| rank-1 check prover | 157 µs | 2.10 ms | 757 µs |
| ratio | 5.7 × 10⁴ | 7.8 × 10³ | 3.3 × 10⁴ |
| materialize `∇W` (2^24) | 44 ms | — | — |
| evaluate `Ĝ(r)` over 2^24 | 543 ms | — | — |
| peak RSS (circuit path) | 2.57 GB | | |

The scaling column is the reliable part: prove/entry is flat at ~300 ns for
m = 16…20 and rises to ~530 ns at m = 24 (allocation and memory bandwidth on
670 MB of tables), i.e. the baseline is linear in `2^m` as expected, with a
memory-pressure knee.

### ⚠ WHAT THE CHECK DOES NOT REMOVE — and this dominates

The step still **commits the updated weights**: 2^24 felts per step. Measured hash
proxy (cshake256 over the LE felts; the deployed PCS is a Merkle tree over
Poseidon2, priced in `phase-profile.md`): **263 ms for `W'` against 116 µs for `δ`
and `x`.**

So the honest per-step accounting after this piece lands is:

```
  gradient PROOF     8.9–25 s   →  0.16–2 ms      (this work)
  weight COMMITMENT  ~0.26 s    →  ~0.26 s        (unchanged)
```

**The rank-1 check removes the `n²` proof; it does not remove the `n²`
commitment.** That is exactly the DARK-TRAINING §3 argument for low-rank updates —
commit `A` and `B`, not `W'` — and this measurement is evidence FOR it: once the
gradient proof is 10⁴× cheaper, the commitment is the whole step.

⚑ **This is also where the brief's carried correction lands.** "The win scales
with batch, not parameter count" was said of the optimizer-linearity result, and
it holds here in the following precise sense: the check's own cost is `2n` per
sample (`2nB` at batch `B`) while the per-step commitment is `n²` regardless of
`B`, so the amortized cost per sample falls with the batch and NOT with anything
this check does. The gradient-proof win, by contrast, IS in parameter count
(`O(n)` against `O(n²)`) — the two statements are about different terms and must
not be merged.

---

## 5. WHAT THIS DOES NOT COVER — precisely

1. **`δ` is not verified to be the correct backpropagated error.** The check is
   entirely relative to the committed `δ` and `x` (`rank1_blind_to_the_error`, a
   theorem). The chain — `δ_layer = (W_{layer+1}ᵀ δ_{layer+1}) ⊙ σ'(z)` — is the
   NEXT piece, and it is a matmul plus a Hadamard product, so it needs a real
   sumcheck (over the contracted index) and the nonlinearity's derivative table.
2. **The nonlinearity's derivative is not touched.** DARK-TRAINING §1's claim that
   `σ'` is virtualizable off the forward table is untouched by this work and
   remains unbuilt.
3. **Only a LINEAR layer.** No bias, no convolution (a conv gradient is a
   correlation, not an outer product — whether it factors similarly is open and
   unexamined), no attention, no normalization.
4. **The individual factors are not pinned, only their product**
   (`outerTable_rescale`). Correct for `∇W`, and worth knowing if anything
   downstream wants `δ` itself.
5. **Nothing about the data.** In-distribution, in-corpus, unpoisoned — none of
   these are proof-system properties of this check. `‖∇‖ ≤ B` (DARK-TRAINING §5)
   is a separate range argument on top.
6. **The openings are assumed.** Both the check and the baseline take `Ĝ(r)`,
   `δ̂(r_row)`, `x̂(r_col)` from a PCS; the commitment scheme's cost and binding are
   out of scope on both sides, and `Selvage/Commitment.lean`'s `OpeningScheme` is
   still POSITIONAL — the wrong shape for a multilinear claim, a standing campaign
   (`gkr-substrate-findings.md`).
7. **The Rust is UNVERIFIED COMPUTE** bound by vectors. Not refinement, not
   translation validation.
8. **Exactness is assumed.** Real gradients are bf16/fp32; the field encoding's
   exactness argument is built for inference, and whether it survives a million
   accumulating steps is DARK-TRAINING §7's open item, untouched here.

---

## 6. BUILD EVIDENCE

Exit codes captured directly, never through a pipe.

| gate | result |
|---|---|
| `lake env lean Selvage/Rank1GradientCheck.lean` | **exit 0**, no output |
| `lake build Selvage` | **2460 jobs, exit 0** |
| falsifier: `= 9` mutated to `= 8` | **exit 1** — `decide` proves it false |
| `cargo test` (whole crate) | **exit 0** — 54 lib tests (43 + 11 new) + 6 new conformance + all suites |
| `scripts/check-import-boundary.sh` | **exit 0** |
| `scripts/check-proof-hygiene.sh` | **exit 0** |
| `grep sorry` on the new Lean | none |

---

## 7. THE ESTIMATE, MEASURED

The brief predicted the bound "should fall out of the existing lemma". It did:
`rank1_sound` is four lines given `mle_zero_uniform_bound`, and the only real work
was the factorization `mle_outerTable` (~20 lines, two mathlib lemmas). The Lean
file elaborates in **~10 s**; the whole lane was one build cycle for the
factorization (a rewrite-order bug: `chiEval_split` must fire BEFORE
`rowHalf_append`, or it re-introduces the terms the latter just eliminated), one
for `omit [Fintype F] in` placement (it goes BEFORE the docstring, not between
docstring and theorem), and one for the bench.

⚑ The reason it was this cheap is worth recording, and it is the same reason as
the degree-3 rung: **the hard object already existed.** `mle_zero_uniform_bound`
was built last week for the zerocheck and is exactly what a two-variable
Schwartz–Zippel argument needs — the "two-variable" part turned out to be zero
extra work, because splitting `r` into halves is a statement about the check and
the probability lemma never sees it.
