# The partial sumcheck — the composition operator the bag lacked

*Lean build lane, 2026-08-16. Target tree: `~/dev/minidregg`, committed at
`37c6b33` (shared tree; other lanes live in it). Brief: build
`scChain_*Honest_partial` at `k ≤ m` and wire one consumer across a module
boundary.*

**Outcome: landed at all three degrees, with the consumer, and the consumer
turned `RingSwitchSecure` from a named obligation into a theorem.** The cost
the inventory left unpriced came in low — the whole thing is a case split, not
an induction — and the one real fight was a unification cliff in the
probability plumbing, not the mathematics.

---

## 0. The two prior claims, re-verified AT THE BINDERS

The brief said to read the binders, not the prose, because a prior lane found
three cases of work priced as open that was already done. Both claims hold.

### Claim 1 — `roundSum` already sums over `SuffixCube`. **TRUE.**

`Selvage/MultilinearExtension.lean:337`, verbatim:

```lean
def roundSum (g : (Fin m → F) → F) (r : Fin m → F) (i : Fin m) (t : F) : F :=
  ∑ b : SuffixCube m (i.val + 1),
    g (glue (Function.update r i t) (i.val + 1) b)
```

The partially folded object is the primitive. `SuffixCube m k` and `glue` are
`{m k}`-generic over `[CommRing F]`; `suffixSplit` peels one coordinate; and
`roundSum_fold`, `roundSum_zero`, `roundSum_succ`, `roundSum_last` are all
already stated at an arbitrary level. Nothing about the full-arity run is baked
into the cube machinery.

### Claim 2 — `AcceptsFalse`'s terminal names no cube, so `sumcheck_soundness` IS partial-sumcheck soundness. **TRUE.**

`Selvage/Sumcheck.lean:227`, verbatim:

```lean
def AcceptsFalse {v : ℕ} (prover honest : ℕ → Polynomial F) (H S : F)
    (r : Fin v → F) : Prop :=
  (∀ i, i < v → (prover i).eval 0 + (prover i).eval 1 = scChain H prover (chalOf r) i)
    ∧ scChain H prover (chalOf r) v = scChain S honest (chalOf r) v
    ∧ H ≠ S
```

The terminal clause compares the two CHAINS at round `v`. No cube, no arity, no
oracle evaluation. `sumcheck_soundness {v d}` (`Sumcheck.lean:243`) and
`adaptive_sumcheck_soundness {v d}` (`SumcheckReduction.lean:296`) are both
generic in `v`, and their `hHonest` hypothesis is `∀ r : Fin v → F, ∀ i, i < v →
…`. So a `k`-round run is priced at `k·d/|F|` by the theorems that already
exist. **The soundness half was landed and nobody noticed.**

⚑ **But there is a wrinkle the inventory did not state, and it is what makes the
missing half load-bearing rather than cosmetic.** `AcceptsFalse` at `v := k`
contains `scChain S honest (chalOf r) k` — and until this lane, *nothing in the
tree said what that quantity IS for `k < m`.* The `k`-round bound was a bound on
an event whose terminal comparison had no name. That is why the realizer half is
not a convenience.

---

## 1. What landed

### 1.1 The residual claim — `Selvage/MultilinearExtension.lean`

```lean
def residualSum (g : (Fin m → F) → F) (r : Fin m → F) (k : ℕ) : F :=
  ∑ b : SuffixCube m k, g (glue r k b)
```

with

| lemma | says |
|---|---|
| `residualSum_zero` | level 0 is the opening hypercube total |
| `residualSum_full` | level `m` is the point `g r` — the final oracle evaluation |
| `residualSum_eq_roundSum_bool` | the verifier's round-`k` check target IS the level-`k` residual (`roundSum_fold`, renamed) |
| `residualSum_step` | folding round `k` at `r_k` gives level `k+1` |

Naming it is most of the work: it turns an intermediate into a **claim of the
same shape as the one the run opened on**, which is precisely what "hand the
rest to another reduction" requires.

### 1.2 The partial terminals, at all three degrees

```lean
theorem scChain_mleHonest_partial (f) (χ : ℕ → F) {k} (hk : k ≤ m) :
    scChain (∑ b, f b) (mleHonest f χ) χ k
      = residualSum (mle f) (fun j : Fin m => χ j.val) k
```

and `scChain_quadHonest_partial` (`Selvage/QuadraticSumcheck.lean`),
`scChain_cubicHonest_partial` (`Assurance/AirSumcheckCubic.lean`).

Two design points, both forced:

* **Stated over a raw challenge STREAM `χ : ℕ → F`, not a `Fin m` tuple.** A run
  that stops at `k < m` draws `r : Fin k → F`, and its `chalOf r` is *not* the
  restriction of any `Fin m`-tuple — it is `r` padded with zeros. `chalOf_restrict`
  is unavailable, so every honest-side lemma a `k`-round run consumes has to be
  stream-form. Added: `mleHonest_boolean_sum_stream`,
  `quadHonest_boolean_sum_stream`, `cubicHonest_boolean_sum_stream`; the existing
  `chalOf` forms are now one-line corollaries.
* **Case split, not induction.** `scChain` is memoryless (`scChain … (i+1) =
  (poly i).eval (chal i)`), so the whole proof is `cases k` + one
  `residualSum_step`. This is why the unpriced cost came in low.

### 1.3 It REFINES, it does not fork

`scChain_mleHonest_final`, `scChain_quadHonest_final` and
`scChain_cubicHonest_final` are now **corollaries at `k = m`** via
`residualSum_full`. Three duplicated case-split proofs were deleted, and with
them the `m = 0` special cases the quadratic and cubic finals each carried
(a five-line `Fin 0` argument, twice). One proof, not two — the anti-fork move
the inventory's §6.2 asked for, done by *removing* code rather than adding a
layer.

---

## 2. The consumer, across a module boundary

`Selvage/RingSwitching.lean` (new `import Selvage.QuadraticSumcheck`).

Theorem 3.5 of Diamond–Posen 2024/504 was carried here as
`def RingSwitchSecure : Prop`, with a docblock naming two gaps. **Both are now
theorems.**

### 2.1 The assembly — and a stale docblock

The docblock said discharging the assembly "needs the product-uniform
marginalization and a union bound, **neither of which exists here**."

Both exist, in `Selvage/Depth.lean`: `uniformProb_prod_le` and
`uniformProb_or_le`, alongside `uniformProb_mono` and `uniformProb_equiv`.
`ringSwitchSecure_holds : RingSwitchSecure L` is four lines against them.

⚑ **This is the same failure the brief was written to guard against, one layer
down.** The inventory found the *soundness* half priced as open because someone
read prose instead of binders; the same file's own docblock priced the
*assembly* as open because someone read a note instead of `Depth.lean`. The
docblock was stale, not the mathematics. It is now corrected at source.

### 2.2 The `2·ℓ′/|L|` leg, SUPPLIED

```lean
theorem ringSwitch_transfer_bound {l k : ℕ} (hk : k ≤ l)
    (Arow t' : (Fin l → Bool) → L) (H : L)
    {prover : (ℕ → L) → ℕ → Polynomial L}
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ χ i, i < k → (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin k → L)
      (AdaptiveAcceptsFalse prover (quadHonest Arow t' 0) H
        (∑ b, (Arow b * t' b - (0 : (Fin l → Bool) → L) b)))
      ≤ (2 * k : ℝ) / Fintype.card L
```

The honest side is **built, not hypothesized**: `quadHonest Arow t' 0` is
`Selvage/QuadraticSumcheck.lean`'s degree-2 realizer, and the paper's summand
`h = A · t′` is `prodDiff` with the subtracted table zero. Only adversary-side
hypotheses remain, as they must.

### 2.3 Why the partial terminal is load-bearing here and not decoration

```lean
theorem ringSwitch_transfer_accepts_iff {l k} (hk : k ≤ l) … :
    AdaptiveAcceptsFalse prover (quadHonest Arow t' 0) H S r
      ↔ ((∀ i, i < k → …round check…)
          ∧ scChain H (prover (chalOf r)) (chalOf r) k
              = residualSum (prodDiff Arow t' 0) (fun j : Fin l => chalOf r j.val) k
          ∧ H ≠ S)
```

At `k < ℓ′` the acceptance predicate's terminal clause is
`scChain S (quadHonest …) … k`. `scChain_quadHonest_partial` is the **only**
thing that says what that is. Without it `ringSwitch_transfer_bound` at `k < ℓ′`
would be a bound on an unnameable event — true, useless, and exactly the kind of
island the brief warned about. With it, the stopped transfer hands over a
well-formed sum-claim over the unvisited suffix cube.

`ringSwitch_joint_bound` composes: `(2k + κ)/|L|` over the joint randomness
`L^κ × L^k`, with both legs supplied and nothing about the sumcheck assumed.
`ringSwitch_transfer_terminal` closes the loop at `k = ℓ′`: the residual there
IS the factored `Â(r′)·t̂′(r′)`.

---

## 3. Teeth

Over `F₅`, the AND gate, `m = 2` (`MLEExample`):

| tooth | what it refutes |
|---|---|
| `residualSum_and_one_ne_full` | the `k=1` residual is `2`, the `k=2` value is `1` — the partial theorem is **not** the final one in disguise |
| `scChain_mleHonest_partial_fires` | the chain after ONE round holds `2`, computed |
| `partial_terminal_agrees_but_check_bites` | ⚑ a prover whose **terminal matches the honest level-1 residual exactly**, on a false total `H = 3`, is still REFUSED — round 0's boolean check `2 + 2 = 4 ≠ 3` fires |

The third is the one that matters. **A partial sumcheck must not become a
partial verifier**, and this is the statement that it did not: stopping the
chain removes no check from the wire. The same point is carried at the consumer
by `ringSwitch_transfer_accepts_iff`, whose first clause is still `∀ i, i < k`.

And `k = m` coincidence is not a tooth here but a *derivation*: the three
`_final` theorems are literally proved from the partial ones (§1.3).

---

## 4. Measured hazards

⚑ **`uniformProb` marginalization written as `fun c => ?p c.1` is not a Miller
pattern, and it costs a heartbeat TIMEOUT, not a slowdown.** First attempt:

```lean
private theorem uniformProb_marginal_fst (p : A → Prop) … :
    uniformProb (A × B) (fun c => p c.1) ≤ ε
```

→ `(deterministic) timeout at whnf, maximum number of heartbeats (200000)` at the
call site. The fix is the explicit-`q`-plus-pointwise-`Iff` shape:

```lean
private theorem uniformProb_marginal_fst (q : A × B → Prop) (p : A → Prop)
    (hq : ∀ c, q c ↔ p c.1) … : uniformProb (A × B) q ≤ ε
```

which is **exactly the discipline `Assurance/ZkmlMatmulSumcheck.lean`'s
`uniformProb_fst_le` docstring already records**, and which I re-derived by
timing out rather than by reading it. Worth the line because the failure mode
does not look like a unification problem from the error message.

Smaller ones: `omit … in` goes **before** the doc comment, not between it and
the `theorem` (parse error `unexpected token 'omit'; expected 'lemma'`);
`div_add_div_same` is not in scope in this import set — use `← add_div`.

---

## 5. Residual, named

* **Duplicated helper.** `uniformProb_marginal_fst` (private, `RingSwitching.lean`)
  duplicates `Assurance/ZkmlMatmulSumcheck.lean`'s `uniformProb_fst_le`, because
  `Selvage` may not import `Assurance` (`scripts/check-import-boundary.sh`). The
  right home is `Selvage/Depth.lean`, next to `uniformProb_prod_le`, with the
  Assurance copy DELETED and its three call sites repointed. Not done here: it
  touches `Assurance/SpartanR1CS.lean` and `ZkmlMatmulSumcheck.lean`, which other
  lanes may hold.
* ⚠ **`Selvage.lean:23`'s registry comment is now stale** — it still reads
  "Named residual [RS-thm35] RingSwitchSecure = the assembly … hypotheses shown
  inhabited". `RingSwitchSecure` is a theorem as of `37c6b33`. **I deliberately
  did not edit it**: `Selvage.lean` was dirty with another lane's new
  `import Selvage.AdditiveBasisBinding` line whose module file is still
  untracked, so a `--only Selvage.lean` commit would have swept an import of a
  file not in the commit — a broken tree at HEAD. Whoever lands
  `AdditiveBasisBinding` should fix the `[RS-thm35]` line in the same commit.
* **The tensor-algebra connection (identity 30) is still open**, and it is undone
  work, not a boundary. `ringSwitch_transfer_bound` is generic in the row
  function `Arow`; instantiating it at the paper's `A` — the row/column
  decomposition of `eq~(r″,·) ⊗ eq~(r′,·)` — is the remaining step for a full
  Theorem 3.5. Nothing about the bound changes; the work is exhibiting `A`.
* **No degree-generic realizer still.** This lane added the fourth parallel
  lemma name to each of the three rungs (`*_boolean_sum_stream`,
  `scChain_*Honest_partial`), so the triplication is now ~9 names per degree.
  The inventory's §6.2 trigger — *write the `HonestRound` structure when a fourth
  degree rung is requested, not before* — is unchanged, but the pressure is
  higher. Cheaper first move remains deleting the d=2 stack in favour of
  `cubicForm_subsumes_prodDiff`.

## 6. What this unblocks next (unmeasured — I built the ingredient, not the consumers)

The inventory's five: Ligerito B1 (**its soundness half is `sumcheck_soundness`
at `v := k`, its realizer half is now `scChain_*Honest_partial`**), B2/B3 as
batched/glued variants, the GKR layer hand-off (`scChain_cubicHonest_partial` is
the shape — `cubicForm_fraction_layer` already supplies the round polynomial),
Spartan's phase-1→phase-2 join (currently a hand-written case split in
`spartan_sound`), and BaseFold descend-then-switch. Only the ring-switching one
is wired; the other four are stated as expectations, not measurements.

---

## Verification

* `lake build` (full tree, 8995 jobs): **green**, 2:13 warm.
* `scripts/check-proof-hygiene.sh`: PASS, 474 tracked Lean files, 217 guarded
  axiom footprints.
* `scripts/check-import-boundary.sh`: PASS.
* 11 new `#guard_msgs (whitespace := lax) in #print axioms` pins, all
  `[propext, Classical.choice, Quot.sound]`. Zero `sorry`, zero new `axiom`.
* **Verified at HEAD, not in the working tree**: fresh detached clone at
  `37c6b33` (working tree carries three other lanes' uncommitted files),
  `lake build Selvage.RingSwitching Assurance.AirSumcheckCubic` — **2372 jobs,
  0 errors**. So the commit is self-contained: nothing I landed depends on an
  uncommitted sibling.
* No existing statement changed. Four declarations show as rewritten in the diff
  (`mleHonest_boolean_sum`, `quadHonest_boolean_sum`,
  `cubicHonest_boolean_sum`, `scChain_mleHonest_final`) — their *proofs* became
  one-line corollaries; the signature lines are byte-identical before and after,
  and every downstream consumer builds.
</content>
