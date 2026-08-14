# The contraction sumcheck — build log

Lane: LEAN + RUST BUILD, 2026-08-13/14. Target: the piece the zkML pillar was blocked
on — matmul as a **vector relation** rather than 318 040 gates. Repo: `~/dev/minidregg`
(NOT breadstuffs). `[measured]` = a command ran; `[read]` = read at source.

**Substrate, said out loud: the constraint semantics is Lean-authored.** The claim, the
honest prover, the round engine, the error bound and the composition are theorems in
`Theory/` and `Assurance/`. The Rust is the prover and the harness, bound by a conformance
vector; it authors no relation.

Landed: `8989d3c` (Lean) and `83c2e14` (Rust + vector) in `~/dev/minidregg`.

---

## 0. What the brief got right, and the one thing it got wrong

`[read]` the brief's obstacle — *"`AirSumcheckQuadratic`'s face is Hadamard-shaped
(`Â·B̂ − Ĉ` pointwise), NOT a contraction, so this is an adaptation"* — is **correct about
the shape and wrong about the consequence**. The adaptation is not to the *engine*; it is
to *which instance of the engine you take*, and the answer turns out to be a **smaller**
instance than the memo assumed, not a larger one.

The degree-3 rung landed `cubicForm_matmul : eq(z,x)·(Â·B̂ − Ĉ)`. That name was wrong.
`Â·B̂` is a **pointwise** product of two tables on one cube; a matmul contracts an inner
index appearing in neither output coordinate. It is now `cubicForm_hadamard`, and the
correction is a theorem, not a rename with an opinion attached:

```lean
theorem matmul_is_not_hadamard :
    ∃ A B, matmulTable A B ≠ fun a b => A a b * B a b     -- decided over F₇
```

The renamed theorem is still a real consumer — the elementwise-product gate's zerocheck.
**Breaking change**: any reference to `Assurance.cubicForm_matmul` must be re-spelled;
nothing outside `AirSumcheckCubic.lean` and two Rust comments did.

---

## 1. The blocker: `foldl → Finset.sum`, and which property is load-bearing

`Theory/ZkmlMatmulSum.lean`. `TOp.denote` gives matmul an **ordered** left fold over
`List.finRange k`; every sumcheck statement is over `Finset.sum`. The bridge is built in
**two named steps** so the place the ordered semantics is discarded is a line you can point
at:

| step | lemma | hypothesis | discards |
|---|---|---|---|
| 1 | `foldl_add_eq_listSum` | `AddMonoid` — associativity + unit | the bracketing |
| 2 | `listSum_finRange_eq_sum` | `AddCommMonoid` — commutativity | the order of the index set |
| ⇒ | `foldl_finRange_eq_sum` → `denote_matmul_sum` → `run_matmul_sum` | | |

⚑ **The load-bearing property is ASSOCIATIVITY, not commutativity.** The brief (and the
build log's §4.3) named commutativity; IEEE-754 addition *is* commutative and is *not*
associative, so step 1 is the one a float-shaped reading breaks. Step 2 has no
counterexample at all — `Finset.sum` over `Fin k` cannot be **written** without
commutativity, so its refutation is a type error rather than a number.

The hypothesis is exercised, on the real denotation: `SatExample` gives a scalar reading
whose `add` saturates at 10 (the shape of every finite accumulator at its range limit), and

```
run satOps satTrace satEnv (0,0,⋆)  =  5        -- the trace's own denotation
∑ p : Fin 3, a 0 p * b p 0          =  9        -- its Finset.sum
```

`sat_bridge_fails` is that disagreement, kernel-decided; `sat_order_matters` shows the
reversed contraction order gives a third answer. So `run_matmul_sum` is **refutable** and
`IsRingReading` is not decoration.

`[measured]` `RingExample.mmTrace_contracts` instantiates the bridge on the landed
2×3·3×2 witness at every `(i,j)` — one theorem application, no per-entry computation.

---

## 2. Padding: matmul needs **no** `Theory/` change — a correction to §4.5

The build log named power-of-two padding as *"the single most concrete new requirement, and
it is a `Theory/` change — the only one matmul needs"*, with a fork: a `pad` **op** with its
own denotation, or MLE machinery over non-dyadic domains.

**Neither.** Zero-padding a contraction is a fact about *tables*, not about *programs*:

```lean
theorem padded_contraction  : contract (padRight A) (padDown B) i j = contract A B i j
theorem padded_matmul_table : contract (padDown A) (padRight B)
                                = padRight (padDown (contract A B))
```

so the padded output table **is** the zero-padding of the true one (the extra rows and
columns are zeros, not garbage the verifier must separately constrain). No constructor
enters `TOp`; `TOp.outTy`, `TOp.denote`, `TOp.arithmetic`, `TOp.macs`, `denote_op_rel` and
`ringHom_denote_op` — every place the thirteen constructors are enumerated — are untouched,
and no existing theorem changes shape. MNIST's dyadic arithmetic is recorded
(`784 + 240 = 2^10`, `100 + 28 = 2^7`, `10 + 6 = 2^4`).

The pad becomes a **commitment-layer** obligation: the committed table must really be zero
outside the true extent. Named `[MATMUL-pad]`.

---

## 3. The contraction face

`Assurance/ZkmlMatmulSumcheck.lean`. Thaler's shape: bind the **outer** indices to random
field points first, sumcheck the **inner** index only.

```lean
def mle₂ f x y = ∑ a, ∑ b, f a b * chiEval a x * chiEval b y
theorem mle₂_row : mle₂ f x y = mle (rowPartial f x) y      -- and mle₂_col
theorem mle₂_contraction :
    mle₂ (matmulTable A B) x y = ∑ p, rowPartial A x p * colPartial B y p
```

Three things worth stating because the prose plan had them wrong:

* **The block MLE is not a new object.** `mle₂_row`/`mle₂_col` prove it IS a composition of
  the landed one-block `mle`, so multilinearity, Schwartz–Zippel and the sumcheck realizer
  all apply with no new proof. (This also avoided flattening into `Fin (μ+κ) → Bool` and
  fighting `Fin.append`, which was the expensive-looking route.)
* **`mle₂_contraction` is an identity at EVERY `(x,y)`**, not just on the cube — no
  probability, no appeal to multilinear uniqueness, just a triple sum reordered.
* **There is no `eq` factor.** The head of the `cubicForm` instance is the constant `1`
  (`cubicForm_contraction`, `E ≡ 1, C ≡ 0, D ≡ 1`), because nothing is left to zero-test
  once the outer indices are bound. The `eq`-headed instance is the *zerocheck* face — a
  different protocol.

So the degree-3 rung serves matmul as **one engine**, and it is **not tight**: the summand
is degree 2. That is stated as a fact about emitted numbers rather than as prose —
`matmulRounds_are_not_cubic` (third finite difference **zero** in every round) paired with
`matmulRounds_are_quadratic` (second difference nonzero), so the message's degree is pinned
from both sides and an affine reader still fails the vector.

### The error has two terms and they are not the same term

```lean
theorem matmul_sumcheck_soundness (hC : C ≠ matmulTable A B) … :
    uniformProb _ (MatmulAccepts A B C prover)
      ≤ ((μ:ℝ) + ν)/|F|  +  (κ:ℝ) * (3/|F|)
```

The second term is the sumcheck. The **first** is a two-block multilinear Schwartz–Zippel
event (`mle₂_zero_uniform_bound`, composed from `Selvage/MultilinearZeroTest.lean`'s
one-block bound over the two blocks — no new probability toolkit) and it exists *because*
the verifier tests the claimed output table at **one** random point. A writeup quoting only
`κ·3/|F|` would be quoting the flattering half of a pair.

Teeth over F₇ against the three ways this could be vacuous: the identity fires **off** the
cube (both sides 5 at `x=3, y=5`); a forged output table is separated at `x=0` but
**survives at `x=1`** — so the `(μ+ν)/|F|` bound constrains a **nonempty** event, exhibited
rather than argued, and a verifier drawing that point proves a TRUE claim about a FALSE
table.

---

## 4. Rust: the driver, the vector, and the measurement

`prover/src/sumcheck.rs` gains `MatmulClaim` / `output` / `row_partial` / `col_partial` /
`tables` / `mle2_eval` / `prove_matmul` / `verify_matmul`. The verifier **recomputes** its
target from the claimed output table with `mle2_eval` and refuses a proof whose claim does
not match, before examining a round; the terminal check combines five openings of which
three are constants it supplies itself.

`Assurance/ZkmlMatmulConformance.lean` writes `prover/testdata/zkml_matmul_conformance.json`
at a fixed 2×4·4×2 BabyBear instance, every value kernel-decided as a named theorem, and
`prover/tests/zkml_matmul_conformance.rs` reproduces all of it (8 tests).

### `[measured]` release build, `[2,1024]·[1024,128]` — MNIST layer 1, padded

| | |
|---|---|
| output (`m·k·n`, owed anyway) | **6.4 ms** |
| bind the outer indices | **9.6 ms** |
| the sumcheck rounds | **0.5 ms** |
| verify | **0.27 ms** |
| transcript | **51 field elements = 408 bytes** + 2 unpriced openings |
| AIR route | **314 000 gates** unpadded / 524 800 padded, ≈**27 MB** of descriptor |

Two findings the split decides, neither obvious before measuring:

1. **The sumcheck is 5% of the prover.** 95% is binding the outer indices — and that step
   is naive here (`chi_eval` recomputed per entry, costing a factor of ν that successive
   folding removes). **The lever for a faster matmul argument is the partial evaluation,
   not the rounds.** Measured by splitting the timer, not inferred.
2. **408 bytes against 27 MB is a real ratio for the RELATION and a misleading one for a
   SYSTEM.** It omits the two multilinear openings entirely.

---

## 5. Honest ledger

* **No inference is proved.** One matmul relation is; MNIST is 26 ops and a sigmoid whose
  `pow`/`div` are still the whole gadget bill.
* **`[MATMUL-pcs]`** — the two openings. While this lane ran, a concurrent lane
  (`0c17553`, `Selvage/MultilinearCommitment.lean`) gave them the correct hash-based shape
  (`MleEvalClaim = (root, point, value)` with `value_unique`) over the existing positional
  `OpeningScheme` and updated this file's residual paragraph directly. The remaining gap it
  names is the braided BaseFold `Reduction`/`RbrKnowledgeSoundness` instance and its BCS
  query realization. In *this* lane's Rust the openings are still handed in by a closure.
* **`[MATMUL-fs]`** — `(x,y)` and the round challenges are drawn uniformly; Fiat–Shamir is
  `[PROVER-fs]`, open.
* **`[MATMUL-pad]`** — proved as a table fact; that the *committed* table is zero outside
  the true extent is unchecked.
* **The ε propagates.** `eltAddSystem_denotes` is an unconditional iff; this is not. A
  design mixing the two rungs must add an ε that only this one has.
* **The Rust is unverified compute bound by vectors.** Not refinement, not TV.
* This note was written at the end of the lane, not incrementally.

## 6. Build evidence

```
lake build Theory Assurance            → 8831 jobs, exit 0   (Lean half)
lake build Assurance                   → 8818 jobs, exit 0   (after the vector)
scripts/check-import-boundary.sh       → OK: Theory, OK: Selvage
scripts/check-proof-hygiene.sh         → PASS (434 tracked Lean files)
cargo test (working tree)              → 60 lib + every integration suite green
cargo test from a DETACHED git archive HEAD extraction → same, green
git diff HEAD on every path I touched  → empty
#print axioms guarded on every headline theorem; no sorry, no native_decide
```

⚠ Same honest limit the degree-3 lane recorded: the **Rust** was verified from a truly
detached extraction; the **Lean** was not (a detached Lean build needs a cold `.lake`).
What was checked instead is that `git diff HEAD` is empty for every Lean path, so the green
build ran on byte-identical content.

## 7. An elaboration finding worth keeping

Three proofs **diverged** — `isDefEq`/`whnf` timeouts that survived a 6× heartbeat budget —
purely from non-first-order unification, and the fix was structural, not a bigger budget:

* a helper stated as `uniformProb (A × B) (fun w => p w.1)` makes `?p w.1 =?= …` a
  non-Miller pattern. Take the event as an explicit `q` with a pointwise `Iff`, and make
  `p` **explicit** so nothing is a metavariable when the `Iff.rfl` is checked.
* after `uniformProb_prod_le`, the fibre goal is a **beta-redex applied to a pair**; a
  `show` that beta-reduces it before any `le_trans` is the difference between 12 seconds
  and never finishing.
* `le_trans (uniformProb_mono fun _ h => h.2) …` leaves both predicates as metavariables:
  name them with `(p := …) (q := …)`.

The file went from >6× budget to **12 s** on these three changes alone.
