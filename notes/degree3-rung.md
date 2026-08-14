# The degree-3 rung — build log

Lane: LEAN + RUST BUILD, 2026-08-13. Target: the rung that unblocks BOTH GKR
fraction trees (`eq·(p_L·q_R + p_R·q_L)`) and zkML matmul (`eq·(Â·B̂ − Ĉ)`).
Repo: `~/dev/minidregg` (NOT breadstuffs — Selvage lives here).

## SPIKE RESULT — GREEN, ~15 min wall, first hour budget intact

`Selvage/EqPolynomial.lean`, elaborates in **17s**, no `sorry`. The spike was
`eqMle` + `eqMle_cubePt` + `eqMle_fold`; it came in at 8 theorems because the
adjacent facts were free once the product shape was in hand.

Only one error on first elaboration (an `if b = b'` vs `if b' = b` argument
order). **The estimate in the design memo is correct: this is a port, not
protocol work.**

What landed in the spike:
- `eqMle z x = ∏ᵢ (zᵢxᵢ + (1−zᵢ)(1−xᵢ))` — both arguments free field vectors.
  The landed `chiEval` pins its first argument to a cube CORNER; GKR and the
  zero-test both need the two-vector form.
- `eqMle_cubePt : eq(z, corner b) = χ_b(z)` — **the new object extends the
  landed one; nothing is duplicated.** This is the load-bearing lemma: it is
  why `eq` can occupy an `mle E` slot in the cubic engine.
- `eqMle_fold : Σ_b eq(z,b)·f(b) = f̂(z)` — **the zerocheck-to-sumcheck
  bridge.** `AirSumcheckQuadratic`'s residual (ii) names exactly this
  identity as missing vocabulary.
- `eqMle_multilinear` — so the landed round-chain skeleton
  (`roundSum_affine/_zero/_succ/_last`) applies verbatim, and multiplying by
  `eq` costs exactly one degree.
- `eqMle_eq_mle : eqMle z = mle (fun b => chiEval b z)` — uniqueness fires.
- Teeth over F₅: `eqMle_offcube` (a genuine extension), the indicator firing
  both ways, the bridge computed against `MLEExample.fAnd`, and
  `eqMle_separates`.

## WHAT LANDED

Four Lean files and one Rust extension; everything below builds green with no
`sorry` and axiom-pinned (`#guard_msgs (whitespace := lax) in #print axioms`).
Full `lake build Selvage Assurance`: **8812 jobs, exit 0.**

### 1. `Selvage/EqPolynomial.lean` (the spike, ~130 lines)
As above. Wired into `Selvage.lean`.

### 2. `Assurance/AirSumcheckCubic.lean` (~460 lines) — THE RUNG
The 2→3 port of the quadratic template, at the shape that covers BOTH targets:

    cubicForm E A B C D (x) = Ê(x)·(Â(x)·B̂(x) + Ĉ(x)·D̂(x))

**Both consumers are named as THEOREMS, not prose** — that was the one place
this could have quietly become a claim rather than a fact:
- `cubicForm_fraction_layer` — `eq(z,x)·(p_L·q_R + p_R·q_L)`, the head being the
  eq table `b ↦ χ_b(z)` whose MLE is `eqMle z` by the spike's `eqMle_eq_mle`.
- `cubicForm_matmul` — `eq·(Â·B̂ − Ĉ)`, i.e. `D ≡ 1` and `C` negated.
- `cubicForm_subsumes_prodDiff` — **the landed degree-2 engine is a SPECIAL CASE,
  not a parallel twin.** Two shapes that agree today are two shapes that will
  disagree later; this makes them one object by theorem.

Engine: `cubicForm_line` → `roundSum_cubicForm` → `cubicRoundPoly_eval` /
`_degree` (d = 3) → the four honest-side hypotheses → `scChain_cubicHonest_final`
(the terminal check FACTORED into five openings the verifier combines itself) →
`cubic_sumcheck_soundness` (`≤ m·3/|F|`, one `simpa`, bound CITED not re-derived)
→ `cubic_retires_constraint` (the mask folds into the HEAD factor).

⚑ **One design choice worth recording: the line restriction is COEFFICIENT form,
not interpolation form.** `k₀ + t·k₁ + t²·k₂ + t³·k₃` needs no division and no
characteristic hypothesis. The `{0,1,2,3}` interpolation the Rust wire uses
requires `p > 3` with `6` invertible — the char-2 binary-tower instantiation
(where `tower256_kernels::fraction_add_layer` already lives) cannot use those
nodes at all. Keeping Lean in coefficient form leaves that fork open instead of
silently closing it.

**Teeth against the vacuity that would survive a build:** a "degree-3 engine"
whose leading coefficient is always zero is a degree-2 engine wearing a cubic
type, and every theorem above would still be true. So `cubic_leading_ne_zero`
exhibits it nonzero on data and `cubic_not_quadratic` computes the third finite
difference. The soundness pipeline fires end to end (`cubic_cheat_caught` ≤ 3/7)
on a **NONEMPTY** accept event — ⚠ the cheat had to be constructed BACKWARDS
from a challenge that accepts it; my first natural choice (constant message, false
total 3) had **no** accepting challenge over F₇, i.e. it would have been a true
bound over an empty event.

### 3. `Selvage/MultilinearZeroTest.lean` (~250 lines) — THE NEW PROOF TERM
`mle_zero_uniform_bound : f ≠ 0 → Pr_{z←F^m}[f̂(z) = 0] ≤ m/|F|`.

Selvage's SZ was univariate everywhere. Induction peels the LSB coordinate via
the LANDED `mle_lsb_recurrence` (`MultiplicativeMleTerminal.lean` — it already
existed, which is why this came in near the low end of the 80–120 line estimate);
the two cases are "half-difference zero ⇒ head irrelevant, IH on the low half"
and "half-difference nonzero ⇒ `uniformProb_or_le` splits into the tail event
(IH) and ONE root in the head per fibre". **No new probability toolkit** —
`uniformProb_equiv`/`_or_le`/`_mono`/`_prod_le`/`_false`/`_mem_finset` all cited.

`eqMle_zero_test` composes it with `eqMle_fold`: **`AirSumcheckQuadratic`'s named
residual (ii) is closed.** The single-shot randomization is now an actual test at
`m/|F|` against the γ round's `(t−1)/|F|`, and `m` is logarithmic in `t`.

Teeth per "prove the floor FALSE": the event is SATISFIABLE (`sz_event_nonempty`),
the bound is TIGHT at m = 1 (exactly 1/5 over F₅), and the hypothesis is
REFUTABLE (`sz_needs_nonzero` — drop `f ≠ 0` and the probability is 1).

### 4. Rust — `prover/src/sumcheck.rs` (+~330 lines) and its tests
- `pow_mod` / `inv_mod` (Fermat) — the engine had only add/sub/mul.
- `eval_lagrange` on nodes `0..=d` with the denominators
  `Dⱼ = (−1)^{d−j}·j!·(d−j)!` precomputed as the constant table
  `LAGRANGE_DENOMS = [[1], [−1,1], [2,−1,2], [−6,2,−2,6]]`.
  ⚑ It returns **`Option`** and the verifier REJECTS on `None`: `p ≤ d` collides
  the nodes and `p ∈ {2,3}` kills a denominator. A refusal that rendered as a
  value would be the "refusal renders as the expected verdict" class.
- `fold_table`, `CubicTables`, `cubic_round_evals`, `cubic_round_sum_literal`,
  `prove_cubic_sumcheck`, `verify_cubic_sumcheck` (fail-closed).
- 29 lib tests + 7 conformance tests, all green.

### 5. `Assurance/AirSumcheckCubicConformance.lean` + `prover/tests/sumcheck_cubic_conformance.rs`
The vector binds the **REAL `cubicForm`**, which is why it lives in `Assurance/`
rather than beside its degree-1 sibling in `Compiler/` (Compiler cannot import
Assurance; a Compiler-side writer could only re-spell the summand — a second
shape). `m = 3`, five distinct LSB-first BabyBear tables, claim + five FACTORED
openings + every round at the FOUR wire nodes, all KERNEL-DECIDED as **named
theorems** (not anonymous `example`s — the degree-1 file's convention, which is
the `#guard`-in-Lean-clothes sin's cousin). The chain identities are the landed
theorems INSTANTIATED, and the Rust exercises the same numbers.

## ANSWERS TO THE TWO QUESTIONS THE BRIEF ASKED EXPLICITLY

### Did table folding get wired? **YES.**
`prove_cubic_sumcheck` is the folded prover: five tables halve each round, so the
whole run is **O(2^m)**, not the literal mirror's O(4^m).
`folding_lifts_the_dimension_ceiling` runs **m = 16** instantly (the mirror would
be ~4·10⁹ MLE evaluations there).

**The `m ≈ 12` TIME ceiling is gone.** What remains is a MEMORY ceiling, and I
should state it rather than say "no cap": the prover holds five `u64` tables of
`2^m`, so m = 20 is 40 MB and m = 25 is 1.3 GB. That is inherent to any
table-based multilinear prover, not to this rung, and m = 20 (the size the
soundness memo prices at 60/2^186) is comfortable.

⚠ But NOT by reusing `mle_kernels::fold_mle_table`, and the reason is a real
interface finding, not laziness: **`NativeMleScalar` carries no runtime modulus.**
Its methods are `add_native(self, rhs)` — the field is fixed at the TYPE level
(`Ext6`, `TowerElem`, `Tower256`). The sumcheck engine is deliberately
prime-GENERIC (`p: u64` threaded through every call) precisely so the Lean
`MLEExample` keystones over **F₅** and the F₉₇ tests bind to the same code as the
BabyBear conformance vector. Implementing `NativeMleScalar` for a prime scalar
would mean pinning the prime in a newtype and **forking the engine away from the
Lean keystones it is bound to.** So `fold_table` is the p-generic twin of the same
recurrence, and `fold_table_agrees_with_the_mle_kernel_recurrence` pins it to that
recurrence explicitly.

⚑ **The binding that matters:** `folded_prover_agrees_with_literal_mirror` checks
the O(2^m) path against the O(4^m) literal Lean mirror for m = 1..5 at every round
and node, and `folded_prover_matches_lean_reference` checks it against the Lean
conformance numbers. Without those the optimization would have *replaced* the
Lean-mirroring path rather than accelerating it, and the seam would be gone.

### `h(1)` on the wire / no partial verifier — **both laws held.**
Round messages are four evals `[h(0),h(1),h(2),h(3)]`; `h(1)` is prover-supplied
and read by the round check. `no_message_passes_both_checks` makes the p3 pitfall
concrete: against a false claim, the honest `h(1)` fails the ROUND check and the
p3-style derived `h(1) = claim − h(0)` passes the round check **by construction**
and then fails the TERMINAL check. The test ASSERTS the derived value differs from
the honest one before checking rejection, so it cannot decay into a no-op
falsifier. No lemma of the form "if every round check passes then…" exists on the
Lean side.

## HONEST RESIDUALS
- The Rust is UNVERIFIED COMPUTE bound by vectors. Not refinement, not TV.
- `eval_lagrange`'s `{0,1,2,3}` nodes exclude char 2. The **char-2 fork is open**:
  `tower256_kernels::fraction_add_layer` (the inversion-free GKR layer) is in the
  binary line with no protocol driver, and it will need coefficient-form messages,
  not node evaluations. The Lean side is already coefficient-form, so the Lean
  does not have to change — only the wire format does.
- `inv_mod` is Fermat and therefore assumes `p` PRIME. Documented at the call
  site; the conformance vector instantiates BabyBear.
- No GKR *driver* (layer recursion, the fraction-tree descent) exists yet in
  either language. This rung is the layer primitive, not the tree.
- The commitment seam is untouched: `Selvage/Commitment.lean`'s `OpeningScheme`
  is still POSITIONAL, the wrong shape for a multilinear claim. Named in
  `gkr-substrate-findings.md`; still a campaign, still not started.

## BUILD EVIDENCE (all exit codes captured directly, never through a pipe)

Commit `6e934ec` in `~/dev/minidregg` — 9 files, 2176 insertions, **0 deletions**
(so no foreign hunks were swept from the shared tree; the other lanes' staged
`docs/LOOM-*` deletions and untracked zkml/uwueave files were left alone).

| gate | result |
|---|---|
| `lake build Selvage Assurance` | **8812 jobs, exit 0** |
| `cargo test` (working tree) | **exit 0** — 43 lib + 7 new conformance + all suites |
| `cargo test` from a DETACHED `git archive HEAD` extraction | **exit 0**, same counts |
| `scripts/check-import-boundary.sh` | **exit 0** (Selvage additions are within Mathlib/Theory/Selvage) |
| `scripts/check-proof-hygiene.sh` | **exit 0** — 428 tracked Lean files, 153 guarded axiom footprints |
| `grep sorry` on committed Lean | only the prose "no `sorry`" in a docstring |
| `git diff HEAD` on my paths | empty — what was built IS what was committed |

⚠ **Honest limit on the HEAD verification.** The Rust side was verified from a
truly detached extraction of the commit. The Lean side was NOT: a detached Lean build
needs a cold `.lake` (mathlib fetch), which was not worth the wall-clock here.
What was checked instead: `git diff HEAD` is empty for every Lean path I touched,
so the green build ran on byte-identical content; and none of my files import
anything uncommitted (`Assurance.AirSumcheckQuadratic`,
`Selvage.MultiplicativeMleTerminal`, `Compiler.SumcheckConformance` are all
unmodified at HEAD, and `lake build Assurance` does not touch the `Compiler` root
aggregator that another lane has dirty). That is weaker than a detached build and
is stated as such.

## THE ESTIMATE, MEASURED

The design memo said "degree 3 is a line-for-line port of a template that exists"
and priced SZ at 80–120 lines. **Both held.** The spike was green in ~15 minutes
with one trivial error; the cubic port took two build cycles (an arg-count
miscount, then a numeral defaulting to ℕ inside a `show`); SZ took three cycles,
all of them mathlib-name friction (`div_add_div_same`, `linear_combination`,
`eq_neg_of_add_eq_zero_left` — I replaced each with name-independent algebra
rather than keep guessing). Nothing in the mathematics resisted.

⚑ The reason it was this cheap is worth recording: **three things the port needed
already existed and none were in the brief** — `mle_lsb_recurrence` (the exact
A + x·Δ decomposition SZ induction needs, in `MultiplicativeMleTerminal.lean`),
`uniformProb_or_le` + `uniformProb_prod_le` (both halves of the union-and-fibre
argument), and the degree-generic protocol layer. The recon that found them cost
one subagent call and saved the whole SZ proof from being rebuilt from scratch.

## ⚠ INCIDENT: `--only` protects the first commit, `--amend` discards that protection

Worth recording because the two commands read as if they compose and they do not.

The rung commit (`6e934ec`) was made correctly with `git commit --only <9 named
paths>` in a tree where another lane had four `docs/LOOM-*` deletions STAGED. The
`--only` did its job: 2176 insertions, **0 deletions**, no foreign hunks.

Then I put a wrong number in a follow-up commit message (claimed the proof-hygiene
gate read "163 guarded axiom footprints, up from 153"; it reads **153**, and it
never moved, because the gate counts FILES carrying pins). Correcting it with
`git commit --amend -F msg` **took the INDEX** — and swept the other lane's four
staged deletions, 732 lines, into a commit titled "pin the eq-polynomial axioms."

Nothing was lost: the other lane meant to delete them, the worktree already
matched, the content sits at `HEAD~`. Only the attribution is wrong. Per house
rule the sweep is REPORTED, not rewritten — the commit message now carries a
paragraph naming all four files so the flag day is findable from the log. A
second, message-only amend fixed the disclosure; tree hash verified IDENTICAL
before and after (`0dda3ec`), so it changed no content.

Two transferable bits:
1. **`--only` is per-invocation.** It guards the commit you type it on and gives
   you no standing protection. Any later `--amend` on a shared tree is a bare
   index commit unless you re-name the paths.
2. **The trigger was a number I did arithmetic on instead of reading.** The
   original commit body would have been fine with "the gate passes"; inventing a
   delta created the need to amend, and the amend is what did the damage. This is
   the guess-becomes-a-diagnosis class, and its cost here was not the wrong
   number — it was the correction.
