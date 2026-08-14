# The blowup drop — fixing the bug we had frozen as a law, and what it buys

2026-08-14. **Written incrementally while measuring.** Each claim is tagged `[derived]`,
`[measured-here]`, `[measured-elsewhere, cited]` or `[open]`.

This is the execution note for `docs/VERDICTS.md` §7.0's *"fix the bug, repair the gate, then drop
the blowup at BabyBear"*, and for `notes/koalabear-migration.md` §1.4c/§8.

---

## 0. What landed

> ## ⚑⚑⚑ **The `log_blowup ≥ ⌈log₂(d−1)⌉` floor is gone. It was one `.bit_reverse_rows()` in a crate we already vendor, and our own gate had made it a law.**
>
> 1. **The gate was inverted.** `circuit/tests/fri_blowup_global_knob_survey.rs` asserted that a
>    chip-bearing descriptor **must refuse** at `(2,57)`. It now asserts the opposite — that every
>    chip-bearing descriptor **proves and verifies** there — and it reds if the bug returns.
> 2. **The fix is in**, in the vendored `p3-fri` (`[patch]` source, so it survives a rebuild), with
>    the upstream provenance and PR #1982's status in its header.
> 3. **Verified by construction**, not by outcome: both PCS paths against an independent coset DFT,
>    a degree-7 AIR verifying at `lb = 2`, and **a corrupted trace still rejecting** —
>    `circuit/tests/fri_extrapolation_row_order.rs`.
> 4. **The query count is re-derived, two-sided, at all three regimes** —
>    `minidregg/Assurance/TwoRegimeQueryBudget.lean` §7b. `q = 57` is minimal at `lb = 2`, and the
>    drop **loses nothing at any regime and gains 20 bits at UDR**, the only unconditionally proven
>    one.
> 5. **The win is measured in exact permutation counts, not wall clock** (this box was at load
>    average 30–52): **the prover does 15.19× fewer Poseidon2 permutations**, and the 38 extra
>    queries cost it **five**. The **verifier does 2.28× more** — that is the whole price, and it
>    reproduces the 2026-08-04 "why 6 stays" verdict exactly.
> 6. **The global config flip is NOT landed, and not for cost.** The trade is genuinely two-sided
>    in exact counts, `ir2_config` already names the right answer (a per-descriptor knob), and that
>    answer has a **real prerequisite that is itself a soundness hole**: the recursion verifier
>    reads `num_queries` off the proof it is verifying and never pins it, masked today only because
>    every child runs 19. §7 — including the flag day, stated in advance.

---

## 1. The bug, stated once

`TwoAdicFriPcs::get_evaluations_on_domain` (`vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs:457`)
has two paths:

| condition | what it does | row order it returns |
|---|---|---|
| `shift == GENERATOR ∧ lde.height() ≥ domain.size()` | prefix of the bit-reversed stored LDE, then one `bit_reverse_rows()` | **natural** |
| otherwise | un-reverse → coset-iDFT → truncate → zero-pad → coset-DFT, then one `bit_reverse_rows()` | **bit-reversed** ← wrong |

`coset_dft_batch`'s result already reads natural through its `Matrix` impl (it is a
`BitReversedMatrixView` over a bit-reversed buffer), so upstream's trailing reversal is **one too
many**. Right values, wrong rows. The caller folds the AIR over permuted trace rows, commits a
wrong quotient, and emits a complete, well-formed proof its own verifier rejects with
`OodEvaluationMismatch`. `[measured-elsewhere, cited: koalabear-migration.md §1.4c]`

The slow path is entered exactly when a matrix's quotient domain outgrows its committed LDE, i.e.
when `log_blowup < log_quotient_degree = ⌈log₂(d − 1)⌉`. **That is the entire content of the
"degree-7 S-box needs `log_blowup ≥ 3`" floor.** It is not a soundness bound, not a property of
FRI, and not a fact about BabyBear.

**Fix** — one inserted call, free at `Radix2DitParallel` (the added call just unwraps the view):

```rust
let result = self.dft
    .coset_dft_batch(coeffs, domain.shift())
    .bit_reverse_rows()          // <-- inserted
    .to_row_major_matrix();
```

### Where the fix lives, and why there

The pin is a **path `[patch]`**, not a cargo git checkout:

```toml
[patch."https://github.com/Plonky3/Plonky3"]
p3-fri = { path = "vendor/plonky3-fri-82cfad73" }
```

so editing `vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs` is the edit that survives a rebuild,
a `cargo update`, and a fresh clone. `vendor/plonky3-fri-82cfad73/Cargo.toml`'s
`package.metadata.dregg.local-delta` now names both deltas. **⚠ The excluded workspaces
(`wasm`, `poa-curator`, `dregg-tui`) resolve `p3-fri` from the git rev and do NOT get the fix** —
they are verifier-side, and `get_evaluations_on_domain` is a prover-only method, so nothing there
can observe it. `[derived]`

### Upstream

`[measured-elsewhere, cited]` — Present on `main` at `f5b7977e` and in every published `p3-fri`
through 0.6.3. Introduced by PR #1352 / `b9863b6b` (2026-03-02), **the same commit that deleted the
guarding `assert!(lde.height() >= domain.size())`** — a loud panic became a silently invalid proof.
The test that commit added, named `extrapolation`, takes the **fast** path and never enters the
branch it was written to cover.

**PR #1982 is this exact one-line change. Checked 2026-08-14: still OPEN, still
CHANGES_REQUESTED**, maintainer `Nashtare`: *"This is to be expected, i.e. you need a sufficiently
large blowup factor for your constraint polynomial."* — the objection restates the symptom as the
requirement, which is precisely the reading our tree adopted. Awaiting a second code owner.
`[measured-here, via the PR page]`

**We do not wait for it.** The fix is ours in the vendored source, with the provenance recorded so
a future upstream sync can drop the delta if #1982 ever merges.

---

## 2. The gate that had frozen the bug

`circuit/tests/fri_blowup_global_knob_survey.rs`, before:

```rust
assert!(!chip_refusals.is_empty(),
    "no chip-bearing descriptor refused at (2,57). Either the chip S-box degree dropped … or no
     case in this grid pulls in the chip table.");
```

It was written to stop someone claiming `lb = 2` was free. It had become the thing stopping anyone
from **discovering that it is** — and it would have gone red the moment the bug was fixed.

After: the grid must contain at least one chip-bearing descriptor (else the leg is vacuous — the
*falsifier-that-stopped-falsifying* class), and **none of them may refuse at `(2,57)`**. The
failure message routes the reader to `fri_extrapolation_row_order.rs` first, because if that file
is green while this one is red the difference is *which `p3-fri` got linked*, not which claim is
true.

Three more inversions in the same file and its neighbours, all of them the same sentence in
different clothes:

- `Point::outcome`'s docblock ("a blowup below a table's constraint-degree floor is **not a point**")
  — now records the retraction.
- `Measured::chip`'s docblock ("the table whose degree sets the descriptor's blowup FLOOR") — the
  column now means *"takes the extrapolation code path"*, which is what it always structurally was.
- §1b's registry census **excluded every chip-bearing golden from the predicted wire total** as
  `n/a (refuses)`. All 132 goldens are now priced.
- `circuit/src/descriptor_ir2.rs`'s `ir2_config` docblock carried the 2026-08-04 "CORRECTION" that
  wrote the bug up as a property of the S-box. It now carries the retraction, quoting the old text
  so the record is legible rather than rewritten.

---

## 3. Verified by construction — `circuit/tests/fri_extrapolation_row_order.rs`

Three assertions, and the third is what makes the other two mean anything:

1. **Both PCS paths equal an independent coset DFT of the interpolated polynomial**, row by row,
   with the *multiset* of rows asserted first so a genuine value error is distinguishable from an
   order error in the failure output. The test asserts up front that its two target domains land on
   opposite sides of `lde.height()`, so it cannot silently test one branch twice.
2. **A degree-7 AIR (`b = a⁷`) proves and verifies at `log_blowup = 2`** — and at `log_blowup = 3`,
   the control, where the fast path runs and nothing changed.
3. **A corrupted trace still rejects at `log_blowup = 2`.** Handled in both build profiles: debug
   `uni-stark::prove` panics in `check_constraints`, release emits a proof that must fail to
   verify. A `#[should_panic]` or a bare `verify(..).is_err()` would each be vacuous in one of the
   two.

Without (3), (2) is satisfied by a PCS that accepts anything. That is the failure mode a
"restores correctness" claim must rule out and usually doesn't.

⚠ **The fix cannot move a deployed proof's bytes.** It is confined to the `else` branch, reached
only when `lde.height() < domain.size()`. Every config this repo has shipped (`lb ∈ {3, 6}`, max
constraint degree 8 ⇒ `lqd ≤ 3`) takes the fast path exclusively. **So landing the fix is not a
flag day; landing the config change below is.** `[derived]`

---

## 4. The query count, re-derived — not assumed

`minidregg/Assurance/TwoRegimeQueryBudget.lean` §7b `[machine-checked, kernel, no
`ofReduceBool`]`. The existing ladder set `(2,57)` from the two **linear** columns (`q·lb` at CBR,
`q·lb/2` at JBR, where `19·6 = 57·2`). That is a correct answer arrived at by an argument that only
covers two of three regimes, so it is re-derived from `queryErr` directly, two-sided:

| config | UDR | JBR | CBR |
|---|---:|---:|---:|
| deployed `(6, 19, pow 16)` | 34 | 73 | 130 |
| **`(2, 57, pow 16)`** | **54** | **73** | **130** |

- `lb2_drop_three_regimes` — the three numbers, two-sided (`Bits k` is `≤ 2^−k` **and**
  `2^−(k+1) <`), so each is a measurement and not a bound that can be loosened.
- `lb2_drop_is_at_or_above_the_deployed_column (r : Regime)` — stated over **all** of `Regime`,
  because "at parity" claims in this repo have been made at whichever column flattered them. There
  is no regime at which the drop is worse.
- `lb2_drop_query_count_is_minimal` — 56 queries drops below the deployed column at JBR **and** at
  CBR. So 57 is derived, not chosen; an over-padded rung would let a cost comparison charge the
  extra soundness to the blowup.
- `lb2_drop_strictly_improves_the_proven_regime` — **`34 → 54` at UDR, +20 bits.** `((1+ρ)/2)²`
  degrades far more slowly in `ρ` than `ρ` does, so at fixed `q·lb` the low-blowup/high-query end
  is strictly the sounder one. **UDR is the only regime this file marks `reportable` and
  unconditionally proven** (`cbr_not_reportable`; the famous 130 is the *withdrawn* column).

So: *"lower blowup needs more queries for the same bits"* is true of the count and **false of the
bits** — it needs 3× the queries and it comes back with twenty more bits on the column that is
actually proven, plus the `ε_C ∝ ρ^−3/2` commit-phase gain already recorded
(`koalabear-migration.md` §2.2: composite λ **+2 leaf to +13.5 wrap**) and four rungs of headroom
at the two-adicity ceiling (`max rows = 2^(27−lb)`: `2^21 → 2^25`).

### ⚑ And the extra queries cost the prover FIVE permutations

`[measured-here]` — exact Poseidon2 permutation counts, `circuit/tests/ir2_phase_profile.rs::
poseidon2_permutation_counts_per_phase` §D2, on the IR-v2 transfer descriptor batch. **Counts, not
milliseconds**: a permutation count is deterministic and contention-immune, and this box was at
load average 30–52 with 41 login sessions while these were taken, so every wall clock on it is an
upper bound and none of it is evidence. §5 says what is still missing from the count picture.

| | prover perms | |
|---|---:|---|
| queries alone, `lb = 2`: `q 19 → 57` | 14,290 → **14,295** | **+5** |
| queries alone, `lb = 6`: `q 19 → 57` | 217,150 → **217,155** | **+5** |

**Thirty-eight extra queries cost the prover five Poseidon2 permutations, at either blowup.** The
prover *reads* Merkle siblings when opening; it does not re-hash them, so the entire query axis is
a handful of transcript permutations. This is the actual reason the trade is good, and it is
absent from every soundness discussion in these notes, which argue it in bits and never in work.

What the drop pays for its queries is **verifier work and wire bytes** — §6.

⚠ The same file's §D used to hold `q = 19` on every row, so it priced the blowup and was silent
about the one thing a blowup *drop* has to buy back. Four points were appended (`(2,19,0)`,
`(2,57,0)`, `(6,57,0)`, `(2,57,16)`) to factor the move into its two independent halves, with the
three facts asserted so a silent inversion reds.

⚠ **`TOTAL perms` in that table is prove + SELF-VERIFY** (`prove_vm_descriptor2_for_config`
verifies its own proof, counted by the same global). Reading it as prover work attributes the
verifier's per-query Merkle paths to the prover and makes the query axis look 1.32× expensive on
the wrong side of the wire — which is exactly what the first draft of this note said before the
assertion caught it.

### The grind-free measurement pair

A wall-clock comparison at `pow = 16` is dominated by grind, which is blowup-independent (12.8 ms
mean, `notes/grind-phase.md`) and carries run-to-run variance that swamps the difference being
measured. Measuring at `pow = 0` fixes that — but then **both** ends need their query counts
recomputed, or the comparison silently moves the soundness as well as the blowup:

| grind-free config | UDR | JBR | CBR |
|---|---:|---:|---:|
| `(6, 36, pow 0)` | 35 | 108 | 216 |
| `(2, 73, pow 0)` | 49 | 73 | 146 |

Both at or above the deployed column at every regime, and both tight to one query
(`the_grind_free_pair_is_at_or_above_the_deployed_column`, `the_grind_free_pair_is_tight`). Note
the query ratio is **2.03×** here against **3.00×** at `pow = 16`: switching the grind off costs
the low-blowup end fewer queries, because a grind bit is worth 17 queries at UDR at `lb = 6` and
fewer as `ρ` grows.

---

## 5. The measured win, in work — and what the count cannot see

`[measured-here]` — `circuit/tests/ir2_phase_profile.rs::poseidon2_permutation_counts_per_phase`
§D2, IR-v2 transfer descriptor batch, **prover permutations excluding the self-verify**:

| move | prover perms | ratio |
|---|---:|---:|
| **blowup alone** `(6,19,p0) → (2,19,p0)` | 217,150 → 14,290 | **15.20× fewer** |
| queries alone `(2,19,p0) → (2,57,p0)` | 14,290 → 14,295 | 1.0003× more |
| **⚑ net, grind-free** `(6,19,p0) → (2,57,p0)` | 217,150 → **14,295** | **15.19× fewer** |

Per phase, the whole reduction is where it should be: `Merkle-commit` **211,965 → 13,245** and
`FRI fold Merkle` **4,413 → 273`** — the Merkle tree is built over an LDE of `n·2^lb` rows, so it
halves per rung, exactly.

### ⚠ The grind is a SAMPLE, and it is not a comparator

`(6,19,pow16)` ground **49,153** permutations; `(2,57,pow16)` ground **98,305**. Those are two
draws from a ~`2^16 = 65,536` mean — the count is *where the Fiat–Shamir witness happened to be*,
not a property of the config. **A ratio taken off that pair (2.22×) is noise wearing a decimal
point.** At the mean, `prove + grind` is `282,686 → 79,831 = 3.54×`, and **grind's share of the
prover goes 23% → 82%** — so this change and the windowed-grind fix are not independent, and this
one should land first.

### ⚠ Three things this number is NOT

1. **It is not a wall-clock speedup.** It is 15.19× less *hashing*. This box was at load average
   30–52 with 41 sessions; nothing timed on it is evidence, which is why this section is in counts.
2. **It is not the whole prover.** ⚑ **We have exact hash counts and no arithmetic counts.** The
   coset-LDE and quotient DFTs also shrink with blowup (`O(n·2^lb·lb)` butterflies: `384 → 16` per
   trace element, crudely), but nothing measures that, so **"the prover is hash-bound" remains
   unproven rather than established.** A field-multiplication counter is the highest-value missing
   instrument in this whole picture and it is not built here. (An untracked
   `circuit/tests/ir2_field_op_counts.rs` appeared in the shared tree during this lane. **Not read,
   not run, not mine** — recorded only so the next reader knows to look.)
3. **It is one workload.** The IR-v2 transfer descriptor batch, not a trace-height sweep. The
   13.13× figure in `koalabear-migration.md` §6.3 is a *different* workload (one descriptor at
   4,096 rows) **and is wall clock on this same contended box** — an upper bound, not a
   measurement. Today's re-run of that same case reads **7.78×** at load 30–52 against **13.13×**
   when it was first taken. Both are upper bounds and neither is the number; the count is.
   **The two workloads must not be composed.**

---

## 5b. The whole grid, at the descriptor level

`[measured-here]` `circuit/tests/fri_blowup_global_knob_survey.rs::
every_provable_descriptor_at_every_parity_point`, release, **green with the repaired assertion**.

> ### ⚑ **The per-descriptor "floor" is now `log_blowup 2` for ALL TWELVE descriptors — chip-bearing and chip-free alike.**
>
> Before the fix, the six chip-bearing rows read `REFUSED · lb=2 IS NOT A POINT FOR THIS
> DESCRIPTOR`. They now prove **and self-verify** at `(2,57)`. That is the repair, end to end, on
> the real registry rather than on a synthetic AIR.

⚠ **Wall clock on a box at load average 30–52 with 41 sessions. Upper bounds; ratios between them
are the least corrupted reading and still not evidence.** The byte columns *are* exact.

| descriptor | rows | commit | chip | bytes @(6,19) | bytes @(2,57) | prove ×(↑better) | verify ×(↓worse) |
|---|---:|---:|:---:|---:|---:|---:|---:|
| poseidon2-hash-arity2 | 2 | 3 | yes | 86,497 | 183,365 | 4.35 | 2.06 |
| turn-chain-binding | 4 | 7 | yes | 88,069 | 187,456 | 1.38 | 2.01 |
| blinded-membership | 4 | 12 | yes | 89,532 | 191,511 | 3.43 | 2.03 |
| merkle-membership-binary-d4 | 4 | 13 | yes | 88,673 | 188,584 | 4.07 | 2.02 |
| presentation-freshness | 4 | 43 | no | 49,709 | 96,705 | 4.68 | 2.17 |
| delegate-scope-v2 | 2 | 24 | no | 17,874 | 26,137 | 1.07 | 1.51 |
| attested-fact-membership | 4 | 34 | yes | 91,945 | 197,826 | 4.41 | 2.15 |
| merkle-membership-4ary-d4 | 4 | 90 | yes | 105,424 | 231,548 | 3.98 | 2.03 |
| pasta-fpadd-sound@64 | 64 | 384 | no | 216,314 | 491,793 | 1.84 | 2.20 |
| pasta-rcb-windowed@1024 | 1024 | 525 | no | 126,796 | 286,848 | 5.94 | 2.14 |
| pasta-fpmul-sound@64 | 64 | 694 | no | 399,809 | 932,564 | 1.76 | 2.16 |
| **pasta-fpmul-sound@4096** | **4096** | 694 | no | 436,776 | 1,030,361 | **7.78** | 2.23 |

**Verify is 1.5–2.2× worse everywhere, with no exceptions** — the same 2.28× the permutation counts
give, arrived at independently. **Prove improves everywhere**, and the top of the range is the
tallest trace in the grid.

### ⚑ A model calibrated on a censored sample

Fixing the bug broke §1b's byte predictor, and the way it broke is worth recording. The
two-regressor fit `Δbytes = 38·(a·W_committed_main + b·n_range_lookups)` was calibrated on the
descriptors that **could be measured at `(2,57)`** — which, while the bug stood, excluded **every
chip-bearing one**. With the censoring removed it misses those rows by up to **99%**:
`poseidon2-hash-arity2` has **three** committed main columns and pays **+96,868 bytes**, and no
function of `(3, 0)` predicts that.

The missing regressor was always structurally there: **a query opens one row of every committed
matrix, and the Poseidon2 chip table is a committed matrix whose width is not in
`W_committed_main`.** It enters as an **indicator** (fixed width, fixed Merkle depth), not as a
width. Refitted:

```
Δbytes(6→2) = 38 · (8.622 · W_committed_main + 43.617 · n_range_lookups + 2535.3 · [chip])
```

⚑ **The tell that the chip term is real and not a curve-fit: adding it moved the other two
coefficients by 0.01%** — `8.623 → 8.622`, `43.613 → 43.617`. The old fit was never wrong about
the chip-free descriptors; it had no term for a matrix it had never been allowed to see.
Chip-bearing per-descriptor error goes **76–99% → 0.0–4.3%**. And §1b's registry census, which had
been printing `n/a (refuses)` for the chip-bearing half of the registry and excluding it from the
total, now prices all 132 goldens.

⚠ One residual, honestly: `presentation-freshness` is at **−63%** (43 committed, 2 range lookups,
no chip; predicted 17,403, measured 46,996) — **exactly where it was under the old fit.** So the
`±63%` that constant has always claimed was a fact about *that one descriptor*: correct for the
chip-free population it was calibrated on, and completely uninformative about the chip-bearing
half. Every other chip-free row is within 25% and every chip-bearing row within 4.3%, so it is
**one descriptor carrying a committed matrix none of the three regressors names** — the same shape
of defect the chip term just fixed, one table further down. Named, not smoothed.

(The measured Δbytes are byte-identical across three runs — 46,996 every time. Only the wall clocks
in the grid above move, and that is contention, not the artifact.)

**The class:** the bug did not only produce a wrong refusal. It **removed half the sample from a
regression**, and the regression then reported a tidy `±63%` about a population it had never
seen. A gate that excludes the cases it cannot measure will report confidently about the ones it
can.

---

## 6. The price: the verifier and the wire

`[measured-here]` The queries are free on the prover and are **not** free on the other side:

| | perms | ratio |
|---|---:|---:|
| verifier, `(6,19) → (2,57)` | 4,040 → 9,213 | **2.28× more** |

That is the honest cost column, and it is the one the 2026-08-04 "why 6 stays" decision was made
on: *"on the axis this system optimizes — wire bytes and verify ms for light clients and on-chain
verifiers — `(6,19)` wins on EVERY measured descriptor by 2.0–2.4× on both"*
(`descriptor_ir2.rs::ir2_config`). **That verdict reproduces exactly in counts: 2.28×.** It was
right then and it is right now.

So the trade is, in exact work:

> **prover ÷15.2 · verifier ×2.28 · wire ×~2.4 · UDR +20 bits · row ceiling ×16.**

---

## 7. The config change — what I am NOT landing, and why

**Not landed: a global `IR2_FRI_LOG_BLOWUP = 2`.** `[decision]`

The greenfield doctrine says a flag day is not a cost and a cost estimate is never a reason to pick
the worse design — and it is right, and it does not apply here, because **nothing is being
deferred for cost.** The blocker is not a VK rotation or a descriptor re-emit; those are a
rebuild. The blocker is that the measurement says the global knob is a **genuine two-sided trade**,
and it says so in exact deterministic counts on both sides:

- the prover wins 15.2× (and more as trace height grows), and
- the verifier and the wire lose ~2.3×, on a chain whose light clients and on-chain verifiers are
  the named optimization axis.

`ir2_config`'s docblock already names the right resolution and it is not "flip the global":

> *"the answer for that family is a **per-descriptor knob** — and the prerequisite is the recursion
> path, which reads `num_queries` from the inner proof structure
> (`recursion/src/pcs/fri/verifier.rs:1378`) and **never pins it against a configured count.**
> That is masked today only because every child runs 19 queries."*

**Verified at source, not relayed** `[measured-here, 2026-08-14]` —
`~/.cargo/git/checkouts/plonky3-recursion-2254dc838bc79d6b/fc3c6df/recursion/src/pcs/fri/
verifier.rs:1378`:

```rust
let num_queries = fri_proof_targets.query_proofs.len();
```

`log_blowup` arrives as a **parameter**; `num_queries` is read off the proof being verified. The
only two later uses are `num_queries != index_bits_per_query.len()` (derived from the same
transcript) and `num_queries == 0`. **There is no pin against a configured count anywhere in the
file.**

**That prerequisite is now the first item of the work, not a reason to stop.** It is also a real
soundness hole in its own right — a verifier that takes the query count from the object it is
verifying is a verifier that can be told to check fewer queries — and it is invisible today only
because every child runs 19. Landing a per-descriptor knob without pinning it first would *ship*
that.

What the docblock named as **the trigger that flips the global answer** has also arrived, and it
should be recorded: it is *"a descriptor needing more than `2^21` rows"*, because
`max rows = 2^(27 − lb)`. At `lb = 6` the ceiling is **exactly `2^21`, i.e. zero headroom**, and
the in-AIR Kimchi/Wrap verifier pads to exactly `2^21`. **zkML traces are `2^16`–`2^20`.** So the
trigger is one rung away on the chain side and already past on the zkML side.

### The flag day, stated in advance

For whoever lands `(2, 57)` — global or per-descriptor:

- **Re-emit:** every by-name descriptor golden's recorded proof; all 132 are affected, not the 89
  chip-free ones (the chip-bearing exclusion was the bug).
- **Rotate:** the IR-v2 VK epoch. FRI shape and Fiat–Shamir both move, so **proofs are not
  interchangeable across the two configs** and the old ones must **refuse to load**, not
  reinterpret. `recursion_vk_fingerprint` hashes circuit *shape* and excludes opened values and
  query proofs — **check whether it sees `num_queries` at all before assuming the rotation is
  automatic.**
- **Re-genesis** the devnet, per `CANONICAL_STATE_SCHEMA_EPOCH`.
- **Pin `num_queries` in the recursion verifier** (`recursion/src/pcs/fri/verifier.rs:1378`)
  *before* any two configs coexist.
- **Do not** touch `IR2_FRI_QUERY_POW_BITS` in the same change: the grind is a separate lever with
  its own sampled cost, and moving both at once makes the measurement unreadable.

---

## 8. What is landed here

| | |
|---|---|
| the `p3-fri` row-order fix | `vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs` (+ `Cargo.toml` delta note) |
| verified by construction | `circuit/tests/fri_extrapolation_row_order.rs` — 3 tests, green |
| the inverted gate, repaired | `circuit/tests/fri_blowup_global_knob_survey.rs` |
| the retracted docblock | `circuit/src/descriptor_ir2.rs::ir2_config` |
| the query re-derivation | `minidregg/Assurance/TwoRegimeQueryBudget.lean` §7b, kernel-checked |
| the deterministic cost measurement | `circuit/tests/ir2_phase_profile.rs` §D2, 4 new points + 4 assertions |
| the censored-sample refit | `fri_blowup_global_knob_survey.rs` §1/§1b — 3rd regressor, all 132 goldens priced |
| **not** landed | the global config flip — §7 |

Commits: `4e6089484` (fix + gate + by-construction + refit), `26b33a37a` (counts) in `breadstuffs`;
`4889368` in `minidregg` (the query re-derivation).

---

## 9. What this leaves open

1. **A field-multiplication counter.** §5's ⚠ (2). Until it exists, "hash-bound" is a hypothesis
   and every prover ratio in this repo is a hash ratio wearing a system label.
2. **Pin `num_queries` in the recursion verifier.** §7. A soundness hole in its own right, and the
   prerequisite for the per-descriptor knob.
3. **The fourth regressor.** §5b's `presentation-freshness` residual — one committed matrix nobody
   has named, the same defect one table down from the one just fixed.
4. **PR #1982.** If upstream merges it, drop the delta from `vendor/plonky3-fri-82cfad73` and keep
   the header note as provenance. If they close it, the header is the record of why we diverge.
5. **The two-adicity ceiling is now the binding constraint on blowup**, not the degree budget.
   `the_row_ceiling_is_two_adicity_minus_log_blowup` is the gate that says so, and at `lb = 6` the
   ceiling is `2^21` with **zero** headroom against a wrap that pads to exactly `2^21`.
