# Poseidon2 virtualization — C3, measured

2026-08-13. BUILD + MEASURE lane against `docs/COMPOSITIONS.md` C3 and
`notes/virtualization-verdict.md`.

**The prediction was: virtualizing the permutation beats committing its intermediates by
4–15×. The measured answer is: YES BY 2.11×, AND NOT FOR THE PREDICTED REASON — and the
predicted mechanism (a sumcheck) LOSES at α=7 against our own measured exchange rate.**

Artifacts:
- `breadstuffs/circuit/tests/poseidon2_virtualization_measure.rs` — census, fidelity, clock
- `breadstuffs/sumcheck-toy/tests/folding_price.rs` — the other half of the exchange rate
- `zkml-research/paper/scripts/poseidon2_virtualization.py` — the crossover, on measured constants

---

## §0 — SAY THE SUBSTRATE OUT LOUD

The deployed Poseidon2 chip AIR **is Lean-authored**:
`metatheory/Dregg2/Circuit/Emit/Poseidon2RoundGates.lean` (`permEmission`) emits the round
algebra, `.../Emit/ChipTableEmit.lean` splices it into the chip's `TableAir`, the JSON lands
at `circuit/src/table_air.rs::CHIP_TABLE_AIR_JSON`, and Rust only *interprets* it. Good.

⚠ The **v1 hash sites are not**: `circuit/src/lean_descriptor_air.rs:1754-1756` pins
`SITE_AUX_COLS = POSEIDON2_PERM_AUX_COLS = 352` from a Rust constant and calls the Rust
gadget `poseidon2_permute_expr`, which its own Lean counterpart's docblock names as
"being Rust-authored AIR — exactly what architectural law #1 forbids". Two spellings of one
algebra; the Lean one is the real one.

**Nothing here authors a constraint in Rust.** The Rust added by this lane is two `#[ignore]`
test files that hold a stopwatch. The change this lane recommends lands in
`Poseidon2RoundGates.lean`.

---

## §1 — THE MATERIALIZE SIDE, COUNTED

`plonky3_prover.rs:278`, mirrored at `Poseidon2RoundGates.lean:97`
(`#guard POSEIDON2_AUX_COLS == 352`):

```
POSEIDON2_AUX_COLS = (TOTAL_ROUNDS + 1) * ROUND_COLS = (21 + 1) * 16 = 352
```

**352 committed base felts per permutation**, per round:

| block | rounds | felts/round | subtotal | nonlinearity in the round |
|---|---|---|---|---|
| post-initial-linear-layer | — | 16 | **16** | none — a linear map of the seed |
| external, first half | 4 | 16 | **64** | S-box on all 16 lanes |
| **internal** | **13** | **16** | **208** | **S-box on lane 0 ONLY** |
| external, second half | 4 | 16 | **64** | S-box on all 16 lanes |
| | | | **352** | |

⚑ **211 of the 352 (59.9%) are values of degree 1.** In an internal round only lane 0 passes
the S-box; lanes 1..15 are `sum + (d_i − 1)·x_i`, affine in the previous round's committed
state — 13 × 15 = **195** felts. Plus the 16-felt initial block, a pure linear map of a seed
the chip already holds in `CHIP_IN0..+16`. The AIR commits all of them and re-binds them
(`Poseidon2RoundGates.lean:264`: "every round's input is a bare column read").

Deployed chip: `#guard CHIP_WIDTH == 386`, `CHIP_AUX0 = 33` — **91% of the row is aux.**
Prover field ops per row, `#guard`-pinned at `Poseidon2RoundGates.lean:713-724`: **2,668** in
the emitted DAG, **2,316** in the Rust arm, the gap exactly `POSEIDON2_AUX_COLS` (one mult per
gate, `a − b` encoded `a + (−1)·b`).

---

## §2 — THE VIRTUALIZATION THAT WINS IS NOT A SUMCHECK

The degree-1 lanes can be virtualized **inside the AIR** — carried as expressions instead of
columns — at **zero degree cost and zero sumcheck**. Upstream Plonky3's own Poseidon2 AIR
already does exactly this (`p3-poseidon2-air`, pinned rev 82cfad73, `air.rs:259-278`):

```rust
state[0] += round_constant;
eval_sbox(&partial_round.sbox, &mut state[0], builder);
builder.assert_eq(state[0].dup(), partial_round.post_sbox);   // ONE column
state[0] = partial_round.post_sbox.into();
LinearLayers::internal_linear_layer(state);                    // lanes 1..15 stay EXPRESSIONS
```

At `WIDTH=16, SBOX_DEGREE=7, SBOX_REGISTERS=0, HALF_FULL_ROUNDS=4, PARTIAL_ROUNDS=13`,
`num_cols()` = 16 inputs + 8×16 post + 13×1 post_sbox = **157**.

**352 → 157 aux felts. 2.24×, at the same `max_constraint_degree = 7`** (`air.rs:139-141`), so
the same `log_blowup ≥ 3` floor and the same FRI ledger. Constraints 352 → 141.

### §2a — the op count falls too

In the same currency `Poseidon2RoundGates.lean §7` uses (which totals the Rust arm at 2,316):

| | arm A (deployed) | arm B (narrow) |
|---|---|---|
| initial external layer | 72 adds + **16 asserts** = 88 | 72 adds, **no asserts** = 72 |
| external round ×8 | 16+64+72+16 = 168 | 168 (identical) |
| internal round ×13 | 1+4+15+32+**16** = 68 | 1+4+**1**+15+32 = **53** |
| **per permutation** | **2,316** | **2,105** |

**−9.1% ops, −55% committed felts, −60% constraints, identical degree. Arm B is Pareto-
dominant; there is no trade to price.**

⚠ Checked for the hidden cost; it is not there. Lanes 1..15 carried across all 13 internal
rounds stay **degree 1** in committed variables (each internal round is affine in them, and
nonlinearity re-enters only through `post_sbox`, itself a committed column), so the S-box
opening the first ending-full-round acts on a degree-1 expression and lands at degree 7 like
every other. No degree accumulation; no blow-up in the shared representation either — on the
prover `AB::Expr` is a packed field value, so each round's 16 lane expressions are 16 numbers
computed once.

### §2b — at the deployed chip

The chip already holds the seed, so arm B's `inputs` block is redundant there and the aux
span is `8×16 + 13×1 = 141`:

```
CHIP_WIDTH = CHIP_AUX0(33) + 141 + 1 = 175       (deployed: 386)
```

**386 → 175 columns, 2.21× narrower, on the object `ChipTableEmit.lean` calls "the hottest
path of the whole system".**

---

## §3 — MEASURED

`cargo test -p dregg-circuit --release --test poseidon2_virtualization_measure -- --ignored`
Both arms under the identical `create_config()` (lb=3, q=38, PoW=16), on the **deployed round
constants** (the test re-cuts `ROUND_CONSTANTS` into upstream's three-block shape and asserts
the internal rows really are lane-0-only, so a dropped constant cannot pass silently).

**Fidelity first, before any clock**: both arms' witness generators are run on identical
inputs and every one of 1,024 final-state lanes is checked against the deployed
`poseidon2_trace`, plus an anti-vacuity perturbation asserting a flipped input bit moves the
output. Same permutation, two arithmetizations. ✅

min of 3; ms-prove, ms-verify, trace cells, proof bytes (json):

| n perms | A prove | A verify | A cells | B prove | B verify | B cells | prove | verify | cells | size |
|---|---|---|---|---|---|---|---|---|---|---|
| 2^10 | 58.6 | 5.6 | 376,832 | 34.0 | 3.9 | 160,768 | 1.72× | 1.44× | 2.34× | 1.38× |
| 2^12 | 94.2 | 6.5 | 1,507,328 | 80.0 | 4.5 | 643,072 | 1.18× | 1.45× | 2.34× | 1.33× |
| 2^14 | 342.4 | 7.8 | 6,029,312 | 243.7 | 6.1 | 2,572,288 | 1.40× | 1.29× | 2.34× | 1.29× |
| **2^16** | **1434.9** | **9.4** | 24,117,248 | **678.8** | **7.3** | 10,289,152 | **2.11×** | **1.28×** | 2.34× | 1.25× |

⚑ **2.11× prover, 1.28× verifier, 1.25× proof size at 2^16 permutations.** The prove ratio
converges toward the cell ratio as the fixed FRI/transcript cost amortizes; the 2^12 point at
1.18× is box noise (a laptop under swarm load), which is why the largest point is the one to
quote and why the table shows all four rather than the best.

---

## §4 — THE OTHER HALF OF THE EXCHANGE RATE, AND WHY IT REVERSES C3

`boundary_exchange_rate.py` prices one committed felt at 3,120 mult-equiv (lb=4) / 12,331
(lb=6) and virtualizing one at `(d−1)·k·10 = 40` per layer. **That `10` is a fudge constant,
and the mult-equiv → wall-clock conversion had never been taken.** Taken:

- `sumcheck-toy/tests/folding_price.rs`, a complete `p3-sumcheck` fold (degree 2, packed,
  deployed challenger), 2^20 values: 11.506 ms ⇒ **10.97 ns per value per layer**.
- The arm A/arm B delta at 2^16: 756.1 ms over 13,828,096 cells ⇒ **54.68 ns per marginal
  committed felt** at lb=3.

**MEASURED EXCHANGE RATE ≈ 5.0 layers.** The script says ~40× at lb=3 in counted
multiplications, 78×/308× at lb=4/6. ⚑ **The gap is ~8×, and it is the conversion**: hashing
SIMD-vectorizes harder than sumcheck folding does, so a scalar multiplication count
over-prices commitment. The threshold rule is exactly as good as that conversion — and the
conversion is what decides C3.

⚠ **`54.68 ns` is an UPPER bound on the pure commitment price** — arm A also carries 211 more
constraints, so the delta bundles quotient work with commitment work. Every conclusion below
moves the same way under a *lower* commit price (virtualizing looks worse), so the verdict is
robust to the confound. Stated because it is the flattering direction for the conclusion, not
against it.

### The crossover, in α and in layers

A GKR arm (arm C) commits only the 16 input lanes and sumchecks the round chain. The values
needing a sumcheck are exactly the S-box inputs (linear layers fold into the claim), i.e.
`R_F·W + R_P = 141` — **precisely arm B's committed count minus the inputs.** So the question
is per-value and crisp: is folding one value once cheaper than committing it?

A Poseidon2 S-box layer is degree `α+1`, not 2. `p3-sumcheck`'s `ProductPolynomial` is
degree-2 only, so the degree scaling is **modelled**, with two bracketing models carried
through rather than one flattering one (LOW: cost ∝ D−1. HIGH: cost ∝ (D+1)/3 × the
addition-chain mults for `x^α`).

| geometry | commit ns | fold LOW | fold HIGH | verdict |
|---|---|---|---|---|
| **BabyBear w16 α=7 (deployed)** | 54.7 | 76.8 | 131.7 | **COMMIT, by 1.4–2.4×** |
| KoalaBear w16 α=3 | 54.7 | 32.9 | 36.6 | **VIRTUALIZE, by 1.5–1.7×** |
| BabyBear w24 α=7 | 54.7 | 76.8 | 131.7 | COMMIT, by 1.4–2.4× |
| KoalaBear w24 α=3 | 54.7 | 32.9 | 36.6 | VIRTUALIZE, by 1.5–1.7× |

**CROSSOVER IN α: folding beats committing iff α ≤ 3 (degree ≤ 4), under both models.**

**CROSSOVER IN LAYERS**: the rule "virtualize while layer count < the exchange rate" evaluates
to a budget of **0.42–0.71 layers at α=7** and **1.49–1.66 at α=3**. A Poseidon2 round-chain
value participates in exactly one layer — so at α=7 the budget is spent before the first
layer, and at α=3 there is room for one and no more.

### The α=7 → α=3 win comes from arm B, not arm C

Arm B's ratio *grows* as α falls, because a smaller α buys its security with **more partial
rounds**, which is exactly where the 16:1 saving lives:

| geometry | arm A | arm B | ratio |
|---|---|---|---|
| BabyBear w16 α=7 | 352 | 157 | 2.24× |
| KoalaBear w16 α=3 | 464 | 164 | **2.83×** |
| BabyBear w24 α=7 | 720 | 237 | 3.04× |
| KoalaBear w24 α=3 | 768 | 239 | **3.21×** |

So the KoalaBear question the brief raised has **two** answers pointing the same way, and the
larger one is the cheap one.

---

## §5 — WHY THIS WAS NOT ALREADY DONE

Two prior measurements looked here and both missed arm B, in the same direction.

1. **`plonky3_prover.rs:504-513`** (2026-06-11, `PROOF-ECONOMICS.md §2c`) measured
   `sbox_registers = 1` — which **adds** 141 columns/perm (493 total) to cap degree at 3 —
   against the inline-x⁷ 352-column form, and correctly kept the inline form. **The grid was
   {352, 493}. 157 was never on it.** Both arms move *away* from arm B: one commits the S-box
   intermediates, the other commits the linear ones, and nobody committed neither.
2. **`Poseidon2RoundGates.lean §7`** closes with the deferral verbatim:

   > ⚠ And none of this is a licence to re-arithmetize: the algebra IS the deployed
   > permutation […] **A cheaper circuit would be a DIFFERENT circuit.**

   True, and not an objection. `breadstuffs/CLAUDE.md` names this exact move: correct fix
   identified, then declined because it changes a committed shape. Arm B *is* a different
   circuit; it computes the same permutation (§3's fidelity gate says so bit-exactly), leaves
   §6's KATs untouched (the round algebra does not change — only which intermediates get a
   column), and costs a VK rotation plus a chip re-emit. Under greenfield doctrine that is
   the price of ordinary work, not a blocker.

⚑ The descriptor param `sbox_registers: 1` is currently a **frozen pin describing a layout the
chip deliberately does not use** (`descriptor_ir2.rs:3524-3528`). Arm B is the moment to make
that field mean something or delete it.

---

## §6 — VERDICT

**C3's prediction is confirmed in direction and refuted in mechanism.**

- ✅ **Virtualizing the permutation beats committing its intermediates — measured 2.11×
  prover, 1.28× verifier, 1.25× proof, 2.24× committed felts, at identical security and
  identical constraint degree.** On the most-committed object in the prover.
- ❌ **The predicted 4–15× does not appear, and the predicted mechanism is the wrong one.**
  The win is *in-AIR* virtualization of degree-1 values — free, no sumcheck, no degree cost.
  The *sumcheck* virtualization the C3 framing had in mind (GKR over the round chain)
  **loses at α=7** against our own measured exchange rate, by 1.4–2.4×.
- ⚑ **The number that moved is the exchange rate itself: 78–308× in counted field
  multiplications, ~5× in measured wall-clock.** The threshold rule survives; the threshold
  does not. Every downstream use of "78×/308×" as a *wall-clock* budget needs re-reading —
  `notes/virtualization-verdict.md` §"What is actually ours", `docs/COMPOSITIONS.md` C3, and
  `docs/SELVAGE.md`'s marquee if it prices in time rather than in multiplications.
- ⚠ **The `map_write_chip` 227 ms vs `umem_write_read_nochip` 14.9 ms corroboration is not
  evidence for C3 as stated.** That 15× is a chip *presence* vs *absence* comparison — a
  whole extra table with its own LogUp, not a materialize-vs-virtualize fork on the same
  relation. It belongs to the "don't instantiate a chip you don't need" result, which is a
  different and also real one.

### What lands, and where

**In Lean — `metatheory/Dregg2/Circuit/Emit/Poseidon2RoundGates.lean`:** a `permEmissionNarrow`
beside `permEmission`, emitting 141 gates instead of 352:

- initial external layer: **no** aux binding — carry `extLayer seed` as definitions.
- external round `r`: unchanged (16 gates binding the post-state to `aux`).
- internal round `r`: **one** gate, `eSbox (state[0] + rc[r][0]) − auxLane r`, then rebind
  `state[0] := auxLane r` and apply `intLayer` to the **expression** state.
- `permOutLane` / `permFinalState` read the last external block, unchanged in meaning.

The existing §6 KAT agreement and §6b tree-vs-shared oracle both carry over as written, since
the round algebra is identical; the new emission needs its own agreement `#guard`s against the
same `Poseidon2BabyBearW16.perm`. Then `ChipTableEmit` re-derives `CHIP_AUX0 + 141 + 1 = 175`,
the JSON re-emits, and the Rust interpreter is untouched.

**Flag day**: chip table AIR JSON re-emit, `CHIP_WIDTH` 386 → 175, VK rotation, descriptor
`sbox_registers` pin re-decided, and every fixture carrying a chip trace re-generated. The old
shape must **refuse to load**, not be reinterpreted.

**Not indicated**: arm C (GKR) at α=7 on this box. Revisit at α=3, at higher blowup, or on
hardware where hashing does not vectorize as well — all three move the exchange rate the
right way, and the first two are already on the roadmap.
