# The two-regime calculator: built, with the regime in the TYPE — and soundcalc-lean has no license

2026-08-13. `minidregg/Assurance/TwoRegimeQueryBudget.lean` (656 lines,
`4b53ec4`+`d183b55`), 22 named theorems, 9 axiom pins all clean, **zero
`sorry`, zero `native_decide`, zero `#guard`, zero floats.**

## ⚑ soundcalc-lean: read, built green here, and NOT usable

Cloned to `/Users/ember/dev/soundcalc-lean`, **17049/17049 jobs green**, its
AxiomsGuard passes. Its claims hold up — real Mathlib proofs, certified √/log₂
enclosures, Goldilocks by Pratt certificate with `native_decide` kept out of
the primality path. **It is better engineered than our equivalent.**

**But: it has no LICENSE. Neither does `ethereum/soundcalc`.** `gh api` returns
`license: null` for both; no LICENSE file in any commit of soundcalc-lean's
history. Under default copyright **we may read it and not vendor, fork, or
depend on it.** That is the gating item and **it is one issue/email to fix** —
worth doing, since they are 8 hours from their last commit and clearly active.

**Two gaps that made building ours the right call anyway:**
1. **Their regime tag is NOT in the type** — exactly what we were sent to fix.
   `Regime` is a bare record of ℚ-valued functions, so `queryErr c (UDR F)` and
   `queryErr c (JBR F g)` are both `ℚ` and `min`/`+`/`≤` between them
   typechecks. There is an unused `inductive SupportedRegime` carrying a
   literal *"FEAT TODO … bind to actual regimes."* **They know; it is undone.**
   That is the natural upstream contribution.
2. **Their report cells are `example`s, not theorems** — 244 `example` vs 119
   `theorem`. Anonymous, un-citable, invisible to axiom accounting. **That is
   our own `#guard` sin in a better costume**, and the one thing not to copy.

**Two things to steal outright**: their `Regime.Standard` device makes the
catalogue regime-*polymorphic* with only two regime-specific proofs; and
⚑ **their CI fails if any module was not actually built** (*"this caught
OpenVM2.lean"*) — **precisely the gate we lack**, per PREFLIGHT's finding that
`Bfv/Mul.lean` and `Bfv/Smudging.lean` sit in no build target with 43
keystones unpinned.

## What ours does that no other artifact does

- **Regime in the type**: `QErr r` is indexed, so UDR and JBR errors are
  *different types* and cannot be summed, min'd or compared. `Regime.status`
  tags UDR `proven`, JBR `idealised` (BCIKS20 at m→∞ — an over-claim at every
  finite m, which our own FriLedger docstring already admits), CBR
  `withdrawn`; **`cbr_not_reportable` is a theorem.**
- **Two-sided by construction**, with `bits_unique` proving at most one `k`
  satisfies it — **the non-vacuity a one-sided `≤` cannot have.**
- **The one genuinely new technique**: a query error is a product of `q`
  survival factors, so **its SQUARE is rational at all three regimes** even
  though JBR's `1−θ = √ρ` is not. `bits_iff_real` proves the squared rational
  statement **equivalent** — not merely conservative — to the two-sided real
  statement. No enclosures needed; everything closes by kernel `norm_num`.

## ⚑ The deployed verdict: one config, three regimes, 96 bits apart

Knobs transcribed from named Rust constants, not assumed:

| config | knobs | **UDR** (proven) | **JBR** (idealised) | CBR (**withdrawn**) |
|---|---|---|---|---|
| **IR-v2 descriptor batch — the deployed mint** | lb 6, q 19, pow 16 | **34** | 73 | 130 |
| recursion tree default (weakest shipped) | lb 3, q 38, pow 14 | 45 | 71 | 128 |
| v1 prod / ZK / BN254 outer | lb 3, q 38, pow 16 | 47 | 73 | 130 |
| ⚠ **IR-v2 with a child minting 1 query** | lb 6, **q 1**, pow 16 | **16** | **19** | 22 |
| zkDTVM v0.8.0 (published proven-128) | lb 1, q 261, pow 20 | **128 ✓** | 150 | 281 |

**`FriLedger` has no UDR column at all**, so 34 was never in it. zkDTVM's 128
**reproduced exactly at UDR from our own formula** — and its JBR column would
read 150, which it does not claim: choosing the conservative regime and buying
261 queries to pay for it *is* the recipe.

**The unpinned `num_queries` is now priced**: confirmed at source
(`plonky3-recursion/.../fri/verifier.rs:1378` takes the count from the proof;
`FriVerifierParams` has no such field, while the *native* verifier pins it). A
child minting one query drops the column **73 → 19 (JBR), 34 → 16 (UDR)**. And
the sharp framing: **the field wall is compiled into the verifier; the query
wall is carried in the proof.**

## ⚑ "Conjectured 130" is CBR-shaped — definitively

`FriLedger.lean:204`: `capacityBits := numQueries * logBlowup + powBits` =
19·6+16 = 130. `q·logBlowup` is `−q·log₂ρ`, i.e. `θ = 1−ρ` — **the capacity
regime, the one `ethereum/soundcalc` deleted** in ffaeb81 ("Remove CBR due to
DG25 and CS25"). **Our tree already knew in two places**; the memory index
still headlines it as the optimistic half of a triple that mixes a CBR query
number, a JBR-family commit number, and a field-size ceiling as if they were
comparable. `ir2_only_the_withdrawn_regime_clears_128` now says it
mechanically: **57 of the 130-vs-73 headroom is the withdrawal, not a knob.**

**Suggested index line: UDR 34 / JBR 73 / (withdrawn) 130**, with 2^123.6
moved to the LogUp row where it belongs.

## Both walls, and they need different fixes

`logupErr = K·H·R/|F|` **takes no `Regime`** (`logup_carries_no_regime`) — it
is a root count, not a decoding-radius bound. At the descriptor validator's own
admitted caps it reads **96 bits at BabyBear⁴, 126 at BabyBear⁵**. **Ext5 buys
30 bits there and exactly ZERO on the query column.** Derived constant worth
keeping: at BabyBear⁴ a LogUp cell clears 100 bits only if `K·H·R ≤ 2^23.63`,
which at the deployed 2^21 row ceiling leaves **`K·R ≤ 6`**.
