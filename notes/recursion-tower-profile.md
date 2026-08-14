# The recursion/wrap tower, profiled — measured 2026-08-14

**Status: COMPLETE for layers 0/1/3/4.** Every figure is `[MEASURED]` (an exact count off a real
object), `[DERIVED]` (arithmetic on measured geometry using a law validated elsewhere), or
`[CALIBRATED]` (a measured rate from the leaf, transported — flagged at every use).

`notes/phase-profile.md` §0 blind spot 6 says *"the recursion/leaf-wrap tower is not measured
here."* Four wins landed on the leaf prover this week and each deferred its real value to this
tower. This note measures it. **All four deferrals were wrong, three of them by more than an order
of magnitude, and the reason is the same every time: the tower was priced as if it were a bigger
leaf. It is not — it is a machine that turns a child's VERIFIER into its own TRACE.**

| the deferral | what it assumed | **measured** |
|---|---|---|
| `permEmissionNarrow` "approaches 1.97× as `s → 1`, and the tower is ~75% in-circuit Poseidon2" | the tower's Poseidon2 is the chip the lever narrows | **the tower contains no `CHIP_TABLE_AIR_JSON` at all**; the lever's factor on a leaf wrap is **1.000×** (§4) |
| in-circuit Poseidon2 is "~75%" of the tower | — | **36.45%** of a leaf wrap's committed cells, **53.98%** of the apex/shrink layer's (§3) |
| the blowup trade is prover ÷15.19 against verifier ×2.28 | the ×2.28 is a *verify* cost | the ×2.28 (here **×2.351**) is a *prove* cost, paid as trace by the wrap: **net ≈ 65× worse** across the tower (§5) |
| hash-bound at 5.0–7.2× | the margin carries up | **hash-bound at ≈ 3.1–3.3×** — `log₂h` eats the margin (§6) |

Harness: `breadstuffs/circuit-prove/tests/recursion_tower_profile.rs` (new), extending
`apex_shrink_trace_anatomy.rs` and `leaf_wrap_mint_blowup_repricing.rs`.
Raw logs: `scratchpad/emb-tower-{l0,l1,l3}.log`.

---

## 0. ⚑ THE INSTRUMENT — and why the brief's two instruments do not reach this workload

### (a) A permutation counter is BLIND to in-circuit Poseidon2, by construction

`ir2_phase_profile.rs` §D counts calls to `Permutation::permute_mut`. An **in-circuit** permutation
is not a call — it is a *row of an AIR*, evaluated by the same LDE/quotient/Merkle machinery as
every other row. Pointing §D at a tower layer reports that layer's **native** hashing and reports
**zero** for the thing the 75% claim is about.

| population | what it is | what sees it |
|---|---|---|
| **native** Poseidon2 | this layer hashing its own committed trace into a Merkle tree | the §D permutation counter |
| **in-circuit** Poseidon2 | rows of `poseidon2_perm/baby_bear_d4_w16` — the child's Merkle paths and challenger re-executed as constraints | the **circuit op census** |

So the primary instrument here is the **op census**: `Circuit::ops` is built deterministically from
the child proof's shape, and counting `Op::NonPrimitiveOpWithExecutor` by `executor.op_type()` gives
the **exact in-circuit permutation count**. Exact, hardware-free, contention-immune — the properties
§D was chosen for. `apex_shrink_trace_anatomy.rs` already ran this census but printed **one summed
`NonPrimitive ops`** across poseidon2 *and* recompose, so the count was not readable off it.

### (b) ⚑ The tower is MONOMORPHIC — §D cannot be injected at all `[MEASURED, at source]`

`prove_vm_descriptor2_for_config<SC>` (`circuit/src/descriptor_ir2.rs:7609`) is generic. Every layer
above it is not:

```rust
// circuit-prove/src/ivc_turn_chain.rs:1830 — a config VALUE, not a config TYPE
pub fn prove_descriptor_leaf_rotated_with_config(
    desc: &EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String>
```

Three independent welds, any one sufficient:

1. `RecursableAir` (`plonky3_recursion_impl.rs:138-148`) names `DreggRecursionConfig` in four
   supertrait bounds, so even the AIR-generic entry points cannot be instantiated elsewhere.
2. `impl FriRecursionConfig for DreggRecursionConfig` is orphan-rule-welded to the concrete type —
   `recursion-verify/src/config.rs:12-14` says so, as the reason the type was moved not copied.
3. That impl's `prepare_circuit_for_verification` hardcodes `default_babybear_poseidon2_16()`
   (`config.rs:259`); `MyHash`/`MyCompress`/`Challenger`/`Dft` are concrete aliases
   (`config.rs:102-118`).

`p3_recursion::prove_next_layer<SC, A, B, D>` **is** generic (`recursion/src/recursion.rs:549`) — the
weld is entirely ours. **A counting twin is undone work, not a boundary**: a second
`FriRecursionConfig` impl over counting hash types plus a `RecursivePcs` instantiation. It is the one
thing that would make the tower's native hash side as exact as the leaf's.

The only other `<SC>` is `shrink_apex_to_outer<SC: OuterShrinkConfig>` (`apex_shrink.rs:161`), and it
still names `DreggRecursionConfig` in its inner slots.

**Where §D DOES reach — and it is the decisive place.** The child of layer 1 is layer 0, which *is*
generic. §2 uses it there, and that turns out not to be a consolation prize.

### (c) ⚠ `circuit-prove`'s 3 private wgpu devices do NOT bear on these numbers

`gpu_backend.rs:269` (`shared_gpu()`), `gpu_backend.rs:6308` (`init_gpu`, wasm-only),
`gpu_hidingfri_fold.rs:87` (`FoldGpu::new`, a second device labelled `hidingfri-fold-device`). The
arena consolidation covered `fhegg-fhe` only. Every number here comes from circuit construction,
table-AIR extraction, and a CPU prove under a counting config — no GPU is touched. A later lane
measuring tower *wall clock* on the GPU path puts them back in scope.

### (d) ⚠ Wall clock is not evidence here

Load average 6–34 across this run, 40 login sessions. Two elapsed times appear in the logs, both
labelled upper bounds; **nothing in this note is derived from a clock** except the single constant
`Y`, which `field-op-counts.md` §4 measured and this note re-uses unchanged.

### (e) Denominators, named up front

Three appear below and they differ by 37 points on the same table:

* **`cells(main+prep)`** — every committed cell. The honest one: preprocessed columns are LDE'd and
  Merkle'd exactly like main ones.
* **`cells(main)`** — main trace only. What a reader who forgot the preprocessed side computes.
* **`rows`** — table rows ignoring width. Meaningless for cost; shown to mark the spread.

Every share below states which.

---

## 1. THE TOWER'S STRUCTURE `[MEASURED, at source]`

Five proving layers plus a non-proving export. The generating rule is one function —
`recursion_layer_over(child)` (`recursion-verify/src/config.rs:571`): **verify at the child's mint
engine, mint at the recursion engine.** `create_recursion_config()` is its fixed point.

| L | name | entry point | verify engine | **mint engine** |
|---|---|---|---|---|
| 0 | IR-v2 descriptor batch (the leaf) | `prove_vm_descriptor2_for_config` (`descriptor_ir2.rs:7609`) | — | lb **6** / arity 8 / **19** q / pow 16 |
| 1 | **leaf wrap** | `prove_descriptor_leaf_rotated_with_config` (`ivc_turn_chain.rs:1830`) | lb 6 / arity **2** / 19 q / pow 16 | lb **3** / arity 2 / **38** q / pow **14** |
| 2 | fold / aggregation nodes (binary tree) | `aggregate_tree` (`ivc_turn_chain.rs:6095`) | lb 3 / 38 q / pow 14 | same |
| 3 | apex (root of the fold tree) | `prove_turn_chain_recursive` (`ivc_turn_chain.rs:2797`) | lb 3 / 38 q / pow 14 | same |
| 4 | **apex shrink** (BN254-native) | `shrink_apex_to_outer<SC>` (`apex_shrink.rs:161`) | lb 3 / 38 q / pow 14 | lb **3** / 38 q / pow **16** (BN254) |
| 5 | export (gnark / Mina) | `export_real_shrink_fri_fixture` | — | no new STARK |

Capacity ledgers (`lb · q + pow`): leaf **130**, layers 1–3 **128 exactly, zero headroom**
(`config.rs:54-57`), outer **130**.

Layers 1–4 all commit **the same table set**, because every one of them is the same kind of object —
a `p3-circuit` verification circuit compiled to tables:

`Const` · `Public` · `Alu` · `poseidon2_perm/baby_bear_d4_w16` · `recompose` · `expose_claim`

`poseidon2_perm/baby_bear_d4_w24` is registered (`config.rs:268`) and has **0 ops in every fixture
measured here**, confirming `WRAP-NATIVE-HASH-DECISION.md:107`'s "the verifier hashes ONLY width-16"
on two new fixtures.

⚠ **There is no `2^20` constant in the tower.** `phase-profile.md` §0.6 says "h = 2^20"; heights are
*emergent* from the op-list and the `TablePacking`, and measured they run `2^11`–`2^20`. **Height is
a property of the child, not of the tower.**

### ⚑ 1a. The tower's Poseidon2 is NOT the chip `permEmissionNarrow` narrows

This is a **display-name collision**, of exactly the class `a-display-name-is-not-a-key` records —
here inside a cost model.

| | the Lean chip | the tower's table |
|---|---|---|
| name | `dregg-ir2-chip-v1` (`CHIP_TABLE_AIR_JSON`) | `poseidon2_perm/baby_bear_d4_w16` |
| authored in | **Lean** — `Dregg2/Circuit/Emit/Poseidon2RoundGates.lean` | **upstream Rust** — `p3-poseidon2-circuit-air` |
| committed width | **386** (→ 175 narrow) | 300 main + 24 prep |
| registered by | the IR-v2 descriptor's table set | `FriRecursionConfig::prepare_circuit_for_verification` (`config.rs:259-273`) |
| what `permEmissionNarrow` does to it | 352 → 141 aux lanes | **nothing** |

`permEmissionNarrow` re-emits `CHIP_TABLE_AIR_JSON`. **A tower layer's own trace does not contain
it.** The lever reaches the tower only *through the child* — §4 measures that reach and it is zero.

---

## 2. ⚑ THE IDENTITY THE WHOLE TOWER TURNS ON, MEASURED TWICE

Two instruments, no shared code path, on the deployed rotated transfer leaf and its wrap:

| instrument | object | result |
|---|---|---:|
| **permutation counter** (§D's `CountingPerm`, re-used) | the child's **native verify** at the wrap's verify engine `(lb 6, arity 2, q 19, pow 16)` | **38,168** |
| **circuit op census** (`Op::NonPrimitiveOpWithExecutor` by `op_type()`) | the leaf wrap's **in-circuit** `poseidon2_perm/baby_bear_d4_w16` ops | **38,168** |

> ### ⚑ **Identical to the unit.** A leaf wrap's Poseidon2 table IS the child's verifier, row for row.

That is no longer a model, and it is the lever that makes the rest of this note quantitative:
**anything that changes the child's verifier cost changes the wrap's biggest table one-for-one.**
`blowup-drop.md`'s "verifier ×2.28" is therefore not a verify-side price at all — it is a **prove**
price, paid by the next layer up, as trace.

The same counter on the same child at the blowup drop:

| child engine | prove perms | verify perms |
|---|---:|---:|
| `(lb 6, arity 2, q 19, pow 16)` — **deployed** | **6,177,520** | **38,168** |
| `(lb 6, arity 2, q 19, pow 0)` grind-free | 6,062,832 | 38,168 |
| `(lb 2, arity 2, q 57, pow 16)` — **the drop** | **405,741** | **89,739** |
| `(lb 2, arity 2, q 57, pow 0)` grind-free | 389,357 | 89,739 |

**prover ÷15.23 (grind-free ÷15.57) · verifier ×2.351.** `blowup-drop.md` reported ÷15.19 and ×2.28
on the *unrotated* batch at arity 8; on the *deployed rotated* child at the *deployed arity-2 wrap
engine* it is ÷15.23 and **×2.351**. Same trade, re-derived on the object that is actually wrapped.

⚠ `prove perms` is a difference of two counted quantities (prove + self-verify, minus a standalone
verify) — `prove_vm_descriptor2_for_config` runs its own `check`. It is exact because both calls are
the same function on the same proof; recorded because reading the raw snapshot as prover work is the
trap `blowup-drop.md` §D2 documents.

---

## 3. ⚑ WHAT FRACTION OF TOWER WORK IS IN-CIRCUIT POSEIDON2? `[MEASURED]`

Real geometry from `get_airs_and_degrees_with_prep` — the same call the prover makes, at
`ProveNextLayerParams::default()` (`TablePacking::new(1, 4)`, `ConstraintProfile::Standard`).

### 3a. Layer 1 — the deployed leaf wrap (child: rotated transfer, mint lb 3)

| table | log₂ rows | rows | main_w | prep_w | cells (main+prep) |
|---|---:|---:|---:|---:|---:|
| Const | 12 | 4,096 | 4 | 6 | 40,960 |
| Public | 11 | 2,048 | 4 | 2 | 12,288 |
| Alu | 18 | 262,144 | 76 | 59 | 35,389,440 |
| **`poseidon2_perm/baby_bear_d4_w16`** | **16** | 65,536 | **300** | 24 | **21,233,664** |
| recompose | 18 | 262,144 | 4 | 2 | 1,572,864 |
| | | | | **TOTAL** | **58,249,216** |

`degree_bits = [12, 11, 18, 16, 18]`. Op census: `Alu 441,684` (of which **HornerAcc 390,716 =
88.5%**), `recompose 160,263`, `poseidon2 38,168`, `Hint 66,777`, `witness_count 1,123,022`.

### 3b. Layer 3/4 — the apex-verifier / shrink circuit (2-turn chain, mint lb 3)

| table | log₂ rows | rows | main_w | prep_w | cells (main+prep) |
|---|---:|---:|---:|---:|---:|
| Const | 9 | 512 | 4 | 6 | 5,120 |
| Public | 9 | 512 | 4 | 2 | 3,072 |
| Alu | **16** | 65,536 | 76 | 59 | 8,847,360 |
| **`poseidon2_perm/baby_bear_d4_w16`** | **15** | 32,768 | **300** | 24 | **10,616,832** |
| recompose | 15 | 32,768 | 4 | 2 | 196,608 |
| | | | | **TOTAL** | **19,668,992** |

`degree_bits = [9, 9, 16, 15, 15]`. Op census: `Alu 138,066` (HornerAcc 104,348 = 75.6%),
`recompose 28,996`, **`poseidon2 22,626`**, `witness_count 279,722`.

### 3c. ⚑ THE ANSWER, with all three denominators

| layer | **cells(main+prep)** | cells(main) | rows |
|---|---:|---:|---:|
| **L1 leaf wrap** (rotated transfer child) | **36.45%** | 48.36% | 11.00% |
| **L1 leaf wrap** (Mina accumulator child — `leaf_wrap_mint_blowup_repricing.rs`) | **36.45%** | 48.36% | 11.00% |
| **L3/L4 apex-verifier / shrink** | **53.98%** | 65.77% | 24.81% |

> ### ⚑ **"~75% in-circuit Poseidon2" is not reached at any denominator on any layer measured.**
> A leaf wrap is **36.45%** of committed cells; the apex/shrink layer is **53.98%**. The closest any
> figure comes to 75 is the apex layer's *main-only* 65.77% — the flattering half of a pair.

⚑ **And 36.45% is not a coincidence across two unrelated children.** The Mina-accumulator wrap's
`degree_bits` are `[14, 13, 20, 18, 20]`; the rotated-transfer wrap's are `[12, 11, 18, 16, 18]` —
**exactly two rungs apart, table for table**. The widths are identical (they are the same AIRs), so
the share is a **structural invariant of the leaf-wrap circuit**: `Alu` and `recompose` sit exactly
two rungs above `poseidon2_perm`, whatever the child. The apex layer differs (53.98%) because there
`Alu` sits only *one* rung above.

### 3d. ⚠ Four documented shapes are stale, and each flatters

* **`degree_bits [9,9,15,14,15]`** is recorded in `docs/deos/APEX-VERIFIER-AIR-REDUCTION.md` and
  `accumulator.rs:249-251`. Measured on a real 2-turn chain it is **`[9,9,16,15,15]`** — `Alu` and
  `poseidon2` each **one rung taller, i.e. 2× the committed cells**. Neither source states the chain
  length it was taken at, and chain length is exactly what moves it.
* **`apex_shrink_trace_anatomy.rs:57`** hardcodes `const LOG_BLOWUP: usize = 6` and prints
  *"MODEL perms @blowup64"*. `OUTER_FRI_LOG_BLOWUP` has been **3** since the rebalance
  (`dregg_outer_config.rs:134`, which itself records the ~8× measurement that moved it). **That model
  over-prices the shrink's hashing by exactly 8×** — 165,806,080 against 20,725,760 leaf-sponge
  permutations on identical geometry.
* **`WRAP-NATIVE-HASH-DECISION.md:102-106`** gives *"Real Poseidon2-w16 perm count ≈ 10,000–13,000
  (central ~11,000)"* via `perms(m) = 19·[(m+5)(m+6)/2 + 5m + 9] + 3636`. **The `19` is the query
  count**, hardcoded; the apex runs at **38** (`RECURSION_FRI_NUM_QUERIES`). Measured: **22,626 =
  2.06× the recorded central value**, and `22,626/2 = 11,313` sits inside the recorded band. The doc
  was taken at `q = 19`, the engine moved, nothing re-derived it.
* **`phase-profile.md` §0.6's "h = 2^20"** — see §1.

---

## 4. ⚑⚑ WHAT `permEmissionNarrow` IS ACTUALLY WORTH HERE — **1.000×**

### 4a. The claim under test

`narrow-witness-gen.md` §3.4:

> *"`s = 13.35%` is one descriptor… Chip-heavy goldens and above all the **recursion tower**, which
> is ~75% in-circuit Poseidon2, run `s` far higher, and at `s → 1` the batch factor approaches the
> per-chip 1.97×."*

Two things must hold: (i) the tower is ~75% in-circuit Poseidon2 — **measured 36.45%** (§3c); and
(ii) `s` means the same thing in the tower as in the batch. **(ii) is false, and it is the
load-bearing half.** In the batch `s` is *the fraction of committed width that is the object the
lever narrows*. In the tower **that object does not appear** (§1a).

> **Substituting the tower's 36.45% for the batch's 13.35% in the lever's formula is a category
> error: the two percentages measure different objects that share the word "Poseidon2".**

### 4b. The three channels the lever can reach through — measured on the deployed child

The deployed rotated transfer batch commits three main traces (`[MEASURED]`, off the rebuilt AIR set
and the proof's own `degree_bits`):

| instance | width | log₂ rows | rows | cells | `⌈w/8⌉` |
|---|---:|---:|---:|---:|---:|
| main descriptor | 3,350 | 6 | 64 | 214,400 | 419 |
| **`dregg-ir2-chip-v1`** | **386** | 8 | 256 | 98,816 | **49** |
| `dregg-ir2-byte-v1` | 2 | 4 | 16 | 32 | 1 |
| **Σ** | **3,738** | | | **313,248** | **469** |

A 386 → 175 chip is `Δwidth 211` and `Δ⌈w/8⌉ 27`, so:

| # | channel into the wrap | scales as | what narrowing removes |
|---|---|---|---|
| 1 | in-circuit Merkle leaf hash of the chip's opened row, per query | `q · ⌈w/8⌉` | `27/469` = **5.76%** of per-query leaf hashing |
| 2 | in-circuit reduced-opening Horner over opened columns | `q · Σw` | `211/3738` = **5.64%** of the Horner term |
| 3 | in-circuit OOD constraint evaluation of the chip's gates — **once** | `O(1)` in `q` | 2,668 → 2,246 field ops, one evaluation, against `Alu 441,684` |

⚠ **What channel 1 does not touch: the Merkle PATH.** ~~Most in-circuit permutations are 2-to-1
compressions along `q` paths of depth `log₂(LDE rows)`~~ — a function of the child's *height* and
*blowup*, never its width.

> ### ⚠ **CORRECTED 2026-08-14 by `notes/leaf-vs-recursion.md` §2: the Merkle PATH term is 5.9%, not "most".**
> A blowup sweep at fixed `q` measures `Δperms/Δm = 209 = 19 × 11` **exactly constant** across
> `m ∈ [9, 16]` — so paths are `q · (11m − 36) = 2,242` of 38,168. **94.1% of in-circuit
> permutations scale with the child's committed WIDTH, not its height.** The struck sentence was a
> model carried in, not a count; this section's own `8,911 = 23.3%` was already the leaf-hashing
> term and nothing here ever priced the paths. The lever is width.

Applying channel 1 to the main commitment round (`q · Σ⌈w/8⌉ = 19 × 469 =
8,911` of the wrap's 38,168 in-circuit permutations, i.e. 23.3%), narrowing removes
`19 × 27 = 513` — **1.34% of the wrap's poseidon2 table.** Channel 2 removes ≈ 2% of `HornerAcc`.

### 4c. ⚑ THE VERDICT — the power-of-two padding absorbs the entire lever

Tower table heights are padded to `2^k`. Measured:

| table | ops today | rows | narrow ops | rows |
|---|---:|---:|---:|---:|
| `poseidon2_perm/baby_bear_d4_w16` | 38,168 | **2^16** | ~37,655 (−1.34%) | **2^16** |
| `Alu` | 441,684 | **2^18** | ~433,700 (−1.8%) | **2^18** |
| `recompose` | 160,263 | **2^18** | ~157,000 | **2^18** |

38,168 sits **16.5% above `2^15`**; a 1.34% cut does not reach it. Dropping `Alu` a rung needs a
50% cut.

> ### ⚑ **`permEmissionNarrow` changes the leaf wrap's committed geometry by EXACTLY ZERO. Every table stays at the same power-of-two height. The tower factor is 1.000×, not 1.97×.**

### 4d. And at the leaf, on the DEPLOYED descriptor, it is 1.077× — reproducing the reported figure

`[DERIVED, on measured geometry]` The lever's leaf-level value recomputed on the *rotated* child
(the one that is actually wrapped), using the `⌈w/8⌉` leaf-sponge law at the deployed `lb 6`:

| committed set | leaf-sponge + compress perms | narrow | factor |
|---|---:|---:|---:|
| main traces only | 2,541,565 | 2,099,197 | **1.2107×** |
| **whole prove** (counted: 6,177,520 — FRI-fold trees, LogUp traces, quotient chunks and the grind do not shrink) | **6,177,520** | 5,735,152 | **1.0771×** |

The chip is a larger share of the *rotated* child's main-trace hashing than of the unrotated one
(256 rows against 8), so the main-trace factor is 1.21× rather than 1.10× — **and the whole-prove
factor lands at 1.0771×, reproducing `narrow-witness-gen.md` §3.3's 1.0760× by a completely
different route** (that note derived it from opened-value counts off the proof; this one from the
`⌈w/8⌉` law against a counted total). Two instruments, two descriptors, same answer.

> ### ⚑ **Honest statement of the win: `1.077×` on the deployed leaf, `1.000×` on the tower above it. The "approaching 1.97×" clause has no workload in this repo behind it.**

⚠ This does **not** make `permEmissionNarrow` worthless — it is a genuine Pareto move (same
`max_constraint_degree`, fewer columns, fewer field ops per row, all as named theorems) and 1.077×
for free is 1.077×. It makes the *deferral* wrong: the value is at the leaf, and there is no larger
prize one layer up waiting on the Rust witness generator.

---

## 5. ⚑⚑ WHAT THE BLOWUP TRADE COSTS **HERE** — net ≈ 65× worse

`blowup-drop.md` §6 states the trade as **prover ÷15.2 · verifier ×2.28 · wire ×~2.4 · UDR +20 bits
· row ceiling ×16**, and §7 declines to land it globally on *wire bytes and light-client verify ms*.

**That decision is right, and the reason given is the small one.** §2 measured the identity: the
"verifier" side of this trade is not something a light client pays once — it is what the leaf wrap
**commits as trace**, every time, for every turn.

### 5a. What moves in the wrap `[DERIVED from measured op counts]`

| wrap table | driver | today | after `(2,57)` | rows |
|---|---|---:|---:|---|
| `poseidon2_perm` | the child's verify perms (§2, **measured**) | 38,168 | **89,739** (×2.351) | `2^16` → **`2^17`** |
| `Alu` | `HornerAcc` ∝ `q` (19→57); the 50,968 non-Horner ops are OOD evaluation and do not move | 441,684 | ~1,223,100 (×2.77) | `2^18` → **`2^20`** |
| `recompose` | ∝ `q` | 160,263 | ~480,800 (×3.0) | `2^18` → **`2^20`** |

⚑ **The power-of-two ceiling is the fourth multiplier and nobody prices it.** A ×2.351 on a table
58% full lands at ×2 in cells; a ×2.77 on `Alu` lands at ×4.

| | cells (main+prep) | native perms `[DERIVED]` |
|---|---:|---:|
| L1 wrap, deployed | 58,249,216 | 66,207,740 |
| L1 wrap, after the drop | **190,369,792** | **220,348,412** |
| | **×3.268** | **×3.328** |

### 5b. The comparison, in one unit

The geometric leaf-sponge law sees main + preprocessed traces only; the prover also commits LogUp
permutation traces, quotient chunks, every FRI fold round's tree, and the grind. **Calibrated on the
child, where both numbers exist**: derived 2,541,565 against counted 6,177,520 = **×2.430**. That
factor is applied to both sides, so it cancels in every ratio below.

| | native Poseidon2 permutations |
|---|---:|
| L0 leaf prove, deployed `(6,19,pow16)` — **counted** | **6,177,520** |
| L1 leaf wrap, deployed — derived, ×2.430 | **≈ 160,900,000** |
| **the wrap costs, per leaf** | **26.05×** the leaf's entire prove |

> ### ⚑ **The layer that verifies the leaf costs 26× what the leaf costs to prove.** So:
>
> * the drop **saves 0.934** leaf-proves at L0 (6,177,520 → 405,741);
> * the drop **costs 2.328 × 26.05 = 60.6** leaf-proves at L1;
> * **net +59.7 leaf-proves — a ≈ 65× loss** — per turn, before layers 2/3/4.

⚠ **READ THAT LAST LINE PRECISELY — it has been misquoted twice.** `65×` is the ratio of the
**loss to the saving**. The per-turn **total** goes from `1 + 26.05 = 27.05` leaf-proves to
`0.066 + 86.65 = 86.72` — **×3.21**, and `leaf-vs-recursion.md` §4b's independent grid puts it at
**×2.96**. It is *not* "65× worse per turn"; that reading has now appeared in this note's own §8
summary and in a downstream lane brief. The trade is still firmly negative; the magnitude is 3×.

### 5c. ⚠ The conditional, because it is the whole verdict

**The blowup drop is `prover ÷15.23` if and only if the leaf is the terminal artifact.** The moment
a leaf is wrapped — which `prove_turn_chain_recursive` does to *every* turn — the sign flips, and it
flips by two orders of magnitude.

**This is not an argument for `lb 6` either.** It is an argument that **the leaf's blowup is not a
leaf knob.** It is a tower knob, and every grid it has appeared in prices exactly one layer of a
five-layer machine. The right shape for that grid is `(leaf prove) + 26 × (wrap growth)`, and no
existing table has the second term.

⚠ Not modelled: the drop's `+20 UDR bits` and `×16 row ceiling`
(`max rows = 2^(27−lb)`: `2^21 → 2^25`). The row ceiling in particular is a *capability*, not a
cost, and this note does not weigh it against the 65×.

---

## 6. ⚑ IS THE TOWER HASH-BOUND? — yes, at ≈ 3.1–3.3×, not 5.0–7.2×

Same conditional form as `field-op-counts.md` §5, so the two are directly comparable:

> **hash-bound iff `Y > X`, where `X ≡ (M + r·A)/P` and `Y ≡ t_perm/t_mul`.**

`r = 0.803` and `Y = 890` (largest working set) … `898` (primary estimator) are re-used unchanged —
the only measured-on-a-clock constants in this note. `X` is what this lane computes.

### 6a. The two exact laws

**`P` — native permutations.** `PaddingFreeSponge<Perm,16,8,8>` absorbs `RATE = 8` base elements per
permutation ⇒ `⌈w/8⌉` per LDE row; `TruncatedPermutation<Perm,2,8,16>` is one permutation per 2-to-1
node ⇒ `(leaves − 1)` per tree, one tree per distinct height. Read off `config.rs:104-105`.

**`M`, `A` — the DFT term.** A coset LDE of a `w × h` matrix by `2^b` is one iDFT of size `h` plus
`2^b` coset DFTs of size `h`, so

```
ADD = SUB = w · (h/2) · log₂h · (1 + 2^b)
```

⚑ **Not a model.** It reproduces all four of `field-op-counts.md` §3's counted points **exactly** —
`(64,8,+3) → 13,824` · `(64,8,+6) → 99,840` · `(256,8,+3) → 73,728` · `(256,8,+6) → 532,480`. `MUL`
is `1.060–1.134 × ADD`, the band measured over those same four points; both ends reported.

### 6b. X across the tower

| layer (mint blowup) | tallest table | `P` | `X` — **DFT + Merkle only** | `Y/X` |
|---|---:|---:|---:|---:|
| L0 child (lb 6) | `2^8` | 2,541,565 | **70.8 … 72.8** | 12.2 … 12.7× |
| **L1 leaf wrap (lb 3)** | `2^18` | 66,207,740 | **182.2 … 187.3** | 4.75 … 4.93× |
| L1 after the blowup drop (lb 3) | `2^20` | 220,348,412 | 200.3 … 205.9 | 4.32 … 4.48× |
| **L3/L4 apex-verifier (lb 3)** | `2^16` | 21,516,285 | **169.4 … 174.1** | 5.11 … 5.30× |

### 6c. ⚑ The verdict, with the calibrated term flagged

`X` above counts **only** LDE/DFT and the Merkle commit. The leaf's full `X` also counts the **open
phase**, and at the leaf that is the *majority* of it:

| leaf | `X` full (`field-op-counts` §5) | `X` DFT-only (recomputed) | open-phase share |
|---|---:|---:|---:|
| b = 3 | 177.7 | 55.9 | **68.5%** |
| b = 6 | 127.7 | 51.9 | **59.4%** |

The open phase is a reduced opening over the **whole LDE domain**, so both it and `P` are
per-LDE-cell — `X_open` is essentially **`h`-independent**, ≈ 76–122. `X_DFT`, by contrast, carries
`log₂h` and nothing else does. Hence `[CALIBRATED]`:

> ### ⚑ **`X_tower ≈ 280` (L1) and `≈ 270` (L3/L4), against the leaf's `X = 177.7` at the same blowup. The tower IS hash-bound — at `Y/X ≈ 3.1–3.3×`, not the leaf's 5.0–7.2×.**
>
> **The whole difference is one term: `log₂h`.** The DFT carries it; the Merkle leaf sponge does
> not. The leaf's tables are 16–256 rows; a leaf wrap's are `2^18`. Width cancels.

**Robustness.** Breaking the verdict needs the open phase at **7×** the calibration (`X > 890`). At
2× it, `X ≈ 380` and `Y/X ≈ 2.3×` — still hash-bound. The *direction* is safe; the **margin** is
what moved, and it moved by 1.6–2.3×.

⚠ **Three things `X` here does not count, and they do not all point the same way.**
(i) `get_airs_and_degrees_with_prep` returns main + preprocessed only; the prover also commits LogUp
traces, quotient chunks and every FRI-fold tree (the ×2.430 of §5b) — these inflate `M`, `A` **and**
`P` together, so `X` moves little. (ii) Matrices sharing a height are hashed into one tree, which
*lowers* `P` slightly and so *raises* `X`. (iii) The grind is excluded; including it lowers `X`.

⚠ **`Y` does not transfer to layer 4.** The BN254 outer MMCS is
`MultiField32PaddingFreeSponge<BabyBear, Bn254, _, 3, 2, 1>` — **16** BabyBear limbs per
permutation, not 8 — and the permutation is a BN254 `t = 3` Poseidon2, not a BabyBear `t = 16` one.
The §3b geometry is identical at both engines (the AIRs are field-agnostic) but the *permutation
count* at the outer engine is **half** the printed figure, at a wholly different unit cost. **The
hash-bound verdict above is for layers 1–3 only**; layer 4 needs its own `Y`, which nobody has
measured.

---

## 7. ⚠ REDS AND DRIFT FOUND ON THE WAY IN — reported, not worked around

1. **`rotation_batchstark_leaf_smoke.rs` is RED at HEAD, twice over, with no `#[ignore]` and no
   feature gate.**
   * `:100` asserts `desc.trace_width == GRAD_ROT_WIDTH`. Measured: the registry's
     `transferVmDescriptor2R24` is **1,896**, `GRAD_ROT_WIDTH` evaluates to **1,841**, and its own
     source comment (`circuit/src/effect_vm/trace_rotated.rs:138`) says **1,647**. Three numbers.
   * Past that, `generate_rotated_effect_vm_trace` emits a base row of width **847** against the
     descriptor's `producer_owned_width` of **857**, and the prover refuses:
     *"columns 847..857 are filled by no prove-time weld, so zero-padding them would fold the AIR
     over values this producer never supplied."*

   The working path — the one the apex fold actually takes — is
   `generate_rotated_effect_vm_descriptor_and_trace_wide`, via `mint_rotated_participant_leg`
   (`turn-prover/src/rotation_witness.rs:159`). Its descriptor is `trace_width 1804 / pi_count 61`,
   still ≠ `GRAD_ROT_WIDTH`. This harness prints both rather than asserting.
2. **`apex_shrink_trace_anatomy.rs:57`'s `LOG_BLOWUP = 6`** against `OUTER_FRI_LOG_BLOWUP = 3` — its
   whole "MODEL perms @blowup64" column is 8× the deployed cost (§3d).
3. **`APEX-VERIFIER-AIR-REDUCTION.md` / `accumulator.rs:249`'s `[9,9,15,14,15]`** — measured
   `[9,9,16,15,15]`, two tables a rung taller (§3d).
4. **`WRAP-NATIVE-HASH-DECISION.md`'s ~11,000 in-circuit permutations** — measured 22,626, because
   the formula hardcodes `q = 19` and the engine runs 38 (§3d).
5. **`phase-profile.md` §0.6 and this lane's brief both say the tower is `h = 2^20`.** No such
   constant exists; measured heights are `2^11`–`2^20` and are set by the child (§1).

---

## 8. WHAT THIS DECIDES

* **The tower is not a bigger leaf. It is a machine that turns a child's VERIFIER into its own
  TRACE**, at 38,168 in-circuit permutations = 38,168 verifier permutations, exactly (§2). Every
  cost intuition carried up from the leaf inverts at that seam, and all four of this week's
  deferrals carried one up.
* **A leaf wrap costs 26× the leaf it wraps.** Any knob priced on the leaf alone is priced on 3.7%
  of the object.
* **`permEmissionNarrow` is 1.077× at the deployed leaf and 1.000× above it.** Bank it at the leaf;
  the Rust witness generator (`narrow-witness-gen.md` §4 item 3) is still the blocker and still
  worth clearing — for 1.077×, honestly labelled.
* **The blowup drop is a tower knob wearing a leaf knob's clothes**, and on the tower it is ≈ 65×
  net-negative. The grid that would settle it is `(leaf prove) + 26 × (wrap growth)`; no such grid
  exists.
* **Hash-bound survives into the tower, at 3.1–3.3× instead of 5.0–7.2×.** A silicon argument aimed
  at Poseidon2 is still the right one, but the Amdahl headroom is `log₂h`-eroded — and the same
  measurement at layer 4 needs a BN254 `Y` that has never been taken.
* **The one instrument gap worth closing**: a counting `DreggRecursionConfig`. It would make the
  tower's native hash side as exact as the leaf's, and it is a port, not a research problem (§0b).
  Everything in §5's derived column would become counted.

## 9. Reproduce

```bash
cd ~/dev/breadstuffs
cargo test -p dregg-circuit-prove --release --test recursion_tower_profile --no-run
B=./target/release/deps/recursion_tower_profile-*
RAYON_NUM_THREADS=1 $B l1_leaf_wrap_over_the_deployed_ir2_leaf                   --ignored --nocapture --test-threads=1
RAYON_NUM_THREADS=1 $B l0_child_prove_and_verify_permutations_at_the_wrap_engine --ignored --nocapture --test-threads=1
                      $B l3_apex_and_l4_shrink_census                            --ignored --nocapture --test-threads=1
```

`--test-threads=1` is load-bearing for the second: the permutation counters are **process-global**
(`ir2_phase_profile.rs` §D's own recorded trap — under default parallelism two tests zero each
other's counters and the corruption arrives as a plausible number, not a failure).

Release only. Every count reproduces bit-for-bit under any load; no wall clock in this file is
evidence.
