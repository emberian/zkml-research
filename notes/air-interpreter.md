# The interpreted AIR evaluator — shape, cost, and compilation

**Status: COMPLETE (2026-08-18).** Repo: `~/dev/breadstuffs`. Commits: `8d41da95f` (flat
tapes, byte-identical), `285dfe8a8` (fmt), `474a73b51` (compile-once cache), `436c2a865`
(doc repair). Raw logs: hbox `/tank/dregg-build/air-interp/` (pp/pp2/rig/rig2 + suites);
laptop scratchpad `baseline1/after1/census1/after2-bytes`.

**One line:** the deployed IR-v2 prover DID interpret its constraints — a recursive walk over
boxed `Add`/`Mul` AST nodes, once per SIMD chunk of each instance's QUOTIENT domain (measured:
56 prover + 12 symbolic + 3 verifier `Air::eval` invocations per transfer prove, ~163k/104k
boxed-node visits per prove at pack 4/8) — and it is now a flat postfix tape with
byte-identical proofs. But the cost was never the brief's "top term": the interpretation
overhead measures **25–40 µs/prove (3–5% of the quotient-eval phase, ≈0.1% of a b=6 prove)**,
and the counters refute two premises — the walk runs over the quotient domain (2–8×,
degree-driven), NOT the 64× LDE ("per row over the LDE'd domain" would be 1,024 main-instance
invocations at lb=6; measured 32), and "a top term in the phase profile" conflated the
`LDE quotient-eval` span (a DFT, ~12.9 ms at b=6 there) with the `quotient eval` span where
the interpreter actually runs (~0.9–1.3 ms, flat in b). ⚑ And the first landing demonstrated
the counts-blindness thesis twice over: operation counts were digit-identical while latency
moved in BOTH directions — the tape sped up its phase AND the naive per-construction
compilation slowed the verifier — visible only to the latency column.

---

## §1. The shape, established at source — READ, not assumed

### Where the interpreter lives (and a correction to the brief's pointer)

The brief pointed at `circuit/src/lean_descriptor_air.rs:128` (`LeanExpr::eval_expr`). That
file's own header (lines 1–9) marks `LeanDescriptorAir` **RETIRED / IR-v1 — not the live
rail**, superseded by `circuit/src/descriptor_ir2.rs` (`Ir2Air` / `parse_vm_descriptor2`).
BUT the *type* `LeanExpr` and its `eval_expr` ARE live: IR-v2's `VmConstraint::Gate`,
`Boundary`, lookup tuples, mem/map/umem fields and ProofBind lanes all carry `LeanExpr`
bodies and call `LeanExpr::eval_expr` from `descriptor_ir2.rs`. The live interpreted
evaluation surface is FOUR recursive walkers, all boxed-tree, all generic over `AB: AirBuilder`:

| walker | AST | leaves | site |
|---|---|---|---|
| `LeanExpr::eval_expr` | `Var/Const/Add/Mul` (boxed) | current row | `lean_descriptor_air.rs:128` |
| `WindowExpr::eval_expr` | `Loc/Nxt/Const/Add/Mul` | current+next row | `descriptor_ir2.rs:1143` |
| `ChalExpr::eval_expr_ext` | `+ Chal(i)` leaf, evaluates in EF | + FS challenges | `descriptor_ir2.rs:1293` |
| `eval_table_expr` | `TableExpr`: `+ Shr(i)/Prep(i)` | + shared defs, prep row | `descriptor_ir2.rs:1199` |

⚑ `eval_table_expr` is already a DAG evaluator: the `defs` prelude (`descriptor_ir2.rs:4483`)
evaluates each shared sub-expression ONCE per `Air::eval` invocation and `Shr(i)` clones the
value. On the Poseidon2 chip that is 2,943 shared field ops standing in for 70,524 tree ops
(`table_air.rs` docblock). So the chip — the widest instance — is NOT a naive tree re-walk;
the naive tree walks are the main descriptor's `LeanExpr`/`WindowExpr` bodies and the
per-node `Box` pointer chase everywhere.

### Per WHAT does the walk run? Per pack-chunk of the QUOTIENT domain — not the 64× LDE

`p3-batch-stark` rev `82cfad73`, `batch-stark/src/prover.rs::quotient_values` (line 695):

- the loop is `(0..quotient_size).into_par_iter().step_by(pack_width)` and each iteration
  runs ONE full `air.eval(&mut folder)` (via `lookup_gadget.eval_air_and_lookups`, line 909)
  over a `ProverConstraintFolder` whose `AB::Var = PackedVal` (BabyBear×8 on AVX2/NEON-ish;
  this box's measured packing width is in the rig output).
- `quotient_size = trace_size × num_quotient_chunks`, where `num_quotient_chunks =
  2^ceil(log2(max_constraint_degree − 1))` per instance (`get_log_num_quotient_chunks`,
  symbolic analysis) — **degree-driven, independent of the FRI blowup**. The 64× at lb=6 is
  the *committed LDE* (Merkle leaves); the constraint interpreter never walks it.
- Confirmed independently by the phase profile: the `quotient eval` span is FLAT in b
  (1.135/1.161/1.360/1.283/1.305/1.168 ms at b=3..8, `phase-profile.md` §2). A per-LDE-row
  walk would double per rung.

So per prove, `Air::eval` invocation count =
`Σ_instances ceil(quotient_size_i / pack_width)` (prover folder)
`+ (symbolic passes: quotient sizing, constraint layout, lookup extraction — a handful per instance)`
`+ 1 per instance at zeta (verifier folder, in the unconditional self-verify)`.
Measured numbers in §2 below (feature-gated counter, `eval-count`).

### Who else runs the same eval — the surfaces a compiled evaluator must not break

1. **Symbolic builders** (`InteractionSymbolicBuilder` etc.): `AB::Expr` is an `Rc` DAG node;
   the eval's `+`/`*` build the constraint graph that sizes the quotient and feeds
   `get_symbolic_constraints`. Constraint DEGREES and COUNT come from this pass.
2. **The prover folder** (per quotient chunk, packed) — the latency target.
3. **The verifier folder** (once at zeta, extension field) — and through it the
   **in-circuit recursive verifier**: `circuit-prove`'s `RecursionInput<'_, DreggRecursionConfig,
   Ir2Air>` is generic over the SAME `Ir2Air: Air<AB>`; the recursion tower re-runs this eval
   under its own builder types. This is the one the brief flags as breaking silently.

### The interpretation overhead is per-invocation, and it has three parts

1. Two `to_vec()` allocations per invocation (`Ir2Air::eval` head: `local`/`next` copied out
   of the matrix view — 386 columns × 2 for the chip).
2. The boxed-tree pointer chase per expression node (`Box<LeanExpr>` etc.), per invocation.
3. The re-dispatch (`match` per node) — identical work whether the tree encodes 3 nodes or a
   Horner chain.

⚑ **Counts are blind to all three by construction** — a Poseidon2 permutation count and a
field-op count are IDENTICAL whether the same polynomial is evaluated by tree walk, flat
tape, or codegen. This class of cost is only visible to the latency column. Naming that is
part of this deliverable.

---

## §2. The static node census — what ONE invocation walks `[MEASURED 2026-08-18]`

Harness: `circuit/tests/air_interp_census.rs::static_node_census` (laptop, release,
`-C target-cpu=native`; counts are hardware/contention-free). Workload: the rig's —
`transferVmDescriptor2`, 1 Transfer. Three instances (main + chip + byte; no memory/map/umem
tables in this descriptor).

| instance | exprs | nodes | adds | muls | max depth |
|---|---:|---:|---:|---:|---:|
| main (42 constraints) | — | **201** | 20 | 22 | 5 |
| · of which 15 `base.gate` bodies | 15 | 99 | 20 | 22 | 5 |
| · of which 6 lookup tuples | 6 | 102 | 0 | 0 | **1 — pure leaves** |
| `dregg-ir2-chip-v1` (1078 defs / 391 gates / 3 interactions) | 1,518 | **7,418** | 1,651 | 1,299 | 16 |
| `dregg-ir2-byte-v1` (0/2/1) | 4 | 10 | 2 | 1 | 4 |

Two consequences, both load-bearing for the design:

1. **The chip table is the whole forest** — 7,418 of ~7,629 nodes, already DAG'd through the
   `defs` prelude. The main descriptor's own algebra is 99 nodes.
2. **The bus-pass tuples are pure leaves** (depth 1, zero adds/muls) — compiling them fuses
   nothing. This is what justifies leaving `Lookup`/`MemOp`/`MapOp`/`UMemOp`/`ProofBind` lane
   expressions on the `LeanExpr` tree walk (`flat_eval::CompiledK::Passthrough`).

## §3. Invocation counts `[MEASURED 2026-08-18]` — the shape, settled by a counter

Instrument: feature-gated `circuit/src/eval_census.rs` (`--features eval-count`; compiled out
of the deployed prover entirely), one relaxed bump per `Air::eval` INVOCATION keyed by
instance × `type_name::<AB>()`. One prove at (lb 6, q 19, pow 0) incl. its unconditional
self-verify, on the laptop (aarch64 → NEON pack width **4**; hbox/AVX2 packs 8):

| instance (trace h, quotient chunks) | `ProverConstraintFolderWithLookups` | `VerifierConstraintFolderWithLookups` | `InteractionSymbolicBuilder` | total |
|---|---:|---:|---:|---:|
| main (64, ×2) | **32** = 64·2/4 | 1 | 4 | 37 |
| dregg-ir2-chip-v1 (8, ×8) | **16** = 8·8/4 | 1 | 4 | 21 |
| dregg-ir2-byte-v1 (16, ×2) | **8** = 16·2/4 | 1 | 4 | 13 |
| **total** | 56 | 3 | 12 | **71** |

(`degree_bits = [6, 3, 4]` read off the proof; chunk counts from symbolic degree analysis.)

**The shape claims, settled:**
- The prover-folder count is exactly `quotient_size / pack_width` per instance — the walk runs
  per SIMD chunk of the **quotient domain** (degree-driven: ×2/×8/×2), and is **independent of
  the FRI blowup**. ⚑ The brief's "per row over the LDE'd domain — 64× the trace height at
  lb=6" is REFUTED by this counter: at lb=6 a per-LDE-row walk of the main instance would be
  1,024 invocations; measured is 32. (Also visible in `phase-profile.md` §2: the quotient-eval
  span is flat in b.)
- Three more builder types run the same eval: 4 symbolic passes per instance (quotient sizing,
  interaction extraction, constraint layout, LogUp trace build) and 1 verifier-folder eval per
  instance at zeta (the self-verify; an external verify pays the same).

**Total interpreted node-visits per prove** (= §2 nodes × these invocations, exact since every
invocation walks the full list): main 201×37 = 7,437 · chip 7,418×21 = **155,778** · byte
10×13 = 130 → **≈ 163k boxed-node visits per prove on this box** (≈ 104k on hbox at pack 8).
The chip table is ~95% of it. This is the entire prize the compiled evaluator plays for — at
~1–5 ns of pointer-chase per visit it bounds the win at a fraction of a millisecond per prove,
i.e. a slice of the 1.28 ms quotient-eval phase, which is itself 1.8% of a b=6 prove.

## §4. The compiled evaluator `[BUILT 2026-08-18]`

`circuit/src/flat_eval.rs` — `FlatExpr`: each boxed AST compiled ONCE (at `Ir2Air`
construction) into a postfix `Vec<FlatOp>` evaluated over a reusable stack whose high-water
mark is precomputed. `CompiledMain` (index-parallel to `desc.constraints` + submask pairs) and
`CompiledTable` (defs/gates/interactions) ride new fields on `Ir2Air::Main` /
`Ir2Air::LeanTable` / `Ir2UniAir`, built only by the constructors — the compilation cannot
drift from the descriptor. Option chosen from the brief: **fuse into a flat postfix sequence
over a small stack** (cheapest; keeps `AirBuilder` genericity — the SAME tape serves the
symbolic builder, the prover folder, the verifier folder, the gate-accept oracle's row builder
and the recursion tower's builders).

Deleted rather than kept beside it (two evaluators that agree today disagree later):
`WindowExpr::eval_expr`, `ChalExpr::eval_expr_ext`, `eval_table_expr` — all had zero callers
after the cutover. `LeanExpr::eval_expr` stays (still the evaluator for ProofBind lanes, bus
tuples and the retired-but-compiled v1 AIRs).

## §5. Byte-identity `[GATE]`

Baseline (BEFORE, tree walk), laptop release `-C target-cpu=native`, blake3 over
`serde_json` / `rmp-serde` bytes; prover byte-determinism established by double-prove at b=6:

| point | json B | blake3(json)[..20] | rmp B | blake3(rmp)[..20] |
|---|---:|---|---:|---|
| (lb 3, q 19, p0) | 301,904 | `a8f5d051200c065640ca` | 124,198 | `389cd68c40fe2710fa9f` |
| (lb 4, q 19, p0) | 311,918 | `de7ed6b04a51100fddc5` | 128,872 | `6d0b91c72fbbee46aa86` |
| (lb 5, q 19, p0) | 321,428 | `3c96dc1316fbf6ee4c96` | 133,544 | `2b218a45dfbcbc5b0cd8` |
| (lb 6, q 19, p0) | 331,386 | `d8b5ed41aae45e67152c` | 138,220 | `6368828370ff66aa3683` |
| (lb 7, q 19, p0) | 341,212 | `d3557cbb7cd493062b87` | 142,894 | `14d56ae252ae485a01de` |
| (lb 8, q 19, p0) | 350,983 | `212b2d6178cb321882f6` | 147,566 | `d0fa471560377f672b5f` |
| (lb 6, q 19, pow16) | 331,251 | `6e22b3bb0332891faba6` | 138,224 | `3cad30a69901631b78c5` |

**AFTER (flat tape, 8d41da95f): IDENTICAL — every row, both serializations, byte-for-byte**
(blake3 equal at all six pow=0 blowups AND the deployed (6,19,pow16) point). **Re-verified
IDENTICAL again after the compile-once cache (474a73b51).** The LDE-layout precedent is met:
the compiled evaluator is a pure re-arrangement of how the same polynomial is evaluated. No
wire change, no VK rotation, no flag day.

Two independent corroborations of the same identity:
- the hbox rig's e1 count tables are digit-identical between sides in both rounds (prover /
  verifier perms, packed width, proof bytes), and the perm-law self-check pins
  `P = 3381·2^b + 766` to the unit on BOTH sides — the counts column is a flat control;
- the rig's proof-byte sizes on hbox (AVX2, pack 8.18) equal the laptop's (NEON, pack 4)
  byte-for-byte per point — proofs are byte-identical across architectures too.

### §5b. The suite gate — HEAD is red-as-steady-state; the gate is the A/B DIFF

Landed as `8d41da95f` (+ `285dfe8a8` rustfmt residue). The full `cargo nextest run -p
dregg-circuit --release --no-fail-fast` at **pristine HEAD (44d0dea45)** on hbox (clean
worktree from the bare repo, `DREGG_REQUIRE_LEAN=0` degraded build): **2015 passed, 102
failed, 1 timed out** — the reds pre-exist this change. One was traced to source: the v1
`cap_delegation_nonamp_descriptor` tests write `pis[41]` against `public_input_count = 35` —
tests missed by the seven-slot PI-compaction flag day (`f7bc7d351`); reproduced byte-for-byte
at pristine HEAD before any comparison was made. ⚠ Some of the 102 may also be artifacts of
the degraded (`DREGG_REQUIRE_LEAN=0`) build — that condition is held IDENTICAL on both sides,
so the gate for THIS change is the failure-set DIFF (after − head = must be empty), not the
absolute count.

**AFTER (285dfe8a8, same box, same degraded condition): 2015 passed, 103 failed, 1 timed
out — name-normalized diff vs HEAD = TWO tests, both timing artifacts, both re-verified
individually on the quiet box:**
- `perf_growth::heap_membership_is_subquadratic_in_leaf_count` — a pure `CanonicalHeapTree8`
  wall-clock ratio test (no proving, no `Ir2Air` in its path); PASSED at HEAD under load,
  FAILED at AFTER under load, **PASSES on the AFTER build quiet (0.29 s vs 2.57 s contended)**.
- `ir2_phase_profile::phase_profile_trace_height_sweep` — **timed out at nextest's 180 s cap
  at pristine HEAD too** (that was HEAD's "1 timed out"); same verdict on the AFTER build
  quiet. A >180 s measurement sweep nextest kills on any box; per-test label read, not a code
  failure.

**Failure-set diff after − head = ∅.** Also: `cargo check -p dregg-circuit-prove --tests`
(the recursion consumer) green against the change.

## §6. Latency A/B `[MEASURED 2026-08-18]` — hbox, both SHAs, interleaved ×3

Method: two worktrees from the bare repo (`air-interp-before` = 44d0dea45,
`air-interp-after` = 285dfe8a8), one shared cargo target dir, per-side binaries preserved and
**provenance verified from the artifact** (the after binary contains the tape's panic string,
the before binary does not — never from mtimes); runs NOT niced, `taskset -c 0-15` (P-cores
only on the i9-12900), `RAYON_NUM_THREADS=1`, `DREGG_PROFILE_REPS=21`, sides alternated
B/A ×3, box load < 1.0 at run time (drained after the suite runs), `DREGG_REQUIRE_LEAN=0`
both sides. ⚠ LATENCY claims only; composes with no work claim.

### §6a. Round 1 (tapes compiled per `Ir2Air` construction) — the phase moved, the prove did not

`quotient eval (arith)` (the span the interpreter runs in), min over 3 interleaved rounds of
per-point min-of-21, ms:

| lb | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|
| BEFORE (tree walk) | 0.922 | 0.867 | 0.862 | 0.871 | 0.922 | 0.959 | 1.075 |
| AFTER (flat tape) | 0.909 | 0.826 | 0.839 | 0.844 | 0.881 | 0.931 | 1.041 |
| ratio | 0.99 | **0.95** | 0.97 | 0.97 | **0.96** | 0.97 | 0.97 |

**The interpretation overhead the tape removes is ≈ 25–40 µs/prove — 3–5% of the quotient-eval
phase — lower in every cell of every round at lb ≥ 3.** Consistent with §3's bound: ~104k
boxed-node visits on this box (pack 8), a fraction of a ns of pointer-chase each on top of the
packed arithmetic that remains.

⚑ **But the naive placement LOST it back, and more, elsewhere** — caught because both
whole-prove instruments ran, not just the target phase:
- `VERIFIER (standalone)` rose +0.13–0.16 ms at every blowup (~+4%);
- the in-prove `verify_batch` span rose +0.15–0.19 ms;
- rig e2 in-pool whole-prove: +0.45 ms at lb 3–5, +1.2 ms at lb 6–7.

Mechanism (derived, then confirmed by the fix): the tapes were compiled **per `Ir2Air`
construction**, and `instance_airs` runs at prove entry AND self-verify entry AND every
verify — the chip's 1,518 expressions (~1,900 small `Vec` allocations) per assembly. The
compile ran where nothing amortizes it: the verifier evaluates ONCE at zeta. A compiled
evaluator whose compilation runs per proof is an interpreter with extra steps.

### §6b. The fix — compile once per process (`flat_eval::compiled_table_for`)

The shared table AIRs are process-global `Arc<LeanTableAir>` statics; the compiled tapes now
live in a Weak-pruned identity cache keyed by the live `Arc`'s pointer (never by display name
— names collide; never by bare pointer — a dropped Arc's entry stops upgrading and is pruned,
so address reuse cannot serve a WRONG tape). Main-descriptor tapes (201 nodes) stay
per-construction — µs-scale. Landed `474a73b51`; byte gate re-run GREEN (§5); nextest over
the ir2/table/exact-public/effect-vm name-space at the new SHA: 276/284 passed, all 8
failures in the pristine-HEAD baseline, zero new. Re-measurement below.

### §6c. Round 2 (compile-once, `474a73b51` vs tree walk) `[MEASURED]`

Same discipline, fresh session (pp ×3 interleaved, rig ×2, plus one REVERSED-ORDER rig pair
as an ordering control). `quotient eval` min-of-3, ms:

| lb | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|
| BEFORE | 0.944 | 0.864 | 0.861 | 0.858 | 0.890 | 0.942 | 1.025 |
| AFTER2 | 0.896 | 0.832 | 0.856 | 0.857 | 0.877 | 0.916 | 1.006 |

Win persists (AFTER lower in 12 of 14 blowup-cells across the two sessions; session noise
±20–30 µs on a ~0.9 ms phase). **The v1 verifier regression collapsed**: `VERIFIER
(standalone)` is now +0.028…+0.044 ms at lb ≤ 6 and ±0 at lb ≥ 7 (was +0.13–0.16 ms) — the
compile-once cache removed the per-verify compilation; the ~1% residual is consistent with
the per-construction Main-descriptor compile (µs) plus code-layout sensitivity.

**Whole-prove (rig e2, lb6, min across rounds):**

| shape | BEFORE | AFTER2 | verdict |
|---|---:|---:|---|
| cold caller T=1 (**the deployed shape**) | 39.32–39.97 | 39.92–40.43 | **wash** — the reversed-order pair read 39.898 vs 39.921 |
| INSIDE pool T=1 | 34.70–34.92 | 35.33–35.59 | after ≈ **+0.7 ms (+2%)**, BOTH orders |
| INSIDE pool T=8 | 14.20–14.26 | 14.63–14.64 | after ≈ +0.4 ms (+3%) |

⚠ **The in-pool ~2% is real, reproducible, and UNATTRIBUTED**: it survives order reversal
(so it is not thermal/ordering), it does not appear in any per-phase span (the same-process
phase matrix sums to ≈ ±0.05 ms), the counts are digit-identical, and the cold-caller shape
does not show it. Its signature — visible only under one calling convention, invisible to
every span, larger than the sum of all attributed deltas — is code-layout/µarch sensitivity
of a 57 KB-smaller binary, but that is a HYPOTHESIS, not a measurement; recorded as an open
residual rather than explained away. What is safe to quote: **at the deployed calling shape
the change is net-neutral; the interpreter's own phase is 3–5% faster; nothing pays the v1
compilation tax any more.**

## §7. Both columns, and what fraction of a prove this is

**WORK column (the control — unchanged, to the digit):**
- Poseidon2 permutations: rig e1 tables digit-identical between sides in every round;
  self-check pins `P = 3381·2^b + 766` on both. DFT census identical (9 calls). Proof bytes
  identical (and identical across NEON/AVX2 boxes).
- ⚑ This is the measured demonstration of the campaign's blind spot: **every count instrument
  this project runs returned IDENTICAL numbers while the latency column moved in both
  directions** (the tape sped its phase up 3–5%; the misplaced compilation slowed the
  verifier ~4%). Interpretation overhead is a class of cost that counts cannot see — by
  construction, not by accident. A counts-primary discipline needs the rig's clock arm
  wherever an "how it is evaluated" (not "what is evaluated") change lands.

**LATENCY column (hbox, quiet, interleaved, min estimators; LATENCY claims only — `compose()`
refuses to mix them with work claims, correctly):**
- Interpretation overhead removed by the tape: **25–40 µs/prove** = 3–5% of the
  `quotient eval` phase, lower in 12 of 14 blowup-cells across two sessions.
- Whole-prove: **net-neutral at the deployed calling shape** (cold caller, both orderings);
  an unattributed ~2% in-pool residual is recorded in §6c and belongs to no phase span.
- What fraction of a prove: the quotient-eval phase is 0.87–1.09 ms FLAT in b — **9.6% of a
  prove at lb=3 (9.06 ms in-pool), 2.7% at the deployed lb=6 (34.5 ms), and less at the
  deployed pow=16 point** (the grind adds a ~12 ms-mean draw). So the tape's whole-prove
  effect is ≈ **0.1% at deployed knobs** — real, measured, and honestly small.
- Conditions: i9-12900 P-cores (`taskset -c 0-15`), not niced, load < 1 at run time,
  `RAYON_NUM_THREADS=1` / rig T=1 and T=8, `-C target-cpu=native` (pack width 8.18 verified
  in-run), `DREGG_REQUIRE_LEAN=0` both sides, N=21 (phase) / 9 (rig) per cell, 3 (phase) / 2
  (rig) interleaved rounds.

**Why the brief expected more, and what the counter said:** the walk runs per pack-chunk of
the quotient domain (measured 56 prover invocations/prove — a per-LDE-row walk would be
~40× that at lb=6), the forest is small and already DAG-shared (7.6k nodes, `defs`
memoisation), and the phase that hosts it was never a top term — `phase-profile.md`'s top
terms are Merkle-commit (hash, 61% at b=6) and the LDE DFTs. **This lane's axis was "evaluate
the same constraints faster"; the measured answer is: the interpreter tax was ~3–5% of a
phase worth ~3% of a prove.** Where it would grow: trace height multiplies the prover-folder
invocation count linearly (the recursion/leaf-wrap tower at h=2^20 was not measured here —
its quotient-eval phase is proportionally larger, and the same tapes serve it unchanged).
