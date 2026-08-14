# `permEmissionNarrow` — the 2.11× Pareto win, landed in Lean

2026-08-13/14. LEAN BUILD lane against `notes/poseidon2-virtualization.md` §6 "What lands, and
where". The measuring lane specified it and declined to build it; this lane builds it.

**Landed: `breadstuffs/metatheory/Dregg2/Circuit/Emit/Poseidon2RoundGates.lean` §8** —
`permEmissionNarrow` beside `permEmission`, **141 gates against 352**, plus the relating theorem,
the degree pin, the KAT, both poles, and the flag-day list. `lake build Dregg2` green
(10,698 jobs); the deployed table-AIR artifacts re-emit byte-identical. See §7 for the reds that
are NOT this lane's.

---

## §0 — SUBSTRATE

**This is Lean-authored AIR.** `Poseidon2RoundGates.lean` → `ChipTableEmit.lean` →
`CHIP_TABLE_AIR_JSON`; Rust only interprets. Nothing in this lane writes a Rust constraint. The one
Rust artefact this lane *names* is a gap, not an addition: the narrow arm's witness generator does
not exist (see §5).

---

## §1 — WHAT THE OBJECT IS

| | wide (`permEmission`, DEPLOYED) | narrow (`permEmissionNarrow`) |
|---|---|---|
| committed aux lanes | 352 | **141** |
| gate bodies | 352 | **141** |
| shared definitions | 1,078 | **1,286** |
| field ops / row | 2,668 | **2,246** |
| expression nodes | 6,766 | 5,919 |
| **`max_constraint_degree`** | **7** | **7** |

Every number is a named theorem on the emitted object (`narrow_emission_shape`,
`narrow_cost_measured`, `the_degree_is_seven_on_both_arms`), `native_decide` + `#assert_compiled`.

The layout: one 16-lane block per external round (8 × 16 = 128), one lane per internal round (13),
nothing for the initial linear layer. `narrow_blocks_tile` proves the blocks tile `[0, 141)`
exactly — a **`decide` in the kernel**, so an aliased or gapped `narrowBase` is caught by a term,
not by eye.

⚑ **More definitions, fewer columns.** 1,078 → 1,286 definitions is the *price*; 352 → 141 columns
is the *win*. A definition is one field op per row; a column is a commitment, and the profiling
lane settled that the prover is hash-bound at every feasible blowup. The op count *also* falls
(2,668 → 2,246), so there is no trade even in the currency where the narrow arm spends more.

⚑ **The residual law survives.** The wide arm's op count is the deployed Rust gadget's 2,316 plus
exactly one multiplication per gate (`TExpr` has no `sub` node). The narrow arm's is **2,105 + 141**
— same law, both terms moved, `narrow_cost_measured` pins it as an equation so a drift in either is
visible.

⚠ **Lane 0 of the post-layer state must be the COMMITTED column, not the S-box expression.**
Feeding the expression forward is the same polynomial and pushes the state to degree 7, then 49 at
the next round. Reading the column keeps every round's input at degree 1. This is upstream's
`state[0] = partial_round.post_sbox.into()`, and it is what the degree pin measures — the "identical
degree" half of the Pareto claim is the half a virtualization gets wrong.

---

## §2 — ⚑ THE SHARING NODE IS A PRECONDITION, NOT AN OPTIMISATION (a finding the brief did not have)

The wide arm has a TREE spelling (`permGateBodies`, 140,850 nodes) because every round's input is a
bare column read. **The narrow arm cannot have one.** Its internal-round state is carried as
expressions, and one internal round multiplies a tree state by ~16× (`intLayer` reads all sixteen
lanes into `sum` and each lane once more). Measured on the emitted objects:

```
internal rounds:   0        1         2
tree nodes:     1104    17900    286670       (×16.2, ×16.0)
```

Thirteen of them is ~5·10^18 nodes. So §6b's tree-vs-DAG agreement oracle — the wide arm's best
instrument — **has no narrow counterpart by construction.** That is why the narrow arm's
instruments are the KAT, the theorems, and the model differential instead, and it is worth saying
out loud: the narrow arm is *only expressible* because `TableAir.defs` exists.

---

## §3 — THE RELATING THEOREM (the safety argument, as theorems)

211 of the wide arm's 352 lanes disappear. Both classes are accounted for **generally** — in `r`,
in the state, in the committed value, in the definition vector and in the row window:

1. **195 = 13 × 15 — the affine internal lanes.**
   `wide_internal_lane_is_a_unit_multiple`: instantiate the wide arm's sixteen free columns at what
   the narrow arm computes for them, and the `j`-th wide gate body equals
   `c_j · δ` where `δ` is the narrow arm's single gate body, `c_j = 1` for `j ≠ 0` and `c_j = p − 1`
   for `j = 0`. **An identity over ℤ** — not a congruence, so nothing hides in a modulus.
   `lane_zero_multiplier_is_a_unit` (BabyBear primality by `norm_num`) makes `p − 1` cancel, hence
   `narrow_internal_gate_is_the_whole_wide_round`: the one narrow gate holds **iff** all sixteen
   wide ones do.
2. **16 — the initial linear layer.** `wide_initial_block_is_a_definition`: those gates say exactly
   "these sixteen columns equal this linear function of the seed", and nothing else. Deleting the
   columns and the gates together deletes a definition.

Then the systems. `WideSat` (352 equations) and `NarrowSat` (141) are stated over value-level round
functions **defined by evaluating §4's emitters** (`roundOutVal r xs = evalSt (valEnv xs) (roundOut r
varState)`) — the emitted algebra's own denotation, not a transcription.

- `wideSat_iff` — the wide system has exactly one solution per seed: the round chain.
- `narrowSat_forces_the_trace` — **the 141 equations force the whole 352-value chain.** Nothing is
  left free by the lanes that stopped being committed.
- `narrow_accepts_exactly_the_wide_witnesses` — ⚑ **for ANY assignment the wide arm accepts, the
  narrow arm accepts a committed vector exactly when that vector is the wide one's projection.**
  Stated against an arbitrary `blk`, not against the canonical chain, so it is not an ∃-over-a-witness
  wearing a theorem's clothes.

All kernel-clean, all pinned with `#assert_axioms`. (The instrument works: an intermediate draft
had a `sorry` in the unit-multiple proof and `#assert_axioms` failed the build with
`depends on non-kernel axioms [sorryAx]`.)

**Both poles.** `wideSat_blocksVal` / `narrowSat_is_satisfiable` and `wideSat_is_refutable` /
`narrowSat_is_refutable`. The refutations probe at round 0 deliberately: the round function is
degree 7 over ℤ with no reduction, so `blocksVal seedv 21` is an integer with ~10^11 bits and a
"refutation" deeper in the chain would be measuring something else.

**Teeth on the emitted object.** `narrow_gates_accept_the_kat` (three inputs, and the witness's last
block IS `P2.perm`) and `narrow_gates_refuse_a_forgery` — one bumped limb in the opening external
block, the **first and last of the thirteen single internal lanes**, the output block and an input
lane, each refused; a column outside the gadget changes nothing. The internal-lane teeth are the
ones that matter: those are exactly the columns whose fifteen wide siblings no longer exist.

---

## §4 — ⚠ THE ONE BRIDGE THAT IS NOT CLOSED, AND WHAT IT COSTS

§8e reasons about `NarrowSat` — the 141 equations. `permEmissionNarrow` emits 141 gate *bodies*
whose content sits in a 1,286-entry definition list that `shareVals` resolves. **That the two are
the same system is not proved.**

This is **undone work, not a boundary.** What it needs, concretely:
- a `shareVals` prefix lemma (`foldl` over an append: `shareVals (a ++ b) = b.foldl … (shareVals a)`,
  plus "a push-fold does not disturb indices below the initial size") — straightforward;
- a fold invariant over `permEmissionNarrow`'s 21 steps carrying "round `r`'s definitions start at
  `base + Σ earlier`", so `ds.getD (b + 6 + i)` resolves to the round's own output definition.

Estimate: a day, mostly `Array.push`/`getD` bookkeeping. Nothing about it is hard, and it would
close the same gap for the *wide* arm, which has never had it either.

**The falsifier standing in for it meanwhile** (`narrow_emission_agrees_with_the_model`): the
emitted DAG's verdict and the value model's verdict, computed independently, on six row windows —
honest plus five perturbations, one per committed region. An aux-offset slip, a `narrowBase` error
or a wrong `shr` index moves one and not the other. **It is case-testing. It proves nothing about
all windows,** and it is labelled that way in the file.

---

## §5 — FLAG DAY (stated in the commit)

Cutting the chip over breaks these, on purpose; each re-emits rather than being reinterpreted:

1. **`CHIP_WIDTH` 386 → 175** = `CHIP_AUX0` 33 + 141 + 1. `CHIP_MULT_NARROW`, `CHIP_OUT` and every
   derived offset in `ChipTableEmit` move with it.
2. **`CHIP_TABLE_AIR_JSON` re-emits** — 391 gates → 180, 1,078 defs → 1,286, `chipState16Table` too.
   The AIR fingerprint changes ⇒ **VK rotation**. The old artefact must REFUSE to load.
3. ⚑ **The Rust witness generator is the blocker and it does not exist.**
   `poseidon2_permute_aux_witness` (`circuit/src/plonky3_prover.rs:492`) writes 352 values per
   permutation; the narrow layout needs 141 (eight external blocks + one post-S-box lane per
   internal round). Until that lands the cutover is **not routable** — saying "the Lean is landed,
   therefore the win is banked" would be exactly the proven-in-Lean-is-not-routable error.
4. **`sbox_registers: 1`** (`descriptor_ir2.rs:3524-3528`) is a pin describing a layout the chip
   deliberately does not use. Re-decide it or delete it at the cutover.
5. **Every fixture carrying a chip trace re-generates**, and the devnet re-genesises.

Not touched: the **v1 hash sites** (`lean_descriptor_air.rs:1754`, `POSEIDON2_PERM_AUX_COLS = 352`)
are a separate, Rust-authored spelling of the same algebra. They are debt already and this lane does
not extend them.

⚠ **Two shapes that agree today disagree later.** The wide arm stays only until item 3 is
discharged; the file says so at §7's closing note rather than leaving "both exist" as a permanent
state.

---

## §6 — WHAT §7 USED TO SAY

`Poseidon2RoundGates.lean` §7 closed, verbatim:

> ⚠ And none of this is a licence to re-arithmetize: the algebra IS the deployed permutation […]
> **A cheaper circuit would be a DIFFERENT circuit.**

True, and not an objection — the different circuit is the one to run. That paragraph is replaced
with the landed narrow emission, which one is deployed, why both exist and for how long, and a
pointer to the flag-day list. The round algebra did not move: §6's KATs are replayed unchanged on
the narrow arm in §8d.

---

## §7 — BUILD EVIDENCE

```
lake build Dregg2.Circuit.Emit.Poseidon2RoundGates   ✔ 73s, no warnings from the file
lake build Dregg2                                    ✔ Build completed successfully (10,698 jobs)
lake env lean --run EmitTableAirs.lean               ✔ all 11 table-AIR artifacts BYTE-IDENTICAL
scripts/check-guard-discipline.py                    Poseidon2RoundGates.lean unchanged at 83
                                                     (this lane added ZERO `#guard`s — every new
                                                     assertion is a named theorem)
```

⚑ **The deployed artifacts do not move.** `EmitTableAirs` was re-run and every one of the eleven
files under `circuit/descriptors/table-airs/` — `dregg-ir2-chip-v1.json` (159,195 B) included —
compares byte-identical to the checked-in copy. The narrow arm is landed *beside* the deployed
emission, not in place of it.

⚠ The whole-workspace `lake build` is RED in `KimchiStepMainPins01/03/05` (another lane's in-flight
Mina work). Verified by import closure that none of the three reaches `Poseidon2RoundGates`; the
`Dregg2` target, which excludes them, is green.

⚠ The guard-discipline gate is RED at HEAD from three OTHER modules (`KimchiStepMainPins13` +1,
`TauPrefixMonotone` +16, `BlocklaceFinality` +30) plus 17 stale rows. Not this lane's; stated so the
red is not read as this diff.

Axiom accounting in the new section: **13 `#assert_axioms`** (kernel-clean — every relating theorem,
plus `narrow_aux_cols_is_141` / `narrow_perm_defs_is_1286` / `narrow_blocks_tile`, which are
`rfl`/`decide` and so strictly stronger than the guards they would have been) and **12
`#assert_compiled`** (the emitted-object computations and the two refutation probes) — the same
evaluator a `#guard` runs on, named rather than silent. No `sorry`, no new axiom.

⚠ The landed commit message says "eight relating theorems / ten computations"; the true counts are
13 and 12. Recorded here rather than amended — an amend takes the index, and this is a shared tree.
