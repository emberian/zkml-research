# The narrow witness generator — unblocking `permEmissionNarrow`

2026-08-14. BUILD lane against `notes/perm-narrow.md` §5 item 3, the blocker that lane named and
declined to build: *"the Rust witness generator is the blocker and it does not exist."*

**Landed: it exists, it is bound to the Lean, and both figures are measured.**

---

## §0 — SUBSTRATE, said out loud

**This lane wrote a WITNESS GENERATOR. It authored no constraint.** The AIR is
`Poseidon2RoundGates.lean` §8 (`permEmissionNarrow`), Lean-authored and unchanged by this lane. What
is new in Rust is `poseidon2_permute_aux_witness_narrow` and its inverse; what is new in Lean is a
`TableAir` **wrapper** — a name, a width and a `prepWidth` around gate lists that already existed —
so the emitted bytes exist for Rust to interpret.

Files:

| file | what it is |
|---|---|
| `circuit/src/plonky3_prover.rs` (after `poseidon2_permute_aux_witness`) | the generator, its inverse, and the layout functions |
| `metatheory/Dregg2/Circuit/Emit/PermArmTableEmit.lean` | **NEW** — the two arms as standalone `TableAir`s |
| `metatheory/EmitPermArms.lean` | **NEW** — their byte source |
| `circuit/tests/fixtures/perm-arms/dregg-perm-arm-{wide,narrow}-v1.json` | **NEW** — the emitted arms |
| `circuit/tests/poseidon2_narrow_witness.rs` | **NEW** — the bind, the falsifier, the counts |

⚠ The two fixtures are **not deployed and not routed through `EmitTableAirs.lean`**. The eleven
`circuit/descriptors/table-airs/` artifacts and `scripts/emit_descriptors.py`'s provenance walk are
untouched; `EmitTableAirs.lean`'s `tableAirs_routes_all_ten` still reads 10.
`PermArmTableEmit` IS imported by `Dregg2.lean`, so `lake build Dregg2` builds it and it cannot rot
unnoticed.

⚠ **A named seam, stated rather than papered over: there is no provenance gate binding the checked-in
fixtures to the Lean emission.** Re-running `EmitPermArms.lean` after a change to
`Poseidon2RoundGates` would produce different bytes and nothing automatically compares them — the
same shape as the `table-airs/` subdirectory being invisible to `verify_provenance`. What stands in
meanwhile is not nothing: `the_emitted_arms_have_the_stated_shape` pins name, width, gate count, def
count, `prep_width` and `max_degree()` against constants derived from `POSEIDON2_PERM_AUX_COLS`, and
a drifted artifact would additionally have to accept exactly this generator's witness and refuse all
157 perturbations. It is a check, not a hash. Routing both files into
`scripts/emit_descriptors.py`'s drift gate is the follow-up.

---

## §1 — THE LAYOUT, DERIVED FROM THE LEAN

The Lean is the spec and the Rust conforms. `narrowAuxWitness` (§8d) and `narrowBase` (§8a) are the
two objects that fix it:

* **141 = 8 × 16 + 13.** One 16-lane block per EXTERNAL round, ONE lane per INTERNAL round, and
  **nothing at all for the initial linear layer** — it is a linear map of a seed the row already
  holds.
* **Column order is round order.** Four opening external blocks at `[0, 64)`, the thirteen single
  internal lanes at `[64, 77)`, four closing external blocks at `[77, 141)`. `narrow_blocks_tile`
  proves that tiles `[0, 141)` exactly — a `decide` in the kernel, so an aliased or gapped base is
  caught by a term.
* ⚑ **The value an internal round commits is NOT one of the wide arm's lanes for that round.** It is
  `(state[0] + rc[r][0])^7` — the post-S-box lane 0, taken **before** the diagonal layer. The wide
  arm's block for round `r` is the diagonal *image* of that value. So the projection wide → narrow
  is not a column selection; it reads lane 0 of the *previous* block and re-applies one S-box.
  Getting this wrong by one block is the error that would compile, pass a length check, and fail
  every gate.

The Rust mirrors are `poseidon2_narrow_base`, `poseidon2_narrow_block_width`,
`poseidon2_round_is_external`, `POSEIDON2_PERM_AUX_COLS_NARROW`.

---

## §2 — THE BIND, IN BOTH DIRECTIONS

The brief asked for the half Lean cannot see. §8e proves the two *AIRs* accept the same
assignments; it says nothing about two Rust *programs*, and the narrow arm is unprovable if the
generator is off by one column.

1. **Forward — `the_narrow_witness_is_the_lean_projection`.** The projection is recomputed *out of
   the wide generator's 352 values and `ROUND_CONSTANTS`*, independently of the narrow generator,
   and compared. Two programs, same 141 numbers, on four inputs including both Lean KAT inputs and
   a near-modulus one. It also asserts the layout offsets as it goes, so a value that is right and
   a base that is wrong cannot both pass.
2. **Backward — `the_narrow_witness_forces_the_whole_wide_trace`.** `poseidon2_wide_aux_from_narrow`
   is `narrowSat_forces_the_trace` as a program: it rebuilds all 352 values from the seed and the
   141, **never calling `poseidon2_trace`**, and must land on `poseidon2_permute_aux_witness`
   exactly. This is the direction that says the 211 dropped lanes really are determined.
3. **Against the emitted object — `the_lean_narrow_air_accepts_the_rust_witness`.** The 141
   Lean-emitted gates, walked by the **deployed interpreter** (`Ir2Air::LeanTable`, via
   `table_air_gates_accept`), accept the row the generator fills. Not a re-implementation: the same
   evaluator the prover uses, on the same bytes.
4. `the_arms_do_not_accept_each_others_witnesses` — the wide row truncated to 157 columns is
   REFUSED, with a guard that the two rows actually differ in that window first.

### ⚠ The falsifier is constructive, and it is a sweep

`every_narrow_column_is_pinned` bumps **each of the 157 columns** by one, **asserts the bump changed
the cell** before reading any verdict (this repo's minted class is a mutation that quietly became a
no-op while the gate stayed green), and demands refusal. `every_wide_column_is_pinned` runs the same
sweep on the deployed arm so the narrow result is read against a baseline measured the same way.

**Result: zero free columns on either arm.** The thirteen internal lanes at `aux + 64 … aux + 76`
are the ones that matter — those are exactly the columns whose fifteen wide siblings no longer
exist, and a witness is still pinned at every one of them.

Both poles are inside each test: the honest row is accepted before and after the sweep, so a
`table_air_gates_accept` that had degenerated to "always false" would fail the test rather than pass
it silently.

---

## §3 — THE MEASUREMENT: COUNTS, NOT MILLISECONDS

⚠ **This box is shared and heavily loaded, and a wall-clock ratio taken on it is not evidence —
not even as a ratio**, because leaf hashing is memory-bound and the quotient is compute-bound and
they degrade differently under contention. Every number below is a **count**: committed cells,
Poseidon2 permutations, proof bytes. All three are deterministic functions of `(config, trace)` and
reproducible on any box.

The counter is a `Permutation` wrapper that increments before delegating (the instrument
`ir2_phase_profile.rs` §D uses). `query_proof_of_work_bits` is **0** on every counted run: grinding
is a random search costing ~2^16 permutations on a transcript-dependent count, which would put
±65k of arm-dependent noise on the number being compared, and it is identical work on both arms.
Everything else is the deployed FRI shape (`lb = 6`, `q = 19`, `log_final_poly_len = 0`,
`max_log_arity = 3`).

### 3.1 — Exact, no measurement needed

| | wide | narrow | ratio |
|---|---:|---:|---:|
| committed aux lanes per permutation | 352 | **141** | **2.4965×** |
| standalone arm row (`seed ‖ aux`) | 368 | **157** | **2.3439×** |
| **deployed chip row (`CHIP_WIDTH`)** | **386** | **175** | **2.2057×** |
| Merkle-leaf permutations per chip row (`⌈w/8⌉`) | 49 | **22** | **2.2273×** |
| gate bodies | 352 | 141 | 2.4965× |
| `max_constraint_degree` | 7 | **7** | **1.0000×** |

⚑ **2.50× is the aux block; 2.21× is the chip's row.** The chip carries 34 non-aux columns
(`CHIP_AUX0 = 33` of selectors/inputs/outputs plus one multiplicity), and those do not move. Quoting
2.50× as the chip's win is already the flattering half of a pair.

The degree row is the load-bearing one: same `max_constraint_degree`, therefore the same
`log_blowup ≥ 3` floor and the same FRI ledger, therefore nothing is traded. `LeanTableAir::
max_degree()` — the deployed interpreter's own degree pass, not a declared constant — reads 7 on
both emitted artifacts.

### 3.2 — PER-CHIP, counted

`the_two_arms_counted_at_the_deployed_fri_shape` proves and verifies both arms through the same
`Ir2Air::LeanTable` interpreter at 2^6 / 2^8 / 2^10 permutations.

| rows | arm | cells | prove perms | verify perms | proof bytes |
|---:|---|---:|---:|---:|---:|
| 64 | wide | 23,552 | 216,262 | 2,237 | 220,622 |
| 64 | narrow | 10,048 | 109,555 | 1,532 | 149,319 |
| 64 | **ratio** | **2.3439×** | **1.9740×** | 1.4602× | 1.4775× |
| 256 | wide | 94,208 | 864,070 | 2,542 | 248,485 |
| 256 | narrow | 40,192 | 437,875 | 1,837 | 177,055 |
| 256 | **ratio** | **2.3439×** | **1.9733×** | 1.3838× | 1.4034× |
| 1024 | wide | 376,832 | 3,455,110 | 2,885 | 280,593 |
| 1024 | narrow | 160,768 | 1,750,963 | 2,180 | 209,186 |
| 1024 | **ratio** | **2.3439×** | **1.9733×** | 1.3234× | 1.3414× |

⚑ **The prover-permutation ratio is 1.973×, not 2.34×.** Committed cells fall 2.34× and prover
hashing falls 1.97×, because the quotient commitment and the FRI folding do not scale with the trace
width alone. The ratio is flat in height to four figures, so this is a property of the
arithmetization and not of one shape. **The previously circulating "2.11× prove" is a wall-clock
number**; 1.973× is what the permutation counter says, and it is the one that reproduces.

⚑ **Debug and release produced BYTE-IDENTICAL counts** (verified: the release build finished later
and the tables match digit for digit). That is the property the switch away from milliseconds was
for — these numbers do not move with the profile, the box, or the load.

### 3.3 — PER-BATCH, counted shape + derived projection

`the_deployed_batch_committed_census` proves the deployed transfer batch under the counting config,
reads every committed matrix's `(width, height)` off the rebuilt AIR set and the proof's own
`degree_bits`, and identifies the chip **by the emitted artifact's name** (`dregg-ir2-chip-v1` /
`dregg-ir2-chip-state16-v1`) rather than by its width — a width is a display name in this repo's
sense, and a census keyed on `386` would silently re-scope the moment another table hit that width.

Measured, deployed transfer batch: **prove 221,190 permutations** (including the self-verify),
**verify 4,040**, **331,386 proof bytes**.

| width | height | cells | leaf perms | permW | quotW | instance |
|---:|---:|---:|---:|---:|---:|---|
| 236 | 64 | 15,104 | 1,920 | 72 | 8 | main (descriptor) |
| **386** | **8** | **3,088** | **392** | 12 | 32 | **`dregg-ir2-chip-v1`** |
| 2 | 16 | 32 | 16 | 4 | 8 | `dregg-ir2-byte-v1` |

⚑ **THE MAIN TRACES ARE NOT THE WHOLE COMMITTED SET, and the two extra rounds DO NOT SHRINK.** The
prover commits three: the main traces, the per-instance LogUp permutation traces, and the quotient
chunks. Narrowing the chip touches only the first — its bus interface is untouched (same tuples,
same multiplicity columns) so its permutation trace stays 12 wide, and its `max_constraint_degree`
is untouched at 7 so its quotient stays 32 wide. Stopping the denominator at the main traces is
therefore quoting the flattering half *again*, one level up from the per-chip/per-batch split:

| committed set | cells | leaf perms | narrow cells | narrow leaf | cell × | **leaf ×** |
|---|---:|---:|---:|---:|---:|---:|
| main traces | 18,224 | 2,328 | 16,536 | 2,112 | 1.1021× | 1.1023× |
| + LogUp permutation | 22,992 | 2,936 | 21,304 | 2,720 | 1.0792× | 1.0794× |
| **+ quotient (the whole set)** | **23,888** | **3,048** | **22,200** | **2,832** | **1.0760×** | **1.0763×** |

> ### ⚑ **PER-CHIP 2.21× on the chip's own row → PER-BATCH 1.076× on the deployed transfer batch.**

The permutation and quotient widths are read **off the proof** (`permutation_local.len()`,
`Σ quotient_chunks[c].len()`), not modelled — and that reading is *checked* rather than assumed:
`trace_local.len()` is the same kind of opening over a matrix whose width is independently known
(the AIR's own `width()`), so a convention of one-opening-per-extension-element would fail that
assertion by a factor of four instead of silently re-scaling every number in the table.

**Independent cross-validation.** The `main + LogUp` row — 22,992 cells and 2,936 leaf perms —
reproduces `koalabear-migration.md` §3.3's span-dump census *exactly*, and its chip share
392 / 2,936 = **13.35%** is that note's figure to the digit. Two different instruments (a tracing
span dump of `coset_lde_batch` dims; opened-value counts off the proof) on two different days agree.
⚠ The 16.94% printed under "CHIP SHARE of the MAIN traces" is a **different denominator**, not a
correction of 13.35% — a reader comparing them without that sentence would think one of them wrong.

⚠ **The narrow-chip columns are arithmetic on measured dims, not a measured prove.** The chip cannot
be cut over until `ChipTableEmit` re-emits at `CHIP_WIDTH = 175`, and this lane deliberately did not
do that. What is measured is the batch's shape and its exact prover permutation count; what is
derived is what that shape becomes when one matrix loses 211 columns.

⚠ **And 1.076× is itself an upper bound on wall-clock.** The per-chip pair measures the gap between
the two: committed cells fall 2.34× there while prover permutations fall only 1.97×, because the
non-trace terms do not follow the width. The same dilution applies inside the batch, so the true
end-to-end batch factor is **below 1.076×** — call it ~1.05–1.07× until the cutover makes it
measurable. **It is not 2.11×, and it is not 2.34×.**

### 3.4 — So is it worth doing?

Yes, and the reason is not this batch. `s` — the chip's share — is what the lever multiplies, and
`s = 13.35%` is **one descriptor**, the thinnest chip workload there is: a single transfer with
eight permutations. Chip-heavy goldens (`poseidon2-hash-arity2`, `merkle-membership-4ary-d4`) and
above all the **recursion tower**, which is ~75% in-circuit Poseidon2, run `s` far higher, and at
`s → 1` the batch factor approaches the per-chip 1.97×. The honest statement of the win is
**"1.076× on the profiled transfer, approaching 1.97× as the workload becomes chip-bound"** — and
the number to quote for any *other* workload is that workload's own `s`, not this one's.

---

## §4 — THE FLAG DAY, VERIFIED AT SOURCE

`Poseidon2RoundGates.lean` §8g states the list. Each item below was re-read at HEAD rather than
relayed:

1. **`CHIP_WIDTH` 386 → 175** = `CHIP_AUX0` 33 + 141 + 1. `CHIP_MULT_NARROW` 385 → 174 and every
   derived offset moves with it (`ChipTableEmit.lean:105-120`). ⓘ The Rust mirrors
   (`descriptor_ir2.rs:3568-3578`) are *derived* from `POSEIDON2_PERM_AUX_COLS`, so on the Rust
   side this item is one identifier — `POSEIDON2_PERM_AUX_COLS_NARROW` — not a table of offsets.
2. **`CHIP_TABLE_AIR_JSON` and `CHIP_STATE16_TABLE_AIR_JSON` re-emit.** Gates 391 → **180**
   (31 selector + 352→141 permutation + 8 output; state16 is +1 selector), defs 1,078 → **1,286**.
   The AIR fingerprint moves ⇒ **VK rotation**, and the old artifact must REFUSE to load.
   ⚑ **Two Lean theorems name the output block's column arithmetic literally** and must be
   re-stated with it: `ChipTableEmit.forged_out_lane_is_unsat` and the lemma above it both read
   `CHIP_AUX0 + 336` (= `352 − 16`), which becomes `CHIP_AUX0 + 125` (= `141 − 16`). They are the
   teeth on a forged output lane, so re-deriving them is not bookkeeping.
3. ✅ **The witness generator** — this lane. `poseidon2_permute_aux_witness_narrow` exists, is bound
   to the Lean in both directions, and the falsifier shows every one of its columns is pinned.
   What still has to happen at the cutover is the *call-site* swap: `descriptor_ir2.rs:4780/4789/
   4800` (`chip_permute_state16`, `perm_aux`, `perm_lanes`) and the chip trace builder must fill
   141-value blocks at the new offsets. Those sites are `poseidon2_permute_aux_witness`'s four
   in-`descriptor_ir2` callers; the other seven callers are the **v1 hash sites**
   (`lean_descriptor_air.rs:1639/1877/7835`, `dsl_p3_air.rs:981`) and two test files, which are a
   separate Rust-authored spelling of the same algebra, are debt already, and this lane does not
   extend them.
4. ⚑ **`sbox_registers: 1` is not a comment — it is a REFUSAL.** `parse_chip_params`
   (`descriptor_ir2.rs:1546-1557`) hard-refuses a chip descriptor whose params disagree, and
   **40 files under `circuit/descriptors/` declare it**. Re-deciding it (the narrow arm is the
   inline-`x^7`, zero-register layout, so upstream's convention is `0`) or deleting it re-emits all
   40. ⚠ The docblock at `descriptor_ir2.rs:3526` calls it *"a frozen descriptor pin (no regen
   off-cycle)"* — **"frozen" is on this repo's own list of words that mean you are shipping the
   lesser design.** Nothing holds the old shape. Re-emit them.
5. **Every fixture carrying a chip trace regenerates**, and the devnet re-genesises.

⚠ **Two shapes that agree today disagree later.** The wide arm — `permEmission`, the
`dregg-perm-arm-wide-v1` fixture, and `poseidon2_permute_aux_witness` — exists only until item 2 is
discharged. It is a measurement baseline, not a permanent second implementation.

---

## §5 — REDS THAT ARE NOT THIS LANE'S

* `cargo nextest run -p dregg-circuit` cannot compile the crate's test set:
  `circuit/tests/fri_blowup_global_knob_survey.rs:719` is `E0277` (`Vec<&&Measured>` from an
  iterator of `&Measured`). It is a **working-tree** edit by another lane — HEAD's copy of that
  file does not contain the line — so it is not touched here. This lane's binary is built with
  `cargo test -p dregg-circuit --test poseidon2_narrow_witness`, which does not compile it.
* The whole-workspace `lake build` red in `KimchiStepMainPins01/03/05` does not reach this lane:
  `PermArmTableEmit.lean` imports `Dregg2.Circuit.Emit.Poseidon2RoundGates` and nothing else, and
  `lake build Dregg2.Circuit.Emit.PermArmTableEmit` is green (9.0 s, exit 0). Verified by building,
  not by assuming.
* ⚑ **The measurements were taken on a shared working tree carrying three other lanes' edits, and
  each was checked to be off this lane's code path rather than assumed to be** (working trees are
  systematically greener — and here, differently-shaped — than HEAD):
  - `circuit/src/descriptor_ir2.rs` — **docblock only**, an 08-04 correction being retracted. No
    code, so `instance_airs` builds the same instance set as HEAD and the census is HEAD's census.
  - `vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs` — a real fix (`bit_reverse_rows()`), but on
    `get_evaluations_on_domain`'s **slow path**, taken only when `lde.height() < domain.size()`,
    i.e. `log_blowup < ⌈log₂(d−1)⌉ = 3`. Every number here is at `log_blowup = 6`, where the fast
    path is taken and the delta is a no-op.
  - `vendor/plonky3-challenger-82cfad73/*` — entirely the **PoW grinding** search. Both PoW knobs
    are 0 in the counting config, so it is not on the path at all.
* This lane adds **zero `#guard`s**. Every new Lean assertion is a named theorem: two
  `#assert_axioms` (kernel-clean — `arm_widths`, `permArmTables_routes_both`) and two
  `#assert_compiled` (`arm_tables_shape`, `arm_cost_ratio`, compiled evaluation of the emitted
  records, said out loud).
