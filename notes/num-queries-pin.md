# The recursion FRI verifier now pins `num_queries`

**Repo:** `~/dev/plonky3-recursion` (branch `update-plonky3-rev`), consumed by breadstuffs
via `p3-recursion = { git = "https://github.com/emberian/plonky3-recursion", rev = "fc3c6df" }`.
**Date:** 2026-08-14. **Status:** pin landed as `52e1fab` (unsigned — 1Password rejected the
signature while running autonomously), constructive falsifier landed and proven red-capable,
family audit below (one further hole found, named, not fixed here).

⚠ **Not yet reachable from breadstuffs.** `breadstuffs/Cargo.toml:370-373` pins
`rev = "fc3c6df"`. The pin only reaches the deployed path once `52e1fab` is **pushed** to
`github.com/emberian/plonky3-recursion` and those four lines are bumped. Pushing is an
outward-facing act, so it is left for the operator. **Until that bump, the hole described
below is still open in breadstuffs.**

---

## 1. The hole, at source

`recursion/src/pcs/fri/verifier.rs:1378` (pre-fix):

```rust
let num_queries = fri_proof_targets.query_proofs.len();
```

…and `FriVerifierParams` (`recursion/src/pcs/fri/params.rs`) had no `num_queries` field.
Every downstream check in the function compared the proof against **itself**:

- `num_queries != index_bits_per_query.len()` — but `index_bits_per_query` was built as
  `(0..num_queries).map(…)` in the caller, from the same proof-derived count
  (`targets.rs:794` non-hiding, `targets.rs:1184` hiding). Self-satisfying.
- `num_queries == 0` — a floor of one, not a pin.

So the FRI query count — a **soundness parameter, linear in the security bits** — was
carried in the proof being verified. The field wall is compiled into the verifier; the
query wall was carried in the proof.

**The native verifier pins it** and is the reference implementation
(`~/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/fri/src/verifier.rs:241`):

```rust
if proof.query_proofs.len() != params.num_queries {
    return Err(FriError::QueryProofCountMismatch {
        expected: params.num_queries,
        got: proof.query_proofs.len(),
    });
}
```

A stale docstring at `recursion/tests/frozen_ivc_replay.rs:92-95` even said the quiet part —
*"num_queries (19) + folding arity are read from the proof in-circuit"* — and treated it as
fine. It has been corrected.

## 2. The pin

`FriVerifierParams` gains `num_queries: usize`, placed to mirror the native `FriParameters`
field order. Both constructors (`with_mmcs`, `unsafe_arithmetic_only_for_tests`) take it
positionally, so **every call site is an arity error** and had to be looked at by hand — no
site could silently keep the old behaviour.

The check lands in two places:

1. **The chokepoint.** `verify_fri_circuit` takes a new `expected_num_queries: usize`
   parameter (exactly parallel to the `log_blowup: usize` it already took) and checks it as
   the **first** shape check, before anything else. This is public API (`pub use
   verifier::verify_fri_circuit`), so any future caller is covered.
2. **Both `RecursivePcs::verify_circuit` impls** (`targets.rs`, non-hiding and hiding), before
   the challenger sampling loop — so an attacker-chosen count never drives `sample_bits` at
   all.

Message, both places:

```
FRI query proof count must equal the configured number of queries: expected {N}, got {M}
```

The pin is an **equality**, not a lower bound, mirroring native: a proof with *more* queries
than configured is also refused, because the Fiat–Shamir transcript would otherwise diverge
from the native verifier's.

Files changed:

- `recursion/src/pcs/fri/params.rs` — the field + both constructors.
- `recursion/src/pcs/fri/verifier.rs` — signature + chokepoint check.
- `recursion/src/pcs/fri/targets.rs` — both `verify_circuit` impls.
- `test-utils/src/lib.rs` — `TestFriScalars.num_queries`, read back from
  `FriParameters::new_testing` so the config and the verifier params cannot drift.
- 12 test/example construction sites, each given its **own config's** count (never the
  proof's).
- `recursion/examples/common/mod.rs` — `create_fri_verifier_params(fp, security_level)`
  now derives `num_queries` by the *same expression* `create_config` uses,
  `(security_level - fp.query_pow_bits) / fp.log_blowup`.

## 3. The falsifier — constructive, and proven red-capable

`recursion/tests/fri.rs::test_fri_verifier_pins_query_count_against_config`.

Deliberately **not** the shape a prior lane found in six `InvalidPowWitness` teeth (all six
were transcript desyncs; nothing had ever mutated the witness). This one:

1. Builds a **real, passing** FRI proof at the configured count (positive control: it must
   verify).
2. **Removes query proofs from it** and their index bits.
3. **Asserts the mutation took effect** — `assert_eq!(len, 1)`, `assert_ne!(len, before)`,
   and that the index bits track it — *before* any verdict is read. If a refactor makes the
   mutation a no-op, these fail loudly instead of the test passing on an unmutated proof.
4. Only then reads the verdict, and asserts the **message** names the query-count pin and
   both counts (`expected {configured}`, `got 1`) — so it cannot drift onto a different
   refusal and still look green.
5. Case 2 does the same in the other direction (a duplicated query proof) to pin the
   equality.

**Red-capability, measured.** The pin was temporarily disarmed (`if false && …` at all three
sites) and the test run:

```
test test_fri_verifier_pins_query_count_against_config ... FAILED
panicked at recursion/tests/fri.rs:1046:
  a proof with fewer queries than configured must be REFUSED: ()
```

The `Ok(())` in that panic is the finding, not just a failed assertion: **with the pin
disarmed, the one-query proof verified.** The pin was then re-armed (`grep "if false &&"
recursion/src/` → empty) and the suite re-run green.

Two existing tests were audited for the same drift hazard:

- `test_fri_verifier_rejects_zero_query_proof` clears `query_proofs`, so the new pin would
  have fired **first** and that test would have stopped exercising the zero-query refusal
  while still passing. It now configures `expected_num_queries = 0` and asserts the message
  contains `"at least one query"`.
- `test_fri_verifier_rejects_per_query_schedule_mismatch` mutates within a fixed query
  count; unaffected, now passes `setup.num_queries`.

## 4. Family audit — every FRI soundness knob in the recursion path

Reference column is the native `p3_fri` verifier at rev `82cfad73`.

| knob | native | recursion, before | recursion, after |
|---|---|---|---|
| `num_queries` | pinned — `QueryProofCountMismatch` (`verifier.rs:241`) | **UNPINNED** — read off the proof | **PINNED** (this lane) |
| `log_blowup` | pinned | **pinned** — `FriVerifierParams.log_blowup` sets `log_max_height` in `targets.rs`, and `verifier.rs:1588` checks the max reduced-opening height equals it | pinned |
| `log_final_poly_len` | pinned — `FinalPolyLengthMismatch` | **pinned** — recovered from the configured `log_max_height`, then `final_poly.len() == 1 << it` is checked against the proof (`verifier.rs:1498`) | pinned |
| `commit_proof_of_work_bits` | pinned — `check_witness` | **pinned** — `params.commit_pow_bits` drives `check_pow_witness`, which samples that many bits and `assert_zero`s each; the count is compiled into the circuit shape (`challenger/circuit.rs:385-406`) | pinned |
| `query_proof_of_work_bits` | pinned | **pinned** — same mechanism | pinned |
| `max_log_arity` | pinned — `checked_log_arity` enforces `1..=max`, `InvalidLogArity` | **UNPINNED** — see below | **still UNPINNED** |
| MMCS on/off (`permutation_config`) | n/a | pinned — `None` reachable only via `unsafe_arithmetic_only_for_tests` | pinned |
| Merkle `cap_height` | derived from `commit.num_roots()` | derived from `commitment_cap.len()` (`mmcs.rs:335`) — **same as native**; the cap *is* the binding commitment, not a knob | unchanged |

### ⚑ New finding: `max_log_arity` is unpinned in the recursion path

`FriProofTargets::new` (`targets.rs:82-91`) reads `log_arities` from
`input.query_proofs.first()`, and `FriVerifierParams` has no `max_log_arity`. The recursion
verifier checks only that (a) `log_arities.len() == num_phases`, (b) every query's per-phase
`log_arity` agrees with query 0's schedule, and (c) the sibling coefficient count matches
`(2^log_arity − 1) · EF::DIMENSION`. Native additionally enforces `1 ≤ log_arity ≤
max_log_arity` per round.

**What is mitigated:** the *sum* is pinned transitively. `total_log_reduction =
log_max_height − log_final_poly_len − log_blowup`, and `log_max_height` is checked against
`reduced_by_height[0].0` (`verifier.rs:1588`), which comes from the verifier-supplied
`commitments_with_opening_points` domains. An attacker cannot shrink the total reduction.

**What is not:** the *partition* of that sum into rounds is attacker-chosen, and
`log_arity = 0` is not rejected. A zero-arity phase leaves `cumulative_bits` unadvanced, so
`folded_height_after` gets a repeated entry and the roll-in lookup
`folded_height_after.iter().position(|&fh| fh == h)` (`verifier.rs:1615`) resolves to the
first match — a roll-in can be routed to the wrong phase.

**Why this matters and what I am NOT claiming:** the round structure is an input to the
commit-phase error term, and the commit-phase column (`friCommitLedger` → `ε_C = 51` at the
deployed wrap) is the one the repo's own notes say binds *below* Johnson. So this is a second
soundness parameter under child control, on the binding column. **I have not derived the
direction or the magnitude** — do not quote a number for it. It is a distinct hole from the
one this lane closed, it is live today (the deployed config sets `max_log_arity: 1`, so any
other schedule is off-config and accepted), and the fix is the same shape as this one:
`max_log_arity` into `FriVerifierParams`, `checked_log_arity`-equivalent per round.

⚠ Sequencing note for whoever takes it: `test_fri_verifier_rejects_per_query_schedule_mismatch`
tampers by `step.log_arity += 1` under a `max_log_arity = 1` config, so a max-arity check
placed where native places it will fire **first** and that test will stop exercising the
per-query schedule check while still passing green. It needs a config with
`max_log_arity ≥ 2` to keep testing what it names.

## 5. Soundness delta, with the regime named

Machinery: `~/dev/minidregg/Assurance/TwoRegimeQueryBudget.lean`. The file defines **three**
regimes (`:105-112`), with `Regime.status` (`:129-132`) marking them:

- **UDR** — unique decoding, `θ = (1−ρ)/2`. `.proven`. **The only unconditionally proven
  regime in the file** (`udr_reportable`, `:138`).
- **JBR** — Johnson, `θ = 1−√ρ`. `.idealised` (BCIKS20 at `m → ∞`).
- **CBR** — capacity, `θ = 1−ρ`. `.withdrawn`; `cbr_not_reportable` (`:146`) is a theorem.

Deployed IR-v2 point (`ir2`, `:320`): `log_blowup = 6`, `num_queries = 19`,
`query_pow_bits = 16`, commit PoW `0`.

| | UDR (**proven**) | JBR (idealised) | CBR (withdrawn) |
|---|---|---|---|
| per query | `1 − log₂(1+ρ)` = 0.9776 bits | `lb/2` = 3 bits | `lb` = 6 bits |
| **configured, q = 19** | **34** | 73 | 130 |
| q = 5 | 20 | 31 | 46 |
| q = 2 | 17 | 22 | 28 |
| **a malicious child's q = 1** | **16** | 19 | 22 |

`ir2_three_regimes` (`:354-357`) proves the 34/73/130 row; **`unpinned_query_count_collapses_the_column`
(`:511-513`) proves the q = 1 row's 16/19 and names this exact defect** — it cites
`recursion/src/pcs/fri/verifier.rs:1378` in its docstring (`:482-494`). The q = 2 and q = 5
rows are not in the file; I computed them in exact rationals against the file's own `queryErr`
/ `QErr.Bits` predicate.

**The delta.** Before the pin, a malicious child chose its own security level and the cheapest
choice cost **2^16** — the query grind alone, with the entire 19-query column worth ~1 bit on
top. After the pin, the child must meet the configured 19, restoring the column to
**2^34 at UDR**.

**Name the regime, because the pair is not at parity:** the honest headline is **16 → 34 bits
at UDR**, the only proven regime. `19 → 73` is the *idealised* Johnson column and `22 → 130`
is the *withdrawn* capacity one. The repo's own exported ledger
(`breadstuffs/metatheory/Dregg2/Circuit/FriLedger.lean:203-204`, `@[export dregg_fri_ledger]`)
carries **only** `johnsonBits` and `capacityBits` — there is no UDR column in the thing that
gets quoted, which is precisely how a below-bar result reads as a win.

**And this is the query column only.** The commit-phase `ε_C` addend (`friCommitLedger`,
reading **51** at the deployed wrap) is untouched by this pin. `TwoRegimeQueryBudget.lean`'s
header (`:84-93`) explicitly **declines** to compose the two, because composing them correctly
requires stating `ε_C` at a matching `θ` and that is not done. **So do not report a composed
number here.** What is true: the query column stops being the cheap leg. What is not
established: what the system's overall bound is once `ε_C` is composed at a matching `θ`.

## 6. What this unblocks

The blowup work concluded the right answer is a **per-descriptor blowup/query knob**
(`breadstuffs/circuit/src/descriptor_ir2.rs:7160-7220`, `ir2_config`). That is exactly the
configuration in which children stop all running 19 queries — the masking condition. With the
pin, a descriptor's `(log_blowup, num_queries)` pair becomes a *verifier-side* commitment: the
recursion `FriVerifierParams` for that descriptor names the count, and a child at any other
count is refused with a message that names both numbers. Without the pin, shipping the knob
would have turned a latent hole live.

## 7. Verification state

- `cargo check --workspace --all-targets`: my edits clean. The **only** remaining errors are
  **43 pre-existing `E0004`s** in `recursion/examples/common/mod.rs` (`RecursionInput::NativeBatchStark`
  not covered) — the variant was added 2026-06-13 in `ccebf66`, which did not touch
  `recursion/examples/` (`git show --stat ccebf66 -- recursion/examples` is empty), and
  `mod.rs` was last touched 2026-05-17. **Zero non-`E0004` errors remain.**
  ⚠ `.github/workflows/ci.yml:106-108` runs `cargo run --example recursive_aggregation`, so
  that CI job has been unrunnable for two months. Fail-open gate class, separate lane.
- `cargo test -p p3-recursion --tests`: all suites green **except** `frozen_ivc_replay`, which
  fails at `circuit-prover/src/air/const_air.rs:203` with an index-out-of-bounds — a stale
  fixture, documented as such in HEAD's own commit `d690290` ("fc3c6df staled the fixtures, so
  the panic reads as a refusal"). Pre-existing, unrelated, unchanged by this lane.
- `recursion/tests/fri.rs`: 8/8, including the new falsifier, which was proven red-capable by
  disarming the pin (§3).
