# Shared-cache Stage0/EMA composition, 2026-09-06

[EXECUTED] The proposed extension has two checked Lean modules and **29 exact
axiom pins**. `Compiler/DisjointOraclePhases.lean` contributes 15; the actual
`Assurance/ResidentMixedPhases.lean` adapter contributes 14. No companion source
was edited. Exact frozen hashes are in `results/source_hashes.json` and the
proposed patch is `minidregg-mixed-oracle-phases.patch`.

[DERIVED, kernel checked] `ResidentMixedPhases.one_global_coin_receipt_bound`
(line 226) bounds the chance of any bad accepted Stage0 or EMA receipt by

```
((t0 + 14) * 4160 + (t1 + 9) * 161) / 2013265921^6.
```

The premise is a **two-phase schedule**. Stage0 runs for `t0` positional queries.
EMA then runs for `t1`; its complete prover strategy, opened plans, and receipts
may depend on the whole Stage0 response history. Every verification address of
every collected receipt must already occur in its respective phase log. Both
phases use one global first-occurrence cache. The proof does not charge the
whole `t0+t1` budget once for each descriptor, and does not add a receipt-count
factor. The EMA reduction explicitly requires `0 < delta < 1/153`; the Stage0
bound reuses its existing checked radius internally.

[DERIVED, kernel checked] The common-cache premise is implemented, not inferred
from byte lengths. `DisjointOraclePhases.mixed_trace_coupling` (line 126) proves
pathwise equality of the one-cache trace and two locally lifted traces.
`run_is_srTrace` (line 161) connects that cache fold to the inherited game's
actual `srTrace`. `ResidentMixedPhases.actual_trace_coupling` (line 67) and
`actual_query_count` (line 80) specialize it to the actual descriptors and prove
`t0+t1` total query entries. `splitGlobalCoins` partitions one uniform query
vector at exactly `t0`; `global_coin_positions` and
`uniform_global_coin_transport` prove the positions and uniform counting
transport. The extra 14+9 coordinates retained from the existing game are
**unused fallback coins**, not free service queries; query completeness is what
allows this existing soundness game to bound the logged event.

[DERIVED, kernel checked] `stage0_oracle_transport` and `ema_oracle_transport`
show equality for every typed query, including repeated or as-yet-unqueried
queries with the common fallback. `byte_cache_transport` (line 163) uses the
previously proved **actual** `programQueryBytes` injection to transport this
same cache to one byte-addressed domain. The source byte injection relies on
these two programs' different full-word widths (4131 and 153); arbitrary future
same-width descriptors still need an external namespace or an analogous
injectivity theorem. No claim is made that these are two independent supplied
oracles. The finite product used by the probability proof comes from the proved
partition of the one positional random vector and cache transport.

[DERIVED, kernel checked] `accepted_program_tags` (line 171) checks that accepted
receipt roots have the actual program labels 0 and 1. The bad events use the
existing context-bound Stage0 wrapper and opened-plan EMA wrapper and their
actual semantic arithmetic/Step predicates. These public full-word interfaces
remain public; this adds no hiding theorem. The probability statement is about
these wrappers, not a newly implemented runtime authorization service.

[DERIVED, kernel checked] Nonvacuity is the SAME pair of actual receipts in
`mixed_two_receipts_premise_inhabited` (line 187): Stage0 addition 1+2 and the
existing EMA 128→143/command248 receipt inhabit their 14- and 9-query complete
schedules, are both accepted under their own **shared sampled zero-coin log**,
carry distinct program tags, and give exactly 23 global queries.
`omitted_tag_breaks_coupling` (line 217) is the failed namespace sibling;
`zero_ema_budget_fails` is the failed query-completeness sibling.

[EXECUTED] The companion finite audit is
`experiments/randomness_composition/mixed/audit.py` with retained `report.json`.
All 64 six-bit positional coin vectors satisfy the shared/local pathwise
coupling and all 384 queried/fallback answer transports. The second strategy
adapts to the first history, and its event has probability 1/2 conditional on
every first-phase raw coin vector. The chosen union event has probability 3/4.
Removing tags causes 40 pathwise mismatches and changes that union probability
to 1. This is an executable specification audit, not an encryption/hash attack.

[EXECUTED] Reproduction:

```
python3 research/learn_infer_only/formal/randomness_composition/mixed/check.py Compiler/DisjointOraclePhases.lean Assurance/ResidentMixedPhases.lean
python3 research/learn_infer_only/experiments/randomness_composition/mixed/audit.py
```

The local checker uses the preserved run_006 dependency overlay (371 prior
pins), compiles the two new modules into owned regular output files, and records
source hashes before/after, commands, dependency-report hash, stdout/stderr,
and output hashes. All failed elaboration attempts are retained in `results/`;
none is an accepted proof. Some attempts exposed Lean's normalization of the
two descriptor challenge-type aliases; the final transport uses explicitly
typed `Ext6L` lists and a general cache/getD lemma. Exact axiom prints were
then pinned and recompiled. The final 29 pins comprise 15 standard triples,
7 `propext, Quot.sound`, 6 `propext`, and one axiom-free falsifier.

[OPEN] The first unsupported extension is arbitrary interleaving. A Stage0
receipt selected using later EMA responses is not representable by this
first-phase `expected`/`receipts0` function of Stage0 history alone. A general
interleaving simulator must reconstruct each program's adaptive local strategy
from its own responses plus a fixed tape for the other tagged cache, transport
the global cache and output selection, and prove exact query-budget accounting.
Neither the union lemma nor byte injectivity supplies that simulator.

[OPEN] Existing residuals remain: classical uniform-Ext6 ROM, deterministic
query-bounded strategies (independent auxiliary randomization can be averaged),
all prior oracle-correlated service transcripts charged/simulated, final-log
completeness rather than timestamped before-publication semantics, public
certificate words, and no byte-uniform cSHAKE/QROM/hidden-state claim. Zero
metered Scry/Kagi queries were used for this tranche.

[EXECUTED] Combined run `experiments/integration/results/run_010/report.json` passed: the preserved 499 pins plus these 29 pins, all 41 selected modules and four umbrellas, actual combined patch application and both source import-boundary checks, with all input/companion hashes and HEAD/status unchanged. The frozen combined snapshot is `formal/integration/minidregg-combined-resident-528.patch`. This remains a selected-module integration against cached read-only dependencies, not a full clean build.
