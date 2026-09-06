# Generic contextual receipt composition and actual EMA adapter

[EXECUTED] The two proposed modules compile with **42 guarded theorem pins**:
24 in `Compiler/ContextualGate.lean` and 18 in
`Assurance/ResidentEmaAdaptive.lean`. Every observed footprint is exactly
`propext, Classical.choice, Quot.sound`. Their final source hashes and patch hash
are in `results/source_hashes.json`. The fresh combined integration also passed
with all 18 finished modules, 307 theorem pins, and four umbrellas:
`../../../experiments/integration/results/run_003/report.json`.

[EXECUTED: independent review] Separate dependency builds and compilation records
are `../../../experiments/adversarial_review/lean_contextual_gate_01.json` and
`lean_ema_adaptive_01.json`. Both pass at the frozen source hashes; the review
records the same-width namespace and mixed-game coupling limitations below.

[EXECUTED] Reproduce the focused checks with:

```sh
python3 research/learn_infer_only/formal/randomness_composition/generic/check.py \
  Compiler/ContextualGate.lean Assurance/ResidentEmaAdaptive.lean
```

The checker writes into this extension's own overlay and uses the preserved
265-pin integration's cached dependency oleans read-only. Each attempt retains
its command, source hashes before/after, stdout/stderr, dependency report hash,
and exit code. Failed elaborations remain recorded. The final combined run
recompiled all selected proposals together instead of trusting those proposal
oleans. Neither operation is a clean rebuild of the companion dependencies.

[DERIVED from checked theorems] `ContextualGate.context_receipt_sound:79` factors
the root-selected `gateRbr` argument over an arbitrary public context type with
decidable equality, a descriptor `d`, word width `n>0`, and `m` sumcheck
coordinates. The residual count must fit `2^m`. The word width is a separate
parameter, as in the existing `gateReduction`; the EMA adapter proves its width
is exactly the actual descriptor's 153 wires. `sound_reading:134` requires
**`0<δ<1/n`** and proves the single false-receipt bound
`(t+(m+1))*gatePrice d m` in the existing uniform-field classical ROM game.

[DERIVED from checked theorems] `all_logged_outputs_bound:317` then factors the
previous shared-log selector proof over that same generic reduction. Its
`AllOutputQueriesLogged` premise says every final verifier prefix of every
collected output occurs in the final common query log. After charging all those
queries in `t`, selection of a bad public full word changes no oracle moves and
therefore costs no extra factor in the number of outputs. This is the
query-bounded mathematical `SrProver` model, not a computation-time claim or a
private-witness extractor. Final-log completeness is not a runtime theorem about
publication order; prior oracle-dependent service histories must be charged or
explicitly simulated.

[DERIVED from checked theorems] `ResidentEmaAdaptive` instantiates those reusable
objects for the **actual EMA descriptor and existing check**:

- `stage0_reduction_is_existing:41` proves the generic Stage0 instance is
  definitionally the preserved earlier adaptive reduction.
- `single_bad_receipt_bound:68` gives `(t+9)*161/(2013265921^6)` with explicit
  `δ∈(0,1/153)`.
- `all_logged_bad_steps_bound:95` maps the actual wrapper's acceptance plus
  failure of `LogicalStep` to that same global false-descriptor event. It retains
  the same price for any positive number of query-complete collected receipts.
- `same_authorized_receipt_inhabited:182` uses one actual receipt for finality,
  canonical openings, recipient policy, the EMA wrapper, descriptor satisfaction,
  the changed logical state, and the generic adaptive verifier.
- `nine_query_same_receipt_premise_inhabited:205` supplies all nine actual query
  prefixes and proves the **same receipt** accepted under its own all-zero sampled
  shared log. `exact_radius_inhabited` supplies `δ=1/306`.
- The empty-log sibling fails query completeness; the linked/materialized
  `128→144` sibling fails the EMA descriptor. The positive update is `128→143`
  with command248. These are public byte witnesses, not secret state.

[EXECUTED: preserved failures] Early generic checks exposed a missing
`DecidableEq C` binder and underconstrained descriptor/context parameters in type
aliases. An initial Stage0 specialization exhausted definitional reduction when
trying to recover 4131 by unfolding the whole descriptor. Factoring the already
independent public word width `n` resolved that problem; no recursion-limit
increase was used to force the final Stage0 comparison. One intermediate guard
correctly refused a failed elaboration's `sorryAx`; no final source contains a
`sorry`, added axiom, or `native_decide`.

[EXECUTED] Proposed patch:
`minidregg-contextual-gate-ema.patch`, SHA-256
`4ea469e2e5122189d7f2a1028547cde536d9bccb5d7bf91d05966ed2b95a3d78`.
It adds only the two modules and their Compiler/Assurance umbrella imports.
Prerequisites are the preserved resident-release, adaptive-context, durable,
and EMA patches. Because independently produced umbrella hunks can overlap,
the combined integration patch is the checked maintainer application artifact.
All earlier patches remain unchanged; no companion writes or commits were made.

[OPEN] Hidden-state confidentiality, byte-digest-to-field distributional
transport, concrete hash realization, QROM security, and runtime publication
ordering remain outside these theorems. Metered Scry/Kagi queries: zero.

## Two-program boundary: what was proved and what is still missing

[DERIVED from checked theorem] `program_query_domains_disjoint:139` proves that
the existing Stage0 query encoding and proposed EMA query encoding cannot alias:
the prefix-decodable wire format contains a public-word vector of length4131
versus153. This holds even for arbitrary contexts and arbitrary intermediate
prefixes. `program_query_bytes_injective` embeds their disjoint sum injectively
into **one byte-address space**. This is an encoding fact; no separate-oracle
assumption is used. EMA did not previously have a concrete byte-oracle function;
its proposed encoder is transported to the existing generic `encodeMove` API.

[OPEN: precise next proof] A mixed-program price still needs a projection of a
single adaptive mixed query schedule into the two homogeneous `SrProver` games.
Disjoint query bytes alone do not construct that projection. It must preserve:

1. Repeated-address caching, including arbitrary cross-program query order.
2. The chosen output and every required verifier prefix.
3. A query count no larger than the original global `t`.
4. The sampled transcript distribution when other-program replies are simulated
   from auxiliary coins independent of the target oracle, rather than supplied
   as free correlated advice.

[HYPOTHESIS: target after that projection] For query-complete collected outputs
of both programs, a direct union bound would target

```text
((t+14)*4160 + (t+9)*161) / 2013265921^6.
```

The final union bound itself does not need event independence. The missing
content is the transcript-distribution/caching transport that would justify both
component prices in the **same** adaptive experiment. No theorem here claims
that target has already been proved. A future same-width descriptor family also
needs explicit descriptor identity in its query namespace; the present width
separation only covers these two particular formats.
