# Fixed EMA utility comparison on reused semantic fixtures

[DERIVED protocol, before evaluation] Evaluate exactly the already specified
private EMA law on the saved `utility/semantic_axis_successor/` feature bytes,
128 teacher texts, 128 query texts and all 64 histories (67000 through 67063).
This is a reused-data exploratory comparison, not another held-out estimate.
No model call, prompt change, parameter sweep, replacement history, query
selection, or new linguistic data is part of this run.

[DERIVED definition] State is two publicly routed arrays of four signed
registers, all initially zero. Read the already inferred bits from the saved
semantic features: a row has the single nonzero value 127 at `4*r+2*a+b`.
The selected address is `2*a+b`; the history's true signed category label
sets `u=120*y`. On Learn, only that route's selected register changes:

```
s[r,b] := floor((7*s[r,b]+u)/8)
```

All seven other registers remain unchanged. Infer returns the selected
register as the plaintext utility score; its label is +1 at zero or above,
and -1 below zero. The actual encrypted probe returns only the negative bit.
Scores therefore have different units from the window's integer dot product;
compare predictions and accuracy, not raw score subtraction as a utility gain.

[DERIVED denominators] Preserve the original teaching schedule: 64 plant,
64 letter, then 64 plant updates with the plant rule reversed. Query all
128 saved IDs at all three original checkpoints, for 24,576 EMA scores,
12,288 updates and 8,192 final labels. Retain every checkpoint state and
per-query score/label/target alongside each saved window comparator. Report
initial learning, exact untouched-route retention, reversal, rule strata,
task/attribute strata and paired history differences. Preserve the original
window's factual-error and synthetic-surface limits.

[DERIVED controls] Recompute the semantic W32 scores from direct last-32
routed observation sums and compare every score to the saved baseline.
Independently audit the EMA by collecting each bin's own label subsequence
and folding `s + floor((u-s)/8)`, rather than using the primary state loop.
Verify all range cases for `s` in [-120,120], labels ±120, plus the previously
registered `0 -> 15 -> -2` witness and a floor-versus-truncation falsifier.
No encrypted execution follows from these plaintext checks.

[DERIVED fixed materialization] Also translate the already materialized first
two histories and its unchanged 16 query IDs to compact EMA requests, all
384 Learn and 96 Infer events. There are no EMA expiry events. Keep full event
identity, public route, inferred address and oracle values in a PUBLIC
synthetic fixture. Do not select a better-performing subset after evaluation.

[DERIVED decision rule] This run is a comparison, not a fresh confirmatory
acceptance test. A later encrypted workload may be proposed if the fixed law
retains useful behavior on this reused corpus, with any regressions explicit.
Root schedules any launch to avoid CPU contention. Such a run remains a
functional/cost test with an unrestricted TFHE client reader key, public
synthetic fixture and no no-master-read, PQ, physical-isolation or protocol
privacy proof claim.

[EXECUTED provenance procedure] `freeze.py` will pin this contract, evaluator,
auditor and all consumed frozen source files before the first evaluation.
The launcher retains commands, output, exit codes and timings. All writes are
restricted to this directory; prior files and shared ledgers remain unchanged.
Search accounting for this tranche starts at zero web, zero Scry SQL/schema.
