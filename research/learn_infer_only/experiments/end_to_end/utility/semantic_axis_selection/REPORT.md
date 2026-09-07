# Teacher-only semantic-axis likelihood selection

[EXECUTED] Direct 0/1 scoring, framing A, passed the frozen teacher gate:
246/256 factual bits (96.09375%) and 118/128 complete attribute pairs.
Both public tasks exceeded the required 85% bit accuracy. The alternative
Yes/No framing B reached 233/256 bits (91.015625%) and 112/128 pairs, with
plant accuracy below that task threshold. Selection therefore chooses A.
This is a reason to register a fresh evaluation, not held-out accuracy or
evidence of useful encrypted adaptation. No utility history ran.

## Complete teacher results

[EXECUTED] Each framing scores both axes of all 128 teacher texts. The tasks
are equally sized, so route-balanced bit accuracy equals overall accuracy.
Each table entry is correct/total; the denominator includes every frozen input.

| Scope | A factual bits | A exact pairs | B factual bits | B exact pairs |
|---|---:|---:|---:|---:|
| All teachers | 246/256 | 118/128 | 233/256 | 112/128 |
| Plant task | 118/128 | 54/64 | 105/128 | 48/64 |
| Letter task | 128/128 | 64/64 | 128/128 | 64/64 |
| Previously inspected eight texts | 16/16 | 8/8 | 12/16 | 5/8 |
| Remaining teacher texts | 230/240 | 110/120 | 221/240 | 107/120 |

[EXECUTED] The remaining 120 texts are teacher material, not a held-out set.
The previous eight examples, prompts and outputs were inspected before this
task. The two new framings were selected as a teacher-development experiment;
both were frozen before their first model score.

| Factual axis | A correct bits | B correct bits |
|---|---:|---:|
| Plant: leaf flexibility | 63/64 | 52/64 |
| Plant: soil moisture | 55/64 | 53/64 |
| Letter: correspondent familiarity | 64/64 | 64/64 |
| Letter: occasion formality | 64/64 | 64/64 |

[EXECUTED] Joint attribute strata expose a weakness hidden by the overall
teacher gate. Bit meanings are fixed public semantic definitions in
`prompts.json`: plants use flexible/hard leaves and wet/dry soil; letters use
known/unknown correspondent and formal/informal occasion.

| Task and true `(a,b)` | A bits | A pairs | B bits | B pairs |
|---|---:|---:|---:|---:|
| Plant 00 | 31/32 | 15/16 | 32/32 | 16/16 |
| Plant 01 | 32/32 | 16/16 | 29/32 | 13/16 |
| Plant 10 | 24/32 | 8/16 | 27/32 | 11/16 |
| Plant 11 | 31/32 | 15/16 | 17/32 | 8/16 |
| Letter 00 | 32/32 | 16/16 | 32/32 | 16/16 |
| Letter 01 | 32/32 | 16/16 | 32/32 | 16/16 |
| Letter 10 | 32/32 | 16/16 | 32/32 | 16/16 |
| Letter 11 | 32/32 | 16/16 | 32/32 | 16/16 |

[EXECUTED] A makes nine wet-soil errors and one hard-leaf error. The latter
is an exact float16 logit tie. A has two ties in total: teacher 36, soil,
correctly resolves to 0; teacher 50, leaf flexibility, incorrectly resolves
to 0. The tie rule was fixed before scoring. B has no ties, and all 23 of its
bit errors choose Yes/bit 0 when the true attribute is 1. These are descriptive
error counts, not a prompt or lexicon fitting step. Complete individual scores,
gold bits and input mapping remain in `scored_teacher_rows.json` and
`issuer_inputs.json`.

## What the score means

[DERIVED: frozen protocol] Each forward takes a public task name, one axis's
two public semantic definitions, and the source text. The model receives no
oracle attribute, teacher record ID, category rule, history label or previous
state. Record IDs in the JSON are bookkeeping; only the saved token sequence
is forwarded. The oracle file is first opened by the separate evaluator after
all 512 model examples have completed. No model weight was fitted.

[EXECUTED] A compares token IDs 15 and 16 (`0`, `1`). B compares token IDs
9642 and 2822 (`Yes`, `No`), mapping respectively to bit 0 and bit 1. All
1,024 prompt-plus-alternative tokenizations equal the frozen prompt tokens
followed by exactly one alternative token. Both choices use the same single
forward for an axis. Final-position logits are converted from MPS float16
to float32 CPU; log-likelihood is logit minus the full-vocabulary logsumexp.
There is no length normalization. Higher logit wins, and equality selects 0.

[EXECUTED] A's two alternatives have mean full-vocabulary probability mass
0.536536 (minimum 0.344039), while the mean chosen probability conditional on
those alternatives is 0.836906. Only 153/256 raw vocabulary top-1 tokens fall
inside A's alternatives. B has mean alternative mass 0.991307 (minimum
0.970590), mean conditional confidence 0.923282, and 256/256 top-1 tokens in
its alternatives. B is more concentrated on its requested answer tokens but
less factually accurate. No free generation was executed; these measures do
not establish that a generated full response would obey a format contract.

[DERIVED] Restricting a decision to two likelihood scores is part of the new
interface. It does not retrospectively accept either previous JSON preflight:
the original sampled run and the corrected greedy run retain their exact
outputs, parser failures, contracts and source hashes. All 26 original and
19 corrected manifest entries were verified unchanged before and after this
run and by the independent audit.

## Runtime, costs and provenance

[EXECUTED] One local model load, 64 actual batch forwards, 512 source-axis
examples, 84,832 real input tokens and 87,040 padded tokens. Each framing uses
256 axis examples, representing 128 two-axis texts. No generated tokens,
downloads, dependency installs, weight updates, held-out inputs or utility
history runs. The scoring process took 104.100 seconds wall and 14.882 seconds
process CPU on this shared local machine. Forward intervals total 93.901
seconds wall; likelihood calculation and device transfer total 0.837 seconds.
CPU model loading took 1.168 seconds wall and transfer to MPS 1.211 seconds.
These component intervals are contained in the process interval.

[EXECUTED] A's 32 batches took 46.621 seconds of forward time; B's took
47.280 seconds. A's measured batch throughput corresponds to 0.3642 forward
seconds per two-axis teacher text, excluding startup and likelihood bookkeeping.
That is an amortized batch measurement, not a measured singleton request
latency or a promise for longer inputs. Shape compilation and shared load
remain part of these observations.

[EXECUTED] The loaded model has 3,075,098,624 parameters. Cached BF16 weight
shards total 6,150,235,008 bytes; actual inference converts them to float16.
Peak process RSS was 10,271,293,440 bytes. At completion MPS reports
6,150,197,504 currently allocated bytes and 7,611,465,728 driver allocated
bytes. These unified-memory counters are not additive. The full batch costs
and raw counters are in `batch_costs.json`, `score_results.json` and `costs.csv`.

[EXECUTED] Runtime is Python 3.14.7, torch 2.10.0, transformers 4.57.3,
macOS 26.6.1 arm64, MPS available and CUDA unavailable. Execution uses eager
attention, float16, eval/inference mode, seed 7901, two CPU threads and one
inter-op thread, batch size 8, left padding with tokenizer pad ID 128012,
explicit masked cumulative position IDs, `use_cache=False`, and
`logits_to_keep=1`. No `generate` or generation-configuration merge occurs.
Each batch verifies a real final token, finite logits and absent KV cache.
No cross-backend, singleton-batch or other-precision equivalence was tested.

[SOURCE: cached source and installed implementation] Model:
`HuggingFaceTB/SmolLM3-3B`, revision
`a07cc9a04f16550a088caea529712d1d335b0ac1`.
The complete model/tokenizer inventory and rendered prompts are frozen.
Installed `modeling_smollm3.py` SHA-256 is
`a7e390e5b8ee2882cd3738537ac2991094ccffe5e522867054ec4aeb5d83c389`;
its lines 449–493 expose and implement the final-position logit interface.
Official-card and runtime-documentation scope are recorded in `SOURCES.md`.
No external benchmark is used as our result.

[EXECUTED] Pre-score freeze SHA-256:
`cb1fda3cef63a87677bc6882c2f8e3e45ab88ed1e95996f7a0adeea8cd93e758`.
Result SHA-256:
`08f08cb58e5a47e66ac70acbbadba298bf7eee2a821ba88e71c71068b903dfbf`.
The independent scalar audit covers all 512 bit scores and 256 framing/text
pairs, complete coverage, task counts, tie decisions, framing selection and
the gate. Maximum conditional-softmax scalar difference is 7.77e-8; scalar
log-likelihood subtraction agrees exactly with the recorded float32 values.
The audit does not rerun or prove the model's numerical internals.

[EXECUTED] Commands, from the repository root, with each full command,
return code, stdout and stderr retained separately:

```text
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_selection/launch.py prepare
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_selection/launch.py score
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_selection/launch.py evaluate
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_selection/launch.py audit
```

## Next hypothesis and boundary

[HYPOTHESIS] Freeze framing A and its numerical/token contract for one new,
separately registered factual-plus-utility evaluation. Use genuinely new names,
sentence surfaces and paraphrase cues, balanced over task and both attributes;
do not reuse the previous failed test surfaces. Keep all joint strata visible,
particularly hard-leaf/wet-soil cases. Introduce new history seeds before
examining scores, compare the same W32 routed add/expire learner with original
mean10 and the structured-attribute positive control, and require simple-rule,
nonlinear-rule, reversal and retained-skill results on the full paired
denominator. Fix any gates and small-feature map before new test encoding.
No extra prompt candidates or per-text corrections are justified by this run.

[DERIVED] A bounded 128-text factual run would require 256 axis examples,
the same count as framing A here; source cost is therefore concretely
measurable in minutes on this machine, with longer text and shared-load
uncertainty. The window arithmetic can be evaluated from saved inferred bits
without additional model calls. This recommendation has not executed a new
surface, utility history or ciphertext operation.

[DERIVED] The 128 teachers repeat two templates per task, eight entity names
per task, four attribute combinations and a small fixed lexical family.
They are correlated teacher material, not 128 independent semantic challenges.
Explicit task definitions and the model's inherited instruction training are
substantial supervision. Passing this gate cannot undo the earlier held-out
failures of other feature methods or establish broad language understanding.

[DERIVED] The trusted plaintext issuer sees the source text, token IDs,
activations and logits. The task route and semantic definitions are public.
Any later small feature, label encoding or encryption happens after this
plaintext computation. This is a candidate semantic issuer for an encrypted
small learner; it is not encrypted 3B cognition, operator-private source
encoding, a no-master-read construction or a release mechanism. No encryption,
authority, reader, companion tree or shared ledger was changed.
