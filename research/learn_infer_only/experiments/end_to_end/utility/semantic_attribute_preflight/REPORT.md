# The 3B runtime works; the first semantic preflight deviated from its contract

[EXECUTED] Cached SmolLM3-3B loaded and generated all eight teacher responses
on local MPSfloat16. **The intended greedy preflight was not fulfilled:**
Transformers silently substituted its model sampling defaults for the supplied
default-valued GenerationConfig fields. This is preserved as a protocol
deviation, not hidden behind the `settings.do_sample=False` intent in the
original result file. Seven responses also violated the unchanged JSON-only
format; only one response passed the strict parser. No held-out text or window
utility evaluation ran.

## Exact scope and added supervision

[EXECUTED] The sole prompt in `PROMPT.txt` defines four semantic axes and their
binary orientations: leaf flexibility, soil moisture, recipient familiarity,
occasion formality. It is222 tokenizer tokens (before chat metadata/source
text). The model gets those public definitions plus a task name and natural
source text. It does not receive generator attributes, example answers or a
history-dependent category label. This is explicit task/prompt supervision,
not unsupervised attribute discovery. The model also carries its inherited
pretraining and instruction tuning.

[EXECUTED] Teacher IDs[0,16,32,48,64,80,96,112] were fixed before model output:
the first entity and first template of all four attribute pairs in each route.
The exact rendered chat strings and token IDs were frozen in
`issuer_inputs.json`, including date metadata inserted by the cached template.
No selection/test text was read by the model. Eight teacher inputs cannot
establish paraphrase transfer or useful adaptation.

[SOURCE] The official card supports non-thinking mode via `/no_think` or
enable_thinking=False, and custom system instructions. Those mechanisms were
used. The card's general sampling recommendation was not our requested mode.
[SmolLM3-3B official card](https://huggingface.co/HuggingFaceTB/SmolLM3-3B).
The local template/config/tokenizer and both weight shards are fully SHA-pinned
in `freeze.json`, at snapshot`a07cc9a04f16550a088caea529712d1d335b0ac1`.

## The configuration error is independently reproduced

[EXECUTED] `run.stderr` explicitly reports replacing do_sample withTrue,
temperature with0.6 and top_p with0.95. `config_diagnostic.py` reproduces this
without loading a model: the original merge selects `sample`; setting
use_model_defaults=False selects `greedy_search`.

[SOURCE: installed implementation] Transformers4.57.3
`generation/utils.py:1704`, `GenerationMixin._prepare_generation_config`, treats
fields equal to global defaults as eligible for model-default replacement when
the saved model version is>=4.50 and use_model_defaults is unspecified. This
includes a supplied do_sample=False. At lines2378–2381, generate selects its
decoding mode from the merged configuration. Installed source SHA:
`a20024b1e82ed5361a524d238d2197be5407abc91297dd9888c57e8284d63fef`.

[DERIVED] A corrected implementation should disable that merge, pass the
decoding mode explicitly and assert/log the effective configuration returned
during the actual generate call. The original inputs, parser, prompt, model,
backend and precision must stay fixed if this is treated as a configuration
repair. No such second model attempt has been run in this report. The first
run remains in place, including its incorrectly optimistic intent metadata;
`PROTOCOL_DEVIATION.md` and `audit.json` identify the discrepancy.

## All eight observed outputs

[EXECUTED] The strict parser requires the entire stripped response to be JSON
with exactly keys a,b and integer0/1 ornull values. It rejects markdown,
duplicate keys, extra prose and extra fields. No markdown stripping or repair
was applied. The table below transcribes visible payloads for diagnosis;
fenced payloads are still **invalid**, not silently accepted features.

| Teacher ID | Gold (a,b) | Visible response payload | Format | Strict pair correct |
|---:|---|---|---|---|
|0|(0,0)|a=0,b=null|JSON inside markdown fence|no|
|16|(0,1)|a=0,b=null|JSON inside markdown fence|no|
|32|(1,0)|a=1,b=0|JSON inside markdown fence|no|
|48|(1,1)|a=1,b=null|JSON inside markdown fence|no|
|64|(0,0)|a=0,b=0|bare valid JSON|yes|
|80|(0,1)|a=0,b=1|JSON inside markdown fence|no|
|96|(1,0)|a=null,b=1|JSON inside markdown fence|no|
|112|(1,1)|a=null,b=1|JSON inside markdown fence|no|

[EXECUTED] The observed strict-format denominator is1/8 valid,1/8 correct
pairs and2/16 correct attributes when invalid outputs count as wrong. Every
response reached EOS before the32-token cap; the nulls are not truncation
artifacts. Raw outputs contain missing-attribute assertions and a wrong occasion
bit as well as formatting failures. These counts describe the deviating sampled
run, not the intended greedy policy, held-out semantics or a general model limit.

## Actual accelerator and source costs

[EXECUTED] The local runtime is macOS26.6.1-arm64, Python3.14.7,
torch2.10.0, transformers4.57.3. MPS is built and available; CUDA is unavailable.
The3,075,098,624-parameter model's cached BF16 weights occupy6,150,235,008B
including serialization metadata. They were converted tofloat16, loaded on CPU,
then moved to MPS. Eager attention, eval/inference mode, two CPU threads/one
inter-op and seed7901 were used. No new package, model download or server was
needed. [PyTorch2.10 MPS device interface](https://docs.pytorch.org/docs/2.10/notes/mps.html).

[EXECUTED] Preparation, including full asset hashes and prompt rendering,
took12.5180s. The model process took57.5335s wall. Within it, CPU loading
took2.9695s, transfer to MPS2.5090s, and the eight sequential generations
32.4579s total (12.6316s process CPU). First generation took10.6110s; subsequent
calls ranged2.4931–4.1656s. These timings overlap the total and must not be added
to it. The eight prompts contained2,340 input tokens and155 generated tokens.
They are observed short-request costs, not a benchmark or a useful-output rate.

[EXECUTED] Peak process RSS was8,215,461,888B. End-of-run MPS allocation was
6,150,205,184B, driver allocation6,703,661,056B. These are different memory
accounting views on a unified-memory machine and must not be summed. Request
KV caches were not supplied to subsequent generate calls; no resident learning
state or category history was present. Actual per-request timings, tokens and
memory snapshots are in the unmodified `results.json` and `raw_outputs.json`.

## What this permits next

[INFERRED] A larger explicitly prompted encoder is locally feasible to execute,
but this run does not establish a reliable semantic source interface. A narrow
decoding-configuration correction can test the intended prompt without changing
the task. A future held-out study would still need fresh text surfaces and
histories, frozen instructions, fixed handling/counting of malformed ornull
outputs, and no selection of successful examples. No such test is launched.

[DERIVED] If a later semantic encoder supplies bits from actual text, its small
conjunction vector could use the same W32 arithmetic. That would be different
from reading privileged generator metadata, but the plaintext issuer would
still see the entire input, prompt, model activations and attributes before
encryption. It adds explicit task semantics and a3B source model; it is not
operator-private source encoding, a no-master-read construction or a new
cryptographic result. No contribution was admitted to the encrypted resident
in this preflight.

[EXECUTED] The independent no-model audit checks all eight prompt hashes/IDs,
all outputs and strict counts, EOS-before-cap behavior and source pins. It
explicitly records `greedy_contract_fulfilled=false`. The freeze verifier hashes
oracle bytes for integrity before inference; oracle JSON is decoded for scoring
only after generation. Neither oracle fields nor record IDs enter model tokens.
This is code/data-flow separation, not OS isolation.

```text
python3 research/learn_infer_only/experiments/end_to_end/utility/semantic_attribute_preflight/launch.py prepare
python3 research/learn_infer_only/experiments/end_to_end/utility/semantic_attribute_preflight/launch.py run
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python research/learn_infer_only/experiments/end_to_end/utility/semantic_attribute_preflight/config_diagnostic.py
python3 research/learn_infer_only/experiments/end_to_end/utility/semantic_attribute_preflight/audit.py
```
