# Greedy decoding was verified; the fixed semantic interface still failed

[EXECUTED] This single authorized correction used the identical eight teacher
inputs and prompt/token IDs, model, MPSfloat16 backend and parser. All eight
actual internal generation-configuration merges were captured and asserted
to select **greedy_search with do_sample=False**. The previous sampling-default
warning did not recur. Every response nevertheless contained prohibited markdown
fences, so the unchanged strict parser accepted **0/8**. No further model
attempt, parser relaxation, semantic prompt change or held-out test was run.

## The implementation correction

[EXECUTED] `run.py` supplies use_model_defaults=False and explicit
do_sample=False, temperature1.0, top_p1.0 to generate(). The latter parameters
are inactive under greedy decoding. A wrapper around the model's actual
`_prepare_generation_config` delegates to the original method, saves the
returned configuration, then asserts its mode/flags before returning it to
the normal generation dispatcher. It records/asserts rather than modifies
the returned configuration. All eight calls used one beam, max32 new tokens
and per-request KV caching. `effective_configurations.json` retains each
complete effective configuration and its corresponding output index.

[EXECUTED] All26 files listed by the original manifest were verified unchanged
before and after execution. The original sampled/protocol-deviating attempt
remains intact. There have been two physical model attempts in total, each on
the same eight teacher inputs: the first deviated from the intended mode; this
one corrected that implementation mismatch. Results are not selected or pooled
across the two runs.

[SOURCE: exact runtime cause] The original no-model diagnostic and
`../PROTOCOL_DEVIATION.md` pin Transformers4.57.3
`GenerationMixin._prepare_generation_config`, whose default merge had replaced
the original requested mode. The correction uses the same installed source,
SHA`a20024b1e82ed5361a524d238d2197be5407abc91297dd9888c57e8284d63fef`.
The decoding assertion is taken from the actual merge during each new call,
not merely from a saved intent configuration.

## Complete output and semantic observations

[EXECUTED] Every response was a JSON-looking payload inside a markdown fence.
Every output reached EOS before the32-token cap. The table transcribes all
visible payloads; it does not turn them into accepted feature vectors.

| Teacher ID | Gold(a,b) | Printed payload(a,b) | Raw format | Strict acceptance |
|---:|---|---|---|---|
|0|(0,0)|(0,0)|markdown-fenced JSON|refused|
|16|(0,1)|(0,1)|markdown-fenced JSON|refused|
|32|(1,0)|(1,0)|markdown-fenced JSON|refused|
|48|(1,1)|(1,0)|markdown-fenced JSON|refused|
|64|(0,0)|(0,null)|markdown-fenced JSON|refused|
|80|(0,1)|(0,1)|markdown-fenced JSON|refused|
|96|(1,0)|(null,1)|markdown-fenced JSON|refused|
|112|(1,1)|(null,1)|markdown-fenced JSON|refused|

[EXECUTED: strict interface] The frozen parser's result is0/8 valid outputs,
0/8 accepted correct pairs and0/16 accepted correct attribute bits when malformed
responses count as wrong. `raw_outputs.json` preserves exact strings, token
IDs, parse errors, timings and configuration-call indices. No fence stripping
or fallback was applied in the encoder.

[DERIVED: visible-content diagnostic only] Literal transcription of the raw
payloads shows11/16 printed bits matching the oracle, three nulls and two wrong
bits; four of eight printed pairs match. `audit.py` checks those transcriptions
against the complete exact raw strings. These are diagnostic observations,
**not accepted-output accuracy**, a repaired parser result, or a utility claim.
The dry-soil answer for teacher48 and formal-occasion answer for teacher96 are
wrong, so changing formatting alone would not remove every observed failure.

## Model, prompt and actual costs

[EXECUTED] The unchanged model is cached SmolLM3-3B snapshot
`a07cc9a04f16550a088caea529712d1d335b0ac1`,3,075,098,624 parameters, with both
weight shards fully hashed against the prior freeze. Cached BF16 weights were
converted tofloat16 for MPS. The environment remains macOS26.6.1-arm64,
Python3.14.7, torch2.10.0 and transformers4.57.3. Eager attention,
eval/inference mode, two CPU threads/one inter-op and seed7901 were unchanged.
No model download, dependency install, backbone update or backend fallback.

[EXECUTED] The prompt remains the same222-token public semantic instruction,
with explicit bit meanings for four axes and no example answers. Total input
was2,340 tokens across the eight frozen prompts; total generation was165 tokens.
Rendered dates, source texts and token IDs were reused exactly. Gold oracle
fields did not enter model inputs; integrity hashing of oracle bytes does not
provide OS isolation between this local process and its scoring data.

[EXECUTED] The corrected process completed in30.7697s wall. CPU model loading
took1.4980s, transfer to MPS1.9118s, and all generation18.1776s wall/11.4711s
process CPU. First generation took5.5101s; the remaining seven ranged
1.5657–2.8255s. These are observed sequential short-request costs under shared
machine load. They are not a controlled speed comparison with the first attempt;
loading/generation times are nested inside the full process total.

[EXECUTED] Peak process RSS was10,474,782,720B. End-of-run MPS current allocation
was6,150,205,184B and driver allocation6,898,663,424B. These accounting views
overlap on a unified-memory machine and must not be summed. Complete per-request
memory, timing and token records are kept. The larger source model's cost is
not represented by the eventual small conjunction/window state dimension.

## Scope and verification

[INFERRED] This establishes execution of the intended greedy configuration,
and a failure of this fixed teacher-only source interface. It does not establish
a general language-model limitation: there are only eight familiar teacher
examples, one semantic prompt and one precision/backend. It also supplies no
held-out paraphrase transfer, W32 utility, encrypted execution, restricted reader
or no-master-read result. No contribution was admitted to a resident.

[DERIVED] The semantic instruction is added public task supervision. The
plaintext issuer still sees source tokens, activations and any inferred
attributes. Successful bit extraction in a future separately frozen test would
be actual language processing rather than generator-metadata access, but would
still not make source encoding operator-private. This run ends without further
prompt, parser or model changes.

[EXECUTED] The independent no-model audit validates all eight actual merge
configurations and output links, the complete strict denominator, EOS-before-cap
behavior, exact visible-payload transcriptions and all26 original file hashes.
It uses no held-out data and executes no model. The child manifest pins these
new artifacts without modifying the original manifest.

```text
python3 research/learn_infer_only/experiments/end_to_end/utility/semantic_attribute_preflight/corrected_run/launch.py prepare
python3 research/learn_infer_only/experiments/end_to_end/utility/semantic_attribute_preflight/corrected_run/launch.py run
python3 research/learn_infer_only/experiments/end_to_end/utility/semantic_attribute_preflight/corrected_run/audit.py
```
