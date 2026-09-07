# One implementation correction of the frozen teacher preflight

[DERIVED: authorized correction] The first run's recorded do_sample=False
intent was replaced by model sampling defaults in Transformers4.57.3.
`../PROTOCOL_DEVIATION.md` and the no-inference configuration diagnostic retain
the evidence. This child run executes the originally intended greedy policy.
The first run, source, outputs and original manifest remain unchanged.

[DERIVED: fixed scope] Use the identical model snapshot, MPSfloat16/eager
backend, seed7901, sequential requests, max32 new tokens, per-request KV cache,
eight teacher IDs and exact rendered prompt/token IDs from `../issuer_inputs.json`.
Reuse the exact original strict parser function without relaxing its grammar.
No prompt, semantic definition, teacher example, model, precision or parser
changes. No held-out data, utility history or encrypted-system call.

[DERIVED: only behavioral correction] Supply use_model_defaults=False and
explicit do_sample=False, temperature1.0, top_p1.0 on generate(). Temperature
and top_p are inactive under greedy decoding. A checked wrapper around the
model's actual `_prepare_generation_config` method records its returned
configuration for every call and asserts mode=greedy_search, do_sample=False,
one beam and max_new_tokens32 before decoding proceeds. It also checks the
explicit merge flag. The wrapper records/asserts; it does not alter logits,
decode tokens, repair output or retry generation.

[DERIVED: stopping and reporting] Exactly one corrected attempt. Preserve any
failure, malformed response, null or wrong attribute. No retries after this run.
Report all eight raw responses and effective configurations, exact8-pair/16-bit
strict-parser denominators, timings and memory. This remains teacher-only
feasibility with a222-token public semantic instruction; it cannot establish
held-out language transfer, useful W32 adaptation or private source encoding.
