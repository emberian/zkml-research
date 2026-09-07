# One prompted semantic-attribute encoder: teacher-only preflight

[HYPOTHESIS] An explicitly instructed larger language model may read the two
stated attributes from text, allowing a later learner to use conjunction
features without reading hidden generator metadata. This adds public task
semantics through a prompt and substantially greater source-model work. It is
not unsupervised attribute discovery or operator-private feature extraction.
This preflight is limited to eight teacher prompts, not a new held-out test or
window-utility run. It neither changes nor reopens the completed E5 results.

[DERIVED: frozen selection] Use cached SmolLM3-3B snapshot
`a07cc9a04f16550a088caea529712d1d335b0ac1`, with the existing installed
Transformers implementation. Select original teacher IDs
[0,16,32,48,64,80,96,112] before output: the first template and first entity for
each of the four attribute pairs in each of the two routes. Keep all eight
outputs, including malformed/refused/wrong answers. This tests runtime and
instruction feasibility on all teacher combinations; eight teacher examples
cannot establish paraphrase generalization or utility.

[DERIVED: one prompt] `PROMPT.txt` is the sole public system instruction. It
defines each semantic axis and its bit orientation, asks for exactly a JSON
object with keys a,b, and permits null when an attribute is unstated. It uses
the established task meanings, not a vocabulary or heuristic fitted to any
failed test. No examples with gold answers or history-dependent category labels
are included. Each user message contains only public route and source text.
Gold a,b values go into a separate evaluation-oracle file, never the prompt.

[SOURCE: interface] Use the cached chat template with enable_thinking=False
and the documented /no_think system flag. Save/hash the rendered prompt strings
and token IDs before inference, including any date metadata inserted by the
template. One request at a time, greedy decoding, max_new_tokens=32, no sampling,
no beam search, no retries or output repair. Parse the entire stripped response
as JSON; require exactly a,b with values integer0/1 or null. Markdown wrapping,
extra prose, missing/extra keys or duplicate keys count as malformed, not a
reason to broaden the parser after observing outputs.

[DERIVED: runtime choice] The local precheck reports torch2.10.0 on macOS26.6.1,
MPS built and available. Use MPS float16, eager attention, eval/inference mode,
no gradients, two CPU threads/one inter-op, seed7901. Weights cached as BF16 are
converted to float16 for this chosen run; no numerical equivalence to CPU or
BF16 is assumed. Keep the ordinary per-request KV cache, discard it between
requests. If this backend fails, retain the failure; do not silently switch
backend or prompt and present a selected success. No new dependency/download.

[DERIVED: cost and scope] Fully hash local model/tokenizer/config/template files;
record source versions, rendered prompt sizes, actual input/output tokens,
load/transfer/generation timings, process RSS and MPS allocated/driver memory.
No window history, encryption, private state, source text from the user or
held-out query enters this run. Report whether local inference and strict JSON
worked, with exact8-example/16-attribute denominators, and the added public
semantic supervision. Any future held-out study needs a separately frozen
prompt, new text surfaces, fresh histories and all failures in its denominator.
