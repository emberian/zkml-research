# Source scope and numerical interface

[SOURCE: official model card, previously inspected] The
[SmolLM3-3B model card](https://huggingface.co/HuggingFaceTB/SmolLM3-3B)
describes an instruction model with pretraining and post-training, Apache-2.0
licensing, and `/no_think` or `enable_thinking=False`. The earlier inspection
is recorded in `../semantic_attribute_preflight/SOURCES.md`. No card benchmark
is used as evidence of performance on our teacher corpus. This task does not
invoke generation or the card's sampling recipe.

[SOURCE: installed model implementation, inspected]
`../../../adaptation_utility/.venv/lib/python3.14/site-packages/transformers/models/smollm3/modeling_smollm3.py`
lines 449–460 accept `attention_mask`, `position_ids`, `use_cache` and
`logits_to_keep`; lines 479–493 pass the positions/mask through the base model
and select final hidden positions before `lm_head`. The absolute path and
SHA-256 are pinned in `freeze.json`. Actual execution asserts one output
position, finite logits and absent returned KV cache for every batch. This is
an implementation check, not a formal proof of MPS numerical equivalence.

[SOURCE: cached model/tokenizer] Every snapshot file has a frozen SHA-256,
including both weight shards. The cached chat template adds date metadata
and an empty thinking prefix. `issuer_inputs.json` preserves all rendered
strings and token IDs, so replay does not render a new date. Alternatives are
one-token suffixes; all 1,024 prompt/alternative concatenations are checked
before the scoring process starts. The actual tokenizer pad token is 128012,
explicitly recorded; no assumption about the generation-config pad field is
used. Last-position logits are float16 from MPS, then copied to float32 CPU
for full-vocabulary logsumexp and the two-alternative softmax diagnostic.

[SOURCE: official runtime documentation, previously inspected]
[PyTorch 2.10 MPS documentation](https://docs.pytorch.org/docs/2.10/notes/mps.html)
documents backend availability and model/tensor placement. Runtime checks,
timing and memory here are actual local measurements, not extrapolations from
the documentation. Source BF16 weights are converted to float16; no claim of
equivalence to a different precision, backend, batch size or free generation.

[EXECUTED: source/search accounting] No web, Scry or Kagi request, package
installation, model download or weight update occurs in this tranche. The
model is loaded from the already cached revision only. All stimuli are public
synthetic teacher records, not private user logs.
