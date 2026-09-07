# Sources and what was inspected

[SOURCE: official card, interface/training summary]
[HuggingFaceTB/SmolLM3-3B](https://huggingface.co/HuggingFaceTB/SmolLM3-3B).
Read model summary, Transformers usage, disabling extended thinking and custom
system instructions. The card describes an instruction model with pretraining
and post-training, supports /no_think or enable_thinking=False, and lists
Apache-2.0 licensing. The chosen greedy decoding differs deliberately from its
general sampling recommendation. External benchmark scores were not used as
our task results. Card text was inspected, not model weights downloaded.

[SOURCE: installed/cached interface] The local snapshot's
`chat_template.jinja`, `config.json`, `generation_config.json` and tokenizer
files were read. The template inserts date metadata and an empty thinking
prefix in non-thinking mode. `issuer_inputs.json` pins each actually rendered
string and token sequence so its content is independent of future render dates.
`freeze.json` fully hashes every snapshot file, including both weight shards.

[SOURCE: official runtime documentation]
[PyTorch2.10 MPS backend](https://docs.pytorch.org/docs/2.10/notes/mps.html).
Read availability checks and moving modules/tensors to the MPS device. Actual
backend availability is measured locally; the documentation does not establish
that this particular model or precision will execute correctly.

[EXECUTED: local runtime precheck] The existing environment reports
macOS26.6.1-arm64, torch2.10.0, transformers4.57.3, MPS built and available,
CUDA unavailable. No packages, accelerators or servers were installed. The
preflight uses float16 and records any failure without substituting a backend.

[EXECUTED: search accounting] Three direct web page fetches: official SmolLM3
card, PyTorch stable MPS redirect, then version2.10 MPS documentation. No search,
Scry or Kagi query was used. No model or PDF download occurred.
