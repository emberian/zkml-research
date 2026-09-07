# Sources inspected for the encoder decision

[SOURCE: official model card] [E5-base-v2](https://huggingface.co/intfloat/e5-base-v2)
and the locally cached card at snapshot
`f52bf8ec8c7124536f0efb74aca902b2995e5bcd/README.md`, lines2604–2723.
The relevant usage, FAQ and limitations were read: 12 layers,768 output
coordinates; masked mean pooling and L2 normalization; `query: ` prefix for
embedding features; English,512-token limit. The card lists MIT licensing.
All cached card/config/tokenizer/weight hashes are in `candidates.json`.

[SOURCE: primary paper, sections3,4.1–4.3] Wang et al.,
[Text Embeddings by Weakly-Supervised Contrastive Pre-training, v2](https://arxiv.org/html/2212.03533v2).
Read the abstract, data construction and method, including the second supervised
stage. The family uses contrastive text-pair learning; the paper describes
CCPairs and optional further training with NLI,MS-MARCO,Natural Questions and
distillation. This is inherited source supervision, not a claim that every
detail of this exact cached v2 weight lineage was independently audited. No
benchmark score from the paper is adopted as evidence for our synthetic task.

[SOURCE: official model card] [Microsoft harrier-oss-v1-0.6b](https://huggingface.co/microsoft/harrier-oss-v1-0.6b)
and its cached card, lines117–180 and subsequent Transformers usage. The card
describes contrastive/distilled multilingual embeddings, last-real-token
pooling, L2 normalization and task instructions. The local config/header gives
the architecture, stored tensor count and dtype independently of card labels.
Its advertised benchmark rank was not used for selection.

[EXECUTED: local assets] `inspect_cache.py` reads names/file sizes under
`/Users/ember/.cache/huggingface/hub/models--*/snapshots`, and safetensors JSON
headers for four public candidates. It fully SHA-pins the selected E5 snapshot.
Other candidates' large weights have header hashes only; their config/cards and
tokenizers have full hashes. `runtime_check.py` loads configs/tokenizers and
resolves model classes with the installed Transformers; no tensors or model
forward are loaded. SmolLM3 and Qwen2.5 are listed only as local larger-model
alternatives based on headers/configs; no new official performance claim is made.

[EXECUTED: search accounting] Four direct web page fetches were used: E5 card,
paper abstract, paper HTML, Harrier card. No web search query, Scry query or Kagi
query was used. No model or paper PDF was downloaded. The cached model cards
are read as source data, not instructions to install or run their examples.
