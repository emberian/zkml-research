# A cached semantic encoder is a principled next hypothesis

[INFERRED] **Use the frozen local E5-base-v2 sentence encoder for the next
bounded experiment.** It changes the representation's training objective and
bidirectional architecture, rather than merely making the unsuccessful tiny
causal model larger. No new inference or benchmark was run in this feasibility
review. This is a candidate decision, not evidence that the new encoder will
transfer the attributes or support useful encrypted adaptation.

## What is actually available

[EXECUTED] The inventory covers38 model directories immediately beneath
`/Users/ember/.cache/huggingface/hub`, traversing their snapshot trees with
`inspect_cache.py`. It found these complete weight/config/tokenizer candidates:

| Candidate | Pinned revision | Stored floating tensor scalars | Weight files, bytes | Architecture |
|---|---|---:|---:|---|
| E5-base-v2 |`f52bf8ec8c7124536f0efb74aca902b2995e5bcd`|109,482,240|437,955,512|BERT,12 layers,768 wide|
| Harrier-oss-v1-0.6b |`f9b9dc8d367d443f2479d27aa5d8d2850c0774ee`|596,049,920|1,192,133,232|Qwen3 embedding model,28 layers,1024 wide|
| SmolLM3-3B |`a07cc9a04f16550a088caea529712d1d335b0ac1`|3,075,098,624|6,150,235,008|causal LM,36 layers,2048 wide|
| Qwen2.5-0.5B-Instruct |`7ae557604adf67be50417f59c2c2f167def9a775`|494,032,768|988,097,824|causal LM,24 layers,896 wide|

[EXECUTED] E5's snapshot is438,967,710B in total; its weight file stores
109,482,240 F32 values plus512 I64 buffer entries. The other listed weights
are BF16. Counts come from safetensors headers, not rounded model names.
E5's ten local files, including tokenizer and official card, are fully hashed
in `candidates.json`. That file records absolute snapshot paths and each larger
candidate's header hashes. Directory existence alone did not count as complete:
for example, SmolLM3-3B-Base and OLMo-2-0425-1B snapshots lack model weights.
This inventory is not an absence claim about other caches or the entire disk.

[EXECUTED] The existing Python3.14.7 environment with torch2.10.0 and
transformers4.57.3 resolves all four model classes and loads their tokenizers
locally. E5 resolves `BertModel`/`BertTokenizerFast`, using the official card's
AutoModel route without installing sentence-transformers. This metadata check
does not establish successful weight loading or a forward pass. Harrier emitted
a tokenizer-regex warning under this environment; it remains recorded in
`runtime.stderr`, was not silently repaired, and needs review if that alternate
is chosen. E5 produced no corresponding warning.

## Why E5 tests something different

[SOURCE] The E5 source describes contrastive sequence representations built
from text pairs, with a later supervised training stage described in the paper.
The official usage uses masked mean pooling, L2 normalization and a `query: `
prefix for feature-extraction tasks. This is an intentional sentence-embedding
interface, unlike our earlier pooling of a next-token model's intermediate
activations. [Official card](https://huggingface.co/intfloat/e5-base-v2),
[paper method](https://arxiv.org/html/2212.03533v2).

[INFERRED] E5 is therefore a better controlled first change than the cached3B
causal model. It is smaller than our135M causal model by stored parameter count,
but its training objective is closer to paraphrase transfer. Harrier is also a
legitimate semantic-embedding alternate, with higher weight and compute costs
and a local tokenizer issue to settle. None of their reported external benchmark
results are evidence for our Boolean-rule teaching task.

## What the current failure does and does not diagnose

[EXECUTED] The frozen calibration fit had100% teacher attribute accuracy, but
the four selection heads scored31/64,32/64,32/64,57/64. New-text test heads
scored32/64,32/64,34/64,40/64; joint attribute accuracy was34/128. The plant
attributes were each at chance in both new templates. In correspondence,
relationship was18/32 and16/32, formality16/32 and24/32 across the two templates.
`failure_diagnostic.json` preserves every route/template cell and links the
unchanged source results by hash. These are diagnostics, not tuning data.

[INFERRED] This pattern motivates testing a representation trained for semantic
similarity. It does not justify adding word lists, hand-coded antonyms or an
ontology fitted to the failed texts. Teacher data had only one cue phrase per
attribute value, so perfect teacher fit did not establish robust semantic
attribute recovery. We have not isolated architecture, objective and pretraining
data as separate causal factors; selecting E5 changes all of them together.

## Cost basis and interface preservation

[DERIVED] E5 requires at least437,928,960B for its F32 parameter values alone;
peak inference memory and wall time remain unmeasured. This machine reports
103,079,215,104B physical memory, not all necessarily free. The metadata-only
runtime check's629,964,800B high-water RSS is not a model-inference measurement.

[DERIVED] At a hypothetical40 tokens, counting dense projection/feed-forward
and attention matrix multiply-accumulates only gives E5 about3.427 billion MACs
(6.854 billion FLOPs at2 FLOPs/MAC). Harrier is17.800 billion MACs on the same
length. `cost_estimates.json` states the config-derived formulas, excluded
softmax/normalization/activation/embedding/pooling costs, and the estimates for
all four candidates. These are arithmetic estimates, not predicted latency;
tokenization and padding can change the compared lengths.

[HYPOTHESIS: next interface] A fixed public Rademacher projection768→576 and a
bias coordinate can retain the exact577-coordinate/range127/W32 arithmetic.
Draw and hash one projection before test; calibrate center/scale using only
public teacher examples. A raw769-coordinate offline control can quantify the
projection's utility loss, but is not the577-coordinate encrypted interface.
The extra dense projection is442,368 public scalar products and441,792 reduction
adds per text; a stored float64 matrix is3,538,944B. It can be regenerated from
a pinned PRNG/version/seed. No history state may enter this feature map.

[DERIVED] This primary would add no attribute-label supervision. E5 brings its
inherited public pretraining/fine-tuning, the public teacher normalization uses
unlabeled source embeddings, and the resident still receives the usual signed
category-labeled updates. Raw source tokens and all encoder activations remain
visible to the entitled plaintext issuer. Moving them into a new encoder does
not make them operator-private or remove the separate full-key reader.

## How a later test stays fresh

[HYPOTHESIS: protocol requirements] Freeze a new contract, new128 complete text
surfaces, unused history seeds and the sole projection before any new test
encoding. Prefix/pooling/normalization follow the official card without a search
over alternatives. A selection report on old selection data may diagnose the
pipeline but cannot change projection/pooling after looking at the new test.
Use identical query IDs, histories, W32 queues and quantization for paired
comparisons; report all simple/nonlinear and joint strata and exact retention.
No current test text or outcome selects an ontology, prompt or projection.
Any fresh baseline encoding would require the separately authorized next
experiment; none was done here. New test counts must not be merged with old
denominators as if they evaluated the same frozen system.

## Separate structured-input usefulness control

[HYPOTHESIS] A separate restricted interface could accept only schema-versioned
facts, for example one of:

```json
{"schema":1,"skill":"plant","leaf":"flexible","soil":"wet"}
{"schema":1,"skill":"letter","relationship":"known","occasion":"formal"}
```

[DERIVED] The public grammar would enumerate exactly two values for each field,
with both alternatives and all required fields fixed in advance. A strict parser
would reject unknown fields/values, duplicate keys, missing facts and ordinary
free text. It would map the supplied facts into four one-hot conjunction slots
per route; the history-dependent category label remains a separate issuer
input. This consumes actual explicit structured bytes, not hidden evaluation
metadata. A useful future control must execute that parser and expose its
restricted vocabulary and refusals. Its task is learning/reversing a private
rule over supplied facts; it does not understand unseen paraphrases.

[DERIVED] Such a control could establish restricted usefulness of the same
window update even if natural-text encoding fails. The earlier privileged
true-attribute baseline alone is insufficient evidence for that parser/frontend:
it read generator metadata directly. No structured parser or new utility run
has been implemented or executed in this review.
