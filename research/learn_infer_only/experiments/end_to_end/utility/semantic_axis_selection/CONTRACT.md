# Two fixed axis-scoring framings, teacher-only selection

[HYPOTHESIS] Comparing binary alternative likelihoods for one semantic axis at
a time may separate factual classification from the previous free-form JSON
format failures. This is a new teacher-selected scoring interface, not repair
or retrospective acceptance of the frozen JSON outputs. The eight earlier
teacher examples and their failed outputs were inspected. This entire128-text
pool is teacher/selection material; none of its accuracy is held-out evidence.
Budget45–60 minutes; one actual scoring run, no held-out or W32 utility test.

## Exactly two public prompt framings

[DERIVED: protocol] `prompts.json` fixes the four axis definitions, bit0/bit1
meanings and two framings before any model score. No text-specific wording,
lexicon, examples or ontology is fitted. Model input contains only the public
task, the selected axis/definitions and the source teacher text. It never
contains a record ID, oracle attribute, category label or history state.

Framing A is direct binary classification: both axis descriptions are supplied
as alternatives0 and1, and the answer alternatives are the tokens for `0` and
`1`. Framing B asks whether the bit0 semantic statement is supported by the
source; answer alternatives are `Yes` and `No`, mapping respectively to0/1.
Each source states both facts; there is no unknown/abstain alternative here.
This forced choice is explicit and must not be confused with what unconstrained
generation would emit. Only these two framings will be scored.

Use the cached SmolLM3 chat template, the documented no-thinking setting and
one fixed short system instruction per framing. Preserve exact rendered
strings/token IDs, including inserted date metadata. Before scoring, verify
each alternative has exactly one token, and that tokenizing prompt+alternative
equals the frozen prompt tokens followed by that token. Failure is a setup
failure, not permission to compare semantic prompt variants after scores.

## Exact likelihood and numerical handling

[DERIVED] Score each alternative as the next token after the assistant prefix.
One actual causal forward yields the final-position vocabulary logits for a
single axis. Convert logits tofloat32; subtract full-vocabulary logsumexp to
record each alternative's log-likelihood. Both alternatives have one token,
so there is no length normalization. Choose bit0 when its raw logit is greater
than or equal to bit1; exact ties choose0. Also record the softmax probability
conditional on the two alternatives for diagnostic confidence only. This
two-class renormalization does not change the decision or selection metric.

Teacher sources are the existing128 original teacher texts, IDs0..127,
64 per task, balanced over four attribute combinations. Score both axes of
every text under both framings:512 source-axis forward examples,256 bits and
128 pairs per framing. Candidate alternatives share each forward; there are
not1024 alternative-sequence model executions. No free generation, output
parser, regex repair or JSON acceptance occurs.

[DERIVED: batching] MPSfloat16/eager, the same fully pinned SmolLM3 snapshot
`a07cc9a04f16550a088caea529712d1d335b0ac1`, installed torch2.10.0 and
transformers4.57.3; eval/inference mode, no gradients/cache, two CPU threads/
one inter-op, seed7901, batches of8. Left-pad with the model pad token; explicit
position_ids=cumsum(attention_mask)-1 with pad positions set to0. Every row
ends at a real token. Request logits_to_keep=1, checked against installed source;
do not generate or reuse prefix/KV state between batches. Both framings share
precision, batch policy, source texts and the exact same semantic definitions.

## Selection gate and complete reporting

[DERIVED] Select the framing with greater route-balanced bit accuracy
(equal task counts make this also overall bit accuracy); ties prefer A.
Report BOTH complete sets of scores, bit and pair accuracies, each task and
each of the four axes, exact ties, conditional confidence and off-alternative
probability mass. Report how many teacher examples were already inspected
(eight), and separate their counts from the remaining120 as descriptive cells;
the120 remain teacher material, not a fresh held-out test.

Recommend a separately preregistered fresh evaluation only if the selected
framing has at least90% teacher bit accuracy and each task at least85% bit
accuracy. Otherwise retain the failure and diagnose without another prompt,
model or scoring run. No one-example selection or promotion to useful encrypted
adaptation is permitted. A later fresh test would need new text surfaces and
histories frozen before evaluation and no tuning to these teacher scores.

## Cost, supervision and boundaries

[DERIVED] This changes how the public semantic task is stated and how answers
are read from logits. The source model and explicit public axis definitions
are substantial inherited/prompt supervision; the resident's category rule
is not supplied. Count actual model forwards, tokens/padding, float16 storage,
float32 likelihood work, wall/CPU/MPS/RSS costs and score/feature artifacts.
No weights are trained or downloaded, and no new dependency is installed.

[DERIVED] The trusted plaintext issuer sees raw source tokens, all activations
and logits before converting any inferred bit to a small conjunction feature.
The known task route and axis definitions are public. This is feasibility of
a plaintext semantic issuer feeding an encrypted small learner, not encrypted3B
cognition, operator-private source encoding or no-master-read authority.
No history, encryption, journal or reader code is changed or invoked.
