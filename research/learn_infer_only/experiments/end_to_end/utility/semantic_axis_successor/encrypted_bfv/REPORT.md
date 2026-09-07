# Semantic fixture through BFV and an independently verifying durable receiver

[EXECUTED] Both frozen semantic histories completed through the actual BFV
pipeline: **384 Learn events, 96 Infer events and 256 expiries**. All 96
received scalar values equal both the frozen oracle and a separately coded
direct integer queue replay. The receiver independently verified all 480
finalizations before releasing their 96 answers. The original baseline reader
decrypted nothing. The measured launcher wall time was **219.733 seconds**.

[DERIVED] This joins the useful restricted semantic learner to the existing
encrypted arithmetic and durable verification machinery. It retains a trusted
receiver with the **full BFV secret key**. The semantic aggregate has only four
effective coordinates per route, eight across both routes. Spanning exact-score
recipients can determine that aggregate. Neither useful adaptation nor this
successful consistency run establishes no-master-read authority or private
source-model cognition.

## Frozen evidence and scope

[EXECUTED] `CONTRACT.md`, `prepare.py`, `run.py` and `validate.py` were frozen
before the first crypto execution. `freeze.json` has SHA-256
`7d03dab6617d7684bb75540d7af521e6756c8cc3b1eb703e5d6cc694fa590377`.
The canonical PUBLIC research fixture is `../materialized/fixture.json`, SHA-256
`bcdda47d227853e546427e9fb42de489b7c227ace65b10a9099cec81f4481b11`.
Its source model predictions and chronology are unchanged. No model forward,
teacher re-encoding, training, prompt change or download occurred here.

[DERIVED: selection] The integration subset is the first two previously frozen
history IDs, 67000 and 67001. It uses the lowest two record identifiers per
task and gold-attribute stratum: 256, 257, 272, 273, 288, 289, 304, 305, 320,
321, 336, 337, 352, 353, 368 and 369. Gold metadata served only the prior balanced
fixture selection; actual feature values use the frozen model-predicted bits.
The 16 query records include eight distinct vectors. All duplicate records
remain as separate policy entries and scheduled evaluations.

[EXECUTED] The earlier full study remains **7,462/8,192** final labels for the
semantic issuer, **4,178/8,192** for original mean10, and **8,192/8,192** for the
gold-attribute diagnostic. The semantic method made 15 wet-soil factual errors;
the weak hard-leaf/wet-soil utility stratum was 696/1,024. See the unchanged
[`../REPORT.md`](../REPORT.md), `../ERRORS.md`, and the copied
`reports/run001/full_survey_reference.json`. Those are the actual utility
denominators. This deterministic two-history integration subset is not a new
accuracy sample or a new success-selected illustration.

[EXECUTED] For complete accounting, the subset's already-frozen label checks
are 76 correct of 96 checkpoint outputs, 68 of 80 nonempty outputs and 28 of
32 final outputs. Every one of the incorrect labels is preserved by the
encrypted computation. Selected records 256 and 288 retain their source
wet-soil errors. The implementation's claim is **96/96 exact arithmetic
matches**, not that all 96 semantic answers are correct.

## Actual normal path and independent checks

[EXECUTED] Each history performs a fresh BFV setup. The trusted issuer encrypts
192 supplied signed vectors with fresh OS-randomized encryption and signs their
context-bound ciphertext authorizations. The persistent keyless host proposes
each transition. The authority recomputes and validates it, then commits a
signed finalization to its SQLite journal. A separate receiver DB and CAS
verify the authorization, parent, revision, nonce/input uniqueness, exact BFV
transition and finalization before permitting decryption.

[EXECUTED] Each Infer is initially pending. After the receiver installs its
independently verified event, the coordinator retries the identical accepted
request and obtains the same finalization with a durable received answer.
All 96 outputs traverse this path: 80 nonempty-route outputs and 16 publicly
known empty-route zeros. The zeros are not substituted by the test oracle.
There are 240 verified journal rows and 48 received answers per history;
the receiver journal and final state exactly match the authority's.

[EXECUTED] The pre-frozen `validate.py` reads the completed private receiver
DB only in the trusted test-oracle role. At each query it directly sums the
dot products of all original, unexpired plaintext contribution vectors; it
does not reuse the BFV or accumulator implementation. All 96 values match.
It separately checks each of 256 expired event IDs against the exact earlier
ciphertext hash and record ID in the accepted envelope. Each history contains
192 distinct fresh ciphertext hashes. The audit also checks all 480 event
identities, routes, revisions, query rows, source vectors and final journals.

[EXECUTED] The BFV binary, service, host, seven journal modules and copied
crypto source files passed pre/post byte checks. All 25 original dependency
pins and 24 snapshot source pins match. All 53 entries in the original semantic
study manifest and all 30 entries in the materialization manifest remain
unchanged. The source snapshot and two adapter diffs are retained.

[DERIVED: adapter inspection] The existing `PersistentRun` class is asserted
byte-identical. The bounded adapter removes legacy staging and unrelated
speedup comparisons, stages the semantic fixture, replaces the old fixture's
hard-coded label-count assertions, and changes report scope/names. It changes
no BFV arithmetic, authorization, durable transaction, verifier or host
validation body. Inherited source docstrings describe the original runner;
the precise adapter differences are `utility_worker_adapter.diff` and
`persistent_worker_adapter.diff`.

## Measured costs

[EXECUTED] Costs come from `run.command.json`, `validation.command.json` and
`reports/run001/costs.json`; detailed per-role measurements remain in each
history report and compressed command/RPC/transition logs. These are one run
on shared hardware, not a latency distribution or a speed comparison.

| Quantity | Measured value | Scope |
|---|---:|---|
| Preparation | 0.168 s | Snapshot and fixture staging |
| Complete launcher wall | 219.733 s | Both histories, setup and cleanup |
| Pipeline interval | 219.560 s | Nested inside launcher |
| Direct replay / evidence validation | 0.700 s | Separate post-run check |
| Mean Learn transition wall | 0.488299 s | 384 full pipeline events |
| Mean Infer transition wall | 0.309589 s | 96 verified release events |
| Actual crypto subprocesses | 5,116 | Includes validation and recomputation |
| Child CPU user / system | 127.602 / 51.689 s | Launcher `RUSAGE_CHILDREN` |
| Maximum child RSS | 89,669,632 B | Child high-water mark, not simultaneous RSS |
| Fresh input ciphertext | 85,103 B | Canonical payload plus bound container |
| BFV public key | 42,628 B per history | Actual serialized key |
| Retained full BFV secret | 4,180 B per history | Ignored runtime only |
| Live ciphertext references | 66 / 5,616,798 B per history | Two accumulators and two W32 queues |
| Retained receiver CAS | 403 files / 33,625,997 B per history | Includes public query objects |
| Final state manifest | 7,601 B per history | Public queue/accumulator metadata |
| Coordinator-to-receiver requests | 22,651,120 B per history | Measured framed RPC requests |
| Receiver replies | 69,776 B per history | Measured framed RPC replies |

[EXECUTED] Each persistent host uses one worker for 240 requests and retains
395 public inspection-cache entries, whose canonical JSON is 249,641 bytes.
Each host makes 25,536 full-blob reads/hashes covering 2,165,144,064 bytes;
every CAS get is rehashed. Its metered crypto calls exactly match the actual
command log. Cache size is not heap usage; cache growth is not bounded here.
Worker startup was 0.083849 and 0.071345 seconds. Wall, worker, transition,
crypto and CPU intervals overlap and must not be added as disjoint costs.

[EXECUTED] Per history, after services stop, the authority SQLite database is
851,968 bytes with a 2,789,272-byte WAL and 32,768-byte SHM; the receiver DB is
1,146,880 bytes with a zero-byte WAL and 32,768-byte SHM. These measurements
include durable journal/answer storage and differ from live encrypted state.

[SOURCE: pinned implementation] The unchanged BFV executable uses degree 4096,
plaintext modulus 4,294,828,033 and ciphertext primes 2,199,023,190,017 and
4,398,046,486,529. It uses 577 signed coordinates bounded by 127 and W32 per
route. The generic signed score bound is 297,805,856; the one-hot semantic
image has the tighter bound 516,128. `source_snapshot.tar.gz` retains exact
`crypto_sources/params.json`, Rust source and Cargo pins. This note does not
derive a new concrete cryptographic security level from these parameters.

[SOURCE: prior executed model cost] The earlier semantic study used the cached
3,075,098,624-parameter SmolLM3 model with fixed public axis instructions and
actual MPS float16 scoring. Its 128 fresh texts required 32 batch forwards
covering 256 axis examples, 61.428 seconds process wall, 48.854 seconds summed
forward intervals and 10,272,817,152 bytes peak RSS. Those are prior source
encoding costs, not measured within this BFV run or singleton latency. No
claim prices language understanding from the four-bin learned state alone.

## Privacy, custody and continuity limits

[DERIVED] This is a PUBLIC synthetic fixture with trusted plaintext source
encoding and a trusted plaintext test oracle. Only encrypted contributions
and signed metadata go to the normal keyless host/authority interfaces.
Public queries, route, counts, revision, expiry and ciphertext identity remain
visible metadata. The source issuer sees its text and labels. Source-feature
provenance and range assertions are trusted signatures, not proofs that a
particular language model correctly interpreted the text.

[EXECUTED] No public-role crypto argv uses `--sk` or plaintext `--vector`;
all 96 decryption stdout/stderr values are omitted from retained logs. Eight
actual secret files across both setups, including raw/hex/base64 encodings
and inner BFV secret payloads, were absent from the retained evidence scan.
Keys and receiver answer DBs remain locally under ignored `runtime/`; they
were not erased. This is a same-account role/file separation fixture, not OS
isolation or an information-flow proof. The public original oracle already
contains these synthetic fixture scores.

[DERIVED] The full-key receiver can decrypt generally. Independently checking
ordinary delivery does not cryptographically remove that capability. Further,
the rank-4 query image per route spans its entire four-bin aggregate: four
exact basis scores determine it. Padding to 577 coordinates adds no hidden
aggregate dimension. This does not determine queue order; sign-only output
has a different disclosure scope. The demonstrated receiver returns exact
scores, so no recipient-coalition aggregate-state privacy is claimed.

[DERIVED] The ordinary successful path tests durable journal installation and
idempotent receipt behavior. It does not prove exactly-once physical delivery,
availability under faults, independent persistence against authority rollback,
or hardware isolation. No crash/adversarial controls or previously stopped
experiments ran here. Classical Ed25519 is retained, so this is not an
end-to-end post-quantum system. This result is the trusted full-key receiver
benchmark, separate from restricted-decryption research.

## Reproduction and retained evidence

[EXECUTED] From the repository root, the actual commands were:

```sh
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/encrypted_bfv/prepare.py
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/encrypted_bfv/run.py
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/encrypted_bfv/validate.py
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/encrypted_bfv/summarize.py
```

[EXECUTED] `run.command.json` and `validation.command.json` retain exact system
interpreter paths, return codes and timings. System Python has the already
installed cryptography dependency; no new environment was created. Preparation
and execution intentionally refuse to overwrite the first frozen run. A fresh
rerun requires a separate sibling run directory and preserved parent fixture;
validation/summarization alone performs no crypto or model calls.

[EXECUTED] `reports/run001/report.json`, `fast_report.json`, `validation.json`,
`costs.json`, source/fixture/prepost pins, accepted envelopes and compressed
logs are the retained evidence. `manifest.json` is the final file/hash census.
Ignored runtime contains reproducible input copies and actual private role
state. No parent artifact, companion, shared ledger or commit was modified.
