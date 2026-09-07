# Live text through independent verified release

[EXECUTED, 2026-09-07] `live_001/report.json` passes the normal sequence
**authorized Infer → actual live text encoding → signed encrypted Learn →
authorized Infer**, using one persistent public host and the independent
verifying reader. The baseline receiver was stopped before the first command.
All three finalized envelopes were independently replayed; two scalar outputs
were decrypted only after their exact finalizations were verified. Both private
integer comparisons passed, and the answer changed after learning.

[EXECUTED scope] This invocation reused the existing private illustration from
the successful baseline `live_text_002`. It performed a new model forward and
did not substitute a cached feature vector (`--expect-record-id` was omitted).
One changed answer is an interface/computation result, not a utility accuracy
estimate. The earlier full 384/96 utility runs and all their denominators remain
unchanged.

[EXECUTED context] Separate signed tickets authorize the same fixed public query
before and after the Learn. Their parent revisions are 0 and 2, with distinct
nonces; the final verified history is Infer/Learn/Infer at revisions 1/2/3. Each
Infer publication waits for public-history sync, then the exact authority retry
delivers through the verifier. The verifier finishes with the same ordered
envelopes and encrypted state as the authority. It receives only initial zero,
public queries and the fresh input ciphertext and computes the results itself.

[EXECUTED costs] On this shared machine, whole-path elapsed time was
**15.418212083 seconds**, including setup, live model work, encrypted issuance,
public recomputation, journal installation and verified release. Staging and
report packaging are excluded. Timing components below overlap and must not be
added as if disjoint:

| Interval | Seconds |
|---|---:|
| Complete live issuer frontend | 12.477338 |
| Model encoder subprocess | 12.186127 |
| Encrypted/signed issuer subprocess | 0.192802 |
| Model load subinterval reported by encoder | 0.767953 |
| Feature forward subinterval reported by encoder | 0.285486 |
| Complete first Infer | 0.618913 |
| Encoder plus complete Learn phase | 12.756723 |
| Complete second Infer | 0.379726 |

[SOURCE + EXECUTED] The tested local SmolLM2-135M revision is
`93efa2f097d58c2a74874c7e644dbc9b0cee75a2`. The existing encoder checks the local
model asset inventory, runs CPU float32 eager inference through all 30 blocks,
takes the masked mean from block 9, and applies the frozen public route-specific
calibration and signed-int8 quantization. It does not train or download a model.
The model load/forward subintervals exclude framework startup and other encoder
work; this run's larger subprocess time is retained without substituting older
timings or an unmeasured prefix-only encoder.

[EXECUTED host] One persistent worker made three proposals, three canonical
inspections, one Learn and two Infer crypto calls. Its 26 CAS gets all recorded
complete hashes, covering 1,878,846 bytes. Startup took 129.812 ms; proposal
caller time totaled 222.930 ms. The final cache held three public metadata
entries. Two verifier decryptions and zero baseline decryptions were observed.

For another private observation, create a private JSON file with exactly this
shape, using your text and observed category:

```json
{"text":"Your observation text","route":0,"label":1}
```

Route is integer 0 or 1; label is integer -1 or +1. The fixed policy selects the
first existing query for that route. This demonstration does not construct a
new query from the observation. Choose unused output directories and run:

```sh
python3 research/learn_infer_only/experiments/end_to_end/verified_reader/live_driver.py --input /absolute/path/private-observation.json --runtime research/learn_infer_only/experiments/end_to_end/verified_reader/runtime/live_002 --reports research/learn_infer_only/experiments/end_to_end/verified_reader/reports/live_002
python3 research/learn_infer_only/experiments/end_to_end/verified_reader/reports/validate_live.py --run live_002
```

[DERIVED interface] The driver copies the input into mode0600 ignored runtime
before execution. The public report contains only aggregate checks and costs.
Actual recipient scalar records remain in the private verifying-reader SQLite
database under `runtime/live_002/run/.private/verified_reader/answers.sqlite3`;
encoder input/vector/diagnostics remain under the private issuer directory.
The original input path and plaintext hashes are not copied into public logs.
The existing model environment and materialized public query fixtures are
prerequisites; no installation or download occurs in this command.

[EXECUTED provenance] Public host, authority and verifier execute frozen source
copies. The already-tested live frontend uses original absolute-path evidence
keys, so its unchanged original files are invoked with source/policy/core hashes
checked before and after. Its owner confirmed those dependencies frozen.
`frontend_dependencies.json` and the source archive record the exact bytes.
No frontend, service, core journal, prior driver or prior baseline artifact was
edited. No adversarial-control code was imported or executed.

- Live driver: `b0d450fda66aa126bb647d98a041d66447afbef9ab2c6805a24a3df0ef103d65`
- Existing frontend: `f084c71abf6f903c89fec34c1a2dcdb526baccafc153749a1d9b722874523365`
- Verifier service: `f0e79c2a33baa32e2867d467735dafd29b26c480deb1f688289e7468bd2de01b`
- Report: `bfa0430db6591d347986b44cabc0ca5fdf760619d710a3f1b338fb2c345acbae`
- Independent validation: `4044cb1eb75ba7869de34d5f08d24727d84593952cd1410e2af6302e38c48a51`

[EXECUTED artifact audit] The separate validator recomputed the direct integer
dot product, checked both delivered values privately, checked the distinct
signed query contexts and exact history, and confirmed the actual model forward.
Expanded public artifacts contain neither the private text/vector nor their
stored hashes, full keys or reader scalar stdout. Four full secret files were
checked in raw, hex and base64 form, including the inner BFV secret payload.
Source/binary/dependency pins and ignored runtime also pass. This is a concrete
artifact audit, not a general information-flow proof.

[DERIVED limits] This remains benchmark R with a plaintext-entitled issuer,
trusted full-key reader, trusted source/range/key provenance and independent
command policy. It does not establish OS isolation, hidden model execution,
feature provenance by proof, no-master-read cryptography or end-to-end
post-quantum security. The verifier narrows arithmetic trust in the authority;
availability and durable reader persistence remain separate assumptions.
