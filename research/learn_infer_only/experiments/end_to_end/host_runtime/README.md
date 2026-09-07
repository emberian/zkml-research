# Persistent keyless host: paired normal-workload result

[EXECUTED] A separate persistent host adapter completed **40 Learn, four Infer,
and eight exact expiries** through the unchanged journal authority and reader.
All 44 complete canonical requests and result ciphertext byte strings matched
the one-shot control. The four reader scores matched exact integer computation;
full public recomputed replay passed. `results/run_001/report.json` records the
run, and `audit.json` independently re-reads the saved request/ciphertext pairs
and command evidence without invoking crypto again.

[EXECUTED] On this one shared Apple M2 Max run, paired host proposal time fell
from **21.782 s to 3.042 s including worker startup: 7.16×**. This is host-only
paired timing. The complete harness took 37.796 s and executed both proposal
paths plus setup, issuer, authority, reader, transport and replay. It is not a
measurement of an optimized end-to-end journal service.

| Measured quantity | One-shot control | Persistent worker |
|---|---:|---:|
| Host processes | 44 | 1 |
| Crypto `inspect` subprocesses | 1,001 | 84 |
| Crypto `host-learn` subprocesses | 40 | 40 |
| Crypto `host-infer` subprocesses | 4 | 4 |
| Total crypto subprocesses | 1,045 | 128 |
| Complete CAS blob SHA256 calls | 2,026 | 2,026 |
| Complete CAS blob bytes hashed | 171,752,166 | 171,752,166 |
| Caller proposal time, excluding worker startup | 21.782 s | 2.981 s |
| Worker startup | included in each one-shot call | 0.061 s |
| Time inside unchanged proposal function | 18.272 s | 2.967 s |

[EXECUTED] Both timing orders were used: baseline first on 22 events and worker
first on 22. Their total host-time ratios were 6.85× and 7.80× respectively,
excluding the single startup. The eight expiry events had a ratio of 10.36×.
These are within-run descriptive results, not independent trials, confidence
intervals, or a prediction for other hardware/workloads.

## The source-backed redundancy

[SOURCE, inspected frozen code] `frozen_core/run.py:54` invokes a fresh
`roles.py propose` process for every event. `roles.py:60` constructs a new CAS
inside that proposal. `common.py:95` initializes `inspected={}`; `common.py:101`
rehashes all bytes on every get and only runs the expensive canonical
inspection when the digest is absent from that dictionary. Process exit loses
previous successful inspections. `model.py:29` validates the whole current
state before each transition, in addition to the proposal's initial validation.
Thus a growing queue is repeatedly re-inspected by new host processes.

[SOURCE, inspected pinned crypto code] The original
`../crypto/src/main.rs:224` inspection command loads ciphertexts strictly.
`params()` at line 35 constructs the BFV context and `load_ct` at line 135
checks canonical serialization. Avoiding repeated inspection therefore saves
process launch, context construction and strict decoding work; the timing is
not attributed exclusively to OS process startup.

[DERIVED implementation] `host.py` imports the seven captured core sources and
calls the **unchanged `roles.propose` function**. Its CAS constructor lookup
returns the same metered CAS instance across stdio requests. The existing
`CAS.get`, SHA256 implementation, action/state validators, signature checks,
query parsing, transition arithmetic, result storage and request construction
are unchanged. Both state-validation passes still execute. No Rust code, core
journal source, authority process or reader process was changed.

[DERIVED measurement boundary] The one-shot control uses the same metering
adapter and exits after each request; the persistent adapter retains its CAS.
This makes complete-read/hash accounting comparable. The first proposal was
also executed by the direct original `roles.py propose` CLI and produced the
identical request and summary. That extra three-crypto-call identity check is
excluded from paired host measurements. The reported 7.16× compares the two
instrumented modes, rather than claiming a separately timed 44-event original
CLI control. Startup source checks and instrumentation are part of their
caller times.

[EXECUTED] The meter delegates to the original SHA256 function and records the
first SHA call inside each unchanged `CAS.get`, which hashes its entire blob.
Every successful get recorded one such complete hash. Both modes performed
identical get/hash counts and byte totals for every individual event. Crypto
command logs independently match all 1,045/128 subprocess counts. Host commands
were only `inspect`, `host-learn` and `host-infer`, with no secret-key or input
vector arguments. Reader plaintext output remains omitted from public logs.

## Workload, retained state and trust

[EXECUTED] The public deterministic fixture uses 40 dense 577-dimensional
integer input vectors, two dense bounded queries, and the normal OS-random
BFV key-generation/public-encryption path. Each event was authorized once and
given unchanged to both proposal paths in separate CAS directories. The
authority independently recomputed and accepted the normal proposal, and the
reader delivered scores 1,725; 4,165; 16,848; and 2,431 at the four registered
Infer events. This is a normal encrypted arithmetic benchmark, with no new
semantic utility or private-ingress claim.

[EXECUTED] The final worker cache contains 84 canonical-inspection metadata
entries. Reconstructing that dictionary from its actual inspection results
gives 53,089 canonical JSON bytes. This is a serialized metadata size proxy;
Python heap/RSS was not measured. The cache includes historical entries and
grows with distinct ciphertexts, while ciphertext CAS and journal retention
remain the original O(T) design. Restarting loses the cache and resumes normal
inspection on demand; this prototype adds no eviction policy.

[DERIVED trust changes] The worker is a longer-lived host process holding public
inspection metadata and one fixed genesis/CAS/crypto configuration. Content
hashes, not caller-supplied metadata, identify prior successful inspection.
Every blob is still re-read and fully hashed, and the pinned binary is still
fully hashed before each actual crypto invocation. The authority independently
recomputes every transition as before; no new release/signing credential is
given to the worker. The client-to-worker transport is a local child-process
stdio pipe rather than repeated command-line process creation.

[OPEN] This is keylessness by configured inputs and command-trace evidence, not
an OS isolation or malicious-host theorem. Filesystem access outside those
arguments is not sandboxed. Existing time-of-check/file-mutation races between
CAS loading and CLI reads, collision-resistance assumptions, and trust in
admitted issuer statements are unchanged. The worker error path and hostile
inputs were not tested in this performance tranche. It is not a production
daemon or a new authority, and it does not close the master-read/release gap.

## Reproduce and resume

[EXECUTED] Source hashes are in `source_pins.json`; the core snapshot is
`frozen_core/`. The crypto binary is copied into ignored run storage and checked
against its frozen hash. The driver does not invoke adversarial controls,
signing-key-compromise cases or routed-output tests. Runtime private keys,
databases and ciphertext CAS directories are ignored locally by `.gitignore`.
Compressed public command/event/request/replay evidence is retained beside
the report. No web, Scry, Kagi, companion writes or commits were used.

```sh
python3 research/learn_infer_only/experiments/end_to_end/host_runtime/freeze.py
python3 research/learn_infer_only/experiments/end_to_end/host_runtime/benchmark.py --name run_002
python3 research/learn_infer_only/experiments/end_to_end/host_runtime/audit.py
python3 research/learn_infer_only/experiments/end_to_end/host_runtime/package.py
```

[DERIVED reproduction note] `freeze.py` refuses source drift. The audit targets
the retained `run_001` and its ignored local runtime; it needs those runtime
bytes to repeat full ciphertext comparisons. The retained digest and command
evidence remains reviewable without runtime secrets. A fresh benchmark should
use a new run name and its own explicit evidence review. Parent integration,
an actual optimized end-to-end utility timing, and any bounded cache policy
are follow-up work, not part of this completed measurement.
