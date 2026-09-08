# Fresh live teaching and proved queries in 21.20 seconds

[EXECUTED] `fast001` completed one fresh two-class BFV learner in **21.201762 s**
for the complete ML subprocess, including Python startup, fresh setup, model
loading, two actual teaching updates, four fresh proofs, gate verification and
the first private receives. It finished at 2026-09-08 22:13:20 UTC with exit 0,
no timeout, unchanged pinned sources and an absent command process group.
The [outer command record](launches/fast001/command.json) and complete
[stdout](launches/fast001/stdout)/[stderr](launches/fast001/stderr) retain this
measurement. The internal demo timer was **20.623207 s**.

[EXECUTED] Both teaching updates were staged from actual fresh encodings, proved,
independently verified again at the durable model journal, and committed. Each
of the two active class-score ciphertexts then received its own new joined proof
covering both signed ciphertext/plaintext products and their final subtraction.
The query gate reconstructed the cases, verified both proofs again against the
fixed template, checked the current accepted revision and wrote public acceptance
with **zero private receives**. Only then did two private receives occur.

[EXECUTED] The omitted-active-class proposal refused with `active_class_coverage`,
no receive, no accepted record and no model change. The accepted head reopened
exactly at revision two. The answer to “Why was I charged a fee for taking cash
out at an ATM?” selected `cash_withdrawal_charge`: **238,227** versus **211,756**
for `card_arrival`. Both decoded scores matched the integer computation performed
after receive and the earlier fixture's scores. The cached local E5 model loaded
once and encoded three texts in this new instance. This is not an accuracy study.

[SOURCE] This additive successor copies the frozen `Live` and `QueryGate` methods
unchanged. The selected pipelines and source-pin construction change, and the
driver adds stage/outer timing and retained update cases. `PIPELINES.json` binds
the two native witness wrappers, their Lean-generated plans, native consumer,
sources and unchanged proof backends/templates into the new instance. The
`Live` and `QueryGate` class ASTs equal their predecessors; all 49 model-source
and 41 query-gate pins matched after execution. `successor.patch` shows the
three predecessor-file changes. No old source, model, key or configuration was
mutated or promoted to a new claim.

[EXECUTED] Actual new pipeline costs, in seconds:

| Fresh proof | Native emission total¹ | Emit wrapper | Prove | Fresh verify | Whole pipeline |
| --- | ---: | ---: | ---: | ---: | ---: |
| Card update | 0.190222 | 0.293135 | 1.990801 | 0.131286 | 2.460510 |
| Cash update | 0.190001 | 0.291672 | 2.252662 | 0.130348 | 2.727523 |
| Card query | 0.486241 | 0.595170 | 4.237101 | 0.183960 | 5.066066 |
| Cash query | 0.483086 | 0.603056 | 3.931259 | 0.182066 | 4.808219 |

[SOURCE] ¹The native executable's own setup/execute/write timer, nested inside
the emit-wrapper time; do not add the columns together. Each update trace has
8,192 rows and 1,017 columns; each query trace has 8,192 rows and 2,509 columns.
The proof sizes were 504,119 / 503,999 bytes for updates and
842,828 / 842,376 bytes for queries. Exact proof hashes, all pipeline steps and
emitter metadata are in [RESULT.json](results/fast001/RESULT.json).

[EXECUTED] Outside those pipelines, the driver measured 0.095639 s for fresh
setup; 6.170756 / 2.943358 s for teaching encode/stage/prove (the first includes
model loading); 0.187797 / 0.184199 s for update gate verification/commit;
10.271498 s for the combined query preparation/proofs; 0.504503 s for both query
gate verifications/acceptance; 0.062659 s for the first private receives; and
0.040457 s to reopen. Pipeline times are nested in these stage times.
`stage_times.json` retains exact nanoseconds. All eight launched public pipeline
and query-gate process groups were absent after successful return.

[REPORTED comparison] The preserved `query_gate_successor/results/gated001/RESULT.json`
records **306.241377 s on its internal demo timer**. The new run uses identical
teaching/query text values and the same fixed arithmetic templates and proof
backends, with fresh randomness/key/state. Replacing interpreted witness emission
with native execution of the approved plans removes the recorded long witness
stage. The new outer **21.201762 s** includes process startup; its internal
**20.623207 s** is recorded separately. These are separate observations, not a
controlled throughput benchmark or matched outer-timer comparison. No baseline
was rerun and no interpreter/native byte-equality trial was repeated here.

[SOURCE] Native witness generation remains **untrusted**: every fresh proof and
all gate verification remain mandatory. The encoder, trusted zero checkpoint,
issuer/FIFO/counts, parser/NTT encoding, model/recipient binding, BFV decoder and
shared OS retain their prior scope. The full BFV reader survives. This result
does not establish restricted decryption, history-bound release or confidentiality.
See [SCOPE.md](SCOPE.md).

[EXECUTED] Issued once from the repository root:

```sh
python3 -B research/vfhe_2026_09_08/proved_journal/fast_live_successor/run.py --run fast001
```

| Artifact | SHA-256 |
| --- | --- |
| `PIPELINES.json` | `623874036e05f5d2e3f4203663d383b00699336016c644d1a7f0eb310610eabf` |
| `live.py` | `3bae74df53d58cb6f9a3ff988b49ae012d556e5da5b11604e745a589f7d4c30f` |
| `gate.py` | `f02a290779b15defffc039d23762ea574118ac80bfe2118fe54eaf608637bf57` |
| `run_demo.py` | `56730ea3ce0ea24527d1eca5dd517afb791ff6b041e30b3728f305956de29c70` |
| `run.py` | `c38bcca5745022ceef2f3eb479af638bd8af734732198dd9a26b08a556ca1066` |
| `results/fast001/RESULT.json` | `1e933da88dd45aba9fec9d5b514e60faf779fb37420bcbe275cf76689787cace` |
| `results/fast001/public_acceptance.json` | `a6769903be072466e498f7e33571a0fbfef1f0bf1f4f4b3e289405077ab81320` |
| `launches/fast001/command.json` | `47bdc828a0ce830f47272b384e2fd72c420a5a268a0a7ea41868537dec4fe9d9` |

