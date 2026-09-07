# Persistent host in the complete verified utility workload

[EXECUTED, 2026-09-07] The same two full public utility histories completed
through actual BFV, the unchanged authority and independent verifying reader
in **201.345117583 seconds**, compared with **682.666087417 seconds** for the
previous complete run. The observed full-workflow ratio is **3.3905×** across
these separate executions on shared hardware. Both runs used fresh OS
randomness. This is a descriptive timing comparison without a paired trial or
confidence interval.

[EXECUTED] All **384 Learn, 96 Infer and 256 exact-original expiries** passed.
All 96 actual outputs equal the frozen oracle and a separate direct integer
replay from the retained input windows. There were 96 verifying-reader
decryptions and zero baseline-reader decryptions. The exact utility denominator
is unchanged: 52/96 correct overall, 44/80 on nonempty state and 18/32 at the final
checkpoint. The 16 known-empty outputs remain explicit. No model was run,
trained or downloaded, and no examples were reselected.

[SOURCE + EXECUTED integration] `fast_utility_driver.py` reuses the frozen
`utility_driver.py` staging and complete worker loop. A scoped staging-launch
adapter adds the existing persistent-host sources to the snapshot. A small Run
subclass changes only `role('propose')` to a canonical stdio request to the
existing `host_runtime/host.py serve` process. The original public host config
and CAS are used. Issuer, command authorizer, authority, verifier, output gate,
integer comparisons and normal pending/sync/exact-retry delivery are unchanged.
No service or journal source was edited, and no adversarial-control module was
imported or executed.

| Quantity across both complete histories | Previous utility run | Persistent-host utility run |
|---|---:|---:|
| Complete elapsed time | 682.666 s | 201.345 s |
| Host proposal processes | 480 | 2 |
| Host crypto `inspect` subprocesses | 25,286 | 814 |
| Host crypto Learn subprocesses | 384 | 384 |
| Host crypto Infer subprocesses | 96 | 96 |
| Verifier decryptions | 96 | 96 |

[EXECUTED worker accounting] Each worker served exactly 240 proposals and
performed 25,536 complete CAS reads/hashes over 2,165,178,024 bytes. Across the
two workers this is 51,072 hashes over 4,330,356,048 bytes. Every recorded get
had one full-blob hash; the actual crypto command logs match the worker meter.
The earlier complete baseline run did not meter full-blob hashes. The separate
44-event paired host benchmark checks equal get/hash counts between its two
modes; that evidence and the unchanged CAS implementation support the
optimization's mechanism.

[EXECUTED cache/startup] Worker startup took 66.244 ms and 69.294 ms. Their
lifetimes, including idle time while the other pipeline roles ran and shutdown,
were 88.641 s and 111.611 s. Proposal caller time including startup was 16.778 s
and 20.848 s. Each final cache held 407 public inspection metadata entries;
reconstructing the actual metadata gives 257,225 canonical JSON bytes per
cache. This is a serialized-size proxy, not Python heap/RSS. The cache lasts
for one history and grows with distinct ciphertexts; no eviction policy was
added. Every get still re-reads and hashes the blob, and every actual crypto
invocation still checks its binary hash.

[EXECUTED timing detail] Complete median Learn times were 0.395 s and 0.466 s
for the two histories; complete median Infer times were 0.257 s and 0.318 s.
These include role work, unchanged public verification, journal installation
and delivery. Both source-feature extraction and live-text encoding are outside
this frozen-feature workload. Per-role crypto costs, host request/cumulative
meters, startup/lifetime, caller/function times and byte counts are retained in
`fast_utility_002/`.

[SOURCE boundary] The existing `host_runtime/results/run_001/report.json`
records a **7.16× paired host-only** result on 44 different normal commands.
That number belongs to the paired host experiment. This note's **3.39×** is the
observed ratio for the actual complete 480-command pipeline in two separate
runs. `comparison_provenance.json` pins both reports and keeps those measurement
boundaries explicit.

[EXECUTED storage and trust] Each learner still references 66 current
ciphertexts totaling 5,616,798 bytes; the verifier still retains 423 CAS files
totaling 34,663,205 bytes per history. The new retained host cache contains
public metadata and adds no release or signing credential. This remains a
public, known-state utility fixture with a trusted plaintext issuer and a
full-key benchmark-R reader. Command policy, issuer provenance and reader
persistence remain trusted; process/file role separation does not establish
OS isolation. Existing hash and file-read assumptions remain. There is no
no-master-read or end-to-end post-quantum claim.

From the repository root, with the prior frozen inputs and crypto binary:

```sh
python3 research/learn_infer_only/experiments/end_to_end/verified_reader/fast_utility_driver.py --runtime research/learn_infer_only/experiments/end_to_end/verified_reader/runtime/fast_utility_003 --reports research/learn_infer_only/experiments/end_to_end/verified_reader/reports/fast_utility_003
python3 research/learn_infer_only/experiments/end_to_end/verified_reader/reports/validate_utility.py --run fast_utility_003
```

[EXECUTED provenance] The completed run is `fast_utility_002`. Its driver and
the independent integer/artifact validator exited zero. The validator checked
all source/binary/fixture pins, all 96 direct integer values, omitted reader
stdout/stderr, eight full secret files including both inner BFV payloads, and
ignored runtime. Root service SHA256 remains
`f0e79c2a33baa32e2867d467735dafd29b26c480deb1f688289e7468bd2de01b`;
the original utility driver remains
`f623dbf5d903c6a6ced87cfb5735dd1bda47f861665f8d88670184f6dc463847`.
All seven host-core hashes match the captured originals.

- Fast driver: `6581d30f17d7e330f1e17cb5517f144232bc720019617299aae114aff594492d`
- Full comparison report: `7620db03319bae72e906d1f89f6408b44509f459ef555cb2fb3a075295236393`
- Full correctness report: `13909aedb5f278b7224bf753546c04b1f594d1634081bec85b7a39ec59b95903`
- Independent validation: `1b132b0cdf5de5df1318710c5fbad75dd4b9807b3c70928e3e7cf91012a9dc09`

[EXECUTED development record] The initial `fast_utility_001` staging attempt
stopped before any workload or cryptographic process because its scoped launch
namespace omitted the `STDOUT` constant. The error and repair are retained in
`startup_failure.json`. The completed run preserves the repaired launch wrapper
and every imported source. Previous utility/test artifacts, core files and
shared ledgers were not changed.
