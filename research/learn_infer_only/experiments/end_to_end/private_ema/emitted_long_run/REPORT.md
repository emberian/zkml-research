# Full emitted fixed-FFT nonlinear workload

[EXECUTED] The frozen pipeline completed successfully at 2026-09-08 08:10:00
UTC. Both histories completed: 384 Learn and 96 Infer events, each with one
independent-process full-byte replay. All 480 pairs matched, all 960 host
processes reported Dif4/base512/FFT512 at polynomial size 1024, and all four
pipeline stages exited zero. There was no retry, timeout or failure record.
`summary.json`, `pipeline.json` and the original reports below are authoritative.

[EXECUTED] After the complete public seal, the authorized private drain checked
four initial states, every one of the 384 primary Learn selected-route state
vectors, and all 96 primary Infer signs. All 484 checks matched the original
integer fixture. The four initials are two histories times two routes.
Replay plaintext was not independently opened: its relation to each checked
primary is the complete public byte comparison. Matching all 96 signs means
agreement with the frozen oracle, not 96 correct classification targets. The
reused fixture's classification score was 76/96 over all checkpoints and 28/32
on the final subset; the original final EMA/W32 comparison remains 28/32 each.
This execution introduces no fresh utility estimate.

[EXECUTED phase order] The original command was `python3 -u pipeline.py`.
The four stages were `run_public.py`, `verify_public.py`, `drain.py`, and
`seal.py`, each invoked exactly once by the retained pipeline record.

| Recorded boundary | UTC on 2026-09-08 |
| --- | --- |
| Public execution started | 05:28:28.472235 |
| All public operations/pairs closed | 08:09:56.356621 |
| Independent public verification passed | 08:09:57.110689 |
| Public seal written, reader count zero | 08:09:57.111440 |
| Authorized private audit started | 08:09:57.410243 |
| All 484 private checks completed | 08:09:59.846219 |
| Separate provenance-only seal completed | 08:10:00.180702 |

[EXECUTED] `reports/run001/public_verification.json` verifies the full fixture
order, state-file continuity, public input/binary hashes, all actual plans,
all 480 complete-byte replays and the 1,364-artifact storage inventory. These
checks and `public_seal.json` preceded the private audit. `seal.py` then performed
the explicitly permitted read-only provenance stage with no crypto calls.
The public phase took 9,687.877 seconds (2h 41m 27.877s); the recorded private
drain took 2.436 seconds. Completion was before the six-hour cutoff at
11:28:28 UTC and the hard 15:00 UTC deadline.

[EXECUTED later collection] Monitoring resumed at 14:30 UTC after agent usage
was replenished. The already completed session returned exit zero, and the old
public worker PID was absent. No cryptographic command was restarted.
`python3 collect_public_provenance.py > collection.stdout.json 2> collection.stderr.txt`
completed at 14:33:43 UTC, rechecking all 39 frozen files, all 1,364 public
artifacts and all 480 complete-byte pairs. It verified phase ordering using
public records, read no private key/plaintext file and left the original seals
unchanged. This later collection is distinct from the prerequisite public seal.

[SOURCE fixed program] The generic interpreter evaluates only the unchanged
Lean-derived Learn/Infer JSON. TFHE 1.6.3 is compiled with `boolean` and
`experimental-force_fft_algo_dif4`. Each host logged its actual cached plan;
there was one sequential worker and `RAYON_NUM_THREADS=1`. No learner semantics,
backend configuration, fixture or runtime setting changed during the run.
Rust/serde/LLVM/TFHE and these Python wrappers remain outside the Lean semantics
proof. See `SOURCE_AUDIT.md` and the frozen `CONTRACT.md`.

[DERIVED costs] Aggregating the retained 1,848 rows in `costs.csv` gives the
following per-process wall costs. Host counts include primary and replay.
These are shared-machine measurements, not isolated benchmark estimates.

| Process role | Count | Minimum / median / maximum seconds |
| --- | ---: | --- |
| Learn host | 768 | 8.879 / 11.411 / 40.972 |
| Infer host | 192 | 0.295 / 0.319 / 0.794 |
| Initial-state issuer | 4 | 0.264 / 0.304 / 0.482 |
| Learn-input issuer | 384 | 0.083 / 0.104 / 0.868 |
| Query issuer | 16 | 0.083 / 0.112 / 0.135 |
| State reader | 388 | 0.00370 / 0.00420 / 0.00677 |
| Sign reader | 96 | 0.00365 / 0.00411 / 0.00503 |

[DERIVED] Maximum recorded host RSS was 552,091,648 bytes (526.516 MiB).
Host gate API calls totaled 263,808 XOR and 151,104 AND across both executions
of every event; these are API counts, not a bootstrap count. The public artifact
inventory contains 97,500,084 bytes. `collection.json` retains exact aggregates.
`contention.json` records the separately owned tiny model/BFV task's actual
05:56:48 UTC start and 27.504062-second outer duration. It overlapped subsequent
Learn work: the first Infer block actually closed at 05:56:25.935979 UTC, while
05:56:47 was a later observation. Other timing variation is not causally attributed.

[SOURCE provenance pins] `freeze.json` pins 39 public/source files, including
all original pipeline sources, the contract, preflight, fixture, issuer/reader
sources and binaries, public keys, fixed-runtime sources/build evidence and
binary, and exact formal snapshots/descriptors. Full identities include:

| Artifact | SHA256 |
| --- | --- |
| Original long-run freeze | `6cc20a07b75330c2fb7aaa19a2021c6b495096c6b477b1554eb4a2a14c7943e8` |
| Fixed generic host binary | `6c0954fae626940e720c47bfb535347ecd3c3fc0b19b36d0834b70465b02d197` |
| Original reused fixture | `76d084577179f90c311549eb931fe8cd312b18099e6063cdb6a5493df4257a62` |
| Lean Learn JSON | `94e8369ffc8fcdf57b8351b278d5af90dc49a26d83600d40f0bd6a0da359dde8` |
| Lean Infer JSON | `b742ed7710d2680119eceeff0c553d675e1ce187a503981fc500a6a4a683b80c` |
| Original public seal | `b2f972552b5383d05207737939ddb2fe81e0c9ff68077104e13939f786dee566` |
| Original completed summary | `581d4d9fd602f63658bd3ad46feea58845f1d021863af812bf4bec2147686e5a` |
| Later public-only collection | `e536a7027fd89bf849d86edda20fd72cd8396e1dc69cdc737cea17f455a3e16f` |

[SOURCE custody and limits] New public ciphertexts remain locally under ignored
`runtime/run001/public/`; their inventory is `reports/run001/public_storage.json`.
The public/server key files were reused read-only from the prior two-step probe.
The unrestricted client key remains at its original private reader path, under
the same OS account; private audit plaintext stays in ignored private storage.
Public manifests do not substitute for the retained ciphertext/key files needed
for an external storage audit. Neither fixed planning nor this finite run proves
general determinism, unknown-input privacy, no-master access control, accepted-chain
composition or PQ security. The older failed run remains unchanged; its failed
outputs were not accessed and its cause is not established here.

[SOURCE observability] The preserved public-worker `progress.json` ends with
phase `public_closed` but keeps its static `public_phase_closed=false` and
`reader_invocations=0` fields. They are not phase gates or final audit counters.
Use `public_phase.json`, `public_seal.json`, `private_drain.json`, `summary.json`
and `pipeline.json` for completed phase evidence. No frozen source or old record
was rewritten to conceal that reporting inconsistency.
