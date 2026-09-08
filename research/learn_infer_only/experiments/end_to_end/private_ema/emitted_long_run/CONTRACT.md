# Full nonlinear workload through emitted fixed-FFT evaluation

[EXECUTED authorization] Root authorized a new full run, six-hour cryptographic
cap and hard 2026-09-08 15:00 UTC cutoff, stopping at the first mismatch/timeout
without retries. All earlier runs stay frozen. Root also authorized the exact
484-open private drain below, after complete public verification and within the
same execution cutoff. Final read-only
provenance sealing is a separate permitted stage, not a public prerequisite.

[SOURCE fixed workload] Use the original utility/materialized_fixture.json,
whose bytes must match the utility manifest: histories 67000/67001, 384 Learn,
96 Infer, zero expiry, unchanged order and record IDs. Each history has two
public routes, each with four signed-byte registers. The fixed law and private
sign query are supplied only by the frozen Lean-derived schedules. Preflight
recomputes the public signed-integer oracle and verifies the existing fixture;
no new fixture, model call, label, selection or utility baseline is introduced.
The original final subset score is 28/32 for both EMA and W32, with the previous
exploratory-data and regression caveats unchanged.

[DERIVED fresh chains and custody] Reuse the prior two-step probe's public,
server and client key files read-only, with explicit hashes only for public keys.
Its unrestricted client key stays at its old private reader path; never copy or
hash it. Use the original pinned issuer and reader binaries. Issue four fresh
encrypted initial states: two histories times two public routes, not duplicated
primary/replay initial states. Issue 384 fresh encrypted Learn inputs and 16
fresh query ciphertexts; each query record is reused at the six original
history/checkpoint occurrences. All new ciphertext files live here. Learn chains
use only this run's preceding successful primary outputs. Private source requests
are stored in the new ignored private directory and never become host arguments.
Same-account roles and the full-reader credential remain explicit limitations.

[SOURCE backend] Execute only the frozen emitted_fixed_fft generic host and
the same exact Learn/Infer JSON descriptors. Pin its source, lock, compiler-feature
evidence and binary, including TFHE 1.6.3 with boolean plus
experimental-force_fft_algo_dif4. Every host process must report the actual
Dif4/base512/FFT512 plan at polynomial size 1024. No learner semantics or TFHE
configuration is edited for this run. Rust/serde/TFHE/cache/serialization remain
source-audited TCB; fixed plan and finite results prove no general determinism.

[DERIVED public execution] One sequential worker, RAYON_NUM_THREADS=1. Evaluate
each event twice in independent fresh processes from identical descriptor,
server-key, parent and encrypted request files. Hash all four public inputs and
the executable immediately before and after each host; require unchanged hashes,
matching tuples and complete output-byte equality. Require successful exits,
the observed fixed plan, and the host's all-Encrypted output boundary. Retain
every actual stdout/stderr, resource log, operation record, public input/output
hash and replay record. Stop on the first failure; no retry, repair, resampling
or decoding any failed output. A process timeout is at most 600 seconds and
also bounded by the remaining six-hour/15:00 UTC public-phase budget.

[DERIVED durable records] Fsync every appended operation/event/replay record.
Update progress atomically with fsync, including accepted event and replay counts,
current operation, elapsed time and reader count zero. Flush and close public
transcripts only after all 480 replay pairs and 960 host invocations complete.
An independent verifier must recheck the full fixture order, source/input/binary
hashes, all actual plans, state-file continuity, unchanged other routes, typed
envelope storage, complete replay byte equality, exact counts and every stored
artifact hash. Seal all public records/artifact metadata and verify that seal
before opening any private audit. A failed/incomplete public phase never drains.

[DERIVED authorized private drain] Only after passing public-phase closure and
verification, invoke the pinned full-key reader for exactly 484 primary artifacts:
four initial route states, all 384 primary Learn selected-route state outputs,
and all 96 primary Infer signs. Compare every Learn state to the original
fixture's full selected-route vector and each sign to its frozen integer score.
The replay artifacts are not independently decrypted; complete public byte
equality is their sole relation to the checked primary plaintext. No audit output
feeds a host or future Learn. Keep plaintext audits private; publish only match
flags, counts and original utility aggregate comparisons. On any audit error or
mismatch stop and preserve it, without cryptographic rerun.

[DERIVED separate post-drain stage] After draining, read-only provenance sealing
may recheck frozen files, the prior public seal and artifacts, and summarize costs
and match flags. This explicitly permitted final integrity stage does not alter
public execution or authorize another host/issuer/reader call. Retain private
audit custody and raw public logs. Root owns integration and commits.

[OPEN interpretation] This is a new full encrypted execution of a reused public
synthetic fixture, not an unknown-input privacy test, improved utility result,
new no-master/read-restriction mechanism, accepted-chain composition, PQ proof or
proof of replay determinism. It does not diagnose or supersede the older failed
long workload, whose output files are never accessed by these wrappers.
