# Source and audit boundaries for the full run

[SOURCE program] The new wrapper never authors learner or query gate semantics.
It calls the frozen generic host from emitted_fixed_fft with the unchanged
Lean-emitted Learn/Infer JSON. The fixed host's parser, wire loop, TFHE adapter,
plan observation and remaining TCB are described in that directory's
SOURCE_AUDIT.md. Its binary hash and all four Rust source files are pinned here.
The issuer/reader are the original pinned byte-compatible executables; no old
handwritten host is invoked by this pipeline.

[SOURCE preparation] preflight.py verifies the original materialized fixture
against its utility manifest and independently computes its signed-integer
trajectory and query scores. It checks the two histories, 384/96 event counts,
zero expiry, 16 stable query record/address assignments and original final
28/32 oracle score. This preflight is public computation on an existing synthetic
fixture. It is not new encrypted execution or a new utility estimate.

[SOURCE key and input flow] common.py points to the two-step probe's existing
public/client/server key files. freeze.py hashes only the public keys and records
private-key custody, existence, byte size and mode without reading or hashing
the client key. run_public.py uses the public key with the original issuer to
create four independent fresh initial ciphertexts, 384 Learn input ciphertexts
and 16 reusable query ciphertexts. The four initial instances are two histories
times two routes. New private request files contain the authorized synthetic
fixture requests; host argument lists contain only public paths and commands.
The full reader remains unrestricted and shares the OS account.

[SOURCE new chains] run_public.py selects one public route file, evaluates the
emitted descriptor twice in fresh sequential processes, and updates a Learn
parent only after successful exits, stable public input/binary hashes, matching
plans and complete output-byte equality. The other route's file is unchanged;
Infer never changes either route. Each new history gets fresh encrypted zeros.
No old failed output path is referenced by common.py or run_public.py.

[SOURCE failure and timing behavior] The driver enforces one host worker and
RAYON_NUM_THREADS=1. Per-process timeout is the smaller of 600 seconds and the
remaining cutoff; the cutoff is the smaller of six hours from launch and
15:00 UTC on 2026-09-08. A timeout kills that operation's process group, preserves
stdout/stderr/resource records and fails the public phase. Any failed process,
hash check, plan check or replay prevents continuation and private draining.
The reader stage also checks the same cutoff and retains failure metadata.
There is no retry or automatic repair branch.

[SOURCE durable records] common.append flushes/fsyncs every JSONL record.
common.save writes and fsyncs a temporary JSON file, atomically replaces its
destination and fsyncs the directory. Operations, accepted events and replay
records are separate. A partial run can leave a completed operation without an
accepted event; verification requires exact final counts and complete continuity,
so such a partial prefix cannot pass as the full workload. These are local
durability checks, not a cryptographic finality or accepted-chain mechanism.

[SOURCE independent public verification] verify_public.py runs only after the
public driver succeeds. It rechecks frozen sources, transcript hashes, every
operation's successful exit, before/after public input and binary identity,
declared plan, gate API counts, artifact paths and typed PEMA envelope framing.
It compares every primary/replay output as complete bytes, verifies the exact
fixture event order and parent continuity, checks initial/checkpoint metadata,
resolves query paths through the public records and inventories every public
artifact. Repeated large inputs are read
once into a metadata cache during this final audit; every operation record is
still compared against its historical before/after tuple and current bytes.
It saves a storage inventory, verification record and public seal before drain.

[SOURCE private checks] drain.py requires passing public-phase and verification
records, a matching public seal, current transcript/artifact hashes and no failure
record. It opens exactly four initial primary states, every one of the 384 primary
Learn selected-route state outputs, and each of the 96 primary Infer signs.
It compares whole selected-route state vectors and signs with the existing
integer fixture. Replay plaintext is never independently opened: its relation
to the checked primary is the previous complete-byte comparison. No private
audit value supplies another host input; plaintext files remain ignored/private.

[SOURCE separate provenance stage] pipeline.py invokes public execution,
independent verification, private drain and provenance sealing in that order,
and exits at any nonzero stage. seal.py performs no host, issuer or reader call.
It rechecks public/frozen records, summarizes the already recorded costs and
match flags, and records final provenance. This post-drain read-only stage is
explicitly authorized and distinguished from the prerequisite public checks.

[OPEN proof scope] Source inspection and this completed run remain finite evidence. Neither the wrapper's Python semantics nor serde/Rust/LLVM/TFHE,
floating-point execution, cache observation, serialized-key validity or universal
replay determinism is proved here. The completed matched trajectory shows this
declared encrypted fixture ran correctly under the retained full-reader audit;
it does not remove that reader credential, explain the older failure, establish
operator isolation or improve the already reused-data utility result.

[EXECUTED completed boundary] The original four-stage pipeline finished at
08:10:00 UTC, all exits zero. The independent public seal preceded the 484
primary-only private checks; all matched, with zero separate replay decryptions.
The later collect_public_provenance.py invocation checked retained public bytes
and aggregate records only. It made no crypto call and modified no original
seal. REPORT.md records exact phase times, costs and the public-worker progress
field inconsistency. No frozen source was changed after launch.
