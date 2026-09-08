# Executed candidate transport with separate recipient credentials

[EXECUTED] The full repaired point completed its file-based usable path in
**160.266 seconds across 45 fresh actor processes**. Public setup, issuer and
evaluator processes never opened recipient private artifacts. Each recipient
generated and saved its own row in a separate process, then later decoded
using a new process and that private file. All 20 designated outputs matched:
all 16 recipients read the final expired two-item window; recipient 0 also
read each of three fresh ciphertexts and the signed 2*C0-C1 state.

| Actual full container | Bytes including header | Packed payload bytes |
|---|---:|---:|
| Public A |37,880,273|37,879,808|
| One recipient registration |592,441–592,442|591,872|
| Complete public A and P |379,390,500|379,389,952|
| One private recipient key |3,801,648–3,801,649|3,801,088|
| One fresh ciphertext |37,901,312|37,900,653|
| Signed2*C0-C1 state |37,901,452|37,900,653|
| Final expired window state |37,901,451|37,900,653|

[DERIVED/EXECUTED] Header-size differences reflect recipient-coordinate
digits and canonical state-lineage metadata. Public residues are packed at
289 bits each; key coefficients use 29-bit two's complement and the unchanged
strict cutoff. These are actual written file sizes, not hypothetical
in-memory packing estimates. The private sizes come from recipient write
receipts and file metadata; report collection does not open private payloads.

| Actual process work | Calls | Total wall time | Per-call range |
|---|---:|---:|---:|
| Public A initialization |1|2.455 s|2.455 s|
| Recipient registration/key generation |16|68.669 s|3.587–5.123 s|
| Complete public setup |1|16.034 s|16.034 s|
| Fresh encode, including public-file loading/output |3|29.645 s|9.582–10.176 s|
| Signed combine |1|2.564 s|2.564 s|
| Window creation/update/expiry |3|10.671 s|2.317–5.131 s|
| Fresh-process designated decode |20|29.770 s|1.290–1.871 s|

[EXECUTED] Peak RSS among actor processes was 982,990,848 bytes, in the third
encoder. The complete elapsed time includes process startup, actual file
reads/writes, operation receipts, synchronization, public-artifact hashing
and the final small malformed-file check. It excludes the preceding toy and
two sandbox policy probes. The workflow is a single sequential run on a
shared machine. Its workload differs from the earlier all-in-memory timing;
we do not infer a speed ratio between them.

## Credentials that actually crossed each process boundary

[EXECUTED] There were16 recipient registration processes, each given public
A, its designated coordinate and two output paths. Each wrote one private
key with mode 0600 under its mode 0700 directory, plus one public registration.
No absent-recipient secret was generated. Finalization consumed A and 16
public registrations, then generated561 missing public rows directly
uniformly. It received no private-key path.

[EXECUTED] Each encoder received the complete public package and one public
synthetic input fixture. Signed/window evaluators received only public
ciphertext/state files. Each of20 later decoder processes received exactly
one private-key path in its own recipient directory plus a public ciphertext
or state. It wrote its designated output to its own mode 0600 file. Public
receipts contain paths, sizes, timings and match Booleans, without decoded
values or key coefficients. Every actor PID was distinct. The orchestrator
inspected private-file metadata only and did not load any private payload.

[EXECUTED] These were actual OS-sandboxed launches, not only object-level
separation. Saved Seatbelt profiles deny `file-read*` and `file-write*` below
the entire private tree for public actors; recipient i is denied all other
recipient directories. Network operations are denied. A harmless public
canary placed under recipient 1's directory was unreadable both to the public
profile and recipient 0's profile, with saved `PermissionError: Operation not
permitted` results. The two probes did not target a secret key. The profiles
and every exact actor command are public saved artifacts.

## Serialization and honest state semantics

[DERIVED implementation] `transport.py` provides init, register, finalize,
encode, combine, window and decode commands. It imports the completed fast
scheme's exact sampler, polynomial arithmetic and single-reader decoder
unchanged. The serialization is canonical fixed-width packed integers with
strict headers, context hashes, bounds, dimensions, padding and file length.
Atomic file creation refuses overwrite. One cheap appended-byte mutation of
a public registration file was rejected by the full workflow; the separate
codec's small deterministic malformed checks are in its package.

[DERIVED/EXECUTED] Ciphertexts bind the setup context and complete public-file
hash. A fresh ciphertext's exact file hash identifies it in a derived state's
sorted signed-lineage map. The window evaluator subtracts the actual original
file and cancels its lineage term before checking the live L1 bound. The
full run's final state contained the second and third inputs; each recipient
decoded their expected sum. The evaluator used no private key to perform
this expiry or the signed update.

## Evidence and remaining scope

```sh
../ring_implementation/.venv/bin/python -B workflow.py --profile candidate_full --run candidate001 > candidate001.log 2> candidate001.stderr.log
../ring_implementation/.venv/bin/python -B summarize.py > SUMMARY.log
```

[EXECUTED] `results/candidate001/WORKFLOW.json` preserves all 45 commands,
actor receipts, public artifact hashes and private metadata. `SUMMARY.json`
derives the table above solely from saved public receipts. Runtime private
keys/outputs and large public binaries stay in ignored `.runtime/`; the
package manifest excludes that subtree. Source hashes stayed unchanged
during the full run. The original implementations and mathematical notes
remain unchanged. No estimator, attack or additional full-run grid was used.

[OPEN] All actors share a host UID; directory permissions alone would not
isolate them. The sandbox claims concern the named experiment paths and
executed commands. Host administration, an unsandboxed launcher, memory
inspection and malicious sandbox escapes are outside this result. No secure
erasure, constant-time, authenticated transport, PQ-security or full-privacy
claim follows. Lineage headers are honest arithmetic metadata, not signatures
or proofs against forged state. The exact sampler's OS-randomness premise,
expected-time uniform sampling and prior cryptographic assumptions remain.
This is a working restricted-key scalar-state transport boundary for a later
learner join, not an implementation of arbitrary nonlinear encrypted learning.
