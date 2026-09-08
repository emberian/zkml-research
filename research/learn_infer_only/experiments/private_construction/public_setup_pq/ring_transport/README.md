# Ring credentials across actual process and file boundaries

[DERIVED implementation] This package transports the completed fast ring
scheme through canonical files and fresh actor processes. The cryptographic
sampler, exact ring arithmetic and integer decoder are imported unchanged
from `../ring_implementation_fast/`. The public constructor never receives
recipient secret rows. Each actual recipient generates one row in its own
process and writes only that row to its private key artifact. Encoding and
evaluation use public cryptographic artifacts. The synthetic input fixtures
are public; a real issuer would also need its own plaintext input.

[EXECUTED] `workflow.py` runs the toy or full repaired profile through actual
setup, registration, encoding, signed combination, two-item window expiry
and designated reads. The completed full run took **160.27 seconds across
45 fresh processes**, with all **20 designated outputs matching**. The
complete public file is **379,390,500 bytes**, a fresh ciphertext
**37,901,312 bytes**, and one recipient key **3,801,648–3,801,649 bytes**,
including headers. See `REPORT.md` and `SUMMARY.json`. Every actor invocation
is a new process. macOS
`sandbox-exec` denies the complete private-artifact tree to public actors;
each recipient is denied the other recipients' directories. Two harmless
canary reads exercise those rules and fail with `PermissionError: Operation
not permitted`. Keys have mode 0600 and recipient directories mode 0700.

## Run the complete path

```sh
cd research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_transport
../ring_implementation/.venv/bin/python -B workflow.py --profile toy --run local_toy
../ring_implementation/.venv/bin/python -B workflow.py --profile candidate_full --run local_candidate
```

[DERIVED] Run names must be fresh. Artifacts are retained under ignored
`.runtime/<run>/public/` and `.runtime/<run>/private/recipient_<i>/`.
Public operation receipts, sandbox profiles and aggregate results are saved
under `results/<run>/`. The orchestrator reads public artifacts and receipts,
and only `stat` metadata for private files; it does not open private key or
designated-output payloads. No secret values are placed in tracked reports.

[EXECUTED environment] The workflow uses the existing isolated Python 3.14,
python-flint 0.9.0 environment and native sampler. The measured process policy
requires macOS `sandbox-exec`. Individual serialization/CLI commands are
reusable Python programs; invoking them directly does not automatically
install the workflow's OS sandbox. The saved `.sb` profiles show exactly what
was enforced during the measured run.

## Reusable actor CLI

[DERIVED API] All verbs use
`python transport.py --receipt <public-receipt.json> <verb> ...`.
Destination directories must already exist. Writes are atomic and refuse to
overwrite an existing artifact. Every role can inspect its public receipt
without revealing secret coefficients or designated output values.

| Verb | Inputs | Outputs / credential use |
|---|---|---|
| `init --profile ... --out A` | Fixed public profile | Uniform public A; no private row |
| `register --public-a A --coordinate i --key-out K --registration-out R` | A | One private key K for recipient i; public R |
| `finalize --public-a A --registration R ... --out P` | A and all public registrations | Complete public P; missing rows drawn directly uniformly |
| `encode --public P --input X.json --out C` | Public P and issuer's complete F_p vector | Fresh ciphertext C; no recipient key |
| `combine --term 2 C0 --term -1 C1 --out S` | Public ciphertexts | Signed state S; no recipient key |
| `window --state W --add C2 --expire C0 --capacity 2 --out W2` | Public state and original ciphertexts | Exact updated/expired state |
| `decode --key K --ciphertext C --out O.json` | One recipient's private K and public C | Private designated output O, mode 0600 |

[DERIVED] A first window update omits `--state` and `--expire`. An update
before reaching capacity omits `--expire`. `decode --expected-lift <integer>`
is optional and used only to compare the public synthetic fixtures; the
receipt reports a Boolean comparison, not the decoded value. The actual
value is written to the recipient's private output file.

## Canonical packed format

[DERIVED] A container is eight ASCII magic bytes `RINGTRN1`, a four-byte
big-endian header length, canonical ASCII JSON, and one packed payload.
Header length is bounded by16384. JSON uses sorted keys, compact separators
and no nonfinite numbers; re-encoding must reproduce the exact bytes.
Unknown/missing fields, a different fixed parameter profile, malformed
context digests, incorrect dimensions, noncanonical residue values,
nonzero high padding, truncation and trailing bytes are rejected.

[DERIVED] Payload values are consecutive unsigned width-bit values in
little-endian bit order. At the repaired point public residues use 289 bits
and must be below q. Key coefficients use 29-bit two's complement; decoding
rejects values outside the unchanged strict cutoff `|z|<2^28`. No native
integer, pointer, pickle or platform-dependent FLINT serialization is used.
Exactly `ceil(width*count/8)` bytes hold each payload; header bytes are
reported separately in operation receipts.

| Kind | Payload count | Width at repaired point |
|---|---:|---:|
| Public A | wN |289|
| Public recipient registration | N |289|
| Complete public A and P | (w+d)N |289|
| One private recipient key | wN |29|
| Ciphertext or state | wN+d |289|

[DERIVED context] Every header carries the fixed parameter profile and a
public setup identifier. Registrations and private keys also bind the exact
public-A file hash; the final public package carries that hash. Ciphertexts
carry both A and complete-public-file hashes. Mismatching contexts are
rejected before combination or read. The public sparse basis is the same
deterministic basis prescribed by the completed implementation's profile.

[DERIVED expiry] A fresh ciphertext's lineage identity is its full file
SHA256. Derived-state headers contain sorted, nonzero integer coefficients
of those original identities. Evaluation adds and cancels this map before
checking its live L1 norm against W. Expiry must name the actual live original
file, and a window contains only coefficient-one entries within capacity.
This records honest state arithmetic. It is not an authentication mechanism
against a party forging the entire state header and payload.

## Process credentials and scope

[DERIVED/EXECUTED] The orchestrator and processes share a host UID. The
orchestrator launches fixed commands and never reads private payloads.
Public init/finalize/encode/evaluation processes have an explicit OS denial
for the private-artifact tree. Registration/decode process i has access to
its own directory and is denied every other recipient directory. Recipient
registration and its later decoder have different PIDs. Public constructor,
issuer and evaluator roles receive no private-key path as an input.

[OPEN] The sandbox profiles restrict this experiment's artifact paths; they
are not a malicious-process escape proof or a defense against the same-host
administrator, an unsandboxed launcher, filesystem backup access or host
memory inspection. Directory permissions alone would not isolate processes
sharing a UID. There is no secure-erasure, constant-time, authenticated
transport, PQ-security or full-privacy claim. Expected-time uniform sampling
and the prior cryptographic assumptions remain. The implemented closure is
fixed-coordinate scalar arithmetic and exact expiry, not arbitrary nonlinear
encrypted learning. These boundaries do not block the demonstrated file and
process workflow.
