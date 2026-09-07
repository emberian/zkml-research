# Private-address encrypted EMA: bounded feasibility result

[EXECUTED verdict] **The preregistered two-step encrypted computation and all
four separate-process byte replays pass.** The host updates four encrypted
signed bytes through encrypted-address equality/MUX and signed floor arithmetic;
encrypted query selection returns one encrypted negative/nonnegative bit.
The full state stays encrypted along the continuation path. This supplies
small nonlinear encrypted evolution with observed deterministic public replay
on the pinned local backend, not a utility or no-master result.

[EXECUTED provenance] The protocol was written in `CONTRACT.md` before the
run. Build command: `cargo build --offline --release --manifest-path Cargo.toml
> build.log 2>&1` (30.97 seconds reported by Cargo). Run command:
`python3 -u run.py > run_001.log 2>&1`. Public metadata was collected with
`python3 collect.py`. All 18 role-process invocations exited successfully.
The first run is retained without retries. Source and binary identities,
commands and before/after source hashes are in `source_manifest.json` and
`runs/run_001/results.json`.

## Correctness, ciphertext continuation and scope

[EXECUTED] A fresh setup writes distinct serialized client, public encryption
and server evaluation keys. Separate issuer processes read only the public
key and their requests; separate host processes read only the evaluation key
and ciphertext artifacts. A reader process uses the retained client key.
Initial state, input, query, successor state and output are all real encrypted
Boolean vectors, serialized under typed local envelopes. The host rejects a
trivial Boolean in these data vectors; its internal public constants remain
trivial as intended.

[EXECUTED] The independent Python integer oracle checks initial state and all
four registers after each of two logical Learn operations. It also checks both
selected sign outputs and that all three unselected registers remain unchanged.
The preregistered update sequence moves the selected register `0→15→-2`, and
the selected sign changes accordingly. Reader audit files are private and
never supply a replacement state to the next host process. The next Learn
uses the preceding serialized ciphertext directly; no intermediate decryption
or re-encryption is required by the continuation algorithm. The out-of-band
correctness audit does decrypt the state, using the explicitly retained key.

[DERIVED fixture limit] The address and labels are publicly preregistered
synthetic values in the contract. “Private address” here describes their
encrypted API representation and the circuit, not an experiment in which the
coordinator or repository reader is uncertain about those fixture values.
This run demonstrates correctness and role file flow, not empirical semantic
privacy, text understanding or useful adaptation on a dataset.

[DERIVED credential limit] The reader's full client key remains an unrestricted
reader for every state and input. Processes share one operating-system account;
neither physical isolation nor erasure is established. There is no no-master,
post-quantum, whole-program privacy or sign-only-credential claim. The honest
issuer enforces labels ±120; the host's ciphertext type checks do not prove the
encrypted plaintext belongs to that set. No journal, finality gate or source
attestation has been composed with this probe.

## Exact replay evidence

| Host computation | Complete bytes compared | Result |
|---|---:|---|
| First Learn and its one replay | 108,441 | Equal |
| First Infer and its one replay | 3,413 | Equal |
| Second Learn and its one replay | 108,441 | Equal |
| Second Infer and its one replay | 3,413 | Equal |

[EXECUTED] Each replay invokes a new process with the same serialized key,
parent and input/query paths. No driver write changes those inputs between
the pair. The complete output envelopes compare equal, covering every
ciphertext coefficient; output hashes are retained. This is four comparison
pairs over two logical Learn and two logical Infer operations, not four
independent learning histories. No encryption coins were fixed or resampled
to force agreement.

[DERIVED provenance limit] The existing driver field
`same_serialized_read_inputs` compares command path strings. It does not hash
each file immediately before and after each individual read. The source's
sequential no-intervening-write behavior and final public artifact hashes
support this honest-run interpretation; independent read-time byte snapshots
were not collected. The independent reviewer identified this precision point;
the first frozen run is preserved. A stronger future provenance wrapper can
pin each invocation's exact read inputs. Four successful comparisons do not
prove determinism across architectures, compiler options or TFHE versions.

## Measured costs

[EXECUTED] Local build: Rust `1.98.0-nightly (91fe22da8 2026-06-21)`,
`aarch64-apple-darwin`, TFHE 1.6.3 Boolean-only, bincode 1.3.3. The chosen
source parameter is `PARAMETERS_ERROR_PROB_2_POW_MINUS_165`; its name is not a
new security/noise estimate. The complete parameter debug output is retained.

| Primary operation | Subprocess wall seconds | Gate evaluation seconds |
|---|---:|---:|
| Setup, including serialized keys | 0.877 | — |
| First Learn | 9.459 | 9.285 |
| Second Learn | 10.004 | 9.825 |
| First Infer | 0.289 | 0.122 |
| Second Infer | 0.291 | 0.123 |

[EXECUTED] Learn replay walls were 9.104 and 9.829 seconds; Infer replay walls
were 0.301 and 0.293 seconds. The table reports original evaluations separately
from replays. Public-key issuance took 0.103/0.100 seconds for the two ten-bit
inputs and 0.057 seconds for the two-bit query, including key reading and
serialization. Fresh 32-bit state encryption took 0.245 seconds. Full per-role
read/write/work timings and per-process `/usr/bin/time -l` logs are retained
in `costs.csv` and the run logs. Peak reported RSS was 568,049,664 bytes during
setup and at most 325,255,168 bytes among host invocations.

| Persisted artifact | Bytes |
|---|---:|
| Public encryption key | 90,316,428 |
| Server evaluation key | 157,865,796 |
| Full reader client key | 11,664 |
| Four-register state | 108,441 |
| Encrypted Learn input | 33,905 |
| Encrypted query | 6,801 |
| Encrypted sign output | 3,413 |

[EXECUTED/DERIVED] One Learn executes 180 AND, 264 XOR, 46 NOT, 32 MUX and
20 trivial-encryption API calls. One Infer executes three MUX calls. These
counts are incremented at the call sites and asserted by the host; they agree
with the source arithmetic decomposition. They are **not measured bootstrap
counts**. Library shortcuts and MUX internals make that a different quantity.

## Persistence and next boundary

[EXECUTED] Every role starts from persisted bytes in a fresh process. The second
Learn reads the saved first state, while the replay reads the same saved parent
and input. Large public keys and private reader/audit files remain retained
locally in ignored run subdirectories; ordinary public ciphertexts, logs and
hashes are retained as reviewable evidence. No private-key value or private-key
hash is included in the public reports.

[SOURCE review] The independent read-only source review checked the 11-bit
arithmetic, LSB-first address ordering, MUX branch directions, typed vector
sizes and gate counts, with no source blocker reported. This is not a machine
proof of the Rust circuit or TFHE implementation. The reviewed local MUX and
bootstrap source equations motivated the byte test; sampled byte equality
provides the execution evidence.

[OPEN next step] Evaluate the already fixed alpha/scale/update rule on the
frozen semantic fixture using plaintext integers before expanding encrypted
work. A two-route extension, meaningful utility, a receipt binding every
serialized read, and stronger restricted-release credentials are separate
obligations. No 384-step TFHE run, extra cryptographic retry, routing or
extraction experiment was executed here.
