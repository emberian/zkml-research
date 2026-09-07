# Independent review of the frozen private-address EMA probe

[DERIVED / decision, 2026-09-07] **Accepted for the stated two-step honest-input feasibility and sampled byte-replay claim.** The frozen source implements the contract's signed arithmetic, four-bin selection, sign inference and top-level gate counts. No implementation mismatch was found. The replay input-provenance qualification below must accompany the result. This is a read-only source/mathematical review and public-metadata consistency check, not an independent encrypted rerun or an implementation-privacy proof.

[EXECUTED / exact target] The author source manifest has SHA256 `2dd31102c7ed58a974814f48102ec2a1f9228b984c766c5b5c47ec5d695b2339`; the final public results have SHA256 `a5e3e6f0d7c19d0b5951a5379cf422353a72824c1418f3197bcb6270d7d0f76c`. The reviewed core library is `fad1864642ff6c0036cdfed66b93bc7e21bb2720572d0ddd30b6effa2c65c880`, host is `f0ba609bdf7d6a2ad2b83298b526d8fecf4d8569f7db28af6c5306c14e159ac2`, and driver is `95f0e4f6f04c159dabca1e56a187f566a21e8a0e4711400ed9bb5641bf78e3b0`. All five Rust files, driver and metadata collector were read. The earlier [contract review](CONTRACT_REVIEW.md) and its input pins remain unchanged.

## Arithmetic and address selection

[DERIVED / source checked] In [src/lib.rs](../src/lib.rs), `add` at line 64 implements the full-adder identities `sum=(x XOR y) XOR carry` and `carry'=(x AND y) XOR ((x XOR y) AND carry)`. The two carry events are disjoint, so the final XOR is the needed OR. Ignoring the final carry gives the eleven-bit modular sum. The signed ranges proved in the contract review ensure that the intended signed intermediates do not overflow.

[DERIVED] `candidate` at line 82 sign-extends both inputs to eleven bits, constructs 8s by appending the original byte above three low zero bits, subtracts s by complement-plus-one, adds u, and returns bits 3 through 10. This is exactly `floor((7s+u)/8)`, including the negative second update. The two-bit address precedes the eight label bits in the input. `learn` at line 100 shares the two address complements and forms one conjunction for each fixed public bin index; no plaintext address indexes the state. Its MUX call uses `(select,candidate,old)` in the library's documented argument order.

[DERIVED] `infer` at line 123 selects sign bits 7/15 and 23/31 with q0, then the low/high pair with q1. This is the least-significant-bit-first address convention. The returned Boolean means negative, with zero nonnegative. The expected source counts are exactly 180 AND, 264 XOR, 46 NOT, 32 MUX and 20 trivial-constant calls per Learn, and three MUX calls per Infer. The host asserts these counts; they include top-level calls simplified internally by TFHE and do not measure bootstrap invocations.

## Role and serialization boundary

[SOURCE / checked implementation] Setup generates ClientKey, PublicKey and ServerKey, writing the complete client key to the reader directory. Issuer reads the public key and its private request and uses ordinary `PublicKey.encrypt`, including for initially zero state bits. Host reads only the serialized ServerKey, a 32-bit state vector, and a ten-bit Learn input or two-bit query. Reader is the only evaluation-stage binary that invokes ClientKey decryption. The driver is explicitly a private fixture coordinator: it creates known requests, runs reader comparisons and computes the ordinary signed-integer oracle. It is not presented as the host.

[DERIVED / exact limits] The selected label restriction ±120 is enforced by the honest issuer. The host does not cryptographically validate encrypted label values or enforce a policy on anyone holding the client key. The retained key can open all state and input ciphertexts. File permissions and separate processes under one account are useful file-flow discipline; they do not establish isolation from the account owner. Preregistered fixture values are public in the contract. The run therefore checks an encrypted-address computation path, not secrecy of an experimentally unknown fixture.

[SOURCE / checked envelope] `read_bits` verifies the eight-byte version marker, kind, payload length, expected vector length, canonical reserialization and the `Encrypted` variant for every data bit. `write_bits` requires that variant and emits the same deterministic envelope without timing or run-specific fields. Public arithmetic constants may be trivial internally; accepted artifact data bits must be actual ciphertexts. These are suitable checks for the bounded local format, not a reviewed hostile decoder, key-compatibility proof or chain-finality protocol.

## Replay and measurement meaning

[SOURCE / checked driver] [run.py](../run.py) runs each host operation twice in separate subprocess invocations, with the same binary and input-path arguments and distinct output paths. It compares the complete output files with byte equality, not just digests or decrypted equivalence. Source hashes are recorded before and after the run. A replay mismatch is retained and prevents the next logical Learn. Inference on the retained first state is still performed, as permitted by the preregistration. Fresh issuer encryption is not repeated merely to manufacture equal input ciphertexts.

[DERIVED / evidence qualification] The field `same_serialized_read_inputs` at driver line 120 compares path strings. It does not compare hashes captured at the time of each read. There are no intervening writes to those key/state/request inputs in the inspected sequential driver, so the normal-run interpretation is coherent under the absence of external mutation. The record must not be described as independent proof of equal read-time bytes. A later stronger provenance record can add per-invocation input hashes; this frozen first run was preserved. The author acknowledged this qualification.

[REPORTED / retained public run] The final [results.json](../runs/run_001/results.json) reports both logical Learn steps, all four registers and both selected signs matching its independent integer oracle, unchanged unselected registers, and all four full-byte replay comparisons matching. It records 18 successful subprocess operations and no errors. The distinct replay wrapper PIDs and host log records match the driver structure. The private plaintext audit files were not read in this review; those correctness comparisons remain attributed to the author's executed record.

[REPORTED / bounded cost evidence] Across the four Learn host evaluations, including replays, the recorded evaluation times range from 8.938 to 9.825 seconds; the four Infer evaluations range from 0.122 to 0.131 seconds. Host read/validation time is separately reported, and subprocess wall time additionally includes process overhead. State envelopes are 108,441 bytes and one-bit output envelopes are 3,413 bytes. Public and server key sizes are reported as 90,316,428 and 157,865,796 bytes. These are one-run measurements, not a calibrated benchmark or a claim of general throughput. The parameter's name is source metadata, not a new failure-probability, security-level or post-quantum estimate.

## Independent public checks and closeout

[EXECUTED] The command

```text
python3 research/learn_infer_only/experiments/end_to_end/private_ema/review/check_public_metadata.py > research/learn_infer_only/experiments/end_to_end/private_ema/review/public_checks.stdout.txt 2> research/learn_infer_only/experiments/end_to_end/private_ema/review/public_checks.stderr.txt
```

[EXECUTED] exited zero with empty stderr. [public_checks.json](public_checks.json) records 22 unchanged source/manifest/result pins, four rechecked compiled-binary hashes, and 54 public log hashes for the 18 operations. Public stdout JSON matches the retained result entries; all eight host counters match the source-derived counts; all host command paths exclude the private directory. The four reported replay pairs have internally consistent equal output hashes and lengths and distinct wrapper PIDs.

[EXECUTED / review boundary] This checker opens public source, binaries, normal logs and metadata only. It does not run any compiled binary, open any ciphertext/key file, inspect a private fixture/audit file, or perform a crypto, malformed-input, routing or extraction experiment. No author, predecessor, shared-ledger or companion file was changed. No additional test or encrypted workload is needed for this review's bounded decision.

[DERIVED / closeout] The reviewed artifact establishes a coherent tiny encrypted state transition with separate issuer/host/reader file flows and successful recorded sample replay. It retains a full reader credential and supplies neither selected-output-only enforcement nor a no-master-read construction. Those boundaries agree with the contract rather than being newly inferred guarantees.
