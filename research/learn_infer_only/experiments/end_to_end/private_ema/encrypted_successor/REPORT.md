# First extended TFHE EMA workload stops at byte-replay mismatch

[REFUTED: deterministic complete-byte replay for this pinned execution]
The prescribed workload stops at **Learn event `h0-e0014`**. Its primary and
replay processes both exit zero, with equal before/after/across-invocation
hashes for the server key, parent and encrypted input. The two complete
108,441-byte outputs differ. The first thirteen Learn replay pairs matched.
This is a failure of the required exact-byte replay path in this execution;
it does **not** establish failed plaintext semantics or incorrect decryption.

[EXECUTED] `reports/run001/public_failure_audit.json` independently rechecks
the retained public bytes and transcript in `seal_public_failure.py`. No
cryptographic program, secret-key read or plaintext decoder is invoked by that
audit. The original run stopped without retry, new encryption or private drain.
No continuation or Infer evaluation was performed after the mismatch.

## Exact discrepancy and preserved inputs

[EXECUTED] The first differing byte has zero-based offset **71,185**, and the
last has offset **81,312**. Exactly **10,015 bytes** differ. Both envelopes
contain 32 `Ciphertext::Encrypted` records, each with 838 little-endian u32
LWE coefficients, native-modulus serialization and scalar width 32. All
variant tags, vector lengths, modulus metadata and envelope bytes agree.

| Boolean record, zero-based | Register / LSB bit | Coefficient byte interval | Changed bytes | Changed u32 coefficients |
|---|---|---|---:|---:|
| 21 | 2 / 5 | [71,185, 74,537) | 3,340 | 838 |
| 22 | 2 / 6 | [74,573, 77,925) | 3,339 | 838 |
| 23 | 2 / 7 | [77,961, 81,313) | 3,336 | 838 |

[EXECUTED] Every other Boolean record agrees byte for byte. Record and bit
positions describe the public serialization layout, not a decrypted bit.
The complete buffer parser consumes exactly the file length and pins the
inspected local source definitions. This is structural ciphertext inspection;
neither output has been decrypted here.

[EXECUTED] Primary output SHA-256:
`f1b421cedb055ed3d9878af7e9ed48fd369eed7681b227b5f89b9ae185be6172`.
The replay output, all three read-input hashes, per-process executable hashes,
full commands, resource reports and stdout/stderr appear in the failed pair
and operation entries of `public_failure_audit.json`. The ordinary public
runtime files remain in `runtime/run001/public/`; its sibling `private/`
contains the retained full client key and was not read by the failure audit.

## Actual counts and environment

[EXECUTED] Start was 2026-09-08 04:12:26 UTC. The public-run subprocess ends
with exit 1 after **424.614 seconds**. All 61 role processes launched before
the assertion exit successfully: one setup, two zero-state issuances, sixteen
query ciphertext issuances, fourteen Learn-input issuances and twenty-eight
host Learn evaluations. There are thirteen accepted logical Learn events,
fourteen tested replay pairs, zero Infer evaluations and zero reader calls.
The 384 Learn/96 Infer workload is incomplete; no encrypted utility result is
claimed.

[EXECUTED] There was one sequential host process at a time. `RAYON_NUM_THREADS`
and `OMP_NUM_THREADS` were both **unset**, as captured in `started.json`.
The host executable is byte-identical to the reviewed original probe:
`d45d096a68a46ecfde022bf2b35a30d512d93d5cb333c9097f64c04aeeebe474`.
The frozen dependency declaration is TFHE 1.6.3, default features disabled,
`boolean` enabled, and bincode 1.3.3; Cargo.lock and all binary identities are
pinned. The machine is macOS 26.6.1 arm64. The parent source manifest records
the original Rust build and inspected library sources.

[EXECUTED] Failure audit hashes all 24 pre-launch pinned files again and
checks the 84 per-invocation public read-input before/after comparisons.
It verifies all fourteen actual output pairs, records every public runtime
file hash and retains `otool -L` output. That command reports declared binary
links after failure, not a captured census of loaded libraries during execution.

[OPEN cause] The reason for process-to-process byte variation is unestablished
by this record. Root's separate source audit may investigate library planning,
arithmetic or runtime choices; no root cause is inferred just from the bytes.
The failed outputs remain unopened. Semantic correctness, noise behavior and
whether a different pinned execution setup can replay deterministically remain
separate questions.

## Utility and security scope remain separate

[SOURCE completed utility] `../utility/REPORT.md` retains the unchanged
plaintext law's 7,486/8,192 final labels (91.3818%) on reused data, versus
7,462/8,192 for W32. The hard/wet stratum regresses to 672/1,024 (65.6250%).
These facts neither prove an improvement nor compensate for the replay
failure. The selected first-two-history fixture's 28/32 label count is a
plaintext oracle result only for this stopped TFHE workload.

[DERIVED] The current client key remains unrestricted, both route identities
are public, data are public synthetic fixtures and processes share an account.
No no-master-read, PQ, protocol-privacy, restricted-release, journal or universal
Rust/TFHE refinement result follows. The earlier successful two-step probe
remains valid in its narrow recorded scope; its sample did not establish
universal byte determinism.

[EXECUTED reproduction of the public audit only]

```
python3 -B research/learn_infer_only/experiments/end_to_end/private_ema/encrypted_successor/seal_public_failure.py
```

[EXECUTED] Audit SHA-256:
`c089857dee7190932e8d644d6bf72c9aec60c36c4bd9b8753267cb20aeb9ccf4`.
The frozen run programs, failed first execution and ciphertext bytes are
preserved. Do not relaunch `launch.py`, run `drain.py`, or retry the failed
pair to repair this result.
