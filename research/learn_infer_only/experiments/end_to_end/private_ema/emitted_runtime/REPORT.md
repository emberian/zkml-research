# Lean-emitted Boolean schedule runtime

[EXECUTED result] A new generic Rust TFHE interpreter executed the exact
Lean-emitted XOR/AND descriptors. The independent plaintext comparison matched
25,600 Learn rows and 49,152 Infer rows. The authorized encrypted smoke matched
both logical Learn states and Infer signs to the integer oracle; all four
separate-process replay pairs matched complete serialized bytes. Actual command
output, public ciphertexts, costs and pins are retained here. This establishes
only those finite executed results.

[SOURCE implementation] `src/lib.rs` parses and validates the descriptor and
executes generic wire/constant/XOR/AND operations. `src/ciphertext.rs` supplies
TFHE 1.6.3 gates and the prior PEMA0001 envelope; `src/main.rs` concatenates the
existing encrypted ingress bits and requires Encrypted output variants. The
runtime contains no hand-authored learner update, MUX, address selector or sign
selection implementation. Its separate public-Boolean backend uses the same
schedule loop, while `compare_plain.py` supplies an independent signed-integer
oracle. `SOURCE_AUDIT.md` states the exact inspected scope and remaining TCB.

[SOURCE emitted artifacts] The formal lane owns
`formal/private_address_ema/emitted_schedule/SCHEMA.md` and its emitted JSON.
The runtime validated 538 Learn gates (342 XOR, 196 AND) under the allocated
11,562-wire bound, with 10,982 unused slots; Infer has nine gates (six XOR,
three AND) under a 46-wire bound, with three unused slots. The CSE numbering
gaps are accepted without remapping. `reports/plain/summary.json` records the
actual parser output and descriptor hashes.

[EXECUTED pins] `freeze.json` SHA256 is
`b45a38b01838b9b44bf8f8bcdd67c7e908bec0850b0f627d051d3a5e75785b3b`.
It pins 29 public files before cryptographic execution, including the prior
read-only key/fixture/reader, contract, runtime source/lock/binary, and:

| Artifact | SHA256 |
|---|---|
| Learn JSON | `94e8369ffc8fcdf57b8351b278d5af90dc49a26d83600d40f0bd6a0da359dde8` |
| Infer JSON | `b742ed7710d2680119eceeff0c553d675e1ce187a503981fc500a6a4a683b80c` |
| Runtime binary | `941f431d7762183bb3f6565d39b93d371331fcf121920c903164b7ff06ef6ab1` |
| Cargo.lock | `37e0e0a6a0570f06663565eb892bed9943868590943c1197375ad471dae58321` |

[EXECUTED build] `cargo test --locked --offline -j 1` passed all eight tests;
`cargo build --release --locked --offline -j 1` succeeded. Exact stdout/stderr
is in `test.log` and `build.log`; toolchain/dependency pins and inspected source
hashes are in `build_pins.json`. No previous source or binary was modified.

[EXECUTED plain coverage] `python3 compare_plain.py` exited successfully.
The Learn rows consist of 12,288 saved utility transitions, 2,048 cases covering
every selected signed-byte state with labels ±120 at all four addresses, and
11,264 cases covering eleven selected-state boundary values with every signed
byte label at every address. The latter two groups use deterministic varied
unselected bytes, not all four-byte states. Infer checks every address for each
saved selected-route post-transition state. `reports/plain/` keeps command
metadata, full losslessly compressed interpreter outputs and the summary.

[EXECUTED encrypted scope] After reporting the exact freeze and plaintext
comparison to root, `python3 -u run_smoke.py` executed exactly two logical Learn
and two logical Infer calls, each replayed once. There was no setup, issuer,
large workload, extra operation or retry. The existing public fixture supplied
the encrypted inputs and initial state. Every host process used the generic
binary, frozen descriptor and server key, with `RAYON_NUM_THREADS=1` and no
concurrent host process from this lane. The initial runtime checks and all
replay/result/input hash comparisons succeeded before the reader audit began.
Then the prior reader opened only these successful new outputs into the ignored
private directory. Both state/sign comparisons and unselected-register checks
passed. `reports/smoke/results.json` retains executed ordering, process arguments,
hashes and match indicators; no private key value/hash or plaintext audit
contents are copied into reports. `reports/smoke/artifacts/` archives only the
eight successful public ciphertexts.

[EXECUTED observed costs] Each row below summarizes four host processes,
including replays; `costs.csv` retains every process measurement. Gate counts
are API calls, and each evaluation also creates two internal public constants.
Workload contention changed during the smoke; wall time is not a controlled
benchmark or an expected deployment cost. Peak RSS reached 485,523,456 bytes
for Learn and 484,933,632 bytes for Infer.

| Operation | Wall seconds, min–max | Evaluate seconds, min–max | Output bytes |
|---|---:|---:|---:|
| Learn | 13.944–27.680 | 13.675–27.394 | 108,441 |
| Infer | 0.544–0.705 | 0.259–0.345 | 3,413 |

[EXECUTED contract wording discrepancy] The frozen driver adds a final
read-only frozen-source/input integrity recheck after private audit. This is
broader than the frozen contract's literal statement that *all* such checks
finish first. Every prerequisite public evaluation/replay/result hash check
did finish before private audit; no extra encrypted evaluation or replay took
place. The original contract/source and actual order are preserved, and root
was informed. Post-run collection additionally checks archival copy integrity.

[REPORTED separate failure context] Root reported a replay mismatch on the
fourteenth Learn in the separate older handwritten-runtime long workload,
after thirteen matching Learn pairs. This lane did not inspect that failed
output or perform a private audit on it. That retained failure belongs to its
own evidence package and makes a general replay-determinism conclusion from
this short emitted sample unjustified.

[OPEN proof and security boundary] The formal lane's emission/CSE/refinement
proof is a separate artifact. Rust/serde parsing and execution, compilation,
TFHE correctness/noise, serialized key validity and universal ciphertext-byte
determinism remain unproved here. The standalone host accepts any valid schedule;
the external freeze binds this particular research run. There is no authorized
program registry, accepted chain, same-account isolation, no-master-read,
selected-output-only, protocol-privacy or PQ result. The reader retains its
unrestricted client key. The earlier failed long workload is not superseded by
this positive smoke.
