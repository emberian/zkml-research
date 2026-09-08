# Source audit and interpretation boundary

[SOURCE implementation] Read `src/lib.rs` in full. Private descriptor fields
can enter `Schedule` only through `Schedule::parse` (line 102). Its validation
tracks initialized slots, verifies every reference, and allows CSE holes under
the allocated upper bound. `Schedule::evaluate` (line 177) allocates optional
slots, copies input values, resolves only validated references, and dispatches
the two gate operators through `Backend`. The plain backend implements Boolean
XOR/AND. This is a source audit, not a proof of Rust operational semantics.

[SOURCE implementation] `src/ciphertext.rs:31` implements exactly TFHE constant,
XOR and AND calls. `src/main.rs:21` completes schedule validation before the
host reads its server key or ciphertext inputs; lines 40–46 concatenate the
existing state and operation-specific ingress bit vectors. Lines 53–57 evaluate,
check Encrypted variants and create the output artifact. No learner arithmetic,
address equality, MUX construction or sign selection is authored in these Rust
files; those operations reside in the separate emitted descriptors. This absence
claim is confined to the three owned Rust source files, read in full.

[SOURCE implementation] `src/ciphertext.rs:59` explicitly selects fixed-width
integer encoding for bincode compatibility and rejects trailing data. The
preceding probe's canonical reserialization check remains. Lines 86–107 verify
the typed PEMA0001 envelope, byte length, bit count and Encrypted variants.
Lines 110–126 check outputs before file creation, use create-new semantics and
sync the write. A failed I/O can leave a partial newly created file; process
failure is not treated as a successful result by the driver. This local format
is not a reviewed adversarial decoder, parameter validator or atomic journal.

[SOURCE implementation] `inspected_source.txt` retains exact numbered excerpts
of TFHE 1.6.3 and bincode 1.3.3 sources; `build_pins.json` retains full-file
hashes. TFHE `boolean/server_key/mod.rs:48–87` forwards the generic public gates
to its Boolean engine. `boolean/ciphertext/mod.rs:14–19` defines serializable
Encrypted and Trivial variants. `boolean/engine/mod.rs:557–592` and `710–746`
show the AND/XOR encrypted and constant branches. Its `919–927` can propagate
a public false constant through AND; `965–972` specializes XOR with public
constants. Internal constants are therefore valid, while the artifact boundary
must separately reject any Trivial outputs. Calls are not bootstrap counts.

[EXECUTED validation] `test.log` keeps the actual offline cargo test output:
eight tests pass, covering sparse writes, generic truth-table execution,
uninitialized/out-of-range references, strict JSON/reference types, duplicate
fields, operation dimensions, constant outputs and fixed-width bincode roundtrip
with trailing-data rejection. `build.log` keeps the successful offline release
build. These checks do not test malicious ciphertexts or prove library safety.

[EXECUTED semantic comparison] `reports/plain/summary.json` and the compressed
full stdout plus per-command metadata retain the independent integer-oracle
comparison. It covers 25,600 Learn rows and 49,152 Infer rows, all matching.
The report separates saved utility transitions, exhaustive selected-byte states
for the two permitted labels at each address, and eleven selected-state edges
for all signed-byte labels at each address. Unselected state bytes in the two
synthetic groups vary by a fixed public formula; this is not enumeration of all
four-byte states. Infer checks each of the four addresses for each saved
selected-route post-transition state. These are finite executed comparisons,
not a replacement for the separate formal emission/refinement theorem.

[DERIVED program binding] Standalone `host` accepts any descriptor passing the
schema; this generic executor does not enforce an authorized-program registry.
For this research run, `freeze.py` pins the exact emitted descriptors and binary,
and `run_smoke.py` verifies those hashes before each operation pair and after
all public work. The host's generic behavior plus the external frozen manifest
is the tested binding. No accepted-chain/finality authorization claim follows.

[OPEN TCB] JSON parsing/serde, Rust memory and loop semantics, compilation/LLVM,
TFHE gate correctness/noise and serialized key validity remain outside the
Lean theorem. Same-account processes do not establish operator isolation, and
the retained reader client key remains unrestricted. Positive ciphertext replay
equality is an observation about exact tested bytes, not a universal theorem.

[EXECUTED contract wording deviation] The frozen driver completed every public
evaluation/replay and all prerequisite frozen-input/result hash checks before
opening any private reader audit. It also performed a final read-only
`check_frozen("after_private_audit")` after the reader stage. The contract's
literal claim that *all* frozen-public-file checks finish first was too broad.
The extra integrity check, original source, frozen contract and executed order
are preserved. No extra cryptographic operation or retry was performed.
`collect.py` later archives only the successful public ciphertexts and compares
their copies with the executed hashes; this is post-run evidence collection.

[REPORTED separate root context] During this lane's small frozen smoke, root
reported that the older handwritten-runtime long utility workload stopped at
its fourteenth Learn replay mismatch after thirteen matching pairs, with equal
public input hashes and successful host exits. This lane did not inspect or
execute that failed workload's output/private audit. Its outcome belongs to
the parent lane's retained evidence, and prevents interpreting any small
successor sample as a field-wide or backend-wide replay guarantee.

[EXECUTED search accounting] This implementation lane used local source reads
and repository file searches only: no web searches, Scry SQL or Kagi queries.
