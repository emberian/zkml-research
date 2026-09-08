# Generic emitted-schedule successor contract

[DERIVED scope, before cryptographic execution] This directory implements a new
generic Boolean schedule interpreter. Only XOR, AND, wire lookup, internal
public constants and ordered output collection occur in its evaluator. It does
not reconstruct the learner, arithmetic, MUX, address selector or inference
logic. The formal bridge separately emits the schedule from its Lean terms and
owns the semantics theorem. The preceding probe/workload remain frozen.

[SOURCE interface] The exact descriptor contract is
`formal/private_address_ema/emitted_schedule/SCHEMA.md`. `learn` consumes 42 bits
and produces 32; `infer` consumes 34 and produces one. The host prepends the
32 encrypted parent state bits to the ten encrypted Learn input bits or two
encrypted query bits, preserving the existing register-major/LSB order.

[DERIVED decoder rules] Deny unknown/duplicate fields, unknown schema or
operators, mixed/ill-typed reference forms, wrong operation dimensions, wire
bound violations, nonincreasing writes, writes to inputs, forward references
and references to CSE holes. `nWires` is an allocation upper bound; holes and
unused final slots are accepted. Validation finishes before key/ciphertext
reads. Local resource bounds are 16 MiB descriptor bytes, 100,000 wires and
100,000 gates, 64 MiB ciphertext envelope bytes and 1 GiB server-key bytes;
these are implementation caps, not measured costs or security parameters.

[SOURCE byte compatibility] `private_ema/src/lib.rs` defines PEMA0001 followed
by one kind byte, a little-endian u64 payload length and bincode 1.3.3 serialized
`Vec<Ciphertext>`. This runtime preserves those bytes and all-Encrypted input
and output checks, uses fixed-width little-endian bincode decoding, rejects
trailing bytes, checks canonical reserialization and exact kind/bit count.
It creates new output paths and syncs successful writes. These checks are a
local probe boundary, not a reviewed hostile network decoder or durable chain.

[DERIVED generic execution] The evaluator initializes exactly the input slots,
creates internal false/true trivial ciphertexts, executes exactly one TFHE
XOR/AND API call per listed gate and resolves outputs in order. The two public
constants may occur inside execution. A trivial output causes failure before
artifact creation. Call counts are API counts, not measured bootstraps. The
inspected TFHE implementation specializes operations with constants; therefore
gate count alone does not equal bootstrap count.

[SOURCE credential continuity] The prior `setup`, `issuer` and `reader`
binaries can supply the same serialized parameter/key/ciphertext formats.
Their pinned setup retains an unrestricted client key. The new host accepts
only the server-key path, parent, input/query, descriptor and output path.
Same-account process separation remains an API/file-flow boundary. This adds
no no-master-read, selected-output-only, protocol-privacy or PQ claim.

[DERIVED proposed positive cryptographic check] Subject to root's schedule and
freeze coordination, reuse the saved preceding two-transition positive fixture
and its public encrypted inputs/parent/key. At most two logical Learn calls
and two Infer calls are evaluated with the new descriptor and each is replayed
once in a fresh process from identical bytes. Root may select a subset. No
fresh setup is necessary. The existing reader may open resulting state/sign
outputs into a private audit directory for the prior integer-oracle comparison.
All public evaluations, replays and frozen-public-file hash checks finish before
the private reader audit begins. Private plaintext/key material is never copied
into public reports. A replay mismatch is preserved and blocks subsequent Learn.
No repeated retries, large utility
rerun, routing experiment or cryptographic attack is authorized by this file.

[DERIVED freeze] Before encrypted execution, record source/lock/binary hashes,
the exact two emitted JSON hashes, this contract and driver hashes, runtime
toolchain and prior fixture binary/key/ciphertext hashes. Record command/output
and replay byte comparisons. A changed schedule/source is a new freeze, not a
silent replacement of a prior result.

[OPEN proof boundary] Even a Lean theorem for emission/CSE/refinement and exact
positive runtime agreement do not prove Rust parsing, memory or loop semantics,
the compiler/LLVM, TFHE gates/noise, serialized keys, architecture determinism
or reader restriction. These remain assumptions/source-audited TCB and scoped
executed evidence. A cross-version or cross-architecture replay claim would
need separate work.

[REPORTED root coordination] Root authorized this exact small successor after
the emitted JSON, semantic comparison and source/contract freeze are saved and
all contract gates pass. Send root the comparison and frozen manifest first;
no additional approval round is required. Use one host process at a time and
record concurrent-workload contention as a limitation of measured wall cost.
