# Bounded private-address EMA feasibility contract

[DERIVED protocol, before execution] This is a tiny encrypted learning and
public-replay experiment using the already cached TFHE 1.6.3 Boolean API.
It extends the earlier `he_closure_costs/tfhe_ema_probe` arithmetic without
changing that probe. The first run is limited to one setup, at most two logical
Learn transitions, private sign inference and one separate-process replay of
each tested evaluation. No long workload, routing/extraction experiment or
malformed-input experiment is included.

## State and permitted operations

[DERIVED definition] One route contains four signed 8-bit registers, initially
zero. A private issuer supplies a two-bit address `b∈{0,1,2,3}` and a signed
label `u∈{-120,120}`, encrypted under the public input key. The host computes
all four candidate values and uses encrypted address equality and MUX gates:

```
candidate_j = floor((7*s_j+u)/8)
s'_j = candidate_j if j=b, otherwise s_j.
```

A query issuer privately encrypts a two-bit address `q`. Infer uses three
encrypted MUX gates over the four sign bits and releases one encrypted Boolean
`s_q<0` to the reader. Zero is nonnegative. The host never receives the address,
label, plaintext registers or decrypted answer as command arguments.

[DERIVED arithmetic] Sign extension to 11 bits, `7s=(8s)-s`, an 11-bit sum and
discarding the low three bits implement signed floor division. For signed
8-bit inputs, `7s+u∈[-1024,1016]` fits 11 signed bits. Starting at zero with
labels ±120 preserves `s∈[-120,120]`. The encrypted address MUX and floor make
this a state-dependent nonlinear transition, not a fixed linear contribution
sum. No utility or language-understanding claim follows from four registers.

## Roles, files and comparison boundary

[DERIVED implementation plan] Separate setup, issuer, host and reader binaries
run as separate processes. Setup generates and serializes a full TFHE client
key, public encryption key and server evaluation key. The client key is saved
only in the private reader directory. Issuer processes read only the public
key plus their private fixture request. Host processes read only the serialized
server key, state and input/query bytes. Reader processes hold the client key.
All roles share this operating-system account, so this is an API/file-flow
boundary, not demonstrated isolation from an account owner.

[DERIVED credential limit] The reader retains an unrestricted client key and
can read all state/input ciphertexts. This experiment has **no no-master-read,
post-quantum, protocol-privacy proof or selected-output-only enforcement claim**.
The parameter name is copied from the source; no security estimate is inferred
from that name. Encryption uses the library's normal randomness; no fixed seed
or deterministic encryption is introduced for replay.

[DERIVED serialization] Pin Cargo.lock, sources, binary hashes, TFHE parameters
and bincode 1.3.3. Serialize public keys and every ciphertext artifact to disk.
Add a small typed/versioned envelope for state/input/query/output bit vectors;
this is a local probe format, not a reviewed network decoder or accepted-chain
protocol. Existing finality/journal code is not modified or implicitly composed.

[DERIVED oracle and positive fixture] An independent Python integer oracle
uses ordinary signed integers and `//8`; it does not mirror the gate circuit.
The preregistered sequence targets private bin 2 with +120 and then -120.
The expected selected register moves `0→15→-2`, while all other registers stay
zero. Query bin 2 after each logical Learn to check the sign change. The reader
also opens the full state into private audit files solely for this normal
correctness comparison, consistent with its explicit unrestricted credential.
Synthetic request and answer contents stay out of public host logs. Public
reports contain match indicators, counts, timings and public artifact hashes.

## Replay and measured evidence

[DERIVED replay test] Execute each chosen host operation twice in separate
processes using identical serialized parent, input/query and server-key files.
Compare the full serialized output bytes, including every ciphertext coefficient.
Do not compare encryptions made with newly sampled coins. A mismatch is a
blocker to this backend's tested exact-byte replay path; record it without
attempting an unproved private-equivalence workaround or repeated retries.
The second logical Learn proceeds only if the first Learn's byte replay agrees.
Inference correctness can still be reported for a retained first result.

[DERIVED instrumentation] Keep subprocess wall time, Rust key/read/evaluation/
serialization timing, byte sizes and top-level Boolean API gate counts.
Counts are not claimed to be measured bootstrap counts. Preserve the first
run and every result, including a mismatch or error. Report feasibility and
cost before any expansion. No ciphertext-byte determinism theorem across
different architectures, compiler options or library versions follows from
matching this sample.

[SOURCE starting point] Earlier probe source and its recorded four-transition
result are read in full. TFHE's Boolean ciphertext serializer derives Serde;
the server-key wrappers call the Boolean engine. The inspected MUX engine
implements two bootstraps on fully encrypted branches, and the inspected
bootstrap evaluation path uses serialized evaluation keys and local arithmetic.
These reads motivate the replay test; they do not replace it or prove universal
Rust semantics. Exact read locations and source hashes will be retained.
