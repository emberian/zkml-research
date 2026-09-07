# Persistent designated DDH public host

[HYPOTHESIS preregistered] Retaining the existing `CAS.inspected` dictionary
across proposals should remove repeated subgroup-validation subprocesses for
unchanged ciphertexts. Every `CAS.get` must continue to read and SHA256 the
entire blob. All existing state, authorization, parent, designated query and
transition code must continue to run.

[DERIVED design] `host.py` adapts the previously measured BFV public-host
wrapper, SHA256 `5f4426feebc68cdeea16cd69a20157e080e47aad7459c3741cfde291a64070a9`.
It imports exact copies of the designated integration's journal modules after
checking their pinned bytes. Their `roles.propose`, `CAS.get`, validators and
transition bodies are unchanged. The wrapper replaces only the CAS constructor
looked up by `roles.propose`, returning one metered instance with its existing
inspection dictionary. One-shot mode uses the same wrapper and discards that
instance at process exit.

[DERIVED] The worker accepts the existing public host configuration's exact
nine keys: `crypto_binary`, `crypto_binary_sha256`, `crypto_sources`,
`native_dependency`, `crypto_context`, `crypto_context_sha256`, `genesis_path`,
`genesis_sha256`, `command_log`. It fixes the full configuration, genesis,
context digest, crypto source/dependency identities and CAS directory for its
lifetime. It checks the pinned setup validation record beside genesis before
reusing public-context validation. That record is trusted setup configuration,
not a cryptographic certificate an arbitrary caller can manufacture.
The original crypto wrapper continues to check source, native library and
context bytes before each actual subprocess. The worker allows only `inspect`,
`host-learn` and `host-infer`; it accepts no scalar-key or plaintext-vector
argument. The experiment is process separation, not OS isolation.

[HYPOTHESIS normal paired fixture] Predeclare six public deterministic signed
577-dimensional contributions and fixed row-0/row-1 queries after contributions
3 and 6. Keep capacity 32; there is no expiry in this small cache experiment.
Copy only the public context and zero ciphertext from the completed designated
crypto positive run, run a fresh full context validation with pinned sources,
and issue fresh OS-randomized ciphertexts using the public key. Do not copy
recipient scalars or initialize a new master. The fixture coordinator owns
only its ordinary issuer/command signing keys; the host receives public signed
actions and ciphertexts.

[HYPOTHESIS comparison] Run each of eight proposals through one-shot and
persistent modes with the same head, authorization and fresh ciphertext in
separate CAS directories; alternate which mode runs first. Compare complete
canonical proposal bytes and result ciphertext bytes. Check the original
unaltered `roles.py propose` entry point on the first event too. Advance the
fixture head by the known public queue rule, checking the proposed state
digest. This is a proposal-equivalence experiment: no authority acceptance,
recipient decoding, utility or private-input result is claimed.

[HYPOTHESIS measurements] Record per-proposal caller/function wall times,
actual crypto calls, CAS gets, full-blob SHA256 calls and bytes, worker startup,
cache size and lifetime. The meter delegates to the original hash function;
the first hash inside `CAS.get` is the unchanged full-blob hash. Both modes
must have equal get/hash counts and byte totals. Source and configuration
checks are additional reads outside those CAS counters. Total harness time
includes both paths and fixture preparation; it is not an optimized full
end-to-end measurement.

[OPEN limits] The cache holds public metadata without pruning until restart.
SHA256/content-address assumptions, the underlying file-read/subprocess
time-of-check boundary, trusted source/configuration and the designated
construction's privacy/continuity limitations remain. No adversarial,
malformed-input, routing or extraction experiment is performed.
