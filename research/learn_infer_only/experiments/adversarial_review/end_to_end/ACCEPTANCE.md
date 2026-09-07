# Independent acceptance contract for the encrypted-window integration

[DERIVED review target; 2026-09-06 resumed run] The smallest useful result is
actual BFV evaluation of the frozen two-route, width-577, capacity-32 learner,
with a keyless authority recomputing each proposed encrypted transition,
committing its current state and exact output identity, and a separate trusted
full-key reader releasing only an authorized finalized result. This is a
meaningful integration target. It is a custody relaxation: the reader retains
the ability to decrypt every ciphertext under its key. A process wrapper does
not remove that capability. No all-role no-master-read or physical isolation
claim is accepted by this contract.

## Saved evidence and what it actually establishes

[SOURCE: local implementation and retained execution read] The frozen
`adaptation_utility/encrypted_window/README.md` and `probe/src/main.rs` report
384 Learn events, 256 exact-object expiries, 80 encrypted score readouts and
16 public empty-route zeros across the two selected histories. The reader
decrypts the entire polynomial; the result at coefficient 576 equals each
selected integer reference. The source separates HostRoute from plaintext
oracle data, but one executable and one Unix account still hold all roles.
The public deterministic seed bytes 201/202 drive the caller-supplied test RNG.
[REPORTED correction, Carver/root 2026-09-07] The dependency also obtains a public
polynomial seed from its internal OS RNG, so those bytes do not reproduce every
public key and ciphertext byte. Secret-key generation uses the caller RNG;
[REPORTED executed owner check] `end_to_end/crypto/rng_audit.json` now records
equal 4,099-byte raw secret keys and successful cross-decryption with a public
caller seed, despite different public-key bytes. The seed therefore remains a
full-secret exposure in that test. Independently of this credential issue,
these published vectors are known arithmetic inputs, not private development.

[DERIVED known-development limit] Switching that published fixture to OS-random
keys does not make its learned state unknown: the contribution vectors and
deterministic update history remain available for plaintext replay. The primary
utility fixture should be described as an arithmetic/integrity/durability
benchmark. A separate role-level private-input smoke case could use freshly
generated issuer-only observations, with plaintext/reference confined to the
issuer and trusted oracle while the host/authority receive ciphertexts. That
would test information flow in the harness, under its explicit isolation and
cryptographic assumptions; it would not prove security against the full-key
reader or the operator of the common Unix account.

[SOURCE: local implementation and retained execution read] The persistent
journal's frozen run005 tests real process crashes, replay and two-worker
SQLite races. Its fresh computational gate is explicitly a two-candidate
allowlist. The saved protocol does not verify BFV, private input provenance or
a cryptographic arithmetic receipt. Its Unix recipient also assumes a trusted
transport boundary. Replacing that allowlist with deterministic ciphertext
recomputation and authenticating the authority-to-reader result are necessary
new work, not claims already supplied by the saved experiment.

[SOURCE / provenance] `baseline_sources.json` records the files read and their
hashes. This review does not rerun the frozen large crypto experiment or modify
either companion tree.

## Minimal accepted semantics

[DERIVED acceptance contract] A fixed genesis identifies the program/version,
two routes, capacity 32, width 577, polynomial degree 4096, plaintext modulus
4294828033, exact ciphertext primes 2199023190017 and 4398046486529, parameter
encoding, public-key fingerprint, issuer policy, query/release policy and
recipient. Cross-genesis and cross-key objects are not interchangeable even
when parameter dimensions agree. Hashes bind complete bytes with an explicit
domain and unambiguous framing; metadata alone cannot prove that a ciphertext
was encrypted under the named key.

[DERIVED acceptance contract] A fresh Learn consumes an authenticated admission
envelope binding its complete canonical ciphertext hash, genesis, key and
parameter IDs, route, observation/nonce and feature/label-policy version. The
authority independently selects the current route accumulator and oldest exact
queued ciphertext, recomputes add-then-expire through the real library, and
compares canonical post bytes. The other route stays unchanged. Duplicate
admission IDs, a substituted or rerandomized expiry, wrong queue order, omitted
expiry and cross-route material must not be accepted as that transition.

[OPEN / explicit issuer premise] Keyless recomputation establishes arithmetic
on admitted ciphertexts. It does not establish that their plaintext vectors
have 577 bounded signed coordinates, implement the claimed feature/label
policy, have honest noise, or use the claimed public key. A signature can
authenticate a trusted issuer's attestation of these facts; it does not prove
them against a malicious signer. The integration must identify this trust
premise or implement the relevant proof. It must not infer honest input
semantics from a syntactically valid ciphertext or a public key ID.

[DERIVED acceptance contract] A fresh Infer selects the actual committed route
accumulator, an independently authorized canonical query, and its intended
recipient. The authority recomputes the two positive/negative plaintext
products and subtraction. Coefficient 576, signed centering, the score/sign
output format and empty-state behavior are fixed by the selected program.
Every one of these choices, the request digest, prior revision/state digest,
next state digest and exact output ciphertext hash enters the finalized
envelope. The reader validates its authority authentication and all selected
fields before decrypting; it accepts only Infer envelopes, not Learn payloads,
state ciphertexts or arbitrary caller-supplied ciphertext/hash pairs.

[DERIVED disclosure scope] Arithmetic query validity and release authorization
are different checks. Allowing every bounded 577-coordinate query allows basis
queries whose exact scores disclose individual current-state coordinates.
The frozen study exercised particular selected queries; it did not certify a
general readout interface as private. The new integration must state whether
it authorizes those public queries, a broader fixed family, exact scores or
only signs, and what quota/history policy applies. A confidentiality claim
cannot silently use the narrow test set while exposing the broader API.
This is an interface-scope observation; this review does not resume the earlier
separate ideal-window disclosure task.

[DERIVED acceptance contract] The generic authority revision advances on both
Learn and Infer, while route admission counts advance only on Learn. A fresh
request names the actual current revision and state digest. A host-restored
manifest never replaces authority state. The database transaction atomically
installs the selected state/delta, consumes identities, records exact request
and result bytes and creates the outbox entry. Blob contents must be complete
and durable before references commit; orphan unreferenced blobs are acceptable,
committed references to missing content are not. Every trusted blob load
checks its full content/hash and uses the checked bytes for the operation.
Client paths must not choose files from authority or reader storage.

[DERIVED acceptance contract] An exact same-ID retry returns the stored
envelope and result bytes, including after unrelated later revisions. A
changed same-ID body is a conflict. Fresh same-parent competitors cannot both
commit, and host restoration does not restore the authority or reader inbox.
Publication follows commit and uses the journaled result, with authenticated
delivery and persistent recipient deduplication. Retried transport may repeat;
the claim is one logical retained release identity, not one physical delivery.
Reader/authority rollback and compromise remain separate continuity assumptions.

## Required adversarial controls once the implementation is ready

[DERIVED planned checks] The positive must accept freshly generated valid
observations and several valid operations through actual recomputation, not
only hardcoded fixture candidate bodies. Its integer oracle should remain
outside the keyless authority. The minimum negative controls are:

- Change one ciphertext coefficient or output byte while retaining the claimed
  result; change a canonical output and recompute its public hash to ensure the
  arithmetic comparison, rather than hash syntax alone, rejects it.
- Change each context field individually: genesis, key/params, program/version,
  parent revision/digest, route, query, recipient, operation, admission nonce,
  output index/format and result hash.
- Substitute another valid ciphertext from the same key, a ciphertext from a
  different key with identical parameters, and a wrong or reencryped old queue
  entry. Classify whether arithmetic, authentication or trusted-issuer policy
  supplies each refusal; do not pretend every refusal proves plaintext validity.
- Send a Learn envelope to the reader, a forged authority envelope, a genuine
  finalized envelope with another output blob, and a packet sent before commit.
- Exercise exact retry, changed-body retry, old committed retry after later
  revision, same-parent competition, host restore and crash boundaries around
  blob persistence, state commit and reader publication.
- Test strict parsing and canonicalization: duplicate/unknown JSON fields,
  Boolean/float values in integer fields, incorrect vector/component counts,
  parameter/level aliases, truncated bytes and public empty-zero normalization.
- Retain an explicitly marked authority-rollback/fork control. A trusted reader
  with the full key can always inspect state outside its service API; excluding
  that action is a trust assumption, not a cryptographic refusal result.

[DERIVED feasibility assessment] The baseline already executes the required
low-depth BFV additions and plaintext products at these parameters. Reusing
them for public recomputation plus the existing journal makes this bounded
integration plausible. Actual serialization, content-addressed retention,
signature checks, subprocess/RPC overhead and recovery must be measured in
the integrated run. Neither the current queue's 66-ciphertext payload nor its
microsecond arithmetic timings include an indefinitely retained durable
journal, all historical blobs, reader keys or role isolation. No practical
obfuscation, masterless release primitive or PQ composition follows from this
engineering feasibility judgment.
