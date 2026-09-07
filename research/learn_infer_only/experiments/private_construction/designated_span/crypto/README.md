# Designated fixed-span DDH backend

[DERIVED specification] This implements the algebra reviewed in
[`../review/REVIEW.md`](../review/REVIEW.md), SHA256
`a5e199591179cf81a4eb9b3754108eb68a7b1b3d8ba921c4d8b84fb42278d840`.
It is a separate research backend. The completed positive execution and source
pins are recorded in [`reports/RESULTS.md`](reports/RESULTS.md): 33 fresh Learn
transitions, four exact private integer comparisons and one real window expiry,
plus the separately preserved first uncached path.

[SOURCE] The group constants are copied from the local `additive_ipfe.py`
(RFC3526 section 3, 2048-bit group 14 prime-order subgroup); the native exponent
helper is copied from `fixed_span/scaling/native_pow.py`. Only `group.py`,
`native_pow.py`, `rows.json`, and `crypto.py` are runtime source dependencies.
The helper calls the local OpenSSL `BN_mod_exp_mont_consttime` through ctypes.
Python inversions, big integers, lookups, allocation, BSGS and the whole protocol
are not claimed constant time. There is no post-quantum or calibrated numerical
security-strength claim.

## Commands and setup roles

```sh
./crypto.py params
./crypto.py keygen --pk PUBLIC.json --sk PRIVATE_RECIPIENT_DIR --zero ZERO.ct
./crypto.py validate-context --context PUBLIC.json
./crypto.py encode-query --context PUBLIC.json --vector FIXED_ROW.json --out QUERY.json
./crypto.py issuer-encrypt --context PUBLIC.json --pk PUBLIC.json --vector PRIVATE.json --out FRESH.ct
./crypto.py inspect --context PUBLIC.json --ct STATE_OR_OUTPUT.ct
./crypto.py host-learn --context PUBLIC.json --acc PRE.ct --fresh FRESH.ct --out POST.ct
./crypto.py host-learn --context PUBLIC.json --acc PRE.ct --fresh FRESH.ct --old EXACT_OLD.ct --out POST.ct
./crypto.py host-infer --context PUBLIC.json --acc STATE.ct --query QUERY.json --out OUTPUT.ct
./crypto.py inspect-recipient --context PUBLIC.json --sk PRIVATE_RECIPIENT_DIR/r00.key
./crypto.py reader-decrypt --context PUBLIC.json --sk PRIVATE_RECIPIENT_DIR/r00.key --ct OUTPUT.ct
```

[DERIVED implementation contract] Unflagged commands check the complete
public context, every public component's subgroup membership, and all 16 token
consistency equations. `validate-context` always performs that full check and
returns the exact context digest and all four validator source hashes. An
integration may then add `--validated-context-sha256 HASH` to operational
commands. This explicitly reuses that validation: every invocation still
reads and hashes the complete file, requires the configured digest, strictly
parses canonical JSON, and checks all field schemas, scalar/group ranges and
identities. It skips only the previously completed public subgroup and token
equations. Ciphertext subgroup checks always run. The integration must bind
the successful validation result, context digest and validator source hashes
to trusted setup and genesis. Supplying an unvalidated digest is outside this
cache trust chain; caching does not prove honest key generation or erasure.

[DERIVED implementation contract] Output metadata includes native
exponentiations, subgroup checks, public consistency rows, full context
validations and pinned validation reuses actually executed. `process_work_ns`
includes context loading, validation, arithmetic, serialization and output file
work, excluding Python startup and stdout encoding. Caller subprocess wall time
is the cost of the complete invocation.

[DERIVED implementation contract] `keygen` orchestrates separate processes.
The `initializer` child samples all 577 master coordinates with
`secrets.randbelow` (OS-backed `SystemRandom`), publishes `h`, privately writes
16 projection deliveries, and exits without serializing the master. Each
`recipient-register` child independently samples its dedicated `a_i`, publishes
`A_i,tau_i`, and saves only `a_i`. The orchestrator assembles the public context;
each `recipient-finalize` child wraps its own scalar with the full context
identity. The private delivery and pending files are removed. Final private
files are `r00.key` through `r15.key`, mode 0600 in a mode 0700 directory. No
private scalar or private-key hash is returned by setup or inspection.

[OPEN setup assumption] Private authenticated delivery, honest initialization,
absence of copied master/delivery values, and physical erasure are assumptions.
Process exit and unlink do not demonstrate forgetting. The processes run under
one account; this is not operator-resistant OS isolation. A service holding all
16 final row keys represents the full fixed-span recipient coalition.

## Exact public and byte identities

[DERIVED] The public context is canonical JSON with exact keys `schema`,
`params_id`, `setup_id`, `rows`, `h`, `recipients`. It includes all 16 original
577-dimensional public rows. Its SHA256 is both `context_id` and `key_id`.
`setup_id` hashes the canonical bootstrap containing the rows and `h`.
Each recipient record has exact fields `row_id`, `row_sha256`, `recipient_id`,
`A`, `tau`, `token_sha256`. Each `recipient_id` is distinct for its dedicated
row key and binds setup, row identity and `A`. `token_sha256` binds that record
without the digest field. The check is `g^tau * A = product(h_j^y_j)`.

[DERIVED] Queries are canonical JSON with exact fields `schema`
(`resident-designated-query-v1`), `params_id`, `context_id`, `row_id`,
`row_sha256`, `recipient_id`, `token_sha256`, `coefficients`. Only byte-canonical
encodings of one of the 16 fixed registered rows are accepted. An issuer vector
is a JSON array of exactly 577 integer values in [-127,127]. It remains an
issuer input. Public validation of its encrypted counterpart does not prove
the source or plaintext range; the journal's trusted issuer attestation is a
separate assumption.

[DERIVED byte format] All binary envelopes use a 179-byte big-endian header:
8-byte `RSDDH001`, 1-byte kind, 32-byte params digest, 32-byte context digest,
2-byte row index, 32-byte row digest, 32-byte recipient digest, 32-byte token
digest, and 8-byte payload length. Every integer payload has exact 256-byte
big-endian width. Kinds are state=1 (578 group elements, total 148147 bytes),
recipient output=2 (two group elements, total 691 bytes), and recipient secret=3
(one scalar, total 435 bytes). State headers use row 65535 and three zero digests.
Public group elements must be in [1,p-1] and satisfy `z^q=1`; secret scalars are
in [0,q-1] and checked against the registered `A`. Canonical bytes are checked
by exact re-encoding. Identity elements are valid, including initial zero state.

[DERIVED] `host-learn` enforces state types and computes componentwise
insertion/division. The caller enforces route, sequence, queue size and that
`--old` is the exact originally admitted ciphertext. `host-infer` accepts a
state and fixed query and emits only its designated output type. The recipient
decoder accepts only its own output row and bound; it never accepts a state.
The bound is `32*127*sum(abs(row))`, at most 14219936 for the frozen rows.
`q > 2*bound` makes this honest signed interval unambiguous. Bounded BSGS returns
`signed_score`, `sign`, `ciphertext_sha256`, `key_id`, row and recipient identity.
Here `sign` is mathematical signum (-1, 0, 1); a classifier using the original
utility study's positive tie convention must compute `score >= 0` explicitly.
This response and its value-dependent decoder timings are private outputs and
must not be copied into public host/authority logs.

## Scope

[DERIVED reviewed conditional privacy] The host has public encryption and
transformation data, with no projection or master scalar. A fixed recipient
coalition has exactly the corresponding fixed-span projection capability for
each individual issued input, including expired ciphertexts. A recipient can
recover its projection key from its own `a_i` and public `tau_i`; keys in its
coalition span are correlated. These are dedicated keys, never general-purpose
ElGamal keys reused elsewhere. The reviewed DDH argument is a mathematical
conditional, not a proof of implementation security or source refinement.

[OPEN] This CLI does not itself bind genesis, parent, source authenticity,
recipient authorization, finality or one continuing history. The sibling
integration supplies public recomputation and signed context handling. A
recipient possessing its scalar can use it outside that local software gate;
neither the decoder interval nor expiry enforces sign-only release, quotas,
revocation or deletion. Host-only privacy excludes recipient feedback. The
fixed-row learner's kernel cannot affect its authorized outputs; ambient
kernel dimension does not establish ambiguity on the actual encoder image,
nonlinear learning, useful private cognition, or a general autonomous resident.
