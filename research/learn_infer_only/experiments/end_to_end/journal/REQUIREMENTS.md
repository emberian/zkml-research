# Keyless verification/journal integration

[OPEN, 2026-09-07] Own journal/CAS/snapshot/receipt/reader-gate wrappers; raw BFV primitives belong to `../crypto`. Follow `../CONTRACT.md`. No BFV secret or plaintext observation enters the authority or host command path. A separately trusted full-key reader is benchmark R, not distributed tier C or NoMasterRead.

[DERIVED design] Ed25519 authenticates issuer observations and authority finalization, with separate OS-random signing keys and serialized public-key identities. This is classical authentication, not a PQ claim. Fresh ciphertext key/range/feature provenance remains a trusted issuer assertion unless a separate proof is actually implemented. Query syntax/range is not query authorization.

[DERIVED design] Immutable ciphertext blobs are addressed by SHA256 of all canonical envelope bytes, which include fixed parameter and key identities. The authority loads by digest inside its own CAS, verifies bytes/hash and strict crypto inspection every trusted load, recomputes actual Learn or Infer ciphertext arithmetic, and compares exact candidate result bytes. Blobs are fully written/fsynced before committing a journal delta. No caller filesystem path is trusted.

[DERIVED design] The accepted context binds genesis, parent global revision/state digest, full parameter/program/version policy, Learn/Infer, route, input or query, issuer/requester identity, recipient, nonce, resulting state and output ciphertext. Global revision advances on every Learn and Infer; per-route admission counts advance only on Learn. The state digest is computed from canonical route→queue/accumulator references, not a renamed arithmetic scalar.

[DERIVED design] SQLite transaction serializes journal lookup, exact replay identity, currentness, public recomputation and delta/outbox insertion. Historical exact retry returns the stored finalized envelope even after later revisions. State reconstruction applies journal deltas and loads verified immutable ciphertext blobs; retained log/blob cost is recorded separately from bounded current route windows.

[DERIVED design] The reader verifies authority signature over the complete finalized context, accepts only Infer, checks independent expected recipient/query/nonce, verifies output bytes/key/params, and deduplicates nonce/output before decrypting. Learn finalization must never grant an arbitrary-state decryption endpoint. The full reader key still permits unrestricted decryption if the trusted reader is compromised.

[OPEN] Required execution controls: actual changing ciphertexts and mixed Learn/Infer with expiry; exact retry; altered fresh/old/result ciphertext, params/program/genesis/parent, route/query/recipient and unauthorized source; crash before/after commit, concurrent competing candidates, host-only restore; authority rollback negative control. Test hooks remain trusted startup configuration, never normal request fields. Scry0/web0 to date.
