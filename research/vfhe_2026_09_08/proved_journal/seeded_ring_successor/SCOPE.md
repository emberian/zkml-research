# Scope of the shared seeded service

[SOURCE] The selected backend is
`research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_seed_semantic_successor/`.
Its `RINGSSM2` format version 3 requires
`honest-dual-seed-384-qrom-v1` and `seed_bits=384` in every header. The existing
sixteen-query general-B registry is fixed before the A seed. Canonical ordered
registered products are committed before an independent missing-row seed.
The full finalized descriptor is bound into this service's genesis and each
update/delivery request. Registered keys bind A, registry and policy; ciphertexts
also bind the finalized public issuer file.

[SOURCE] A and the missing public rows are seed-described and reconstructed as
needed; they are not stored or sampled as independent ideal-uniform tables in
this concrete run. The explicit public payload contains the sixteen registered
product rows. No missing-row private keys or universal reader are generated.
The arithmetic parameters and Gaussian sampler are inherited unchanged from
the semantic backend. The seed policy has a conditional QROM interpretation;
SHAKE supplies its concrete heuristic. This run is not a proof that SHAKE is a
random oracle, that its expansion is literally ideal-uniform, or that the
chosen Ring-LWE parameters have a measured security level.

[SOURCE] Full deterministic recomputation checks the complete canonical
`acc + fresh - old` candidate: every ring coefficient, scalar mask, context and
lineage byte. Candidate and verifier use the same frozen arithmetic
implementation. No succinct proof, compiler proof or proof over another
modulus is used. Fresh encryption is supplied by an honest issuer; this gate
does not prove that arbitrary input ciphertexts encode their named vectors.
Input identity, fixed registry, current parent, class/FIFO and resulting model
root are application bindings.

[SOURCE] Each exposed key remains usable on retained inputs and allowed
combinations outside the service. A coalition obtains its per-input registered
query span. Expiry, accepted-state visibility and delivery IDs are local
continuity/integrity rules, not cryptographic history-bound release. The journal,
delivery ledger, honest registry/setup/issuer/sampling, canonical parser and
arithmetic, decoder, filesystem and shared OS remain trusted boundaries. The
normal path is serialized; no distributed authentication, concurrent-load,
power-loss or malicious-administrator result is claimed.

[SOURCE] The fixture comprises already-public cached linear semantic vectors
and expected scores. No encoder/model forward or accuracy benchmark is part of
this run. Scalar agreement checks correct arithmetic/transport/continuity for
that known fixture; it does not establish hidden-text confidentiality or
natural-language ambiguity. Recipient workers read only their own key paths
under the generated sandbox profiles. Private key payloads and large
ciphertexts remain in ignored runtime storage; the seeds, compact public
issuer bundle and public receipts are retained separately.
