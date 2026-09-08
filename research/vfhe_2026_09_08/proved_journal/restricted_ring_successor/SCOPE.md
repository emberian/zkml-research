# Scope of the restricted-ring join

[EXECUTED] The evidence covers one fresh full-profile setup, sixteen honest
registrations, six encrypted observations, a two-class capacity-two journal,
two exact expiries, six whole-candidate recomputations, one changed-candidate
refusal, one stale-parent refusal, a historical retry, a revision-four reopen and
sixteen registered recipients reading the accepted revision-six model.

[SOURCE] The cryptographic backend is the frozen
`research/learn_infer_only/experiments/end_to_end/restricted_query_learner_2026_09_08/`
general-B construction and `RINGSEM1` codec. Its genesis-pinned profile uses
N=16384, d=577, w=64, sixteen registered rows, p=28439893 and
q=4294967767·2^256+1. Directly uniform missing public rows have no generated
missing-row secrets. Key holders receive their registered projection, not a
universal BFV decryption key. This run does not measure the parameter set's
hardness or strengthen its existing assumptions.

[SOURCE] The narrower key scope is per input: each retained issued ciphertext
can be evaluated by every exposed key in its fixed span. Local expiry and
accepted-head checks do not revoke that ability. Colluding recipients obtain
the span of their registered rows. No cryptographic history-bound release,
arbitrary-query privacy, or full resident-system privacy is claimed.

[SOURCE] The complete update is publicly recomputed in the actual ring and
compared canonically byte-for-byte. The candidate and verifier use the same
frozen arithmetic implementation. This is neither a succinct proof nor a
Lean/compiler proof, and no proof over a different modulus is reused. Fresh
encryption is performed by the honest issuer; the public transition verifier
does not prove that arbitrary supplied ciphertexts encode their named inputs.
Input identity, exact bytes, registered context and FIFO are bound by the
service protocol.

[SOURCE] The SQLite journal, parser/codec, Python/FLINT/native sampler,
recipient wrapper, registration and issuer, randomness, file permissions and
shared OS are trusted. The current CLI is serialized and local. The normal run
does not establish concurrency linearizability, malicious-administrator
resistance, atomic power-loss recovery, or a distributed authentication protocol.
The recipient receipt namespace permits one delivery per coordinate. An
additive continuation interface is needed for repeated delivery requests.

[EXECUTED] Utility inputs and expected outputs were already public cached
linear semantic fixtures. No encoder/model was rerun and no private key or
previous setup was reused. Score/decision agreement measures correct transport
and service continuity on that fixture, not new semantic accuracy, natural-
language ambiguity, private teaching, or hidden-output confidentiality. Setup
and ciphertexts are retained locally under ignored runtime storage; public
receipts are retained separately from private key payloads.
