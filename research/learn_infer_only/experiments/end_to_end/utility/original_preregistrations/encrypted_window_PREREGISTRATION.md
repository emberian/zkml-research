# Cached representation histories through actual Q83 BFV

[DERIVED; preregistered 2026-09-06 09:24 UTC, before this tranche's fixture scores or encrypted outcomes]
Use the first two test history seeds, **63000 and 63001**, in the frozen
`representation_histories.json`. The previously selected `model_window_routed`
configuration is `mean_10`, total capacity 64, hence **32 per public skill route**.
Reuse `text_transfer_data.features` on cached `representation_features.npz`,
then the original `clip(rint(features * 127), -127, 127).astype(int8)` recipe.
The issuer provides each original phase's signed label times its feature vector.

Queries are the **two lowest test record IDs in each (skill,a,b) group**, sorted
by ID, at the ends of phases 1, 2 and 3 (64, 128, 192 Learn steps). This selects
16 queries per checkpoint and 96 total across two histories, including the
untrained second skill at the first checkpoint. Selection uses public metadata,
not scores. No other history or query will replace a failing case. Test RNG
seeds are ChaCha20 `[201;32]` and `[202;32]`, assigned in history order; they are
public reproducibility fixtures, not secret production randomness.

Primary acceptance: every decrypted coefficient 576, interpreted as a centered
integer, equals the exact Python integer rolling-window dot product. Also check
byte-exact equality of each encrypted accumulator with the sum of its currently
retained original ciphertext objects and compare all 577 accumulator coefficients
at phase boundaries. The untrained route may be represented by the library's
zero ciphertext; any unsupported empty-state operation will be recorded and
handled by public structural zero, never hidden by dropping its query.

Record issuer encryption, host addition/expiry, query products, readout and test
reader timing separately, plus ciphertext counts, exact serialization sizes and
source/dependency/input hashes. A separate diagnostic may show a deliberately
wrong public query returns a different value; this is not a receipt rejection
or authenticity guarantee. Do not alter the host using decrypted values.

[SCOPE] This is a concrete integration correctness/measurement experiment,
not a new utility estimate, cryptographic security proof or deployed resident.
The issuer and oracle have plaintext. The test reader retains the full key,
uses public deterministic test coins, and decrypts the whole polynomial.
There is no restricted sign release, authentic input enforcement, continuity
gate, no-master-read construction, model training or model execution here.
The existing Q83 parameter provenance is reused without asserting PQ security
bits or importing the independent noise proof as a complete Rust refinement.
