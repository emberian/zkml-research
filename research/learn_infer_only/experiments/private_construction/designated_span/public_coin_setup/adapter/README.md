# Public-coin setup adapter

[OPEN] Separate approved positive implementation of `../PROPOSAL.md`, accepted
by the independent written review in `../review/REVIEW.md`. Exact inputs and
unchanged four-file operational backend are pinned in `SOURCE_PINS.json`.
Only this directory is owned by this lane; previous evidence remains immutable.

[DERIVED: intended setup] Independently authenticated fixed recipient slots
publish honest independent `A_i=g^a_i` before public coins are drawn. The public
constructor samples tau directly in F_q and U directly as nonzero field elements
in F_p, then computes free group elements by squaring U and completes the pivot
coordinates by public group arithmetic. The full-rank original16x577 rows and
first16 pivots are fixed before sampling. No scalar master or scalar projection
key delivery belongs to this setup path. Recipients finalize only their own a_i
against the same frozen context schema. Legacy dealer commands remain present
in the frozen backend but are never invoked by this adapter.

[DERIVED: limits] The accepted tau/U values are the public randomness transcript.
OS RNG seeds/state and private encryption coins are excluded. Honest direct
field sampling and independent recipients are premises; public consistency does
not certify absence of additional logarithm knowledge. This is a classical DDH
construction, with the full fixed span available to its recipient coalition.
The known positive fixture and shared-account role separation establish no
operator confidentiality or OS boundary. Registration signatures use independent
Ed25519 keys, never a recipient a_i, and add a separate classical authenticity
boundary. No new malicious-setup, routing, extraction or malformed-input test
is authorized or included.
