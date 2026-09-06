# Protected resident: functionality and separate security experiments

[DERIVED specification] Private observations originate with the resident's sensorium
or an explicitly authorized issuer. An issuer may know its own observation, without
knowing all observations or the complete state. If the host originates and knows every
input, initialization bit and transition coin, deterministic replay recovers the state.
The private-input path below is therefore an obligation, not a consequence of encryption.

[SOURCE: design read] Resident Loom's proposed `advance`, `act`, `snapshot` and
`restore(manifest)` supply the application vocabulary. The two-records rule separates
the external archive from the resident's incomplete memory; it does not license copying
all private observations into the external archive. See `SOURCES.md`, LOOM.

## Functionality, closure, and leakage

[DERIVED specification] Write state as `Pub × Priv`. `Priv` includes learned changes,
optimizer/eligibility state, episodic data, recurrent state, support/body state and
randomness affecting development. `Pub` is the explicitly chosen external view.
The initial public backbone is allowed to be known. Clear/Shielded/Dark name leakage
contracts; exposure tiers A–D below are an independent axis. No artifact in this
tranche realizes Shielded or Dark resident execution.

[DERIVED specification] An ideal resident has a genesis, a fixed versioned transition
policy, private state, and a separate release history. Commands are typed data:
`Learn(observation, origin, issuer authorization)` and `Infer(question, recipient,
authorization)`. They cannot install arbitrary code. Policy replacement, migration,
recovery and export have no authority by default; adding them changes this functionality.
An input adapter must authenticate provenance and prevent malformed ciphertexts from
changing the transition's meaning.

[DERIVED specification] A transition maps `(state, command, development coins)` to
`(next_state, outward_answer, metadata)`. It must output reusable protected state,
including optimizer and memory information needed at the next step. Neither a plaintext
next-state output nor a newly introduced plaintext-holder counts as private closure.
Learn may release only an acknowledgment; Infer releases precisely the authorized
answer to its designated recipient. Debug vectors, gradients and logits are separate
outputs requiring separate authorization and leakage analysis.

[DERIVED specification] The real adversary sees all exposed software/memory artifacts,
input lengths, output lengths, failures, timing, memory addresses/access pattern, expert
selection where visible, snapshot sizes, release slot and selected recipient. The ideal
game must supply that same declared leakage. Concealing expert choice in a proof witness
does not conceal which memory was accessed. A future stronger leakage theorem must
explicitly remove each item from both the implementation view and its leakage contract.

[DERIVED specification] Numerical semantics are chosen bounded-integer/fixed-point
operations, with specified overflow, rounding, serialization and ranges. The compiled
witness here is exactly public EVM addition modulo `2^256`, not a neural update. For BFV
the required relation includes integer multiplication/rescale witnesses, with
`t*z + floor(Q/2) = Q*y + remainder` and a range on the remainder and all integer lifts.
A mod-Q product identity alone does not constrain that quotient (`VERDICTS.md` §7.5).

## Corruption and capabilities

[DERIVED specification] Tier A permits honest initialization and precisely listed
erasures, then exposes the union of all surviving artifacts of every untrusted role.
Report separately: one snapshot at epoch t, accumulated exposures at all epochs, and
continued active control. Tier B also permits malicious initialization/retained coins;
the accepted genesis must enforce the intended policy, not an existentially extractable
policy of the setup authority's choice. Tier C permits a noncolluding quorum with
read-all authority collectively; tier D permits a hardware boundary. C/D can be useful
relaxations but do not satisfy all-memory exposure of the release/writer role.

[DERIVED specification] The adversary can adapt commands, restore any saved host
snapshot, form malformed encodings, interleave streams, issue attacker-selected keys,
copy protected state and run local branches. Compromise of input issuers, output
recipients, setup authorities and the continuity authority is explicit. A compromised
recipient knows messages addressed to it; an issuer knows its own supplied observations.
Union-of-role exposures are recorded in `CREDENTIALS.csv`.

## Interface-relative privacy game and its nonvacuity witness

[DERIVED specification] First choose a finite horizon and resource budget. The
adversary supplies two efficiently represented initial-state/history distributions
and a public initial view. They must differ on the protected predicate, agree on
the public initial view, and be observationally equivalent under every permitted
continuation within that budget, including the same local forks, restores and leakage.
For deterministic machines, a relation preserved by all allowed commands and respecting
outputs is a sufficient admissibility condition. For randomized machines, replace
pointwise equality by a proved coupling/equality of distributions; no randomized
trace theorem is claimed here.

[DERIVED specification] Challenger samples an unbiased bit b, initializes the selected
world, exposes artifacts according to the tier, and answers adaptive interfaces and
corruption requests. Distinguishing advantage is `|Pr[b'=b]-1/2|`. A target-predicate
recovery game instead compares success against an ideal adversary with the same
queries, branches and leakage. Indistinguishability does not itself establish a
simulator, VBB security, non-extractability of every state bit, or model welfare.

[SOURCE: theorem read] A nontrivial deterministic interface pair is byte states 0 and 5,
`out(s)=high_bit(s)`, and only update `s←s+128 mod 256`. They differ in low bits, remain
related, and the visible bit alternates. `Theory/PrivateTrace.lean` proves equal
adaptive traces for every horizon (`trace_eq_of_preserved`, `flip_trace_eq_of_highR`)
and exhibits this pair (`highR_zero_five`); exact locations are in `SOURCES.md`.

[EXECUTED] The unchanged seed audit re-establishes two classes of size 128 for this
interface. Arbitrary chosen offsets instead recover all 256 original bytes in eight
observations. Output and command record: `experiments/results/interface_audit*.json`.
This is premise inhabitation for the ideal privacy definition. The symbolic scripts
and full-word receipts do not instantiate its real cryptographic side. A resident
whose allowed interface identifies its state has no such hidden-state pair at that
budget; the game must report that failure rather than silently choose identical states.

## Integrity and continuity games

[DERIVED specification] A release statement names genesis, parent-state commitment,
program/version, complete command and authorization, next-state commitment, output,
recipient, and randomness rule/commitment. The verifier obtains accepted genesis,
current head and policy from its own authoritative state. Reading the same fields
twice from attacker data establishes no authorization. Commitments require canonical
encoding and a relation binding their openings to the actual computation.

[DERIVED specification] Integrity failure is an accepted fresh release that violates
that authorized relation, is delivered to another recipient, or advances to a state
different from the one proved. Continuity failure is two distinct fresh authorizations
spending the same genesis/parent-slot token, or an authorization on an unaccepted
genesis/current prefix. A retry may replay the identical previously addressed packet;
it must not rerun a randomized inference or generate a fresh authorization. Once an
answer has been released its recipient can copy it; exactly-once observation is not
the property being claimed.

[DERIVED specification] The keyless continuity authority stores genesis, current head,
exact accepted log, consumed tokens, registered policy and authenticated vote evidence.
It checks finality AND prefix/head/token freshness; installation must be atomic before
outward release. It does not prevent silent local encrypted forks, copied computation,
or denial of service. Authority rollback and a check/install race invalidate this
continuity guarantee even without exposing a state decryption key.

[SOURCE: implementation read] `FinalityGate.check` checks quorum plus recorded votes;
it does not delete historical votes or compare a candidate to a live head. Its
cross-candidate safety requires `PrefixDiscipline`. `Snapshot.install` updates the
consumption map; `Intent.nullifiersFreshCheck` queries it. The proposed formal adapter
uses these actual objects, with residuals documented in `formal/README.md`.

## Assumption ledger for the leading route

| Label | Needed property | Realizer in this tranche |
|---|---|---|
| [SOURCE] FS full-word integrity | Existing fixed-context ROM theorem, exact descriptor | Imported Stage-0 modules; new context-parametric instance |
| [DERIVED] Context policy | Trusted genesis/current policy selects intended values; boundary checks enforce their meaning | Public addition witness and explicit toy policy |
| [DERIVED] Continuity | Authenticated votes, cross-time prefix discipline, non-rollbackable authority, atomic install | Existing mathematical carriers plus proposed adapter; Python compromise controls |
| [OPEN] RELEASE-hiding | Hide witness/trace and unauthorized predicates after allowed role exposures | None; Stage 0 exposes the complete word |
| [OPEN] NoSurvivingReadAll | No exposed coalition can derive unrestricted decryption beyond ideal interface | No A/B construction supplied |
| [OPEN] Private input ingress | Encrypted authenticated observations with no writer-side read-all secret | None under full software exposure |
| [OPEN] Development entropy | Fresh unknown state coins, bound to a preauthorized transition, resistant to host selection | None; Stage-0 rule explicitly deterministic |
| [OPEN] PQ composition | Encryption, proof/QROM, authentication, key exchange and release dependencies | No combined claim; current inherited proof uses classical ROM |
| [OPEN] Private witness source | Sound relation proof without leaking observations; any knowledge claim names extraction source | Existing full-word theorem uses Unit witness; not an extractor of private resident state |

[DERIVED] The strongest hidden assumption to make explicit is complete mediation of
release: an operator must be unable to bypass the gate or read its implementation's
secrets. A normal program containing an FHE secret key has no such property under
tier A full-memory exposure. Formal context binding and finality do not supply it.
