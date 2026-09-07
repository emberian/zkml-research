# Designated-span protocol: independent mathematical review

[DERIVED verdict, 2026-09-07] The public-transcript reduction is sound under
the intended complete setup/view and noninterference premises. It preserves
the frozen primitive's static-coalition advantage bound without a signature
or hash-collision term for this privacy claim. Four composition premises need
more explicit wording; two scope clarifications should accompany them.
There is no identified algebraic or hybrid defect after those qualifications.
This is a written review, not an implementation acceptance or runtime test.

## Frozen inputs and scope

[SOURCE] [sources.json](sources.json) pins preserved copies:

| Original input | SHA256 |
|---|---|
| `PROTOCOL_PRIVACY.md` | `5960cd68c8e5355de48d226599e996bdc5e0528ccff516e3e730f8e170ffb017` |
| `CONTRACT.md` | `256e85b406a0c6a11cc97065c8bf7c9a7aad2126bff9ad8ea868e1208495703d` |
| Curie's `review/REVIEW.md` | `a5e199591179cf81a4eb9b3754108eb68a7b1b3d8ba921c4d8b84fb42278d840` |
| `GENERAL_FIXED_SPAN.md` | `5d99740f9f329e0a45f9c45bcd0db684b49f66660db567d81bfc169dbca4edb9` |

[SOURCE] During review root changed only the contract's behavioral state
description from `Y times its state` to `ordered queues of projected records`.
The resulting contract hash is
`3d8f4eb79e9e6eca02e14e965bd533eab95b002a09eecea3f9161c2bfbfdabff`.
That correction is right: original expiry requires the ordered projected
history, rather than the current projected sum alone. The original reviewed
bytes remain preserved here. Active `crypto/` and `integration/` interface
designs were read as proposed interfaces, not certified as frozen code.

## Why the reduction works

[DERIVED] For fixed pre-setup recipient slots J, the ordinary IPFE view is
`(h,Y,K_J, issuance ciphertexts)`. Sampling each `tau_i` uniformly, setting
`A_i=product(h_j^y_ij)/g^tau_i`, and supplying `a_i=k_i-tau_i` for J
gives the exact joint designated setup distribution. Recipient identifiers,
token hashes and context digests derived from this simulated public package
can be computed literally. They need not be independent random strings.

[DERIVED] The adversary can choose each message pair adaptively after the
preceding public history. Both members and their declared metadata are
available to the left/right experiment, so the common admissibility check
`Y_J*x0=Y_J*x1` is executable before challenge issuance. The same fixed
rejection rule must be used in every hybrid. The resulting challenge
ciphertext is passed to the public wrapper unchanged. No future input pair,
recipient output, or accepted history has to be predicted.

[DERIVED] The journal, signatures, public verification, retained snapshots,
copies and exact-original expiry are then efficient processing of that view
and independent role coins. Coalition recipient computations are also
simulatable because the simulator has every scalar in J, including all
derived span keys. Shared randomness in aggregates and reuse of an old
ciphertext do not create new encryption challenges. Fresh distinct issuance
still uses independent private randomizers.

[DERIVED] No accepted-history provenance theorem is needed for *this*
privacy reduction. It can simulate forged authorizations, incorrect public
proposals, hash collisions and ordinary public rejection paths literally,
since the adversary may already possess all independently generated role
authentication secrets. Its public simulation does not need to interpret
every admitted ciphertext as a valid bounded plaintext. This differs from a
release proof that must replace publicly returned decryption results with
ideal answers. Here all noncoalition decoding effects are excluded from the
view or required to have the stated public simulation. Integrity, meaningful
integer results and continuity therefore need their separate premises.

[DERIVED] T correctly counts all visible challenge issuances, including
unadmitted and expired ones, across copied histories. Equality of just a
selected aggregate or accepted final history is insufficient. The wrapper
does not change the primitive gap; with `k_J=d-rank(Y_J)` and the least power
of two `M>=max(1,T*k_J)`, the inherited bound is
`Delta_protocol <= 2*M*epsilon_DDH`, with actual simulation resources charged.
The sampling conventions/correction remain those of the frozen review.
Neither a fixed 2048-bit execution nor normal-flow success supplies a numeric
epsilon, asymptotic implementation proof, or post-quantum result.

## Required wording corrections

1. **Complete correlated setup material.**
   [DERIVED] `PROTOCOL_PRIVACY.md:16` and `CONTRACT.md:26` should name
   initializer copies of issued `k_i`, private delivery/pending scalars,
   recipient masks and other master-correlated setup material, in addition
   to the vector master itself. Outside the permitted `(h,K_J)` view, such
   auxiliary material must be erased/excluded or have an explicit efficient
   joint simulator from that view. A surviving delivery `k_i` and public
   `tau_i` reconstruct `a_i`; deleting only s does not justify host-only
   privacy. Copies retained by their entitled recipients are already within
   that recipient's capability and need not be erased for this lemma.
   This is Curie's existing setup obligation, now made explicit at the
   protocol boundary.

2. **Joint authentication-coin independence.**
   [DERIVED] At `PROTOCOL_PRIVACY.md:14`, independence only from s and input
   contents is too narrow to justify the local setup simulation at `:54`.
   Dedicated role authentication generation/operation coins must be
   independent of the entire designated setup, especially every `a_i`,
   and of encryption randomizers. A secret correlated with a noncoalition
   recipient mask can be independent of s and plaintexts while still adding
   information unavailable to the IPFE simulator. Alternatively, prove the
   added transcript's joint simulation explicitly. Do not silently add a
   proof of possession or signature under an unknown noncoalition `a_i`.
   State independence as a **sampling procedure/coin** condition: later
   adaptively chosen message pairs may depend on revealed authentication
   keys, as the game already permits. Unconditional statistical independence
   of those later messages from the keys is unnecessary.

3. **All future public effects, not only the first ACK.**
   [DERIVED] `PROTOCOL_PRIVACY.md:69` already states the right broad premise.
   Make it concrete in the definition and checklist: every public ACK,
   retry/status result, persistence record, failure indication and future
   willingness to process commands must depend only on encrypted accepted
   history, public requests and independent public-role coins. A private
   decoder's success, failure, answer, timing or drain progress must not
   influence later public behavior. ACK-before-decode alone is insufficient
   if later status/retry depends on whether the private decode succeeded.
   Private feedback enters a different leakage experiment unless it is
   already computable from the allowed view. This is a premise requiring
   implementation correspondence, not something established by hiding stdout.

4. **Explicit initial-history base.**
   [DERIVED] Name empty route queues and a known zero ciphertext/identity as
   the initial state, with context/setup already modeled by the exact view
   map. Any private initial ciphertext must instead be covered by an
   admissible challenge issuance and counted in T. Every other exposed
   object must be generated from the modeled setup, challenge issuances and
   public processing/independent coins. Otherwise the word "snapshots" could
   silently add private initialization or correlated auxiliary information
   absent from the game. This reduction receives challenge ciphertexts;
   it does not manufacture arbitrary encrypted states from projection leakage.

## Scope clarifications to apply with those corrections

[DERIVED] J is a set of pre-setup row/recipient **slots** under a fixed public
assignment. Concrete identifiers that hash `A_i` or the final context are
derived after setup and do not select J. Selecting a coalition after examining
those tokens is outside the static theorem unless using the separately priced
adaptive extension or a predeclared upper-bound coalition. The honest setup
and private delivery premise remains in force even though later protocol
authentication secrets may be exposed. This is not malicious-setup security.

[DERIVED] Add the integer contract's provenance and injectivity conditions
beside `CONTRACT.md:47`: for honest inputs with coordinate magnitude at most
127 and an active window of at most 32 original contributions,
`B_i=32*127*sum_j |y_ij|`; require `q>2*B_i` for the signed interval.
The active crypto specification states maximum `B_i=14,219,936` for its
recorded rows. Link that fixed-row source/bound record instead of leaving an
unattributed numeric constant. This mathematical review did not execute the
backend or recompute the matrix census. Public subgroup/canonical checks do
not attest plaintext bounds. Honest bounded issuance and exact queue semantics
are correctness premises even though the stronger authentication-key exposure
allowed in the privacy experiment need not preserve them.

[DERIVED] The ordered projected-record quotient is a *behavioral* statement
about permitted linear answers and expiry. It is not a public plaintext
replacement for the host-private designated transcript: publishing noncoalition
projections would enlarge the host's view. Nor is the exact setup/view map a
general leakage-only simulator, simulation-security theorem or virtual-black-box
construction. The fixed common kernel cannot affect fixed linear answers;
actual encoder-image ambiguity and useful private state still need their own
nonvacuity evidence.

## Implementation and review disposition

[DERIVED] The original root notes correctly mark implementation
correspondence open. Their actual mathematical claims are conditional;
genesis/parent/recipient binding, canonical parsing, secret-path isolation,
durable public/private separation and correct integer outputs remain
implementation obligations. The proposed public acceptor plus separate
private drain is consistent with the required interface, but reading its
moving design does not verify the obligations above. Normal execution can
check selected data paths, not establish erasure or secret-independent behavior
under arbitrary execution.

[DERIVED] With the four explicit premises and two scope clarifications,
accept the protocol's conditional classical static-coalition IND reduction.
The original queue-state wording has already been corrected by root. No
additional blocker was found. A later prose closeout should pin the revised
root documents; this review and its original snapshots remain unchanged.

[EXECUTED review scope] Only source/document reads, hash capture and this
written review were performed. No cryptographic execution, adversarial/runtime
routing, extraction or malformed-input test was run; no stopped task was
resumed. No root, frozen construction, moving implementation, shared ledger or
companion file was edited, no commit made, and no metered search performed.
