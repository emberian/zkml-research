# Independent mathematical review of verified-reader privacy

[DERIVED verdict, 2026-09-07] The proposed extension to a malicious host and
authority is sound as a conditional transcript argument under a precise issuance
and accepted-history game. I found no step that requires the authority to remain
honest or requires the encryption reduction to decrypt an adversarial ciphertext.
The independently checked provenance and computation are what make that possible.
The original note needs the explicit game conventions below before being treated
as a fully specified proposition. These are required wording/premise corrections,
not a newly demonstrated cryptographic attack or a proof of the current BFV
instance's security.

[SOURCE / scope] This review fixes `verified_reader/PRIVACY_ARGUMENT.md` at
SHA256 `cbda02868ad5381cc1741712707c3ccdc5b6c071433e6e9a1b8e3b7b1460ce99`,
retained here as `PRIVACY_ARGUMENT.reviewed.md`, and `service.py` at
`f0e79c2a33baa32e2867d467735dafd29b26c480deb1f688289e7468bd2de01b`.
`source_manifest.json` records ten read sources and their exact hashes. The
repaired helpers are common `32afcec1`, model `bcbac3ba`, roles `a42bf9dc`, and
reader `d39c3538` (complete hashes in the manifest). This tranche performs source
and mathematical review only: no new runtime, extraction or routing experiment,
no stopped task resumed, no metered searches, and no companion or core edits.

## Required precisions in the original note

### 1. Name the complete trusted boundary and its public simulation

[DERIVED correction] The introduction explicitly trusts the reader and issuer
but should also name honest setup and the independent command authorizer.
Otherwise the later simulator's ability to issue honest query signatures has an
unspecified origin. The adversary receives the authority signing key; it does
not receive the issuer or command signing keys, BFV secret, or direct filesystem
write authority over reader/issuer configuration, code, CAS and retained database
outside the validated service APIs. Normal adversarial `put` requests remain
permitted. Giving an
authority role its signing key is different from giving the shared-machine
operator access to every process. The note already acknowledges the latter
implementation boundary at lines 118–124.

[SOURCE / DERIVED] `journal/roles.py:6` constructs the fixed genesis, independent
role signing keys and an empty-window public zero. `reader.py:11` reads and pins
the full secret before service initialization. Therefore the reduction can run
the public validation/state functions and simulate trusted initialization; it
cannot literally instantiate the whole concrete Reader constructor without a
secret file. The public simulator premise should say this explicitly. The base
plaintext state for this program is the known empty-window zero, not an arbitrary
unknown private initialization component omitted from the challenge streams.

[DERIVED correction] Private-role side-channel exclusion must cover the issuer,
reader and setup, including work timings, resource behavior, secret-dependent
failure paths and any external logs. `common.py:74` records command timings even
when private stdout/stderr are omitted. This is consistent with the note's
conditional omitted/common-law view, but selected runtime logs do not establish
that condition. The full output law and observation interface must be fixed
before asserting indistinguishability.

### 2. Define issuance provenance independently of accepted record uniqueness

[SOURCE] `roles.py:39` encrypts one input and signs the resulting whole action.
It accepts caller-supplied record/request/nonce strings and retains no global
issuance ledger. `service.py:109` prevents nonce reuse in the reader's accepted
history, and `service.py:112` prevents accepted record-ID reuse. Those are not
proofs that every honest issuance call used a globally unique semantic identity.

[DERIVED correction] A sufficient game convention is an honest issuance ledger
mapping each canonical authenticated input message to one known semantic
issuance instance, its input pair, context and exact ciphertext bytes. A unique
authenticated issuance handle is one way to obtain this. If the same signed
message can be issued again, its ledger interpretation must remain consistent.
The simulator's internal call index alone is not a wire-level identity that the
reader authenticates. Nor should the proof equate the semantic instance with
the bare `record_id` string unless honest issuance enforces that convention.
Other carefully defined provenance projections are possible; this is a clean
sufficient formulation, not a claim that all protocols need a new handle field.

[DERIVED correction] Every accepted private ciphertext must have such a known
origin: a challenge issuance instance or a separately simulated known/common
input. Include unaccepted and subsequently discarded issued ciphertexts in the
adversarial view. The reduction may not quietly assign a plaintext to an
otherwise valid signature on a message absent from its honest signing ledger.

[DERIVED correction] The real honest-input oracle is an encryption-and-issuance
procedure, not a general-purpose oracle signing any host-supplied ciphertext.
The query oracle enforces the declared public authorization policy. Ordinary
chosen-message signature security can bound forgeries against these procedures,
but does not turn arbitrary legitimately signed input bytes into known honest
plaintexts. The latter provenance is supplied by the issuance interface.

### 3. State the challenge relation over semantic prefixes in either endpoint

[DERIVED correction] Let a semantic history record accepted issuance instances,
routes and queries in reader order. The projection removes world-specific
ciphertext bytes, their hashes and signed parent digests. Let
`Reach_b(A)` contain the semantic accepted prefixes possible for adversary A in
endpoint world b, under the fixed issuance/query interfaces and retained reader
history. A precise sufficient condition is:

```
for every h in Reach_0(A) union Reach_1(A),
every Infer prefix of h has the same prescribed output
when evaluated on the left and right input streams.
```

[DERIVED] The comparison evaluates the *same* semantic prefix in both streams,
even when that prefix is reached in only one of the actual endpoint executions.
It does not compare just the two realized schedules, require their ciphertext
hashes to match, or assume adversarial scheduling is independent of ciphertexts.
Histories must include every admissible reordered/subset admission sequence the
adversary can actually authorize and install, not just prefixes of the original
chronological input list. Reader rejection/admission policies remain part of the
public machine; changing ciphertexts can change its realized path, and the same
machine is simulated in each hybrid.

[DERIVED correction] The left plaintext semantics must be efficient and total
on every semantic history reached by the stopped hybrid simulator. Compatibility
is needed for endpoint histories; a mixed hybrid's actual decrypted output need
not equal its simulated output. This distinction permits the usual hybrid
argument without requiring a decryption oracle. For a theorem uniform over
adversaries, quantify over all PPT adversaries satisfying the declared challenge
relation, or use a common admissible history language containing both reachable
sets. Do not hide a world-specific or efficiently uncheckable promise inside
the simulator's algorithm: admissibility is the theorem's premise.

[DERIVED correction] If prescribed outputs are granted to the host/authority as
a conservative extra observation, define that stronger observation interface
from the start and quantify compatibility for its permitted strategies. The
actual transcript with privately delivered outputs omitted is then a projection.
Do not first establish compatibility for a restricted observer and silently
enlarge its adaptive observation interface afterward.

### 4. Cache outputs at their verified Infer prefixes

[SOURCE] `service.py:138` permits release of an exact retained verified Infer
after later reader progress. `reader.py:26` separately registers query tickets;
`reader.py:51` checks that ticket and deduplicates delivery. Neither release nor
registration needs to coincide in time with acceptance of the Infer record.

[DERIVED correction] On accepting an Infer at prefix h, the simulator computes
and stores the left plaintext output for that prefix under the exact retained
envelope/request identity. A later valid receive emits that stored value;
retries reuse its delivery record. It must not compute the old query against
the current, later plaintext state. This is required for delayed or out-of-order
historical delivery and remains an efficient simulation over polynomial history.
The high-level trace therefore contains both accepted events and their later
delivery selections, although the compatible value is attached to the original
Infer prefix.

[DERIVED] One logical delivery under retained persistence does not imply one
physical decryption attempt through every instruction-level crash. The source
decrypts before committing the received row (`reader.py:58`). The current view
excludes private computation details and the note claims no availability. A
formal crash-aware refinement must specify which partial effects are observable
and how the public scheduler/recovery is simulated. The selected SIGKILL result
does not discharge that universal implementation obligation.

[DERIVED clarification] Copying a well-formed reader snapshot can preserve valid
provenance separately on each branch. What the one-reader persistence condition
protects is the single global accepted history and its retained delivery/nonce
accounting. The original note should distinguish that global condition from the
weaker statement that every branch state has some genuinely issued ancestry.
An interface permitting reader forks would need its own stated history and
observation relation; this review does not investigate such an interface.

### 5. Make the stopped hybrids and endpoint bad events explicit

[DERIVED correction] In every hybrid, stop with a fixed public outcome on a
detected valid but unissued issuer/query authorization, or a relevant distinct
preimage collision that would make byte provenance ambiguous. Maintain the
honest signed-message ledger and public hash/preimage records needed for those
decisions. This gives a total efficient simulator even when a mixed hybrid
contains such a bad event. In particular, do not condition the whole experiment
on “no forgery/collision” and then apply IND-CPA to that conditional distribution.

[DERIVED] Correctness failure need not be detected in a mixed hybrid. The
simulator always uses its known left output table. Correctness is used only to
couple each real endpoint to the corresponding simulated endpoint until failure.
Authentication/hash stopping can be checked using public messages and ledgers;
the reduction never needs to test a secret decryption in order to decide its
behavior.

[DERIVED] With this stopped construction, the note's endpoint-only bad-event
accounting is valid. No sum of bad-event probabilities over all intermediate
hybrids is necessary. Signature security is needed for the honest issuer and
command keys; no unforgeability assumption is made for the exposed authority
key. Ordinary EUF-CMA on new canonical domain/payload messages suffices for this
provenance argument; a new signature encoding of an already issued message does
not itself create an unknown input. Strong signature unforgeability is not
silently required by the argument.

[DERIVED] This proof does not invoke a separate circuit-privacy or general
chosen-ciphertext-security theorem: all evaluated ciphertext computations are
public transformations of the issued ciphertexts, and the only secret-key
outputs are replaced by compatible prefix outputs. That observation applies to
this provenance-constrained interface. It is not a claim that arbitrary FHE
evaluation plus an unchecked decryption endpoint would admit the same proof.

## A precise sufficient proposition and proof outline

[DERIVED formulation] Fix an abstract encryption/parameter family and polynomial
resource bounds, or a finite concrete resource-bounded game. At most m private
challenge issuance instances occur, each with an efficiently known valid pair
`(x_0,i, x_1,i)`. Honest encryption uses fresh prescribed coins. All other private
state entering the learner is either the known zero base or included in an
explicitly simulated input law. The honest issuance/query interfaces and their
semantic ledgers are as above. Public context/signature objects are built from
the actual ciphertext history in that run. The adversary receives the public
configuration and authority signing key and interacts through the declared
reader/issuance/query interfaces. Reader persistence and private configuration
remain trusted.

[DERIVED premise] Require the compatible-prefix condition above, efficient
public simulation and plaintext semantics, the declared private-role observation
law, and correctness of admitted evaluation for the entire adaptive endpoint
execution except with an explicit probability. Suppose the needed encryption,
issuer/query authentication and binding assumptions hold for the specified
resources. This is a conditional proposition; the current fixed BFV instance
and its library are not assigned those advantages by this review.

[DERIVED public invariant] Maintain a public simulation state consisting of CAS
bytes, installed encrypted head, verified records, authorized tickets and
delivery identities, plus the private-to-the-reduction semantic issuance ledger
and cached left outputs. Genuine input authentication identifies an issued
ciphertext; collision-free binding relates the digest used at the reader to
those exact bytes. The reader's current-parent check and public recomputation
then extend precisely one reader history. Learn enqueues the selected issued
instance and expires the exact oldest one; Infer preserves the queue and caches
its prefix's output. Historical sync and receive preserve the corresponding
records. All other decisions are public computation or the prescribed common
observation law. Authority signatures and scheduling are arbitrary efficient
adversary actions inside this machine.

[DERIVED endpoint coupling] Let `R_b` be a real endpoint and `S_b` the stopped
simulator with every private issuance encrypted as world b, always using the
left plaintext-output table. Define `Bad_b` as the union of relevant honest-key
authentication forgery, relevant distinct-preimage collision, and endpoint
correctness failure. Under the retained-boundary assumptions, couple the public
coins and adversary coins of `R_b` and `S_b`. Until `Bad_b`, provenance identifies
the same accepted semantic prefix; public decisions agree; and every delivered
cached value agrees by correctness and, for b=1, compatibility. Hence for any
test of the observable transcript,

```
|Pr[R_b returns 1] - Pr[S_b returns 1]| <= Pr[Bad_b].
```

[DERIVED hybrid step] For i from 0 to m, define `H_i` to encrypt the first i
challenge issuance instances from the right stream and the remainder from the
left, always running the same stopped public simulator and left output cache.
Changing the i-th ciphertext is a resource-bounded IND-CPA experiment: its two
messages are known, all remaining encryptions can be generated using the public
key, and all further signatures, public computations, scheduling, stopping and
output lookups are efficiently executable without the BFV secret. If issuance
is online, use the matching online left/right game, or an explicit reduction
to the one-challenge game at that issuance call. Fixed known streams with a
fixed issuance indexing admit the usual simpler hybrid construction. A missing
i-th call contributes no observable switch.

[DERIVED bound] Let `epsilon_i` bound the i-th adjacent hybrid gap for its actual
resource use. Since `H_0=S_0` and `H_m=S_1`, the triangle inequality gives

```
|Pr[R_0 returns 1] - Pr[R_1 returns 1]|
  <= Pr[Bad_0] + sum(i=1..m, epsilon_i) + Pr[Bad_1].
```

[DERIVED] A suitably defined multi-message advantage may replace the sum.
Here m counts all challenged issuance ciphertexts visible to the adversary,
including unaccepted/expired/alternate-history objects, not only installed
Learn events. Correctness probability must cover the complete adaptively
selected admitted execution and all relevant releases. A fixed-query error
estimate or a count of successful recorded comparisons cannot silently replace
that probability. Authentication terms are those of the honest signing
interfaces under the actual signing/query budget. Hash terms cover the actual
canonical bytes/preimages used for provenance and state/output binding.

## What remains open after the wording corrections

[OPEN implementation correspondence] The source checks support the intended
public invariant, but there is no universal Python/Rust refinement, information-
flow proof, crash/serialization proof, or instantiated adaptive BFV correctness
and security reduction in this note. The normal interface's trusted private
storage and code boundary must remain part of the theorem, especially because
the executed roles share an operating-system account.

[OPEN challenge nonvacuity] The argument is not circular: output compatibility
does not assume ciphertext indistinguishability, and IND-CPA supplies the latter
conditional step. Nevertheless an actual authorization family may leave few or
no distinct compatible input histories. The note does not establish a
nonidentical, useful, lifetime-compatible pair or a coupled private observation
law for the deployed policy. Selected test questions and successful encrypted
execution do not establish such a relation. This review runs no new disclosure
or routing experiment to investigate it.

[OPEN adaptive inputs] An adaptive fresh-input extension needs a uniform,
efficient coupled pair generator and common-law policy/metadata behavior on
every reachable public transcript, including the history dependent ciphertext
and authorization context. Correlated private auxiliary state must be explicitly
generated or simulated. The fixed-stream argument does not provide that
generator simply by naming it as an alternative. This is the substantive open
composition task after the present game is made precise.

[DERIVED overall scope] Reader-side verification removes the authority's
unchecked-arithmetic assumption in this conditional role model. It moves the
retained final history check into the trusted reader. It does not remove the
reader's full key, turn an issuer signature into a hidden-input validity proof,
establish arbitrary private adaptation, or supply a post-quantum system theorem.
The identified game conventions are sufficient to complete the mathematical
outline; the stronger implementation and primitive obligations remain open.
