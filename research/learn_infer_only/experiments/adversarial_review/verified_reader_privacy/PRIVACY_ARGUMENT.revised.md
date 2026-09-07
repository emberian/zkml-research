# Conditional privacy with an independently verifying reader

[DERIVED successor, 2026-09-07] This argument replaces the honest-authority
premise in the parent [transcript note](../PRIVACY_SCOPE.md) with a reader that
independently validates the complete admitted ciphertext history. The host and
authority, including the authority signing key, may be adversarial. Honest setup,
the reader, input issuer, command authorizer and their private configuration
remain trusted. Reader persistence, selected code/dependencies and the private
execution boundary belong to this trusted computing base. This
is a conditional argument for benchmark R, not a no-master-read construction
or a proved security parameter for the present BFV library.

## Interface and invariant

[DERIVED idealized interface] Setup fixes the public arithmetic program,
genesis, recipient policy, issuer/command verification keys and BFV public key.
The reader holds the matching BFV secret and independently initialized encrypted
state. Public input issuance produces an authenticated fresh ciphertext and
public metadata from one valid private vector. The game records each authenticated
issuance instance and its known plaintext pair, identified unambiguously by the
canonical signed message or a unique signed issuance handle. Reissuing the exact
same authenticated message must preserve that interpretation. This is an honest
issuer/game premise: roles.issue has no issuance ledger, and accepted record_id
uniqueness alone does not establish it. Query authorization selects public query
bytes, recipient and context.
Neither issuer metadata nor authorization leaks an additional private feature.

[DERIVED] The reader may receive arbitrary public blobs and authority-signed
envelopes. It accepts a new envelope only after checking the original input or
query authorization, unique identifiers, its own exact current parent and
revision, and public recomputation of every next-state/output field. An exact
historical envelope may be retried without changing state. A release must match
an already verified Infer envelope and independently registered query ticket;
each such ticket has one logical delivery. A Learn envelope is never a release.
All rejection decisions before decryption depend only on public objects and the
reader's encrypted history. Its secret key is used only for a verified output.

[DERIVED inductive invariant] On executions with no authentication forgery or
relevant content-address collision, each reader-installed state is the public
evaluation of a sequence of genuinely issued input identities and permitted
queries starting at genesis. Its integer meaning is the corresponding window
semantics whenever BFV correctness holds. Proof: the initial state supplies the
base; a new Learn checks an issued fresh input and recomputes exact-original
expiry; an Infer checks its query and frames the queue; an exact retry preserves
the state. The reader's own parent test supplies the induction order regardless
of which envelopes the authority signs, omits, reorders or proposes.

[DERIVED persistence condition] This invariant uses one retained reader history.
The claim of one global history and deduplicated delivery does not hold across
arbitrary rollback or cloning of that database without a fork-aware ideal
interface. Each clone might still have valid branch-local provenance. A copied
authority database alone does not reset the reader. Availability and progress
are not postconditions of this argument.

## Challenge relation and simulation

[DERIVED premises] Use a polynomially bounded execution and two efficiently
known challenge streams of valid input vectors. Alternatively use an explicitly
defined efficient coupled adaptive stream generator; this note supplies no new
such generator. Common public metadata may include route, sizes and semantic
input identity. Ciphertext hashes, signed parent contexts and revisions are
computed from the actual public ciphertext history, rather than assumed equal
as byte strings between worlds. Require:

1. For the same semantic sequence of issuance instances and permitted queries
   in the union of both endpoint reachable-prefix sets, both challenge streams
   have identical prescribed outward outputs. Both remain valid for the issuer's
   range/feature rules. Compatibility covers every accepted continuation,
   including reordered/subset admissions, not only recorded questions. Plaintext
   semantics and the left output simulator are efficient and total on every
   public history that an intermediate ciphertext hybrid can produce, even when
   that hybrid has no interpretation as a real compatible plaintext history.
2. All public verification, history maintenance and authentication can be
   simulated efficiently from public ciphertexts and independently generated
   role authentication keys. Private-role timing/resource behavior is omitted
   or has a common efficiently simulatable law. Reader rejection and acknowledgment
   metadata meet the same condition.
3. Fresh challenge encryption has the needed multi-message IND-CPA security,
   and evaluated ciphertexts decode to the specified integer results on admitted
   histories except with an explicitly bounded probability for the whole adaptive
   endpoint execution. A per-fixed-ciphertext correctness assertion is insufficient.
   Authentication and full-byte content addressing have their stated security
   assumptions. Honest issuance supplies the plaintext/noise/key provenance
   that the code's public key-ID and signed range assertions do not prove.
4. The reader discloses only the prescribed selected outputs and common metadata.
   Its raw key, internal decrypted polynomial and private computation side
   channels are outside the adversary's view. Including the prescribed outputs
   in that view is conservative when actual delivery remains private to a
   separately trusted recipient.

[DERIVED simulator] Given challenge ciphertexts, the reduction runs the same
public reader validation and encrypted state machine. It hands the authority
signing key to the adversary. It can issue the honest input/query signatures
using independently sampled keys, and record the semantic identities of their
authenticated ciphertexts. It computes and caches an ideal scalar at each
accepted Infer prefix using known left plaintext semantics at that issuance/query
sequence. Delayed historical delivery or retry uses that cached value, not the
current plaintext state. Compatibility makes that answer correct in both worlds. It simulates historical
retry, refusal and deduplication from public history, without decrypting arbitrary
adversarial ciphertexts. Every hybrid is a total stopped public simulator:
detected valid-but-unissued issuer/query authentication or a relevant byte-binding
collision stops with a fixed public result. It does not silently assign an unknown
plaintext or condition on noBad. Correctness failures need not be detected by
this simulator; they are charged only when coupling the two real endpoints.

[DERIVED hybrid] Switch the input ciphertexts one at a time while retaining
this same plaintext-output simulator. The simulator still runs the actual
public ciphertext computations and context checks in each hybrid. Mixed-world
encrypted states need not have the simulated scalar as their decryption; those
intermediate experiments are analytical. Only the two endpoint distributions
must coincide with real reader outputs, which follows from compatibility and
correctness. Thus malicious authority scheduling and signatures are efficient
postprocessing inside the reduction, not a new decryption oracle.

[DERIVED bound form] Let m bound all challenged issuance ciphertexts exposed to
the adversary, including unaccepted, expired or alternative branches. The gap
is at most the sum of m appropriately resource-bounded encryption gaps, plus
the two endpoint probabilities of the union of authentication-forgery,
content-address-collision and correctness bad events. A primitive multi-message
bound can replace the sum. This statement does not assign numeric advantages
to Ed25519, SHA256 or this BFV parameter set, and does not infer PQ security.

## What the executed code contributes

[EXECUTED correspondence evidence] [Run004](reports/README.md) exercises the
service at SHA256
`f0e79c2a33baa32e2867d467735dafd29b26c480deb1f688289e7468bd2de01b`:
40 private Learn, four Infer, eight expiries and 23 refusal controls, with exact
authority/reader state and ordered-journal agreement. All scalar comparisons
pass. The verifier refuses a fixed public wrong-output envelope that the
signature-only baseline accepts. Historical retries and an actual reader
SIGKILL/restart retain four total decryptions. Independent review checks the
status read transaction under a concurrent real commit.

[OPEN correspondence boundary] Those executions are evidence for selected
paths, not a universal Python/Rust refinement or an information-flow proof.
Actual process memory is under one operating-system account, the issuer/test
oracle retains private inputs, and the reader retains the full BFV key. Removing
the authority's unchecked-output route therefore improves integrity and the
conditional host/authority privacy boundary without removing every unrestricted
read credential. Replacing the full-key reader is a separate construction task.

[DERIVED review completion] Independent [mathematical review](../../adversarial_review/verified_reader_privacy/REVIEW.md)
accepted the core malicious-authority reduction with the issuance, total-semantics,
historical-output, persistence and stopped-hybrid qualifications now explicit
above. It preserves the original note and service bytes. This correction adds no
runtime tests, encryption instantiation, adaptive private-input composition
theorem or removal of the reader key. The separately reviewed honest-authority
note remains unchanged.
