# Independent end-to-end review log

## 1. Crypto component at source 500f6681

[EXECUTED] `crypto_boundary_review_001.json` records 36 actual subprocess
checks against source SHA256
`500f66817e30feb059c4233de3912d1b1e8824d5a2643c7e1bb917cd77b7b8e7` and
binary SHA256 `93307bdaed3fa666c8b5c81c9598eb6c9e350ce908b476947535cffc3847ca37`.
`crypto_boundary_runner_001.json` retains the outer command, successful exit and
unchanged source hashes. A snapshot of this exact source is retained under
`snapshots/crypto_500f6681/`; test keys and binaries remain in ignored runtime
storage. Source identity is also checked against the saved binary's own params
response before executing the tests.

[EXECUTED positive] Two OS-random test keys and four actual encryptions are
generated through the CLI. Repeated encryption of one public test vector has
different ciphertext bytes. Adding to canonical zero returns the original
ciphertext, and add-then-subtract-the-exact-old yields the second input's exact
bytes. An actual encrypted dot product over 577 coordinates decrypts to the
independent integer score 587. This is the arithmetic atom; the two-input
expiry check does not pretend to instantiate the capacity-32 authority schedule.

[EXECUTED refusal] Wrong magic, object kind, parameter ID, trailing/truncated or
oversized body, an extra component, wrong level, unknown protobuf fields and
PowerBasis/NttShoup ciphertext forms all fail strict inspection. Boolean,
floating-point, out-of-range, overflowing, short and long query vectors are
refused. Noncanonical query whitespace and duplicate fields are refused, and
the host arithmetic command rejects a supplied secret-key argument. These are
parsing/role-argument checks, not operating-system information-flow proofs.

[EXECUTED further codec checks] `codec_domain_review_001.json` adds eight
actual calls against the same saved binary. A coherent degree-8 polynomial
payload, with matching shortened coefficient bytes, fails both strict CT
inspection and normalization; an altered public key carrying that same
encoding fails even after its public key-ID hash is updated. This tests the
source-domain issue found in the dependency decoder, which can otherwise pad
short degree encodings into a larger context. A genuine public seeded
encryption of zero normalizes to full canonical ciphertext and decrypts to
zero. Normalization uses public ciphertext data; the test decryption remains
an explicitly trusted oracle.

[EXECUTED boundaries, not defects] A valid foreign-key ciphertext relabeled
with the expected header key ID passes syntax inspection. Also, changing a
serialized polynomial coefficient while retaining canonical form passes
inspection. Neither result contradicts the CLI's stated metadata scope.
They demonstrate why the journal must authenticate the admitted ciphertext
and compare the recomputed exact transition; canonical encoding and declared
key identity do not establish ciphertext provenance or integrity.

[OPEN] No finalized-reader, durable-journal or full capacity-32 end-to-end result
is included in these 44 component calls. Public test vectors and a raw full-key
oracle establish arithmetic compatibility; they do not establish secrecy of
known development or absence of master-read authority. Later source versions
require their own version-specific review rather than inheriting this hash's
result without checking the changed code.

## 2. Conditional transcript argument and authority credential

[SOURCE / DERIVED review] The revised `end_to_end/PRIVACY_SCOPE.md`, SHA256
`e6c8af45523757d558afcbe2392d372cd815eff38dec2ea70f870a768e72223e`, is a
conditional passive-view argument with an honest validating authority, trusted
issuers/command authorizers and a trusted full-key reader. It does not establish
the all-role exposure target. The review prompted three explicit premises:
efficient common-output simulation, omission or common simulation of every
private-processing role's timing/resource leakage, and honest authority
validation. The note now states all three. In particular the issuer CLI's work
timing cannot silently be included in a plaintext-independent view.

[DERIVED] The ciphertext hybrid argument need not decrypt mixed-world state.
For fixed efficiently specified challenge streams, the reduction can answer
every ideal reader call by the left plaintext semantics on the actual public
command history. Compatibility makes this endpoint-faithful in both worlds;
intermediate hybrids are public ciphertext computations plus that same
simulator. Their actual mixed plaintext outputs may differ. Independent signing
keys let the reduction produce the public authenticated objects. A proof or
attestation whose public law depends on unavailable private coins would require
an additional simulator; ciphertext-only trusted assertions do not establish
such a proof. Adaptive fresh-input pair generation remains expressly open.

[EXECUTED small controls] `python3
research/learn_infer_only/experiments/adversarial_review/end_to_end/privacy_scope_review.py`
passes and records `privacy_scope_review_001.json`. Two distinct valid width-577
vectors e0 and e1 both answer 1 to the fixed query e0+e1, while zero answers 0.
This inhabits a nonconstant illustrative fixed-query challenge relation; it does
not establish compatibility with the actual feature policy or every deployed
query continuation. In a two-Learn schedule, streams [e0,e1] and [e1,e0] both
answer 1 to e0, while the one-input-switched hybrids answer 2 or 0. The common
output simulator still returns 1, demonstrating the precise endpoint argument.
These finite integer controls implement no encryption or security reduction.

[DERIVED critical credential boundary] If a reader trusts the authority's
signature without independently checking the admitted state, exact query and
arithmetic, a compromised authority can substitute a ciphertext for a different
computation at a valid release opportunity. In the first pair above, substituting
e0 for the authorized e0+e1 changes equal outputs into 1 versus 0. This is an
indirect disclosure capability even though the signer has no BFV secret. Its
scope depends on available independently authorized release opportunities;
signing power alone does not mint a requester's credentials or an unlimited
quota. Root sent the implementation owner a corresponding expected boundary
test. No actual finalization-signature/service exploit has yet been executed by
this review. The baseline must trust authority validation, or add an independently
checked reader path. Either version still retains the reader's full decryption
key.

[OPEN] The note leaves actual BFV security and resource-bounded advantage
uninstantiated. A formal asymptotic theorem needs a parameter family; a concrete
parameter instance needs a finite adversary/resource bound. Neither follows from
the current known-input benchmark. Public metadata, admission behavior, private
input laws, reader rejects and side channels must satisfy the declared view;
the note is not evidence that the implementation already meets those premises.

[REPORTED source correction] Carver found that the historical caller seed does
not fix all public key/ciphertext bytes: the dependency also invokes its own
OS RNG during public-key construction. The acceptance note now separates this
fact from caller-seeded secret-key generation and the unconditional known-vector
replay limit. This does not make the published fixture private. Exact raw
secret-key repeatability is being checked by the crypto owner.

## 3. Executed signed-context alias defect in the first journal source

[REFUTED: exact canonical signed-action binding at this source] The initial
`model.py` hash `6f52483bc80e928f0268962553a10dbe8365fa7613fa57fd35a4632324393323`
uses Python object equality for `payload == action`, while several numeric
fields lack strict type checks. Python equates integer 1 with both `True` and
`1.0`, and integer range bounds with their float counterparts. Thus a host can
change the canonical request action without changing its signed authorization.

[EXECUTED] `journal_alias_review.py` runs real copied-source authority/reader
processes, real Ed25519 signatures and the final crypto binary at source
`22f0cbe304772263094c228f6598eb4cbfa00432902ba9e5de0993f6735e1b7c`.
`journal_alias_review_001.json` records an honest Learn followed by three
accepted host mutations under unchanged authorization bytes:

- Infer `program_version: 1` becomes `true`; the reader accepts and decrypts.
- Learn `program_version: 1` becomes `1.0`.
- Learn `range_assertion: [-127,127]` becomes `[-127.0,127.0]`.

[EXECUTED scope] All three changed canonical payloads differ from the original
signed action. The same numerical meanings are preserved in these particular
witnesses; this is a signature-to-context binding defect, not evidence of an
additional plaintext extraction or changed arithmetic result. The independent
public-vector oracle checks the delivered score 1. The final revision is four.
Exact original sources are retained under `snapshots/journal_initial/` with a
manifest; test keys, database, ciphertexts and binary are ignored runtime data.

[REPORTED repair in progress] The owner agrees that canonical payload/action
equality and strict numeric types are required, and plans duplicate-field
rejection for JSON parsing. A repaired source must be checked separately; the
three refusals are not yet claimed here. The source snapshot permits future
reproduction of the original accepted aliases after the owner changes files.

## 4. Independent compact finite-learner check

[EXECUTED] `compact_quotient_review.py` checks the frozen `compact.py` source
`05b0987c953ad88b2659e348b357b8e97f3738f0c5143c3dc4e9154343058b84` without
importing the author's compiler, catalog, history enumeration or oracle. An
independent backward partition refines every raw state by its six immediate
outputs and successor classes. For all 289 states, at every horizon 0 through
12, those equivalence classes are in bijection with the compact clamped scores.
The class counts are 1, 4, 16, 36, 64, 100, 144, 196, 256, then 289 from H9.
All 20,808 local comparisons of the actual compact transition to the independent
raw update pass. `compact_quotient_review_001.json` retains the exact hashes.

[EXECUTED] Two actual isolated initializer/evaluator subprocess pairs for
(-8,-2) and (-7,-2) produce identical H4 resident bytes and outputs
`[0,"ack","ack",1]` for the selected adapting sequence. Altering the visible
representative changes an inference and is accepted, as the artifact's lack of
integrity predicts. The review writes no author-owned artifacts or results.

[DERIVED] The stated all-integer forward simulation and converse distinguishers
check: clamping preserves sign, commutes with a mistake update followed by
decreased horizon, and distinct representatives admit a distinguishing command
sequence within the remaining budget. This is a functionality-specific compact
behavioral quotient, not an encryption theorem. It makes the finite complete-fork
interface genuinely executable without preserving the original inaccessible
confidence values. Setup privacy and erasure remain assumptions; public runtime
has no further hidden raw state, fresh private ingress or integrity mechanism.
No defect was found in the scoped quotient statement.

[SOURCE / REPORTED RNG refinement] The crypto owner's separate
`end_to_end/crypto/rng_audit.json` reports caller seed 37 produces equal 4,099-byte
raw secret keys, differing public-key bytes, and successful cross-decryption
using the regenerated secret. The record contains only booleans and lengths.
This supports the narrower full-secret exposure statement while correcting
the earlier all-public-byte reproducibility claim. This reviewer read that
result; it did not independently rerun this credential experiment.

## 5. Concurrent export is not an atomic snapshot in the initial source

[REFUTED: atomic journal/head export at the initial source] `Authority.handle`
reads all journal rows, ends that database read, then obtains `self.head()`
through another connection. A valid intervening commit can make the returned
journal and head refer to different revisions. This concerns snapshot
consistency, not transition soundness or signature forgery.

[EXECUTED] `journal_export_review.py` uses the same saved initial source and
real BFV/authority processes as §3. After revision 1, an audit-owned authority
instance starts the original export method. Its head call is delayed while a
separate real authority process accepts and commits revision 2, then the
original head read resumes. `journal_export_review_001.json` records a returned
journal containing only revision 1 and a head at revision 2. The audit changes
no read/result logic; it schedules an ordinary concurrent interleaving through
a method delay on its own instance. Full quiescent public arithmetic replay of
the same two committed transitions succeeds afterward.

[REPORTED repair in progress] The owner will read journal and meta inside one
explicit SQLite read transaction. Existing quiescent replay results remain
valid; they should not be promoted to concurrent snapshot consistency until
the repaired source is tested against this interleaving.

[SOURCE version comparison] A direct diff from reviewed crypto source 500f6681
to frozen 22f0cbe3 shows only the private/regular secret-file retry check,
removal of the misleading oracle-keygen command, and its direct save regression
test/import. The decoder, canonicalization and arithmetic are unchanged. The
independent real journal tests in §§3 and 5 also execute the newer binary,
SHA256 `9c79c02e7d919ecdc24851c6f77e50ed6990397bd669f571a886f8e2b85058c2`.
The 44 malformed-codec checks remain explicitly attributed to the old source;
the source diff explains the narrower continuity evidence for those routines.

## 6. Repaired journal passes the same boundaries

[EXECUTED] `journal_repair_review_001.json` independently checks the repaired
source. Core hashes are common `32afcec1c2db4a6e1ccf9eb475ad22780a0f0d4deceb18c39e66246b5a1b6b1e`,
model `bcbac3baac92aaeacf2fdbbf174dd0d1c57c9e0fffed93b9d7307f2b96da28eb`,
authority `2030998d92bf2baa92055bd8e522b0c0001ffeadd5f43100f0a33e4e6ef08039`,
and reader `d39c3538d8c0e660539d4e776627926449fec5fb1fc1c866853643d47ce76c9a`.
All source files and the complete manifest are retained in
`snapshots/journal_repaired/`. The code now compares canonical signed actions,
requires exact numeric types, rejects duplicate/floating JSON and exports under
a read transaction.

[EXECUTED] Eighteen independent refusals pass through real authority/reader
RPCs. These include all three original aliases; Boolean/float route and parent;
changed recipient, genesis, program and key; forged request/finalization
signatures; duplicate JSON fields; a genuine Learn receipt at the reader;
a canonical wrong result refused by actual recomputation; and missing or altered
already-inspected CAS contents. The honest path accepts three Learn events and
one Infer, whose public-vector oracle score is 1. Historical Learn and Infer
retries retain exact envelopes after later commits, and the reader reports a
deduplicated Infer retry. Full independent public arithmetic replay succeeds.

[EXECUTED concurrent snapshot] A connection trace callback pauses the export
between its two original SELECTs. A real separate authority process commits
revision 4 while that export is pending. The export returns both journal and
head at revision 3, and a later head is revision 4. The callback schedules the
interleaving only; it does not alter SQL, rows or returned values. This is the
green counterpart to §5's retained inconsistent snapshot. These targeted checks
do not duplicate or substitute for the owner's full capacity-32 fixture run.

## 7. Verified reader's status snapshot during an actual sync

[SOURCE / DERIVED review] The new verified reader commits its own encrypted
head and journal after checking exact issuer/query authorization and recomputing
the full transition. Its receive path requires exact retained verified Infer
membership before the inherited query-ticket/decryption path. This addresses
the earlier signature-only arithmetic trust seam, while retaining the full
reader secret, trusted issuance/command policy and reader persistence assumption.
An authority may still withhold progress or choose among preauthorized valid
continuations. No general all-role privacy conclusion follows.

[EXECUTED] At service SHA256
`f0e79c2a33baa32e2867d467735dafd29b26c480deb1f688289e7468bd2de01b`,
`verified_status_review_001.json` records an independent status consistency
test using the exact strict RPC handler, real Ed25519/BFV Learn envelope and
SQLite WAL. A trace callback pauses status after reading revision 0 and before
counting records. Another RPC verifies the real Learn and commits revision 1.
The pending status returns revision/count `[0,0]`; the next status returns
`[1,1]`. Thus its two SELECTs use one snapshot under the tested interleaving.
The exact service and repaired helper sources are retained in
`snapshots/verified_status/`.

[OPEN scope] This focused one-transition status test performs no plaintext
release and does not establish the successor's full mixed-history, expiry,
compromised-signature, crash or rollback behavior. Those tests belong to the
crypto owner's separate driver. It is evidence for this status transaction and
the actual successful encrypted sync used to exercise it.
