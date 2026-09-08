# Concrete public-seed positive adapter contract

[DERIVED scope, 2026-09-08] One normal implementation witness for the frozen
[public-seed proposal](../PROPOSAL.md), accepted by the
[independent mathematical review](../../../../../adversarial_review/public_seed_setup/REPORT.md).
This adapter runs a named SHAKE256 recipe; it does not establish the ROM
assumption for SHAKE256, QROM security, physical timing privacy or deployment
confidentiality. The old proposal, review and implementations remain frozen.

[SOURCE] `source/public_setup/setup.py` and its four nested `source/crypto/`
files are byte-identical copies of the earlier accepted direct-setup adapter.
SOURCE_PINS.json identifies originals, copies, native dependency and this
contract. The new wrapper reuses only its fresh independent authentication
and recipient generation, matrix equations, public completion and context
serialization. The driver never calls the old public sampler or any legacy
initializer/keygen/projection-delivery branch.

## Fixed recipe and chronology

[DERIVED] Before public hash derivation, one new run creates all 16 independent
Ed25519 registry-signing keys and invokes 16 separate honest recipient-init
processes. Each samples one fresh dedicated scalar `a_i` with the frozen
OS-backed sampler and emits signed `A_i=g^a_i`. There are no missing rows,
reused registries, selective key redraws or registration retries. Public row
identities, the complete 16×577 matrix and its first-16 pivot rule are fixed
before key generation. The existing exact determinant is -812032080.

[DERIVED] The complete hash-domain JSON includes full p/q/group values,
all rows, coordinate order, cap, suite, and every ordered row identity,
independent verification key and A value. Canonical JSON has sorted keys,
ASCII escaping, no whitespace and no floats. Query encoding is the fixed
version prefix followed by a four-byte part count and, for each part, an
eight-byte big-endian length and those bytes. The five parts are **full
canonical domain bytes**, fixed seed bytes, ASCII role, four-byte coordinate,
and four-byte counter. The domain's SHA256 digest is inventory metadata only;
it is never substituted into SHAKE's actual input.

[DERIVED] The one predeclared seed is ASCII
`resident-designated-public-seed-positive-001`. It is supplied only after all
fresh announcements are collected and validated. A constant seed is allowed
by the theorem; no beacon or seed secrecy is asserted. There is one candidate
and no seed search, redraw after rejection, alternate domain, extraction or
negative crypto test in this tranche. This harness does not measure an
adversary's Q_pre or computational security level.

[SOURCE] The concrete primitive is Python `hashlib.shake_256`, with `.digest(n)`
returning the requested byte count. SHAKE256 is specified in
[FIPS 202](https://csrc.nist.gov/pubs/fips/202/final);
[Python's documented interface](https://docs.python.org/3/library/hashlib.html#shake-variable-length-digests)
defines the variable-length digest call. Reading these official pages does
not certify this environment's implementation or instantiate a ROM theorem.

[DERIVED] For each coordinate, SHAKE is independently invoked on the distinct
counter input. Let ell be `(upper-1).bit_length()` and request
`ceil(ell/8)` bytes. Interpret the raw block as a big-endian integer and shift
right by `8*byte_count-ell`, keeping the high ell bits. Accept the first word
in `[0,q)` for tau and `[1,p)` for U, among counters 1 through **128**. For the
fixed group, ell_tau=2047 and ell_U=2048; both use 256 bytes, with one unused
low bit for tau and none for U. The raw block retains every discarded bit.
Hash calls stop at first acceptance; unqueried later counters remain fully
specified and publicly recomputable. All observed prefixes, rejected words,
accepted counters, accepted values and full domain are public transcript data.

[DERIVED availability] In the ideal independent-bit model the exact one-seed
failure probability is
`1-(1-beta_q^128)^16*(1-beta_p^128)^561`, where
`beta_q=1-q/2^2047`, `beta_p=1-(p-1)/2^2048`. Each beta is less than one half,
so failure is strictly below `577/2^128`; this is an availability bound for
one modeled candidate, not a measured probability or hash-security estimate.
Successful accepted samples have no rejection bias in that model. The
proposal exactly simulates failure tapes, so this is not an extra privacy
error in its capped game. Tau zero and `U=±1` are valid; U zero is rejected.
Hashing a public scalar and exponentiating g is not this recipe.

[DERIVED] If the single normal candidate exhausts the cap, its rejection
record retains the complete domain, registry digest, signed announcements,
source identity and partial raw derivation tape. No context is created and
no replacement seed or crypto workload is launched.

## Normal workload, ordering and evidence

[DERIVED] The single allowed root is `reports/normal_001`, which must not
exist at launch. The source gate requires an accepted independent prelaunch
report matching SOURCE_PINS.json and records that root was notified.
Every subprocess checks the frozen sources/native bytes. The normal harness
has a 1,200-second overall budget and at most 300 seconds per child, reduced
to the remaining overall budget. Any failure stops the run; no retry or
private drain after public failure is permitted. Public-helper arithmetic
and hash tests may run before review; crypto operations may not.

[DERIVED] Public setup derives all 16 tau and 561 U values, completes all 577
group coordinates with the frozen algebra, and constructs zero state. The
public verifier independently re-invokes SHAKE on every prefix and recomputes
the entire canonical transcript and context. The frozen uncached backend
then validates group/token equations; its digest permits later validation
cache reuse. All 16 recipients finalize their own scalar envelopes; pending
copies are removed. No private scalar master or projection delivery is
computed by this path. Redundant-copy deletion is not a physical-erasure claim.

[DERIVED] Inputs are the predeclared public vectors
`x_t[j]=((t+3)*(j+5) mod 17)-8`, for t=1..33. Fresh private issuance coins
come from the unchanged backend. Learn keeps a 32-input FIFO, with exact
original c01 expiry at step 33. Infer uses rows 0,1,2,3 at steps 1,16,32,33.
This is a known public integer functionality fixture, not text/model utility
or an encrypted secret-state privacy experiment.

[DERIVED] After all 33 Learn and four Infer operations, a separate public
reference process recomputes each state from its active original ciphertext
product and each designated output from that state's public row and tau.
It compares complete canonical envelope bytes with direct CPython integer
arithmetic. This shares the frozen wire serializer; it is not a universal
native refinement or independent subgroup proof. A second complete setup
replay finishes next. All subprocesses have exited before public/ receives
PUBLIC_COMPLETE.json, which inventories every prior public evidence file.
No public command or public/ write is allowed thereafter.

[DERIVED] Only then do four separate recipient processes decode the already
selected outputs. Scalar keys, answers, decode costs and exact comparisons
remain under `.private/`. An independent direct integer-window formula checks
the four scores. The aggregate `RESEARCH_RESULT.json` and stdout are research
reporting **outside** the closed `public/` cryptographic transcript. Their
timing/success observations are not covered by the privacy theorem. Public
replay, source/context verification and public closure never depend on a
private decoded answer.

## Credentials and remaining assumptions

[DERIVED] The host-visible data are public registry/announcements, full seed
domain and hash prefixes, tau/U/h, vectors in this deliberately known fixture,
ciphertexts, outputs and public logs. Private surviving files are 16 recipient
scalar envelopes and 16 independent registration-signing keys; encryption
coins are used inside issuer processes. The public constructor has no scalar
master and does not perform any scalar-key delivery. Source inspection and
this run do not prove OS isolation, memory erasure or absence of a separate
operator's plaintext knowledge.

[DERIVED] Every recipient still has its full per-input row projection; all
recipients together retain the 16-row span for all issued and expired inputs.
The software-selected four outputs do not cryptographically narrow that
capability. Honest independent registration, classical DDH and the ideal
oracle model remain distinct from concrete SHAKE execution, Ed25519
authentication, fresh input randomness and source/runtime correspondence.
No general-purpose recipient-key reuse, malicious registration, multiple
deployed challenge keys, QROM, hidden nonlinear learner, sign-only release,
semantic input ambiguity or physical timing claim is added.

[DERIVED credential precision] All 16 registered scalar envelopes are
deliberately created. “No missing-row credential generation” here means no
additional authority or keygen for directions outside this fixed row span.
It does not mean only the four exercised recipients possess keys, and does
not exclude scalar keys derivable for linear combinations of registered rows.
