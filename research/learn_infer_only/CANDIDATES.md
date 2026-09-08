# Candidate decisions during the autonomous swarm

[DERIVED current comparison, renewed constructive swarm] The actual restricted-key ring construction now runs a continuing semantic learner: six teachings, two expiries and 96 matching scores, with no universal reader constructed. Its sixteen recipients retain their complete per-input query span. Separately, new text traverses encoding, a fresh BFV update proof, durable commit and a real query in 42.368 seconds; that path retains a full reader. An actual nonlinear BFV kernel and its bounded nine-to-four rescale proof now run, while a bounded MIFE Replay construction remains symbolic with a conditional privacy argument. Current builders are connecting complete query proofs to receiving, reducing rescale cost, proving more of native PBS, and closing finite-round commitment accounting. These are distinct constructions; their conjunction is still open. See [current results and exact scopes](../vfhe_2026_09_08/STATUS.md).

[DERIVED historical closeout comparison, 2026-09-08] The nonlinear TFHE path now executes the full 384/96 contract with matching public replays and deferred primary audits, but retains full-reader custody. The completed SHAKE public-seed adapter preserves fixed-span continuation without constructing a scalar master under its stated model; fixed-span recipient powers remain. A ring fixed-coordinate variant has reviewed mathematical and heuristic sizing, with finite samplability but no implementation. No candidate yet joins these strengths into one malicious-operator, history-bound, no-master-read resident. See STATUS.md and the exact artifact reports before interpreting the historical route notes below.

[DERIVED] Keep Route 3 for integrity/continuity work and the exact window/EMA as
small numerical targets. Restricted FE continuations and real encrypted loops now
exist here; no artifact joins them into the full authenticated-ingress,
restricted-release, no-master-read, PQ resident. DECISION.md gives the current
comparison; the route-specific historical derivations below retain their scope.

[EXECUTED / DERIVED second run] Benchmark R now joins actual BFV learning,
durable history and independently verified release over the complete fixed
384 Learn/96 Infer workload. All 96 integer outputs match; the full key remains
at the reader. The optimized normal run takes 201.345 seconds. Separately,
the fixed-span DDH control runs actual encrypted continuation after no-export
master setup, under explicit honest erasure. It exposes both fixed projections
on every input and retained snapshot. Its adaptive specialization passed bounded
independent review; the 577-coordinate/16-query scaling experiment is separate.
See [the main demo](experiments/end_to_end/README.md) and
[fixed-span scope](experiments/private_construction/fixed_span/README.md).

[DERIVED decision] Keep those results separate: a verified full-key reader
provides stronger history/recipient mediation, while exposed fixed FE keys permit
local reads and forks. Their conjunction is not supplied by either experiment.

## Route 1: pre-constrained encryption

[SOURCE: construction read] The local `2024/1294.pdf`, printed pp.15–16, fixes the
function list at setup and takes plaintext x at `Enc`. Its single-function construction
on p.22 encrypts f under FHE, evaluates `G[x](f)=f(x)`, and gives the authority the
underlying `FHE.sk`. Source version/hash/access records are in `SOURCES.md`.

[DERIVED] Concrete attempted transition: fix `f(s,command)=Step(s,command)`; an
initializer can encode `(s0,c0)` and the authorized key releases `Step(s0,c0)`. If that
output includes plaintext s1, the authorized reader reads it. If it omits s1, the
ordinary syntax has supplied no reusable next-state encoding. Encrypting s1 directly
under that same FHE public key does not repair this: the surviving authority holds
its full decryption key. Encrypting it under a second key instead requires a second
credential lifecycle and a proof for the resulting composition. Those are unresolved.

[DERIVED correction in scope] Fixing f is NOT by itself an obstruction to new
observations: f can accept `(state, observation)` or a bounded history as its input.
The unresolved step is turning protected output back into protected input without
giving an exposed role plaintext or a universal key. Thus the companion's phrase
“obs cannot enter” is too strong when read as a syntax impossibility. This does not
change its conclusion about the unaudited recurrent composition.

[SOURCE: abstract/metadata read; REPORTED construction analysis] The original
[PCE paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2022.4)
explicitly constrains setup authority decryption. The landed
`notes/pre-constrained-encryption-read.md` §1a/§3 reports its general-constraint
PCE→iO construction at printed 4:5/4:11. This tranche did not re-read that full proof.

[DERIVED] The companion's general-circuit closure attempt therefore inherits its iO
obligation. This is not a proof that EVERY restricted, fixed transition requires iO.
Small constraint families/NISC or other restricted constructions remain legitimate
targets. Do not turn a missing realization into a field-wide impossibility result.

[REFUTED: naive one-hop sPCE continuation with plaintext output, or re-encryption
under the authority's retained FHE key] Neither continuation satisfies the exposure
target. Relaxation: place the reader/reencryptor behind declared tier-C custody or
tier-D hardware, or supply a new constrained mechanism and audit its complete loop.

## Route 2: the static writer credential

[SOURCE: construction read] `2022/1599.pdf` §6.2, printed pp.57–58, has
`Enc.ST=(FPFE.msk,FE.ct)` and stores each element as a function-private FE key for
`H_i`. On its normal branch H encrypts the hardwired x_i into a caller-provided valid
inner setup. Ordinary evaluation uses an inner setup produced inside G. The writer
state is not updated by `Enc`. The local `2024/1213.pdf` pp.49–50 uses the role-swapped
form reported in the landed audit; that variant is recorded separately, not executed
as if it were the GKS23 construction.

[DERIVED] Complete recovery path: the exposed writer master secret encrypts one
attacker-selected valid inner setup for FPFE; each stored H-key evaluates against it;
one projection function key for the attacker's inner setup reads the ordered prefix.
The outer master secret and authorized outer function key are unnecessary. A
deterministic known Step can then replay recovered observations into the internal
state if it has all initialization and development inputs.

[EXECUTED] `writer_recovery.py` recovers 288 values in 64 synthetic histories through
that ideal-primitive path. It refuses missing/wrong writer credentials, the wrong H
branch, invalid initial encoder state, missing/repeated/skipped prefix positions and
cross-inner-setup ciphertexts. It intentionally ACCEPTS a same-setup replacement at
the correct index: the model does not fabricate original-history authentication.
Exact transcripts, capability list and operation counts are retained under
`experiments/results/writer_recovery*.json`.

[DERIVED scope] These negative controls enforce the prerequisites of the modeled
correctness path. They are not a claim that a concrete implementation of the paper
detects every malformed/out-of-order input; such robustness is not supplied by the
correctness equations being modeled.

[REFUTED: exposing this construction's writer state to the resident host] Erasing only
the outer master key does not suffice. No paper theorem is contradicted; its intended
games keep this writer state secret. The failure of a particular symbolic path after
removing the writer credential is not a proof of security of the remaining artifacts.

[DERIVED correction in scope] Absence of a function-hiding theorem means we cannot
promise that a private initialization hardwired into f is hidden. It does not alone
prove that every function key reveals f's entire representation. The concrete
read-all finding here is the correctness-based writer path, not that inference.

[OPEN] Keeping `FPFE.msk` outside the host, without simply installing an unprotected
read-all custodian, requires a separate construction. A threshold issuer is tier C;
a hardware issuer is tier D. No new survey or absence claim about all SFE variants
was attempted in this tranche.

## Route 3: context-bound receipts and a keyless continuity authority

[DERIVED construction] Reuse the existing Stage-0 full-word FS receipt with root
`(Context, oldRoot)`. The context is independently selected by authorization, encoded
with the existing prefix codec, and included in every FS query. Explicit boundary
checks connect context parent/command/output to the arithmetic word; the next state
equals that output. The concrete wire profile has a distinct cSHAKE domain. A context
change cannot be hidden in an ambiguous byte encoding; this is encoding injectivity,
not an assumption of collision-free hashes.

[DERIVED construction] Put the identical Context in the durable intent's event.
`FinalityGate.check` confirms votes on that exact candidate. An external authority
then checks its current exact prefix/head, accepted genesis and policy, and consumes
the derived `(genesis, slot)` token. Host `restore(manifest)` never changes that
authority. Accepted transitions can continue from their next state without resetting
the authority's release counter.

[EXECUTED successor] Finality is not currentness. Historical votes remain valid;
the guard checks the live prefix. The first adapter's empty-rootWrites witness is
now superseded by actual materialized DataIntent/full preflight and a journal-first
release path. Exact installed bytes and packet origin are checked. A constant-root
genuine-receipt falsifier keeps logical Step semantics separate. The checked EMA
descriptor-to-cell successor now binds canonical logical pre/post values, under its
descriptor premise and separate fixed-context ROM price. See DURABLE_INTEGRATION.md.

[DERIVED conditional claim] With the specified policy/current-head checks,
authenticated monotonic vote discipline and atomic authority update, accepted release
is context-bound; outside the inherited descriptor-failure event it executes the
specified public addition. At one slot, prefix-disciplined checked finality forces
the same entire Context. This neither proves hiding nor prevents arbitrary local
copies. `formal/README.md` gives the actual theorem names and recorded checks.

[EXECUTED] The Python model checks two continuing additions, stale manifest restore,
all context-field substitutions, re-voting an arithmetically invalid parent, wrong
delivery recipient, thin quorum, fork refusal, and explicit authority-rollback,
compromised-vote and non-atomic-release failures. It also exhibits randomness selection
bias and the integer-rescale distinction. No cryptographic primitives run in this model.

[OPEN] For encrypted resident state, replace the public Step with an authenticated
private transition relation and a gate whose exposed implementation cannot release
extra predicates. Merely installing an FHE key inside the release program fails
tier A. Fresh private input issuance, unbiased hidden development coins, witness
hiding, implementation leakage and a post-quantum composition remain open.

## Restricted continuations and numerical controls

[SOURCE/EXECUTED] PRIVATE_CONSTRUCTION.md records three distinct positives.
The AES-GCM response tree realizes a bounded behavioral quotient with exponential
preprocessing; the byte example's quotient becomes singleton at horizon 8.
DDH IPFE supports compact public additive continuation with one retained projection
key after honest master erasure. ALS modular LWE supports public additions modulo p
at q=p^k with constant noise; its executed small parameters are insecure equation
witnesses. Hidden kernel coordinates do not affect the allowed fixed projection.

[DERIVED] These positives do not supply the resident's release policy. The holder
can project fresh accessible ciphertext inputs and can run copied histories.
An authentication/currentness wrapper does not remove a projection already callable
from exposed software. Fresh-input noise, stateful key-issuance consistency and
private nonlinear behavior must be audited for each extension. The practical RLWE
source/decoder findings in experiments/private_construction/RLWE_AUDIT.md block
promoting those author-code artifacts to a checked concrete instantiation here.

[EXECUTED] HE_CLOSURE_COSTS.md records actual TFHE EMA and BFV additive-window
continuations. Identical-ciphertext expiration cancels old noise; re-encrypted
expiration does not. These runs retain full secret keys for testing, so they
establish encrypted computation, not absence of a reader. The window's queue,
sign-release and issuer/feature origins remain in its bill. ADAPTATION_UTILITY.md
supplies a useful structured control and a held-out neural-feature failure for
the same family, rather than assuming cryptographic feasibility implies utility.

## Additional closure lead: updatable encrypted RAM

[SOURCE: construction/game/proof outline read] Arriaga–Iovino–Tang,
ePrint 2016/1179, §3 pp.9–15 and Figure 9 p.17, really updates encrypted RAM.
Each preissued token contains an obfuscated transition circuit with a decryption
key; it validates encrypted Merkle paths and reencrypts changed nodes using a
puncturable PRF. Theorem 1 requires iO **and** distributional-indistinguishability
security for its specified sampler class, plus CCA encryption, NIZK and hashing.
This is a stronger, specifically stated obfuscation assumption, not an LWE-only
construction or a measured implementation.

[SOURCE: game/syntax read] Tokens carry sequential ids and TokenGen requires the
master secret. Figure 8 chooses both memories and the complete program sequence
before setup, and requires equal outputs and access patterns. It does not list
mpk among A1's inputs. Section 4 leaves adaptive token acquisition and relaxing
access-pattern equality to future work.

[DERIVED deployment consequence] Honest setup could preissue a bounded sequence,
then erase both PKE secrets, token-generation PRF originals and private input
copies. That gives a genuine protected-state-to-protected-state candidate for
that sequence under its assumptions. Extending the sequence after erasure,
introducing unknown observations, and exposing public encryption material need
additional syntax/security arguments; the displayed game does not establish them.
The token id lives inside copyable ciphertext, so it supplies local sequencing,
not an independent no-rollback authority. A token that internally performs a
bounded computation is distinct from indefinitely issuing new resident commands.

[SOURCE: contrasting syntax read] Cini et al., ePrint 2022/1284 and published
Journal of Cryptology 37:8, §3 Definition 5 and §5.2, use ciphertext *updates* to
change an access tag once. Update tokens are generated from the master key;
they do not implement a general learned-state update. Its lattice construction
is useful for a separately scoped migration audit, with ROM and token/query
restrictions. It should not be substituted for the encrypted-RAM continuation
above merely because the titles share “updatable”.

[OPEN] Neither additional source supplies a proved, efficient PQ resident meeting
the full handoff. These are two algorithm-level distinctions to carry into the
candidate/credential review, not a field-wide impossibility claim.

## Reverse-setup randomized-FE ladder

[SOURCE/DERIVED] The new fixed H2 candidate uses 2013/729 Definition 2.4,
Lemma 2.9, Theorem 4.1 and Appendix C. It generates independent instances from
the terminal read backwards, so each transition function can embed the next
public key before its own setup. The compatibility proof retains the complete
future public/function-key package and handles joint next-ciphertext outputs.
The current setup and master remain independent of the pre-setup auxiliary view.
Details and exact access scope are in
[FINITE_LADDER.md](experiments/private_construction/FINITE_LADDER.md).

[DERIVED] This offers a bounded protected-state-to-protected-state path after
honest erasure, with public commands and full forks. It exposes three public
keys and seven function keys for H2/B3. It does not issue an unrestricted raw
master to the host. The obfuscated function keys contain sensitive constants;
the assumed FE security theorem supplies the restricted-capability claim.
Object counts do not price obfuscation or establish practical performance.

[EXECUTED] Finite behavior is nonvacuous: 14 classes of byte states at H2,
meaningful update-order effects, and an independent adaptive/fork-policy audit.
No encryption implementation is supplied. Growing horizon, private fresh-input
composition and QPT lifting are active separate audits. A terminal-to-root key
cycle does not inherit the reverse setup argument.

[SOURCE/DERIVED scoped alternatives] The related static predicate and same-key
recurrence audits are in
[PREDICATE_CLOSURE.md](experiments/private_construction/PREDICATE_CLOSURE.md) and
[RFE_RECURRENCE.md](experiments/private_construction/RFE_RECURRENCE.md).
Their conclusions concern inspected syntax and theorem applicability, not a
field-wide impossibility result. The separate [PQ audit](PQ_COMPOSITION.md)
retains the conditional average-case-iO assumption and correctness/game gaps.

## Third overnight checkpoint — 2026-09-08

[EXECUTED/DERIVED] The public-coin designated setup now completes the normal
40-Learn/four-Infer/eight-expiry durable journal, with all44 public replays and
four deferred integer matches. The constructor computes no scalar master under
its specified honest sampling algorithm. Recipients retain their full per-input
span, and accepted-value security excludes instrumented timings and sampler
tapes. See [journal report](experiments/private_construction/designated_span/public_coin_setup/journal/README.md).

[DERIVED reviewed] A new PQ candidate makes a full invertible basis change,
lets each prescribed recipient independently sample its own coordinate key,
and samples unissued public rows uniformly. Its fixed-coordinate QPT argument
uses polynomial Gaussian widths with explicit advice and residual-dimension
conditions. [Finite sizing](experiments/private_construction/public_setup_pq/costs/FEASIBILITY.md)
is expensive and remains uncertified: the n1024 example has84.43MB ciphertext
and86.46GB public key. A finite regularity bound alone does not establish total
security. General nonlinear learned-state closure and history-bound release
are not supplied by scalar-linear same-key updates.

[EXECUTED] The nonlinear FHE branch now consumes a Lean-derived gate schedule
through a generic runtime. The original long handwritten run failed exact byte
replay at Learn14 before any private decode. A separate fixed-FFT configuration
passes five public controls; a new long trajectory is being prepared. The full
TFHE reader key remains in this branch. These advances do not combine the
restricted DDH/PQ recipient credentials with the nonlinear learner.

## Finite smudged setup and public-seed refinement — 2026-09-08

[DERIVED reviewed] The fixed-coordinate smudged construction uses ordinary
QPT LWE, independent Gaussian recipient rows and uniformly sampled absent
public rows. A scalar flood masks the joint key/error shift; augmented-matrix
regularity handles exposed recipient keys. The finite proof includes repeated
input hybrids and sampling tails. The original compact sizing point fails
valid primal hardness sanity checks. A coupled larger point meets the named
heuristic cost comparisons and finite inequalities at a public-matrix cost of
157,649,414,144 bytes. This is a conditional mathematical candidate, without
an implemented sampler or certified security level.
[Independent proof review](experiments/adversarial_review/smudged_fixed_coordinate/REPORT.md),
[independent hardness review](experiments/adversarial_review/smudged_hardness/REPORT.md).

[DERIVED reviewed] A separate classical programmable-ROM proof replaces the
honest public sampler in the DDH setup with a deterministic public-seed tape.
It binds a fresh independent recipient registry before seed choice and charges
pre-registration guesses and adaptive seed selection. Its capped rejection
sampler models failed tapes explicitly. Concrete XOF execution and quantum
oracle security do not follow from that proof. A fresh adapter is in preparation.
[Proposal](experiments/private_construction/designated_span/public_coin_setup/public_seed/PROPOSAL.md),
[independent review](experiments/adversarial_review/public_seed_setup/REPORT.md).
