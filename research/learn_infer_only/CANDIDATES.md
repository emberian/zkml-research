# Candidate decisions after the first continuation tranche

[DERIVED] Keep Route 3 for integrity/continuity work. No candidate audited here realizes
the combined tier-A/B no-master-read resident. The added formal witness is a public
addition process. Its two-step executable loop is useful evidence about release
authorization and closure of that control model, not encrypted learning.

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

[DERIVED limit] Finality is not currentness. Historical votes remain valid; the new
guard checks currentness. The Lean adapter reuses `Snapshot.install` and
`Intent.nullifiersFreshCheck`, but is not yet a DataIntent/full-preflight integration:
its public witness does not write materialized cell roots. This is named in both
formal files and `formal/README.md`; a root-backed production integration is still due.

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
