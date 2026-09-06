# Decision: extend the integrity boundary; keep the privacy gap explicit

[DERIVED decision, 2026-09-06] Keep proof-bound release as the leading construction
attempt, with a narrower current result: context-bound public computation and
keyless release continuity. No audited candidate here survives the combined tier-A/B
exposure as a closed private learner. §6C now has an executed symbolic transcript;
§6D has an executed model and a checked proposed Lean adapter; §6E has a checked
context-binding extension, not a private end-to-end realization.

## What is new

[EXECUTED] The writer exposure derivation is now an ideal-primitive program:
64 synthetic histories, 288 recovered values, no outer master key or authorized
outer function key. It has missing-credential, wrong-setup/branch and incomplete-
prefix controls. Same-setup, correct-index replacement is accepted rather than
silently ruled out. These checks support the specified correctness path, not
cryptographic robustness or a claim that every SFE variant fails.

[EXECUTED] The restore model performs two authorized continuing transitions. An old
finalized certificate remains final, yet the current-head/consumption gate refuses
a fresh release from its restored manifest. Authority rollback re-enables it;
non-atomic check/install permits duplicate authorizations; compromised prefix
discipline permits conflicting finality; silent local copies remain possible.

[EXECUTED] Both proposed Lean modules check with 31 exact-output axiom pins. They
reuse the actual Stage-0 receipt, finality checker and durable consumption objects.
The receipt root and concrete transcript encoding now contain genesis, parent,
program/version, command/authorization, recipient, randomness rule/commitment,
next state and output. Explicit semantic checks connect the arithmetic fields to
the descriptor. Accepted context substitution is refused; under the actual finality
prefix discipline, same-slot checked candidates have identical Context events.

[DERIVED] This is stronger than attaching metadata to an old proof: the proposed
root participates in the existing verifier and FS query encoding, boundary fields
are checked against the word, the same context enters finality's exact event, and
the independent authority checks currentness. Its limits remain concrete: public
addition; deterministic randomness; public delivery pair; no materialized rootWrites
or full durable preflight in the adapter's closed witness.

[EXECUTED] The original interface seed also passes: all 256 bytes recovered with
eight chosen-update observations, restricted positive relation preserved, 2,048
output-routing cases and 990 bounded-history checks. These results validate finite
interface reasoning, not an encryption implementation.

## Strongest supported conditional statement

[DERIVED] In the staged control model, accepted finality plus independent current
genesis/head/policy/token checks and accepted context-linked receipt force the
selected context. If the existing descriptor is true, the public next state and
output equal the specified wrapped sum. Under the existing cross-epoch
`PrefixDiscipline`, two accepted candidates at one slot carry the same complete
context. Following an authority advance, restoring the same host manifest cannot
obtain a fresh authorization. The proof uses an inhabited, state-changing witness.

[SOURCE/DERIVED] The inherited full-word receipt has fixed-context classical-ROM
price `(t+14)*4160/2013265921^6`. `bad_release_implies_bad_descriptor` exposes the
event inclusion needed to use it. The price does not include adaptive multi-context
composition, a concrete cSHAKE reduction, QROM, input authentication, consensus,
durability or hiding. It is not a whole-resident security level or a private-state
knowledge/extraction theorem. See `formal/README.md` for exact theorem boundaries.

## Where private information and authority went

[DERIVED] Fresh private observations must come from a source outside the host's
knowledge and enter the protected computation without an exposed writer/read-all
credential. Unknown initialization or development randomness can also contribute
private information. Public encryption coins alone do not. None of those ingress/
entropy mechanisms is instantiated here; the public arithmetic witness has no
unknown state or random input.

[DERIVED] The most restrictive remaining assumption is a release mechanism that
both completely mediates outward decryption and remains restricted when all its
claimed-untrusted software artifacts are exposed. An ordinary helper containing
the FHE secret key fails that condition. The keyless continuity authority can
govern release without reading the resident, but does not make a decryption helper
unreadable. Its own mutable state must additionally resist rollback and races.

[REFUTED: audited plain writer deployment] The GKS23 writer credential gives a
correctness-based recovery path. Restricting the writer to a separate custodian
changes the threat model; it does not eliminate that authority. [OPEN] No new
software-only A/B construction closes this seam. Tier C/D remain explicit controls.

## Proposed corrections for the maintainer, without editing VERDICTS

[DERIVED] Add the explicit distinction “finalized historically” versus “eligible
for fresh release now”; the new restore theorem composes the latter from independent
prefix/head/consumption checks. Keep complete mediation, durable atomicity, private
inputs and entropy as separately named obligations.

[DERIVED] Narrow two phrases in the companion/lane notes. A fixed Step can accept
new observations as data; static functions alone do not prove recurrent closure
impossible. Lack of function hiding does not itself prove recovery of the function's
entire representation. The stronger credential failure stands on the explicit
writer path, without either overstatement. General-circuit PCE closure inherits
the reported iO obligation; no lower bound for every restricted Step was proved here.

## Verification and next decision

[EXECUTED evidence] `experiments/results/` retains commands, stdout/stderr, source
hashes, successful tests and failed Lean attempts. The latest successful Lean logs
check the pinned sources. `patch_review.json` records staged umbrella elaboration,
import-boundary check, patch applicability and CSV checks. The companion patch is
provided for maintainer folding, with root imports; it has not been applied.

[DERIVED next decision] The smallest useful integration is to replace the public
adapter's empty rootWrites with an existing materialized cell/DataIntent and prove
that accepted receipt next state is exactly the installed root, with atomic
consumption/retry behavior. This can establish a stronger actual integrity path.
It cannot by itself change the A/B privacy verdict: that requires a concrete
restricted-release/private-input mechanism whose full credential exposure survives.
`NEXT.md` separates these decisive tasks.
