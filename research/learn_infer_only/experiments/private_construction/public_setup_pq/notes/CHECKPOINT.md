# Public setup/PQ source tranche checkpoint

[EXECUTED, 2026-09-08] Read the prior LWE/RLWE audit and the accepted DDH
public-coin proposal/review before route analysis. No cryptographic, runtime,
attack, disclosure/routing or malformed-input work is planned or performed.
Own only this new directory; shared ledgers and companion trees remain untouched.

[SOURCE/DERIVED baseline] The DDH proof uses two exact facts: recipient masks
are translation-invariant uniform field elements, and free public group samples
admit an efficient conditional transcript sampler without computing their logs.
ALS LWE instead uses a prescribed short-secret distribution and publishes its
linear image; RLWE adds prescribed secret/error widths. Arbitrary finite-field
pivot solving need not preserve these distributions or their correctness bounds.
This is a premise to audit, not yet a general lattice obstruction.

[DERIVED completed draft] AUDIT.md gives a positive fixed-policy construction:
a public invertible message-basis change, independent recipient Gaussian rows,
and directly uniform public syndromes for the remaining coordinates. ALS
Appendix C Lemma10 bounds the complete joint setup distance by
(d−r)·2^−Ω(n), including every recipient key and accepted public setup coins.
The construction retains the full state, finite-noise bounds and per-input span.
Independent sampling of arbitrary overlapping YZ fails a covariance check,
but moving the basis change to the plaintext avoids that Gaussian-fiber issue.
The conditional theorem explicitly leaves the source QPT proof scope open.

[SOURCE] Wee–Wu 2025/1039 supplies a second positive finding: transparent
registered access-control setup via decomposed LWE. This is not numeric IPFE.
The full Liu–Wang–Fu 2025 multi-authority lifecycle remains an unread source.

[EXECUTED final discovery counters] Web-search8; SQL4 submissions (2 capacity
errors, 2 successful retries); schema0/Kagi0. Successful rows4+1, reported spend0;
failed calls supplied no spend. Eight local PDF extracts, zero PDF downloads.
Provenance-only verification output is notes/pin_sources.stdout.json.

[OPEN handoff] Independent review of the joint setup/transcript theorem is
in flight. Next bounded tasks: source QPT reduction audit, concrete encoder-image
witness, and parameter/noise feasibility if adopted. No shared ledger, companion
tree or frozen capsule artifact was changed. Root owns STATUS/NEXT and commits.
