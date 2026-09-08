# Sources, instruments and retained computation

[EXECUTED, 2026-09-08] The source/math lane uses the paths below. Hashes are
in SOURCE_PINS.json. All existing construction files and the local PDF were
read-only. Full extracted PDF text is an ignored local reading aid, not a
new claimed result or a file to commit.

## Local proof inputs actually read

[SOURCE: full construction and proof] `../PROPOSAL.md` and
`../review/REVIEW.md`, particularly review lines 77–95 (full joint law),
111–138 (root simulator and chronology boundary), 155–181 (DDH and sampling
bound), and §§5–6 (rejection tape and malicious sampler boundary). The older
proposal's “pending review” wording is historical; the review accepts its
specified honest direct-sampling experiment. No old verdict was overwritten.

[SOURCE: full construction and game] `../../review/REVIEW.md`, §§1–4:
dedicated recipient masks, coalition view equivalence, adaptive LR game,
`2*M*epsilon_DDH`, and its conservative scalar sampling correction.

[SOURCE: complete direct reduction]
`../../../fixed_span/scaling/GENERAL_FIXED_SPAN.md`, lines 92–140:
uniform padded hybrid selection, signed averaging, adaptive messages,
common rejection, and the bounded scalar-sampler budget. The proposed ROM
reduction treats this local conditional result as its ordinary-IPFE lemma;
it does not reattribute the adaptive theorem to a paper.

[SOURCE: full existing bibliography note] `../sources/PRIOR_ART.md`, §4:
the prior lane already identified the regular preimage-sampling source below.
This run follows that lead; it does not claim discovery of the technique.

## Primary external material actually inspected

[SOURCE: local full paper, selected definition and reduction pages read]
Brier–Coron–Icart–Madore–Randriam–Tibouchi,
*Efficient Indifferentiable Hashing into Ordinary Elliptic Curves*,
[ePrint 2009/340](https://eprint.iacr.org/2009/340).
Read `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2009/340.pdf` using
`pdftotext -layout`. Definition 1, PDF p.4, gives regular finite-fiber
encodings with an efficient random-preimage sampler. Definition 4, PDF p.6,
generalizes regularity and sampling. Theorem 1 and simulator, PDF pp.7–8,
compare the joint group/lower-oracle systems by choosing preimages.

[DERIVED attribution boundary] Squaring `F_p*→QR_p` with random-sign square
roots instantiates the exact regular-preimage idea. Our joint recipient
registration, seed-index reduction, failure-tape lemma and prequery bound
are local derivations, not claims that this source proved the full scheme.

[SOURCE: official specification sections read]
[RFC 9380](https://www.rfc-editor.org/rfc/rfc9380.html#section-5),
§§2.2.5, 3.1, 5 and 10.5. The source specifies domain separation, wide
reduction for field hashing, an RFC-specific rejection-sampling prohibition,
and a conditional-preimage simulation sketch. It motivates precise oracle
and timing boundaries; this proposal is not an RFC 9380 suite.

[SOURCE: author-hosted abstract only]
Bellare–Rogaway, *Random Oracles are Practical: A Paradigm for Designing
Efficient Protocols*, CCS 1993,
[author page](https://web.cs.ucdavis.edu/~rogaway/papers/ro-abstract.html).
Only the abstract's distinction between an oracle-model protocol and later
function substitution was used. No reduction or concrete-hash theorem from
that paper was read or invoked.

## Query accounting

[EXECUTED] Two web **search queries**, in one batched tool call:

1. `site.rfc-editor.org/rfc/rfc9380 hash_to_field rejection sampling random oracle`
2. `site.cs.ucdavis.edu Rogaway random oracles practical paradigm designing efficient protocols 1993`

[EXECUTED] Two primary-page open operations (RFC HTML; Rogaway author
abstract), and two RFC find operations (`Implementors MUST NOT` and
`10.5. hash_to_field Security`). No failed web request. Scry SQL: zero;
Scry schema: zero; Kagi: zero; eprint HTTP/abstract/PDF requests: zero.
One PDF was read from the specified absolute mirror path. Search-result
PDF links were not opened or downloaded. One attempted read of a nonexistent
local `fixed_span/review/REVIEW.md` returned ENOENT; the actual dependency
was then read at `fixed_span/scaling/GENERAL_FIXED_SPAN.md`.

[DERIVED scope] The instrument is targeted web search plus the named local
proof files and one local primary PDF. This is not a literature survey.
No field-wide absence or novelty claim is made.

## Exact executed public arithmetic

[EXECUTED command, repository cwd]

```sh
python3 research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/public_seed/finite_witness.py > research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/public_seed/finite_witness.log
```

[EXECUTED output] Exit zero; retained JSON states
`all exact public arithmetic checks passed`. It exhausts the F7 accepted
joint law and the complete capped registry/tape law, including failures,
then checks a nontrivial kernel pair and two false shortcuts. The 54,
55,296, 3,072, 18, `31/256`, `1/3` and `5/9` values in PROPOSAL.md are
computed there. No crypto backend, private credential, ciphertext, extraction
experiment, adversarial endpoint or private runtime file is accessed.

[OPEN validation boundary] This is a proof draft with finite distribution
evidence, not a machine-checked theorem, full independent review, concrete
hash implementation or measured cryptographic protocol. The safety-stopped
tasks listed in the overnight brief were not accessed or resumed.
