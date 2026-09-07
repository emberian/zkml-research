# Independent review of the adaptive fixed-span lemma

[DERIVED verdict; 2026-09-07] **Accept the conditional algebraic privacy
lemma and its padded adaptive-hybrid bound.** The chosen setup map is
invertible, supplies exactly the two issued key scalars, and is independent
of future challenge messages. The uniform-C argument remains valid for
messages chosen from the actual preceding transcript. No blocking algebraic
or hybrid error was found.

[DERIVED qualifications to fold] Make two routine game branches explicit:
return a fair bit when the selected request is never reached, and define a
common abort for inadmissible pairs or require admissibility on every
transcript reachable by the reduction. Also qualify the term **strict PPT**:
power-of-two padding makes *rank selection* a bounded fair-bit algorithm;
exact uniform scalar sampling remains a separate group-model convention.
The exact `Delta <= 2M epsilon_DDH` statement is accepted with the ordinary
ideal exact group-sampling convention. A literal bounded fair-bit machine
needs a sampler failure term, described below. Python `secrets.randbelow`
does not establish a strict worst-case runtime bound.

[EXECUTED frozen target] Reviewed
`experiments/private_construction/fixed_span/ADAPTIVE_FIXED_SPAN.md`, SHA-256
`091403d6f3e1a7a65e5baef3977dc789595584582d17bbbf2190878fa18874d9`.
The author note, scripts, saved result and synthetic fixtures remain
unchanged. `results.json` preserves complete before/after hashes. No author
source, shared ledger or companion was edited, and no commit was made.

## 1. Exact setup and one-challenge proof

[DERIVED] Let `y0=(1,1,0)`, `y1=(0,1,1)` and `w=(1,-1,1)` over the prime
field Z_q. A difference d is orthogonal to both issued vectors exactly when
`d=(d0,-d0,d0)=d0*w`. No inverse of 2, 3 or the squared norm of w is used.

[DERIVED] The map

```text
(t0,t1,a) -> (t0+a,t1-a,a)
```

[DERIVED] has inverse `(s0,s1,s2) -> (s0-s2,s1+s2,s2)`. Thus independent
uniform t0,t1,a produce an exactly uniform master vector s. The exposed
scalars are `dot(y0,s)=t0+t1` and `dot(y1,s)=t1`. The public group elements
are exactly `g^s`. Their correlations with the exposed scalars are part of
this identity; the proof does not assume the keys are independent of mpk.

[DERIVED] For a real DDH tuple, substitution of `B=g^b` and `C=g^(ab)` into
the proposed challenge gives

```text
(g^b, g^((t0+a)b+x0), g^((t1-a)b+x1), g^(ab+x2)),
```

[DERIVED] which is exactly ordinary encryption with fresh scalar b. In the
independent DDH world, fix the public setup, the entire preceding transcript,
and B. The selected pair is already determined before C is used. For
`right-left=k*w`, the bijection `C -> C*g^(-k)` carries the right ciphertext
to the left ciphertext. It preserves the uniform measure. Consequently the
whole selected ciphertext has the same conditional law on either side.

[DERIVED] The selected B and C must remain unused before this request. The
construction does so: preceding requests use ordinary public encryption
with separately sampled coins. Later requests may depend arbitrarily on
the selected ciphertext, but the same efficient continuation applied to
equal distributions cannot distinguish the hidden selection bit. No
rewinding, guessing a future message, or conditioning on an efficiently
recognizable equivalence event is needed. Equivalence is itself the public
linear test `Y*left=Y*right`.

[DERIVED] For a single pair, if A outputs a bit Z and the reduction outputs
`[Z=mu]`, its real-DDH success probability is
`(1-Pr[Z=1|mu=0]+Pr[Z=1|mu=1])/2`; its independent-DDH success is exactly
1/2. The absolute DDH event gap is therefore Delta/2. The note's constant
uses the absolute event-gap convention, not an unconverted guessing
advantage convention.

[EXECUTED] Independent finite checks cover 495 setup-map and key identities,
495 kernel equivalences, 3,107 real-DDH ciphertext identities, and 20,175
conditional uniform-C multiset equalities in groups of orders 3, 5 and 7.
Every translation identity is checked pointwise as well. These small groups
serve only to verify equations and distributions; no DDH hardness or
privacy strength is attributed to them.

## 2. The adaptive multi-input reduction and its two edge branches

[DERIVED] Define H_j to answer the first j requests with side 0 and all
remaining requests with side 1, and let `p_j=Pr[A outputs 1 in H_j]`.
Sample a rank r uniformly in the padded set `{1,...,M}`. Before rank r,
answer side 0; after rank r, answer side 1. At r, use the single DDH
embedding with a fresh fair mu. This simulation executes A exactly once,
and every pair is chosen from that simulation's actual transcript.

[DERIVED] When `r<=T`, the two real-DDH branches are exactly H_r and H_(r-1).
The signed difference between the reduction's real-DDH success and 1/2 is
`(p_(r-1)-p_r)/2`. Summing these signed quantities before taking absolute
values gives

```text
Pr[D(real DDH)=1] - 1/2 = (p_0-p_T)/(2M).
```

[DERIVED] This is a single uniform rank-mixture reduction. It does not
select a favorable hybrid nonuniformly or replace the signed sum by an
unjustified sum of absolute gaps. The adjacent hybrids can have different
signs without affecting the identity. Therefore the exact conditional bound
is `Delta_total <= 2M epsilon_DDH`. For `T>0`, `T<=M<2T`; T=12 gives M=16
and coefficient 32. T=0 has no hidden-bit-dependent reply and Delta=0.

[DERIVED missing-rank completion] Because the game permits **at most** T
requests, even a rank below T may never be reached. Such a run must return
an independent fair bit, just as a padded dummy rank does. Equivalently,
draw mu up front and compare it with the final adversary bit; if the target
request never occurs, mu has not influenced any interaction. This branch
then has success 1/2. It does not introduce an extra loss. The frozen note
explicitly handles padded dummy ranks but should also name this branch.

[DERIVED admissibility completion] Specify either that all-transcript
admissibility holds for A, including in intermediate/random-DDH games, or
have the LR interface test each pair and halt on failure with one fixed
public output in both hidden-bit worlds. Merely requiring valid pairs in
the two honest endpoint games leaves the intermediate oracle behavior
unstated. The public linear test makes the standard common-abort completion
efficient. It preserves the simulation and the bound; it supplies no extra
secret oracle or protected runtime validator.

[EXECUTED nonvacuous adaptive control] The independent T=3, M=4 finite
control chooses pairs from mpk, the issued keys, and the actual prior
ciphertexts. A public ciphertext condition can stop the transcript early.
The four hybrid event probabilities are

```text
370/729, 112/243, 341/729, 380/729.
```

[EXECUTED] These give a nonzero endpoint gap `10/729` with intermediate
increments of both signs. The complete rank-mixture DDH experiment returns
probability `1453/2916` in the real world and `1/2` in the independent world:
its gap is exactly `(10/729)/(2*4)`. The enumeration includes 7,290 real and
21,870 independent-world dummy/unreached selections. Events inspect public
ciphertext encodings; no state recovery or extraction procedure is run.

## 3. What the strict-PPT wording needs

[DERIVED] Sampling a padded rank uses exactly log2(M) fair bits, as claimed.
The initial t0,t1 and ordinary encryption scalars still have to be sampled
uniformly in Z_q. When q is an odd prime, no fixed finite number of fair
bits produces an exactly uniform q-valued output without a failure or an
additional sampling primitive. Exact rejection sampling has expected
polynomial time. This is a model distinction, not a failure of the group
algebra or the adaptive basis.

[DERIVED] One literal strict-machine completion caps each scalar draw at K
trials of ceil(log2 q) fair bits, accepts a trial below q, and otherwise
aborts with a fair output. Each draw fails with probability less than
`2^-K`. There are at most T+2 reduction-owned scalar draws: two masks and at
most T ordinary encryptions. Coupling against exact sampling gives
`delta_samp <= (T+2)*2^-K` per DDH world, hence the conservative bound

```text
Delta_total <= 2M * (epsilon_DDH + 2*delta_samp).
```

[DERIVED] This is one sufficient explicit completion, not a claim that this
extra term is optimal. If exact uniform scalar sampling is part of the
abstract group interface, the original exact `2M epsilon_DDH` formula is
unchanged. Concrete scalar-sampling costs and adversary runtime belong in
the stated reduction resources. The Python implementation uses rejection
sampling and variable-time arithmetic, so the padded-rank sentence should
not be read as a strict worst-case runtime proof for that implementation.

## 4. Exposed-package, window and lifetime scope

[DERIVED] The postprocessing claim is valid for every efficient operation
on the public key, both scalar keys, all received ciphertexts, and public
auxiliary randomness: arbitrary derived span keys, group-valued reads,
ciphertext products/inverses, retained snapshots, and a polynomial number
of adaptive window operations. All are available locally to the host.
No new independently directed key or master-correlated credential is
generated by this simulation. An initial auxiliary view correlated with
the hidden setup beyond the supplied package would require its own joint
argument.

[DERIVED] Every challenged input pair must agree on both projections.
Equality of only final or current window answers is insufficient. In
particular, expiration changes the live queue but does not revoke the
holder's old ciphertexts or its ability to read their two projections.
The correct protected object is an equivalence class of entire admissible
input histories modulo the fixed span. The proof is IND security for this
game; it is not a general simulation-based, recipient-only, forward-private
or continuity theorem.

[DERIVED] The supported algebra admits arbitrary finite sequences of
insertions/removals without a ciphertext-noise budget. The privacy reduction
allows a public polynomial upper bound T in a cryptographic group family.
That does not establish secrecy against an unbounded lifetime adversary or
give a numerical security level for one fixed 2048-bit group. There is no
post-quantum claim. Source uniform-randomness and honest-erasure assumptions
are not hardware or operating-system erasure guarantees.

[SOURCE / DERIVED implementation read] `span.py` imports only reference
equations from `additive_ipfe.py`; it does not call that module's guarded
main. The three CLI modes export public group elements and two projection
scalars, issue fresh ciphertexts using the public key, and evaluate the
four-item queue. Exact removal multiplies by the inverse of the actual
expired ciphertext, so the aggregate equals the product of the current
queue. Loading checks fixed framing, subgroup membership and that same
aggregate equality. It does not authenticate a checkpoint, prove its age,
prove honest bounded input issuance, or impose external finality.

[DERIVED] For honest coordinates in [-2,2], each two-coordinate projection
of at most four inputs lies in [-16,16]. The 33-entry decoder is injective
in the selected large-order group. The keys nevertheless allow
group-valued outputs and every span combination on arbitrary ciphertexts;
the decoder interval is not an enforced leakage gate. The positive fixture
demonstrates changing projection outputs and both classifier values while
preserving the designated history equivalence. It does not demonstrate a
nonlinear hidden transition or neural utility.

[EXECUTED] The approved **positive** `audit.py` was rerun from byte-identical
copies under this review's ignored `reference/` directory. All 13 checked
semantic result fields match the author's saved results, including 48
projection-output comparisons, 24 exact queue-product checks, 16 expirations,
two continuations and a 5,140-byte framed checkpoint. Fresh timing samples
are retained only as new local measurements. Initializer/issuer/evaluator
process arguments demonstrate the intended interface separation; they do
not prove OS isolation, erased process memory or excluded issuer timing
channels. The old `additive_ipfe.main()` and its earlier experiments were
not executed.

## 5. Primary-source attribution and reproduction

[SOURCE] Abdalla–Bourse–De Caro–Pointcheval,
[Simple Functional Encryption Schemes for Inner Products](https://eprint.iacr.org/2015/017),
local PDF SHA-256
`353f454857a5ef421ab7b17545b9657f5d192dc0a37f022cca7b71e916f84712`.
A fresh local extraction is pinned with SHA-256
`2f15d7761a28d7337214d6f7b30d2029017cf62767981fa87c0aa0e41c1094c6`.
Read scope: §2.3 and Figure 2 on PDF pp.6–7; DDH definition and Construction
3.1 on pp.7–8; Theorem 3.2 and its sketch on pp.8–9. The source explicitly
states selective IND-FE-CPA and constructs its setup basis using the
challenge-message difference. Its decryption equations first produce the
group-valued inner product and need a bounded efficient discrete-log
decoding regime for integer outputs.

[DERIVED] The new note properly attributes its stronger fixed-span adaptive
statement to its own direct proof, rather than to Theorem 3.2. The direct
fixed map above removes the selective challenge dependency for precisely
this key family; it does not prove general adaptively chosen independent
function-key security for the source scheme.

[EXECUTED] Reproduce in the owned review directory from the repository root:

```sh
pdftotext -layout /Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/017.pdf research/learn_infer_only/experiments/adversarial_review/fixed_span/extracts/2015-017.txt
python3 -B research/learn_infer_only/experiments/adversarial_review/fixed_span/review.py > research/learn_infer_only/experiments/adversarial_review/fixed_span/stdout.txt
```

[EXECUTED] `results.json`/`stdout.txt` preserve the independent exact controls,
command, Python version, review-code hash, positive-audit command and all
source hashes. The isolated audit's stdout/stderr and full replay result
are retained. `review_manifest.json` pins delivered files and the replay
result. Accounting: zero Scry, Kagi or web queries, one local PDF extraction,
zero PDF downloads, zero recovery/extraction experiments. No recursive
agents were used.

[OPEN bounded follow-through] Fold the unreachable-rank and invalid-pair
branches into the theorem statement, qualify strict sampling as above, and
record this independent acceptance. The README's old in-progress paragraph
can then be updated by its owner. No additional reduction or construction
claim is required to preserve the correctly scoped positive result.
