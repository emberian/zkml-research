# Narrow predicate output and additive continuation

[DERIVED; 2026-09-06] A one-bit predicate key can hide more than an inner-product
value in a static encryption game. The audited lattice candidate supplies that
restricted public-encryption interface after honest setup erasure. It does not
also supply exact public updates to its hidden attribute. For sign predicates,
that extra update capability would contradict the unchanged static privacy game;
the corresponding dynamic interface itself can reveal bounded magnitude.

[EXECUTED] `python3 predicate_closure.py` records the semantic and algebraic
witnesses in `predicate_closure.stdout.txt` and `results/predicate_closure_results.json`.
No secure predicate-encryption implementation was built. Source paths, hashes,
access levels and search accounting are included in the result JSON.

## The exact update obstruction

[DERIVED] Let the issued predicate be `P(z)=[z≥0]`, and suppose a public update
algorithm converts an encryption of z into a valid encryption of z+u. Initial
states1 and2 agree under P. Public update−2 produces states−1 and0, whose predicate
bits differ. Therefore the original static full-attribute-hiding challenge, which
admits that pair and its P key, is distinguishable after this public computation.
This only refutes combining **that game** with **that update family**. A dynamic
game may instead require equality under every permitted future predicate trace.

[SOURCE: HPE syntax/game inspected] Clear–Hughes–Tewari,
[*Homomorphic Encryption with Access Policies*](https://arxiv.org/abs/1302.1192v2),
§3, PDF pp.5–7, states the matching necessary condition in Eq.(3.3):
predicate equivalence must be preserved by public attribute operations. Its
non-monotone discussion allows stronger challenge restrictions that account for
future transitions. §4 pp.7–8 discusses independently blinded KSW/AFV aggregation,
which preserves conjunction-style access with overwhelming probability, rather
than an exact known sum of the unblinded attribute vectors.

[EXECUTED] All256 initial scores in [−128,127] are recovered with eight sign
observations, each preceded by a known additive update. At threshold t, set the
current offset to−t and observe `[z−t≥0]`; binary search determines z. The test
uses incremental offset differences, so restoration is unnecessary. Every tested
state lies in [−255,255]. This is an ideal-interface result, not a cryptographic
attack or a claim about an arbitrary neural classifier.

[DERIVED] Replacing a projection release with a sign release does not preserve
hidden magnitude when arbitrary threshold-shifting updates remain available.
Private input ciphertexts are also subject to every exposed public operation and
the predicate key; the same threshold search can read their bounded projection
before any proposed receipt. Continuity alone does not fix this no-fork witness.

[EXECUTED positive control] Parity equivalence is preserved under arbitrary
addition: 2,048 tested equal-parity state pairs/update choices keep the same bit.
ALS2015/608's already-audited modular IPFE with p=2 is a source-conditional linear
class-output positive. It is not a sign classifier or hidden nonlinear learner;
fresh encrypted inputs retain the existing noise and ingress-projection limits.

## Actual narrower static primitive: one-key fully hiding predicate encryption

[SOURCE: algorithms/game/theorem statement read] Wang–Wang–Lai–Wang,
[*Predicate Encryption from Lattices: Enhanced Compactness and Refined Functionality*](https://eprint.iacr.org/2025/361),
Construction1 pp.14–15 and Theorem3.1 p.16, provides `(1,poly)-sel-SIM` full
attribute hiding under LWE: at most one authorized pre-challenge key and
polynomially many unauthorized keys. Definition2 pp.13–14 specifies the simulator
and selective attribute timing. The complete reduction was not audited here.

[DERIVED static candidate] Fix a bounded-depth circuit f with decryption allowed
when f(x)=0, and use constant payload0. Issue only `K_f` at setup. Publicly encrypt
fresh x and read success0 versus failure⊥ as one class bit. The setup trapdoor can
then be erased. The source's full attribute-hiding claim is relevant on both
class outcomes, unlike a weak-only game. This gives a narrower source-conditional
static output than exposed IPFE magnitude, with public input issuance and no online
writer master. It is not a closed evolving encrypted state construction.

[SOURCE syntax] Let `G` be the gadget matrix and `Gbar` its upper n rows. With
`m=(n+1)log q`, `L=ℓ(n+1)^2 log²q`, setup creates a trapdoor for B and publishes
`(B,{B_j}_{j≤L},P)`. Its master secret is that trapdoor. A function key is a short
matrix `K_f` satisfying `[B|B_fhat]K_f=P`, generated using the trapdoor and a
Gaussian masking matrix J. Encryption independently samples s,e,e′ and forms:

```text
β0 = B^T s + e
Ψ_i = [ B ; s^T B+e^T ] R_i + x_i G
ψ = bit-representation of (Ψ_i)_i
κ = P^T s + e′ + payload encoding
c_j = (B_j + ψ_j Gbar)^T s + W_j^T e
ct = ((Ψ_i)_i, β0, κ, (c_j)_j)
```

[SOURCE] Decryption homomorphically evaluates f on the inner Ψ, evaluates the
corresponding outer attribute encodings, and combines them with K_f. The same
secret s participates in both layers; Lemma2.8 pp.10–11 identifies `(s,−1)` as
the inner GSW decryption secret. No public state-update algorithm is included in
Construction1. `HEval` inside Dec is not itself a new complete PE ciphertext.

[DERIVED closure seam] Applying an additive circuit to Ψ changes its public bit
representation ψ. The old c_j then encode the old bits. Keeping s fixed, a natural
repair would add `(ψ′_j−ψ_j)Gbar^T s` to each c_j. Publishing the exact repair
helper `Gbar^T s` reveals every component of s through the gadget's identity
columns; `(s,−1)` then decrypts every inner attribute bit. This refutes that
particular repair helper as a no-read-all credential, not every possible compiler.

[EXECUTED equation witness] A deliberately insecure q257,n2 gadget example shows
that changing the inner bit while keeping its outer encoding makes the required
encoding relation fail. The proposed helper restores that relation and also
recovers the entire secret `(17,29)`. It then decrypts all six inner attribute bits
`[1,0,1,1,0,0]`. This implements the source equations with small chosen errors;
it is not a secure LWE instance or an executed attack on a deployed system.

[SOURCE detail] Printed Dec step3 tests all m rounded coordinates for zero, while
the following correctness paragraph requires only the first m−1 coordinates.
The candidate here deliberately fixes payload0, for which this particular mismatch
does not affect the predicate-only reading. Payload1 behavior needs clarification
before treating the printed general-payload pseudocode as executable evidence.

| [DERIVED] surviving artifact | capability / required erasure |
|---|---|
| B trapdoor/master key | issues arbitrary predicate keys; erase after fixed-key issuance |
| fixed K_f and mpk | reads the chosen predicate on any publicly encrypted input |
| encryption-local s,e,R_i and plaintext x | issuer can read that input; erase if later issuer exposure must hide it |
| inner Ψ without matching new c_j | incomplete updated representation, not another PE ciphertext |
| proposed exact Gbar^T s helper | reveals inner decryption secret and all encoded attribute bits |
| saved PE ciphertexts | repeat evaluations and forks; no finality or receipt binding |

## KSW: genuine predicate-only keys, but aggregation is not vector addition

[SOURCE: full algorithms/correctness read] Katz–Sahai–Waters,
[*Predicate Encryption Supporting Disjunctions, Polynomial Equations, and Inner Products*](https://eprint.iacr.org/2007/404),
§4.2 pp.7–8 constructs predicate-only inner-product PE. Setup uses composite-order
bilinear groups; the public key contains `g_p,g_r,Q=g_q R0,H1_i,H2_i`. The master
includes factorization p,q,r, subgroup generator g_q and hidden h terms. Public
Enc samples fresh s,α,β, with components `C0=g_p^s`,
`C1_i=H1_i^s Q^(αx_i) R3_i`, `C2_i=H2_i^s Q^(βx_i) R4_i`.
Its fixed predicate key yields a pairing product
`D=e(g_q,g_q)^((αf1+βf2)<v,x>)`; Dec tests D=1. The class is zero inner product,
not sign, and the source assumptions are not post-quantum.

[DERIVED] Honest setup can issue one v key and erase the master; encryption still
needs only public parameters. But multiplying independently produced ciphertexts
gives exponent `σ1<v,x1>+σ2<v,x2>`, where each σ comes from that ciphertext's
independent blinding. It does not give `σ<v,x1+x2>` for a shared known σ.
Two inputs with scores1 and−1 can therefore have zero clear sum while their
aggregate predicate rejects. Changing polynomial depth does not repair this
semantic mismatch. Same-attribute multiplication is a different supported case.

[EXECUTED] With toy q101 and effective masks26/38, scores1 and−1 give aggregate
phase89, hence rejection despite zero clear sum. Exhausting 10,201 mask pairs gives
101 accidental acceptances, illustrating the source's 1/q cancellation event.
The toy q is deliberately small; this is an exponent identity, not instantiated
pairing encryption or an estimate of secure-parameter failure probability.

[DERIVED repair limit] For public known updates, an initializer might additionally
provide `Q^α,Q^β` so each coordinate can be translated. For v=(1,1,0,…), pairing
those helpers with its first key components exposes
`T=e(g_q,g_q)^(αf1+βf2)`. The old predicate product is then `D=T^<v,x>`: bounded
candidate testing recovers magnitude. The modified construction has no inherited
KSW full-hiding theorem. [EXECUTED] A toy order101 subgroup recovers all41 scores
in [−20,20] from T,D. No claim of full-vector extraction follows from this one key.

## Nearby names that do not supply the missing restriction

[SOURCE / DERIVED] Brakerski–Cash–Tsabary–Wee,
[*Targeted Homomorphic Attribute Based Encryption*](https://eprint.iacr.org/2016/691),
Definitions2.1–2.3 pp.7–8 and construction pp.11–13, makes the policy f govern
which **public attributes** may be used. Evaluation takes a separate arbitrary
function g. The ciphertext explicitly includes x; the policy key can decrypt
the identity computation on every permitted payload. Fixing f does not restrict
g to sign/class, so exposing that key exposes the original admitted payloads.
Setup erasure and public encryption are possible, but do not remove this read
capability. The source's selective ABE game deliberately excludes authorized
keys from challenge confidentiality; it does not promise the proposed restriction.

[SOURCE / DERIVED] GVW,
[*Predicate Encryption for Circuits from LWE*](https://eprint.iacr.org/2015/029),
§4.1 pp.21–22, publicly encrypts using a freshly sampled inner FHE secret key,
which becomes a hidden attribute of a partially hiding PE ciphertext. Its release
key enumerates possible decryption-phase values. §1.3 p.5 explicitly says that
this approach reveals the exact phase and does not provide full attribute hiding.
Thus weak PE alone is insufficient evidence for a one-bit-only successful release.
The2025 bounded-key construction above is a materially stronger static candidate;
these are different algorithms and guarantees.

## Decision, accounting and next question

[DERIVED] Keep one-key fully hiding PE as a narrower **static** positive and the
specific ciphertext-repair helper as a scoped failure. For additive sign/class
learning, first state the full trace equivalence and useful surviving classes.
Neither an HPE name nor an FHE subroutine establishes closed attribute updates.

[OPEN next construction] For a finite command alphabet, preissue randomized FE
keys `F_cmd(s)=(Enc_FE(pk,Step(s,cmd)),answer)` and erase the master. Audit whether
same-scheme encryption fits the supported circuit class without a self-embedding
circuit-size recurrence, and whether the randomized-FE game admits computationally
encrypted outputs rather than demanding equal plaintext-output distributions.
Compact general FE/iO may give a conditional positive; it is not established here.

[EXECUTED accounting] Four new Scry SQL queries, zero new schema calls; lane total
seven SQL plus one schema, Kagi0. Fifteen new web search queries, cumulative26.
Primary algorithm reads used the absolute local mirror for four ePrint PDFs;
arXiv1302.1192v2 was fetched from arXiv and hashed locally. No ePrint PDF downloaded.
The checked corpus is these five named papers and recorded discovery queries;
no field-wide absence claim is made. Full paper extracts/PDFs stay git-ignored.
