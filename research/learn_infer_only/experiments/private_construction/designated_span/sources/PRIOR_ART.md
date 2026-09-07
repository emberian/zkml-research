# Designated-span construction: bounded prior-art audit

Status: source audit complete, 2026-09-07. This note makes no novelty claim.
The reviewed local target is [the sibling review](../review/REVIEW.md), SHA-256
`a5e199591179cf81a4eb9b3754108eb68a7b1b3d8ba921c4d8b84fb42278d840`.
Source identities, access limitations, extracts, and query counts are pinned in
[sources.json](sources.json). No cryptographic runtime or extraction experiment
was performed in this tranche.

**[DERIVED]** Numeric functional proxy re-encryption is relevant prior art; it
must not be conflated with predicate-based inner-product PRE. Of the four
requested leads, the Feng author poster is the closest inspected example of
re-encrypting a numeric function result by subtracting a mask. The Luo preprint
provides an actual numeric IPFPRE game and construction, but delegates a vector
between FE key domains and excludes the recipient-key exposure of interest.
Neither source is being cited as a theorem for the local construction.

## The exact local target

**[SOURCE: local reviewed construction, §§1–2]** For fixed public rows
`y_i ∈ F_q^d`, let `k_i = <s,y_i>`, `h_j = g^{s_j}`, independently sample
dedicated recipient scalars `a_i`, and publish

```
A_i = g^{a_i},   τ_i = k_i − a_i,
C = (c_0,c_1,...,c_d) = (g^r,h_1^r g^{x_1},...,h_d^r g^{x_d}),
D_i(C) = (c_0, ∏_j c_j^{y_ij} / c_0^{τ_i})
       = (g^r,A_i^r g^{<x,y_i>}).
```

**[DERIVED: comparison criterion]** This is a *row-specific scalar* transform.
The input encryption algorithm is public and uses a fresh independent `r` on
each issuance. A recipient's dedicated scalar, combined with the public token,
reveals the ordinary IPFE row key `k_i = a_i + τ_i`. The intended coalition
claim therefore permits exactly the exposed rows' span; it does not promise
recipient-key secrecy after related rows have already been exposed.

**[SOURCE: local review, §§3–4]** The local review establishes an exact joint
view simulation from ordinary fixed-span IPFE by sampling all `τ_i` uniformly
and setting `A_i = (∏_j h_j^{y_ij}) / g^{τ_i}`. For an exposed row,
`a_i = k_i − τ_i`. Its principal game fixes the exposed recipient set before
secret setup and permits adaptive message pairs having equal exposed-row
values. Its adaptive-recipient extension has an explicit subset-guessing loss;
it is not a general polynomial-key adaptive FE theorem. Integer readout is
separate from group-valued correctness.

## 1. Kawai–Takashima: predicate PRE, not numeric IP output

**[SOURCE: construction and syntax]** Yutaka Kawai and Katsuyuki Takashima,
*Fully-Anonymous Functional Proxy-Re-Encryption*, ePrint 2013/318, inspected
local PDF dated October 11, 2013. The relation in §1.1 and §4 is
`R(v,x)=1 iff <v,x>=0`. Definition 3, printed p.8 / PDF p.9, encrypts a separate
payload `m` with an attribute `x`; re-encryption changes the attribute to `x'`.
Correctness recovers `m` when the original and destination predicates pass.
The §4.1–4.2 algorithms, printed pp.11–13 / PDF pp.12–14, use hidden basis
transformations and encrypt transformation matrices. They do not expose the
numeric value `<v,x>` as the decryption result.
[Primary record](https://eprint.iacr.org/2013/318).

**[DERIVED]** This lead establishes functional delegation terminology, but
does not instantiate the local numeric scalar-output interface or its
`τ_i=k_i−a_i` mechanism. This is a scope distinction, not a criticism of its
predicate-security theorem.

## 2. Feng et al.: close numeric masked-output prior art; poster access only

**[SOURCE: author poster, PDF p.1, “System Model”, “Construction of MI-FPRE”]**
Xinyu Feng, Qingni Shen, Cong Li, Yuejian Fang, and Zhonghai Wu,
*Privacy Preserving Federated Learning from Multi-Input Functional Proxy
Re-Encryption*, **ICASSP 2024**, DOI `10.1109/ICASSP48485.2024.10446283`.
The inspected [author poster](https://sigport.org/sites/default/files/docs/ICASSP__24___Poster___MI_FPRE%20%281%29.pdf)
uses secret client encryption vectors `ek_i=s_i`, public label hashing
`[μ_l]=H(l)∈G²`, and group encodings of `μ_l^T s_i+x_i`. A trusted noncolluding
KGC issues encryption and function keys. Re-encryption subtracts a key-dependent
mask from a weighted ciphertext sum. Recipients remove a residual mask to read
the numeric aggregate. The poster's formulas mix client/coordinate indices and
do not provide a complete security game.
[Conference record](https://cmsworkshops.com/ICASSP2024/view_paper.php?PaperNum=7767),
[author posting](https://sigport.org/documents/privacy-preserving-federated-learning-multi-input-functional-proxy-re-encryption).

**[DERIVED]** Abstracting those displayed masks as `v_i`, the intended algebra
has the form `Σ_i(v_i+x_i)y_i − [Σ_i v_i y_i − s'Σ_i v_i]`, leaving
`Σ_i x_i y_i + s'Σ_i v_i`. This is close conceptual prior art for masked numeric
function output. It does not identify the local static public scalar token:
the masks depend on labels and secret writer material. The poster alone does
not settle the recipient's complete auxiliary key material or joint collusion
conditions. These observations do not refute the full paper.

**[OPEN: source access]** The conference manuscript link redirected to IEEE
Xplore, which returned no paper body to this retrieval. Only the author poster
was inspected at algorithm level. The supplied “TIFS 2024” venue label is not
supported by the inspected metadata; the primary conference and poster identify
ICASSP 2024. No full-paper theorem is imported from this lead.

## 3. Luo et al.: numeric vector-domain re-encryption; narrower exposed-key game

**[SOURCE: syntax, game, construction]** Fucai Luo, Haiyan Wang, Willy Susilo,
and Weihong Han, *Public Trace-and-Revoke Proxy Re-encryption*, TechRxiv
`10.36227/techrxiv.21671849.v1`, posted December 11, 2022. Section 2.3, printed
pp.5–6 / PDF pp.6–7, supplies numeric IPFPRE: `FKeyGen(msk_j,x)` supports
arbitrary rows, while `ReKeyGen(pk_i,msk_i,pk_j)` takes no row. Re-encryption
preserves every destination inner product. Section 3, printed p.6 / PDF p.7,
uses LWE vector key switching. Definition 5 rejects honest-to-corrupted
re-encryption queries and disallows functional-key queries at honest
non-challenge users. Theorem 1, printed pp.7–8 / PDF pp.8–9, proves the stated
IND-CPA game. The inspected version is the 2022 preprint, not a silently
substituted final journal edition.
[Primary preprint copy](https://www.researchgate.net/publication/366187847_Public_Trace-and-Revoke_Proxy_Re-encryption/fulltext/63967447e42faa7e75b76f4d/Public-Trace-and-Revoke-Proxy-Re-encryption.pdf).

**[DERIVED]** Exposing the destination master permits basis-row keys and thus
whole-vector recovery by correctness. One could instead erase that master and
retain only designated destination function keys, but Definition 5 excludes
those non-challenge honest-user key queries. Consequently its theorem does not
establish that modified coalition game. This finding neither refutes the
modification nor substitutes a new security proof for it.

**[EXECUTED: access]** The supplied CloudFront PDF was initially readable through
web extraction but later failed retrieval. The same version's ResearchGate PDF
was readable through web extraction, including page-indexed algorithms/game.
Direct local retrieval returned HTTP 403. There is no local PDF hash for this
source; cached web excerpts have their own explicitly separate hashes.

## 4. Zhang–He–Shen: designation lead remains unresolved at algorithm level

**[SOURCE: primary abstract and metadata only]** Mingwu Zhang, Chao He, and Gang
Shen, *Identity-Based Key Verifiable Inner Product Functional Encryption
Scheme*, BlockTEA 2023 proceedings, published May 3, 2024, pp.3–22,
DOI `10.1007/978-3-031-60037-1_1`. The abstract discusses identifying designated
ciphertext recipients, limiting master-key information leakage, and verifying
decryption keys. The [publisher page](https://link.springer.com/chapter/10.1007/978-3-031-60037-1_1)
is an explicit subscription preview; the [EUDL record](https://eudl.eu/doi/10.1007/978-3-031-60037-1_1)
exposes the abstract, not the algorithms.

**[OPEN]** No primary full-text construction or game was accessed in this
bounded audit. It would be unjustified to identify its recipient mechanism with
`τ=k−a`, to deny that relationship, or to claim its theorem covers our coalition.
Search-engine text from an unrelated ebook upload was not adopted as verified
primary evidence. No request was sent to the authors and no access control was
bypassed.

## Consequence for the local claim and the next source read

**[DERIVED]** The defensible description is: a designated-output IPFE variant
whose stated coalition distribution is analyzed in this repository, with
related numeric functional PRE already in the literature. Its local proof
should remain attached to its exact algorithms, setup erasure, dedicated key
use, and static-span game. Replacing that proof citation with an unspecified
“functional PRE security” claim would lose the exposure conditions.

**[OPEN: bounded absence statement]** No inspected source theorem was matched
to the complete local package `{h,Y,A,τ,a_J}`, public repeated unknown-input
issuance, and the reviewed coalition game. The search corpus was two bounded
OpenAlex/Scry token queries plus focused web searches for the four supplied
leads; source reading reached the levels stated above. This is not an
exhaustive literature search and carries no novelty conclusion.

**[DERIVED: next action]** The most useful next source acquisition is the full
Feng ICASSP paper: resolve `RKGen`/recipient auxiliary material and its
corruption/label game against the complete exposed package. The identity-based
chapter remains a second access-limited lead. Neither requires changing the
local reviewed theorem while access remains incomplete.
