# Independent review of the smudged fixed-coordinate variant

[DERIVED verdict, 2026-09-08] **Accepted within the stated conditional scope.**
The frozen variant has a sound joint setup comparison and fixed-coalition,
classical-interface confidentiality proof through uniform interval smudging,
ordinary QPT-LWE, and augmented Gaussian syndrome regularity. It supports the
entire finite-field input space through a bijective centered basis transform
and the stated bounded integer additions, exact expiry, and offsets. This is
an independent source/math review of a new restricted theorem, not approval
of a published general-functional-key theorem at these parameters, a concrete
security level, or cryptographic execution.

[DERIVED scope] This review covers `SMUDGED_FIXED_COORDINATE.md` §§1–5 and
the HYL construction, decoder, parameter and comparison claims in `AUDIT.md`
§§1–4. The adjacent-source triage in `AUDIT.md` §5 is preserved and hash-checked,
but is not independently approved by this bounded review. No author file was
edited; comments about advice, private encryption coins, offset bounds, and
strict key storage were incorporated by the author before the reviewed freeze.

## 1. Frozen subjects and primary evidence

[EXECUTED] All paths below are relative to
`research/learn_infer_only/experiments/private_construction/public_setup_pq/alternatives/`.
The checker pins exact bytes before and after its arithmetic.

| Subject | SHA-256 |
|---|---|
| `SMUDGED_FIXED_COORDINATE.md` | `a7f98b9f17b0e9b37537ca763697f7a9235df498364df4e0dd774f293d9b9327` |
| `AUDIT.md` | `593faaffcd84f2bade468d9e570a3e2dd3d11eafc76b46ec71b046d22d884307` |
| `results.json` | `75d69f3c18d502a2761a9b4acab3924c0d18bbd38ca16375ee98dab3b63aae54` |
| `MANIFEST.json` | `0bf70a6a12442a02f3fced956a456722985d8279ee651e299a501fdff3741654` |

[SOURCE] Han–Yi–Liu–Gu (HYL), *Tightly Secure Inner-Product Functional
Encryption Revisited: Compact, Lattice-based, and More*, ePrint 2025/1613,
local mirror `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/1613.pdf`,
SHA-256 `3d5d47484e6e8b75c7d747eeb654559093cf06f7680ba1253a8a4958e6ccdc2e`.
Read Defs.1–2/Fig.1 pp17–18, LWE/Gaussian conventions and Lemmas1–2 p24,
Fig.4 and public/private evaluation pp25–26, Theorems2–4 pp26–27, Fig.6 p28,
Corollary1 and Table2 p29. Rendered and visually inspected pp24,27–29; the
root placement in Theorem3 is `σK ≥ sqrt(d) X l′` after renaming dimension.

[SOURCE] Micciancio–Peikert, ePrint 2011/501, local mirror, SHA-256
`bf1160f088825ed28c343b299f5bc2acdca41cc50293310a03a4506d2fdbdb84`,
Definition2.2, Lemma2.3 and Lemma2.4/equation(2.1), pp12–13. Gentry–Peikert–
Vaikuntanathan, ePrint 2007/432, SHA-256
`7e747881cddd16b7dcf82893682cb9b4c788d7cec5712f80aa4193f2bd30a5b3`,
Definition2.5/Corollary2.8 pp10–11 and quotient/syndrome isomorphism in
Lemma5.2 p18. Their exact local text and rendered pages were already read
in this reviewer's preceding finite-regularity review and are reused here.

[SOURCE/DERIVED] The reused explicit bound is
`adversarial_review/public_setup_pq/quantitative_regularity/BOUND.md`,
SHA-256 `b07d7714ca6078a63bf1281ad8edbd07dc39094d91f6808e1c3868a3503dc2e5`.
This reviewer independently accepted its general expectation and joint-row
derivation in `adversarial_review/pq_finite_costs/REPORT.md`; the present
application uses that general bound, not its stronger-height simple certificate.

## 2. Exact law, credentials, and setup comparison

[DERIVED] In row convention the public matrix is `A∈F_q^(l×n)`, with `P`
having `d` rows. Every actual recipient independently draws an integer row
`k_i←D_(Z^l,σK)` and publishes `P_i=k_i A`. Only `r` such rows are generated.
Other public rows are directly uniform. This is an honest independent
registration theorem; arbitrary malicious rows and proofs of correct sampling
are not supplied. Recipients' integer rows are actual reusable read credentials.

[DERIVED] In the comparison experiment all `d` Gaussian rows are independently
sampled. Conditional on `A`, the exposed recipient rows and their products
come from the same kernel in both experiments. The hidden Gaussian syndromes
can therefore be replaced while retaining **all** `k_[r]`, not merely one
recipient or the eventually chosen coalition. Their shared `A` is kept in the
joint tuple; no arbitrary conditioning on a fixed unusually bad `A` or public
syndrome is performed. The setup bound is `δ_(d−r)(n)`, and switching setup
at the two endpoints of a distinguishing game costs twice that amount.

[DERIVED] For a prime `q`, the MP expectation and GPV quotient result give

```text
ηZ = sqrt(ln(2l(1+1/ε0))/π),       t=ηZ/σK<1,
S_N = (q^N−1) max(q^−1,t)^l,
R_N = (1+ε0)(1+S_N)−1,
δ_h(N) ≤ min(1, ρ_N+2hR_N),      ρ_N < q^(N−l)/(q−1).
```

[DERIVED] The prime specialization counts `q^N−1` nonzero dual cosets.
On a surjective matrix, the conditional row distance is at most twice its
dual Gaussian mass. Sum over independent rows, average over `A`, and pay
rank failure **once for the full tuple**. This retains exposed rows through
a common conditional kernel. The argument is an average joint law, not
prime-field hashing of arbitrary short-secret distributions. Gaussian mass
uses `exp(−πz²/σ²)` and its actual integer normalizer throughout.

[DERIVED] Accepted public sampling outputs and copies of them are already
functions of `A,P`. Revealing a sampler seed, rejection history, or other tape
needs its own conditional simulation argument. The absent comparison rows'
sampling tapes are neither generated in actual setup nor exposed in the game.
The distributional comparison supplies an honest full-state key image up to
its statistical error; it does not give an efficient method to recover a
missing row from a public syndrome or a pointwise guarantee after grinding.

## 3. Smudging, LWE, and adaptive masking

[DERIVED] Write `a(x)=center_p(Bx)`. For a fixed coalition `J⊆[r]`, equality
`Y_J x0=Y_J x1` over `F_p` is exactly equality of the centered integers
`a_J(x0)=a_J(x1)`. The game can expose entire integer rows `k_J` at setup.
It has no private decryption oracle or new-key/adaptive-corruption interface;
the adaptive challenge pairs and other public computations use classical
interfaces, while adversarial internal state may be quantum.

[DERIVED] In the full-Gaussian setup, an honest target has
`c=Aw+e` and `h=KA w+f+Δa`. Its private-evaluation replacement is
`h=Kc+f+Δa`. For a fixed integer shift `v`, the exact interval identity is

```text
TV(Unif{−F,…,F}, Unif{−F,…,F}+v) = min(1, |v|/(2F+1)).
```

[DERIVED] Product coordinates and a union bound give
`TV(f,f+Ke)≤min(1,Σ_i |(Ke)_i|/(2F+1))`, conditional even on all `K,w,e`
and the message. Thus no false independence of `Ke` or matching-covariance
argument is needed. With `|K_ij|≤BK` and `|e_j|≤BL`, the cost is at most
`d l BK BL/(2F+1)` plus the two tail probabilities. The target coins are
fresh and independent of its prior adaptive transcript. In particular `f`
and its tape stay private: appending the same actual `f` to both views would
invalidate this joint shift argument.

[SOURCE/DERIVED correction] HYL Lemma2 p24 prints the equality `B/B′` for
an arbitrary shift `e∈[−B,B]`. That equality is false for `e=0`, among other
choices. The frozen variant derives the correct discrete interval bound
directly and does not rely on that printed equality. This is a scoped formula
correction, not a refutation of the source's cryptographic field or all results.

[DERIVED] The ordinary LWE reduction receives `(A,c)`, independently samples
`K`, publishes `P=KA`, and forms `Kc+f+Δa`. It requires neither the LWE secret
`w` nor its error `e`. Therefore its comparison is exactly uniform-secret
decision LWE with dimension `n`, `l` samples and product integer Gaussian
error of width `σe`, versus independent uniform `c=u∈F_q^l`. No ALS hinted-LWE
reduction, nonlinear function of an unknown error, or smaller transformed
noise parameter is used.

[DERIVED] After this switch `[A|u]` is a uniform `l×(n+1)` matrix. For every
unexposed row, the **joint pair** `(k_i A,k_i u)` becomes an independent
uniform pair under `δ_(d−|J|)(n+1)`, while `k_J` and its pairs remain. Hence
the unexposed `h_i` are perfectly masked even after conditioning on their
public `P_i`; the exposed target terms match because their `a_i` match.
Replacing only `k_i u` while ignoring its joint law with `P_i` would not
justify this step, and is not what the frozen proof does.

[DERIVED adaptive check] Change the hidden bit at one of at most `T` challenge
positions at a time. Every other response is an original public encryption
using `P` and fresh coins. For either target endpoint, setup, earlier
responses, adversarial state and choice of target messages, and later
responses form one common channel applied to the appropriate joint tuple.
The target augmented matrix has only one new column: there is no simultaneous
replacement of all challenge columns that discards their shared-`K`
correlation. The mask endpoint is identical for both target message bits,
including subsequent adaptive behavior. This supports the stated conservative
acceptance-probability-gap ledger:

```text
Adv_public ≤ 2δ_(d−r)(n)
           + 2T [ε_QPT-LWE(n,q,σe,l)
                 + d l BK BL/(2F+1) + τK + τe
                 + δ_(d−|J|)(n+1)].
```

[DERIVED QPT boundary] All reductions use classical sampling and arithmetic
around one straight-line invocation of the adversary. Statistical distance
of the classical input tuples bounds trace distance after their common
quantum channel. Independent parameter-dependent quantum advice is passed
once; it need not be copied, measured, or rewound. The LWE premise must cover
the same uniform/nonuniform QPT or QPT/qpoly class. Secret-correlated advice,
superposition encryption queries, and a promotion from classical security
are not obtained. Ideal exact Gaussian sampling is the specified distribution;
an efficient approximate implementation and its accumulated TV error remain
premises before applying the reduction to a concrete runtime or time budget.

## 4. Correctness, ranges, and nonvacuity

[DERIVED] For each actual recipient the cancellation identity is exact:
`h_i−k_i c=Δa_i+f_i−k_i e (mod q)`. On the joint key/error event, each issued
phase error has magnitude at most `E=F+lBKBL`. Scalar integer combinations
of issued ciphertexts with coefficient L1 norm at most `W` have noise at
most `WE` and accumulated centered lift at most `WX`. Uniform flooding is
always bounded, independently of Gaussian tail events.

[DERIVED] Put `R=WX`, `D=dX` and `Δ=floor(q/D)`. If `D≥2R+1`, the cyclic
wrap gap for points `{Δt mod q:−R≤t≤R}` is
`q−2RΔ≥(D−2R)Δ≥Δ`; consecutive gaps are `Δ`. If also `Δ>2WE`, nearest-point
decoding is unique under every allowed error. This proves the needed range
directly rather than inheriting the printed source's broader decoder. Decode
the bounded integer sum and only then reduce modulo `p`.

[DERIVED/EXECUTED scoped source control] For the generic printed range
`[−D,D]`, `q=97,D=10,Δ=9` gives the same noisy residue 8 from `t=−10`
with error `+1` and `t=1` with error `−1`, both of magnitude at most `Δ/4`.
This arithmetic control illustrates the source's endpoint spacing gap; it
is not a cryptographic or protocol run. The new restricted range avoids it.

[DERIVED] Exact expiry subtracts the exact original ciphertext. Public offsets
add `Δ` times an integer lift only within the same total lift and noise
budgets. Since generally `Δp≠0 mod q`, a cancellation modulo `p` does not
license an unlimited integer offset. Arbitrary matrix evolution, nonlinear
updates, new recipients and unbounded coefficient growth are not proved.
The existing per-input read capabilities remain available on retained inputs;
this construction does not enforce a chosen execution trace.

[DERIVED/EXECUTED] The complete `B` transform is bijective over `F_p^577`,
so all `p^577` inputs and all 577 coordinates are represented. An independent
modular elimination on the frozen 16×577 public policy matrix produces the
nonzero vector `h` retained in `results.json`: its 17th coordinate is 1,
coordinates 18–577 vanish, and all sixteen `Y_i h` are zero. Thus `x0=0,x1=h`
are distinct admissible ambient challenges even for the full recipient
coalition; invertibility of the leading 16×16 block also verifies the stated
identity completion. This is not a witness inside the learner's semantic
encoder image, which still requires a separate analysis.

## 5. Finite certificate and arithmetic costs

[DERIVED/EXECUTED] The exact independent checker verifies the author's tuple
`d=577,r=16,p=28,439,893,W=32,T=384,n=1024,l=16384`, with
`2^288<q<2^289` prime, `σK=2^32,σe=2^10,F=2^244,BK=2^35,BL=2^13`.
Primality of the small application prime `p` is checked by trial division.
Bertrand's theorem inhabits the large prime interval; no particular large
prime has been selected or certified here. The bounds hold for every prime
in that interval; hardness is a premise for the particular eventually selected
LWE problem, not a consequence of prime existence.

[DERIVED/EXECUTED] At `ε0=2^−192`, `ηZ<8`, so
`max(q^−1,ηZ/σK)<2^−29`. The resulting `S_n<2^−179200` and
`S_(n+1)<2^−178911`, with negligible explicit rank terms, imply
`δ_h(N)<h 2^−189`. Crucially, the simple certificate requiring roughly
`l≥(n+1)log_2 q` fails here. The general expectation bound succeeds because
the much smaller ratio `ηZ/σK` supplies enough Gaussian entropy. No source
matrix-height requirement is silently weakened.

[DERIVED/EXECUTED] The regularity ledger is bounded by
`444258/2^189<2^−170`. Since `lBKBL=2^62`, the total bounded smudging part
is less than `443136/2^183<2^−164`. The conservative scalar tail
`Pr[|G|≥8σ]≤3σ 2^−256` gives `τK≤3dl/2^224<2^−199` and
`τe≤3l/2^246<2^−230`. Even charging both tails in all `2T` endpoint
transitions leaves contributions below `2^−189` and `2^−220`.
Their exact rational sum is less than `2^−163`. The distinct computational
term remains **`768·ε_QPT-LWE(1024,q,D_Z,1024,16384)`**.

[DERIVED/EXECUTED] Correctness holds simultaneously for all permitted
combinations of these `T` issued ciphertexts when their common key event
and all `T` error-vector events hold. Paying the key event once yields the
additional conservative bound `τK+Tτe<2^−198`. This is an ideal-sampler
correctness failure bound, not a confidentiality security level. For every
prime in the interval, `D=8,204,908,842≥2WX+1` and
`floor(2^288/D)>2WE`. The checker additionally uses
`2WX/D+2WE/2^288<1` to control the centered phase for all `q`, accounting
for the dependence of `Δ` on `q`.

| [EXECUTED] quantity | Independent value |
|---|---:|
| Ciphertext residues / packed bytes upper bound | 16,961 / 612,717 |
| Public-key residues / packed bytes upper bound | 17,368,064 / 627,421,312 |
| Recipient key bytes on strict tail event | 73,728 |
| All 16 recipient keys on that event | 1,179,648 bytes |
| Encoding scalar modular products | 17,368,064 |
| One coordinate read scalar modular products | 16,384 |
| One addition's residue additions | 16,961 |
| Live 66 ciphertext bytes upper bound | 40,439,322 |
| All 384 ciphertext bytes upper bound | 235,283,328 |

[DERIVED] The 36-bit key encoding prices `|K_ij|<2^35`, whose integer set
has `2^36−1` elements. The inclusive algebra bound has `2^36+1` elements and
would require 37 bits; the frozen note now states the distinction explicitly.
The same tail already bounds the strict storage event's complement. Entries
of `A,P` use at most 289 bits. These are bit-packed counts excluding metadata
and the separately costed public basis policy matrix. Scalar modular product
counts are not wall-clock costs or a proposed memory allocation.

[SOURCE/DERIVED/EXECUTED] HYL Table2's height requirement fails the naive
`λ=128` substitution: `l′=16128` but already the elementary lower bound
`2n log_2 q>216832` exceeds it. The author's square-parameter table fields
also reproduce exactly; its largest displayed row only passes that one
height check. The derived proof does not inherit HYL Theorems2–4 or their
hidden finite constants. It uses its own explicit regularity/smudging constants
and the exact ordinary LWE premise instead. Its smaller ciphertext and key
figures versus the ALS row compare conditional arithmetic across different
assumptions and reductions, not equal computational security.

## 6. Executed controls and remaining boundaries

[EXECUTED] Command, with stdout and stderr retained:

```text
python3 research/learn_infer_only/experiments/adversarial_review/smudged_fixed_coordinate/check.py > research/learn_infer_only/experiments/adversarial_review/smudged_fixed_coordinate/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/smudged_fixed_coordinate/stderr.txt
```

[EXECUTED] PASS: all 31 derived fields and 36 source-table fields match;
328 scalar interval shifts and 363 product interval shifts satisfy their
exact TV identity/bound; 1,273 decoder cases cover 38,005 noisy integer
points. The proof above is the justification for the general statements;
these finite controls are not proof substitutes. The script verifies all
25 author manifest links: 6 primary PDFs, 5 reused public inputs and 14
owned artifacts, plus the exact manifest and frozen subjects. Author result
and retained stdout bytes agree. No subject changed during the checks.

[EXECUTED scope] Only local source text/rendering, public integer/rational
arithmetic, and hashing were used. No author script was imported or run.
No key, Gaussian/flood sample, ciphertext, estimator, protocol, private-data
read, routing control or stopped experiment was executed or inspected.
Current review discovery counters: remote searches 0, new source-discovery
queries 0, downloaded PDFs 0; the named local extracts were searched with
`rg` and primary pages read directly. This is no absence claim about a field.

[OPEN] Selecting and certifying a particular large prime, specifying efficient
samplers and their total errors, exposing additional transcript fields,
evaluating the exact LWE assumption against the chosen advice class, and
establishing the intended learner's semantic-image nonvacuity and complete
closure remain separate tasks. The accepted result is the frozen restricted
conditional theorem and its finite arithmetic certificate. It supplies no
implementation approval, erasure/host-security theorem, or security bits.
