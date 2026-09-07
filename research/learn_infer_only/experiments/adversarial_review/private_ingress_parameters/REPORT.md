# Independent review of private-ingress parameter closure

[DERIVED verdict; 2026-09-07] **Scoped acceptance with one strict-bound
correction.** The frozen note correctly rejects the proposed implication from
current PKE ciphertext length to next function/output/randomness length. Its
fixed-horizon example is a coherent dimension model, and its warning that
negligibility supplies no polynomial route to the required exponential joint
gap is correct. It does not establish a private-ingress construction.

[DERIVED correction] In `PARAMETER_CLOSURE.md:144`–`169`, the separating-output
test actually excludes **L <= E**, including equality. Its necessary width
condition can be strengthened to **L > E**. The statement that equality in
*any* of the three inequalities is undecided is therefore too broad. All
saved sizing rows already satisfy strict inequalities, so this correction
does not invalidate the note's dimension escape or its decision.

[EXECUTED frozen target] Reviewed
`experiments/private_ingress/provenance_review/PARAMETER_CLOSURE.md`, SHA-256
`f7bce8ced8c8460c13a7fe43dfaffbad8bd644f698303f62dc9497b790858fca`.
The author script, results, stdout and source manifest match all five entries
in `parameter_hashes.json`. No author source was edited. Full before/after
hashes and independently executed controls are in `results.json`.

## 1. What the primary source does and does not size

[SOURCE] Datta–Guan–Korb–Sahai,
[(Multi-Input) FE for Randomized Functionalities, Revisited](https://eprint.iacr.org/2025/330),
local PDF SHA-256
`b7133ad8161f287b2a4b4d1a15664c4ace47fbce451d5f569a6d795261108fd2`.
A fresh owned `pdftotext -layout` extraction equals the retained extraction,
SHA-256 `88e4fa7f4120767c0724bf37d757e0ea1ed24ca0d6eefa9ea181148fa2249e54`.
The following locations were read as definitions, algorithms or proof steps,
rather than inferred from the abstract. Page numbers are PDF pages, which
agree with the printed labels at these locations.

| Inspected location | Supported conclusion |
|---|---|
| Definitions 3.2–3.6, pp.15–17 | PRF/PPRF take an independent output length m; the punctured-point challenge replaces an output by m uniform bits. |
| Definition 3.8, p.18 | PKE correctness is perfect; ordinary IND-CPA is asymptotic and negligible. |
| Definitions 4.1–4.4, pp.21–23 | Input length, description length, randomness length and output length are separate polynomially bounded quantities; compatibility supplies f and the left/replacement inputs to its tester. |
| §6.1 and Construction 2, pp.48–49 | s measures a current PKE component ciphertext. The encryption-key program has public keys/PRF key and checks current encryptions. The function-key program contains f. |
| Theorem 6.1, p.50; Hybrid 2,w,0, p.51 | The compatibility threshold is epsilon = 2^(-2ns-lambda_iO); w enumerates the 2ns-bit current PKE tuple. |
| Hybrids 2,w,4 and 2,w,5, pp.57–58 | The displayed functional random samples literally have lambda bits. |
| Lemmas 6.2–6.3, p.64 | The outer PKE hop is justified only by ordinary CPA negligibility; this is separate from the small subhybrid budgets. |
| Lemmas 6.7–6.8, pp.65–66; final sum, p.67 | PRF2 replaces one output at a punctured current tuple; no enumeration over output bits appears. The final count remains proportional to 2^(2ns). |
| Malicious-encryptor Hybrid 2, p.70 | The displayed lazy PRF2 key sample also uses lambda despite the enlarged parameter declarations. This corroborates the notation mismatch; it is not a full audit of that theorem. |

[DERIVED] With fixed-length perfectly correct ciphertexts, distinct current
messages have disjoint nonempty supports, so ellX <= s. There is no analogous
counting implication for ellF, ellR, ellY or lambda_next. Even a circuit
encoding charging every used input/output wire does not connect the length
of that circuit back to the plaintext-only current PKE ciphertext.

[DERIVED qualified width completion] Giving PRF2 input length 2ns and output
length ellR, and reading the two point samples as ellR-bit samples, is the
natural well-typed completion of the displayed syntax. It preserves the
enumerated input tuple and fits the source's PPRF definition. The inspected
point-switch arguments add no ellR-dependent exponential enumeration. The
author correctly labels this as a derived completion, not an author-confirmed
erratum or an independently proved general-ellR cryptographic theorem.
Security assumptions must still cover the resulting polynomial-size
circuits and their reduction costs. This review supplies no missing
cryptographic reduction.

[DERIVED important distinction] The short-seed proposition concerns the
effective uniform seed used by the *ideal randomized function F*. It is not
a claim that a short PRF key cannot computationally support a longer ideal
output distribution. The actual PRF2 implementation and its computational
replacement are a separate source assumption. The frozen note need not
restrict ellR to the number of bits in an issued PRF key.

## 2. The collision proof and the equality correction

[DERIVED] Fix an allowed common f and the supplied left/replacement inputs.
Let P and Q be its left/right projected output laws on an L-bit alphabet.
Assume both laws have total mass one and their supports are disjoint, as
follows from the note's fixed distinct next-state component and perfect
correctness premise. The tester independently samples one left evaluation
and compares the projected result with the challenge. Its advantage is

```text
sum_c P(c)^2 - sum_c P(c)Q(c) = sum_c P(c)^2.
```

[DERIVED] This uses one evaluation and one comparison; it needs neither a
decryption key, support membership oracle nor an efficiently found heaviest
atom. Independence of the fresh tester coins from the challenge coins is
essential and is available to an ordinary randomized compatibility tester.

[DERIVED strict version] Write m = |support(P)|. Nonempty Q and disjointness
give `m <= 2^L-1`. Cauchy–Schwarz then gives

```text
gap >= 1/m >= 1/(2^L-1) > 2^-L.
```

[DERIVED] Therefore `L <= E` implies `gap > 2^-E`, including `L=E`.
For integer bit widths the sharpened necessary condition is `L >= E+1`.
Suggested local correction to the author's list:

```text
h >= E;
L > E;                         # nonempty disjoint separating supports
rho + lambda_next >= E;        # stated independent-coin layout only
```

[DERIVED] Equality in the first or third displayed *lower bound* need not
decide compatibility, and no one of these necessary conditions is sufficient.
For example, an h-bit seed can have an atom exactly 2^-h in a larger ambient
output alphabet. This is an identity about the identified tester, not a
claim that all efficient distinguishers have that advantage. Without the
disjoint-support premise the collision difference can be zero; overlapping
randomized next states or a common failure result require a different bound.

[EXECUTED] Independent controls cover 1,467 positive dyadic histograms in a
specified bounded family, verify the strict inequality, retain a zero-gap
overlap sibling, and give five exact h=E atom/collision boundary examples in
larger alphabets. Another 63 deterministic seed maps verify that stretching
a short uniform seed cannot reduce the fixed-seed output atom below 2^-h.
These are distributions on labels. No encryption, state recovery or
extraction experiment is implemented.

## 3. Fixed-H sizing is coherent only at its declared level

[DERIVED] With M=16k^3 and rho=k, the author's recurrence simplifies to

```text
lambda_(i+1) = 18*lambda_i + 8*M + 2*k + 1 = 2*E_i + 2*k + 1,
lambda_i = 18^i*k + (8*M+2*k+1)*(18^i-1)/17.
```

[DERIVED] For each fixed i, this is polynomial of degree three in k.
The claimed next-coin, separating-width and partial-event exponents are all
strictly greater than E_i. Explicit output/description budgets formed by
fixed polynomial operations remain polynomial, even when they greatly
exceed s_i. Similarly, fixed powers used in §6.1 for PRF/OWF parameters
remain polynomial at a fixed number of independently parameterized layers.
A general growing horizon is outside this reasoning; the particular linear
recurrence may permit some growing horizons, which is not a generic claim.

[SOURCE / DERIVED packet check] The saved
`experiments/private_ingress/provenance/PROVENANCE.md`, §1, encrypts state,
opening and bounded semantic history. Its next observation carries public
proof/commitment metadata, and its function contains the next state-slot
encryption key. It does not copy that next key or its ciphertext into the
current plaintext, nor certify full ciphertext bytes. This supplies no
unavoidable circular size inequality of the proposed kind.

[DERIVED implementation boundary] An actual proof/commitment/authorization
encoding must still fit the selected plaintext budget. The illustrative
metadata and authentication budgets are not a theorem about the sizes of
Groth–Sahai, iO, a selected PKE or a full verifier circuit. The frozen note
already says this. A concrete scheme might force new dependencies and a
different recurrence; the dimension example does not discharge them.
Likewise, polynomial ciphertext *upper* bounds say nothing about useful
entropy or small separating projections. Padding is not a cryptographic
escape.

[EXECUTED] All five saved result groups were reproduced by importing only
the author's pure functions with bytecode disabled. The author's writing
`main()` was never called. The k=16 rows, both hypothetical-rate rows and
all saved large output/description integers agree exactly. Independent
checks verify the closed form and strict inequalities in 54 layer cases at
six k values; the metadata inequality is checked for k>=2, not k=1.

## 4. Negligible is not the required quantitative future-package gap

[DERIVED] The author's counterexample is correct:
`a(t)=2^(-(log_2 t)^2)=t^(-log_2 t)` is negligible. For any polynomial lift
`t(lambda) <= C*lambda^d`, eventually

```text
-log_2 a(t(lambda)) = (log_2 t(lambda))^2 = O((log lambda)^2) < lambda <= E.
```

[DERIVED] Consequently this otherwise negligible allowed rate exceeds
2^-E after every polynomial parameter lift. This is a counterexample to
deducing a sufficiently small *upper bound from unspecified negligibility*.
It is not a lower bound on the advantage of every actual encryption scheme.
Theorem 6.1 and Lemma 6.2 do not give a contrary exponentially small bound
for their ordinary PKE contribution.

[DERIVED conditional escape] If an actual theorem supplies the **whole
relevant joint law's absolute gap**, with all future/prior keys, contexts,
replacement inputs and simulation costs covered, and bounds it by
`q(t)*2^(-t^c)` for fixed polynomial q and fixed c>0, a sufficiently large
polynomial lift works arithmetically. The constants, resource family,
advantage convention and reductions must belong to that theorem. Marginal
CPA security, one honest input path, or a fresh uncorrelated auxiliary view
does not establish the required joint premise. In particular, a CPA success
advantage and an absolute acceptance-probability gap require their usual
factor-of-two conversion before an exact comparison.

[EXECUTED] Sixteen independent slow-rate witnesses and four conservative
integer checks of the explicitly hypothetical `t^3*2^-sqrt(t)` rate pass.
The finite checks illustrate the inequalities; the asymptotic argument
above establishes the general polynomial-lift limitation.

[SOURCE / DERIVED no construction implication] `DUAL_MODE.md` was read only
to check its scope and relationship to the parameter claim. It leaves the
same-context encrypted-message switch with the full future package open,
and separately records the current-parent/replacement-state difficulty.
The later parameter note revises an all-parameter obstruction, not those
semantic or joint-distribution obligations. No source-conditioned H=2
private-ingress construction follows from these artifacts.

## Reproduction and bounded next step

[EXECUTED] Run from the repository root:

```sh
pdftotext -layout /Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/330.pdf research/learn_infer_only/experiments/adversarial_review/private_ingress_parameters/extracts/2025-330.txt
python3 research/learn_infer_only/experiments/adversarial_review/private_ingress_parameters/review.py > research/learn_infer_only/experiments/adversarial_review/private_ingress_parameters/stdout.txt
```

[EXECUTED] `results.json` and `stdout.txt` preserve the exact analytic checks,
command, Python version, script hash and input hashes; `review_manifest.json`
pins the delivered review files. All input hashes remain unchanged. This
review used zero Scry, Kagi or web queries, one local PDF extraction, zero
PDF downloads and zero state recovery/extraction experiments. No companion,
shared ledger or author source was edited; no commit was made.

[OPEN next] Fold only the strict L>E correction into the current note.
A subsequent construction attempt should expose one actual per-epoch
primitive/width/coin allocation and a quantitative joint future-package
reduction for its entire compatibility domain. Until that bound is derived,
neither further dimension enlargement nor a marginal-security experiment
answers the remaining question.
