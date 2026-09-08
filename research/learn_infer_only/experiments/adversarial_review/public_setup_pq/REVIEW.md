# Independent review: fixed-policy ALS public setup

[EXECUTED scope, 2026-09-08] Independent source and mathematical review of
`experiments/private_construction/public_setup_pq/notes/AUDIT.md`, specifically
its ALS construction, joint setup/transcript lemma, conditional security theorem,
and arithmetic/cost claims. This lane performs no cryptographic experiment,
private-state inspection, attack execution, or stopped-task work. The reviewed
author note is frozen at SHA-256
`2c6f649fa0891be05dd1f3a1f89c935692091195e71f0b1959d78b5ef9061007`.
[EXECUTED] `shasum -a 256` independently matches that author-supplied hash.

[DERIVED final verdict on frozen candidate] The positive construction and joint setup bound
survive this review under the stated honest-sampling, fixed-policy, classical-
interface assumptions. The basis must act on the plaintext before encryption;
recipient rows use their exact source row marginals; the retained public coins
are accepted public matrix entries. The source QPT security assumption and
correctness of finite arithmetic remain distinct hypotheses. This is not an
instantiated post-quantum resident or a malicious-setup theorem.

## Source pins and access

[SOURCE] Agrawal–Libert–Stehlé, *Fully Secure Functional Encryption for Inner
Products, from Standard Assumptions*, ePrint 2015/608, local mirror:
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/608.pdf`.
The PDF SHA-256 is
`a7d5c231b70961ea59ca544c91b2392fb35c166c88e42b898640cfdc7dbb94d0`.
Read: §4.2 algorithms/correctness/parameters and Theorem 3, printed pp.16–20;
§4.3 Theorem 4 and Lemmas 3–5, pp.20–22; Appendix A Definition 8, p.31;
Appendix C Lemmas 6–10, pp.33–34; Appendix D Lemma 11, p.35; and the referenced
Theorem 2 hybrid, pp.13–16. The exact extracted text is `extracts/2015-608.txt`.

[EXECUTED] Independent extraction command:

```text
pdftotext -layout /Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/608.pdf research/learn_infer_only/experiments/adversarial_review/public_setup_pq/extracts/2015-608.txt
shasum -a 256 /Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/608.pdf research/learn_infer_only/experiments/adversarial_review/public_setup_pq/extracts/2015-608.txt
```

[EXECUTED output] The command succeeded. Extract SHA-256:
`a1170661edc061a9b011367d43b9b75ed6dfc073cfd0aa477459c20f14d1ecdd`.

[SOURCE web metadata only] The [primary ePrint abstract page](https://eprint.iacr.org/2015/608)
reports its last revision as 2022-12-30 and identifies the CRYPTO 2016 publication.
This page was opened once; its abstract is not used as the theorem proof. Local
PDF bytes, not an inferred matching revision date, identify the reviewed source.
[EXECUTED counters] Web opens 1; web searches 0; Scry SQL/schema 0/0; Kagi 0;
PDF downloads 0. No field-wide absence claim is made.

## 1. Exact distribution: accepted with a joint-view proof

[SOURCE] The source plaintext/key domain is the whole `F_p^d`, with `q=p^k`
and message scale `Δ=q/p`. Every Gaussian entry of `Z` is independent. Row `i`
has centered width-`σ1` left half and width-`σ2` right half centered at the
source's canonical vector `δ_i` (p.18; dimensional embedding explicit in
Lemma 4, p.21). Rows are independent but their right-half centers differ.
The source key for an independent query `e_i` is exactly `(e_i,Z_i)` (p.17).

[DERIVED] For one missing row, write `A=(A_L;A_R)` and `Z_i=(L_i,R_i)`.
Lemma 10, p.34, applies to `(A_L,L_i A_L)` because `m` is even,
`m/2 ≥ 2 n log_2 q`, `q=p^k`, and the prescribed `σ1` meets its lower bound.
Its conclusion is joint in the public hash matrix and syndrome, with error
`η=2^-Ω(n)`. It is a Gaussian syndrome regularity result for prime-power
modulus; an arbitrary universal-hash claim over `Z_q` is not needed.

[DERIVED] Independently adjoin `A_R,R_i`, then add the shift `R_i A_R`.
Uniformity of a syndrome is invariant under this shift. Independently sample
every other source Gaussian row and compute its syndrome from the same `A`;
generate already-hybridized rows uniformly. This is the same randomized
postprocessing kernel in both experiments, even when it reveals all recipient
rows `Z_[r]`. It cannot increase statistical distance. Replacing the missing
rows one at a time therefore proves

```text
SD((A, ZA, Z_[r]), (A, U_public, Z_[r])) ≤ (d-r) η.
```

[DERIVED qualification] The claim is an average joint-distribution bound over
uniform `A`, not a pointwise guarantee after conditioning on an arbitrary rare
matrix or transcript. Revealing independently generated recipient rows is
covered. Conditioning on an arbitrary acceptance/grinding event may amplify
distance and requires a new bound; malicious or correlated registration is
outside this statement.

## 2. Public coins: accepted with the stated restricted meaning

[DERIVED] The public setup tape in the author's exact experiment is
`(A,U_(r+1),...,U_d)`. The source comparison can expose it by copying the same
entries from its public key. This adds no information and preserves the bound.
The simulator does not need a Gaussian preimage for any of these rows.
Accepted direct-uniform coordinates are uniform in the real experiment and
statistically close to uniform in the source comparison; exact equality is not
being claimed.

[DERIVED boundary] This does not expose the ordinary honest ALS master setup
tape, which includes the missing Gaussian rows. Exposing that different tape
would disclose a full master and is excluded. Nor does the proof automatically
cover a CSPRNG seed or complete rejection-sampler log. Extra logs are admissible
only after specifying and proving a common efficiently samplable conditional
kernel for those logs given the accepted output. A prescribed public-coin
algorithm can avoid that additional obligation by exposing only the exact
accepted values modeled here.

## 3. Security transfer and quantum scope

[SOURCE] Definition 8, p.31, is single-challenge IND-CPA against PPT adversaries
with classical key/message interfaces; challenge equality is required for
every issued function key. Theorem 3, p.18, invokes multi-hint extended LWE.
Theorem 4, pp.20–22, reduces a specified ordinary LWE distribution to that
assumption with dimension/noise loss. It is not a theorem about an arbitrary
practical ring-LWE implementation.

[DERIVED] Querying only the fixed coordinate keys `e_i`, `i∈J`, faithfully
provides the coalition's exact secret rows. Since the first `r` rows of the
public invertible `B` are `Y`, equality `Y_J x_0=Y_J x_1` is precisely source
equality for those keys on `Bx_0,Bx_1`. Distinctness is preserved by invertible
`B`. The dependent-key stateful rule is never invoked by this reduction.

[DERIVED] Adaptive fresh-message histories admit the stated ordinary hybrid:
select one challenge position, generate earlier/later challenge encryptions
publicly in the selected adjacent worlds, and submit that position's adaptively
chosen valid pair to the source. Public ciphertext postprocessing belongs to
the adversary. Equality must hold for each fresh input pair on every admitted
history; equal final readouts alone are insufficient. Per-input projections on
retained ciphertexts remain available to coalition recipients.

[DERIVED] With advantage defined as the difference between two acceptance
probabilities, the bound `T Adv_ALS + 2(d-r)η` is valid. ALS Definition 8's own
guessing advantage is half that difference, so conversions to its convention
must retain the factor of two. The two statistical terms come from one setup
comparison in each message world, not one comparison per ciphertext.

[DERIVED quantum transfer] Statistical distance of these classical views
equals trace distance of the diagonal states. Applying the same QPT channel,
including adaptive processing and auxiliary state generated from the view,
cannot increase trace distance. The fresh-message hybrid is straight-line and
uses classical message interfaces. Therefore the *transfer theorem* is valid
for QPT adversaries if the source game is QPT-secure. This argument does not
automatically allow independent secret-correlated quantum auxiliary input,
superposition challenge/key oracles, or prove a QROM compilation.

[OPEN] No published QIND statement is inferred from the PPT wording. This
review has not supplied a complete quantum lifting of the source's adaptive
proof or its LWE reductions. The author's explicit conditional source-QPT
assumption is necessary at this review's evidence level.

## 4. Basis, domains, noise and actual closure

[DERIVED] A public `B∈GL_d(F_p)` that is applied to plaintext as `a=Bx mod p`
does not multiply the ciphertext errors or Gaussian secrets. Canonical integer
lifts of `a` always lie in `[0,p)^d`; the whole domain is supported by §4.2.
This step does not introduce a `||B||` or `||B^-1||` noise penalty. In contrast,
applying an integer lift of `B` to an existing ciphertext is a different
operation and carries its corresponding error coefficients.

[DERIVED exact correctness] For a recipient row and one ciphertext,

```text
c1_i - Z_i c0 = Δ a_i + (e1_i - Z_i e0)  mod q.
```

[DERIVED] For integer coefficients `b_t`, public scalar ciphertext combination
and a plaintext offset produce phase
`Δ (Σ_t b_t a_t + Bv) + Σ_t b_t(e1_t,i-Z_i e0_t) mod q`.
This decrypts to the intended residue if the absolute final error is below
`Δ/2`. A sufficient bound is `Σ_t |b_t| E_t,i < Δ/2`.
Exact subtraction of an original ciphertext cancels its original noise;
subtraction of a newly randomized encryption of the same plaintext does not.
Adaptive choice of bounded coefficients is safe on the event that all input
errors satisfy the retained bounds. A joint tail/union bound must cover that
event; single-ciphertext correctness alone is not an unbounded-history claim.

[DERIVED integer semantics] The source promises residues. To interpret an
authorized output as a signed integer `Y_i x`, the admissible integer range
must inject into `F_p`; centered decoding is sufficient when
`|Y_i x| < p/2`. Cumulative state updates and scores need the same no-wrap
condition if their intended semantics are integers. Large coefficients in the
*authorized integer row* can therefore enlarge `p` and the source parameter
bill, even though arbitrary completion rows of `B` do not themselves increase
initial encryption noise. For general finite-field semantics no integer
no-wrap promise is needed.

[DERIVED closure limit] Common-key scalar combinations, addition/subtraction
and public offsets are supported. A general update `x←T x` induces
`M=B T B^-1`. Sending `c1←M c1` replaces its public randomness coefficient
`U` by `M U`; the retained row `Z_i` still cancels only `U_i`. Fixed-key
correctness therefore does not follow unless the relevant row cancellation
identity is separately satisfied. Evolved public keys, derived span keys or
refresh are separate constructions. The candidate does not obtain nonlinear
learning, arbitrary matrix updates, or fresh later functional keys merely
because it preserves the full modular vector.

[DERIVED cost warning] Source p.18 uses `K'=(sqrt(d) p)^d`, prescribed
Gaussian widths, `α^-1 ≥ d² p³ B_τ ω(sqrt(log n))`, and associated modulus and
LWE-dimension/noise constraints. These must be priced jointly before selecting
concrete parameters. Recipient-only correctness can use its sharper actual
row error expression, but that does not by itself authorize replacing the
source security widths by smaller practical ones.

## 5. Nonvacuity and remaining evidence

[DERIVED] The author's `d=3,r=2` witness with
`Y=[[1,0,1],[0,1,1]]`, `B=[[1,0,1],[0,1,1],[0,0,1]]` and
`h=(-1,-1,1)` has `det B=1`, `Yh=0`, `Bh=e_3`, and a changing third state
coordinate over every prime field. It is a valid whole-coalition nonvacuity
witness on `F_p^3`. An actual learner's reachable/encoded image must contain
an admissible pair; full-domain rank deficiency does not prove that fact.

[EXECUTED public mathematical controls] Command:

```text
python3 research/learn_infer_only/experiments/adversarial_review/public_setup_pq/checks/public_algebra.py > research/learn_infer_only/experiments/adversarial_review/public_setup_pq/checks/public_algebra_output.json
```

[EXECUTED output] PASS: 503 basis roundtrips and equal-output/distinct-state
pairs over primes 2,3,5,7; 15,625 bounded-error phase combinations at `p=5`,
`Δ=25`, with maximum absolute error 8. Public arithmetic controls show that
error 13 crosses the radius, the integer score 4 centers to -1 modulo 5, and
a transformed first public row can leave symbolic residual `U_3-U_1` under
the old key. The script constructs no keys or ciphertexts and reads no private
data; it is not a security experiment. Output and script hashes are retained
in `checks/public_algebra_output.json` and the final manifest.

[DERIVED status] The frozen candidate is accepted within its stated scope.
Its added centered-integer and general-matrix qualifications agree with this
review. No change to `docs/VERDICTS.md` is made or currently required by the
review itself; this is a new, conditional fixed-policy construction, separate
from the deployed FHE/PQ claims in §7.8.

[OPEN next] A separate `FIXED_COORDINATE_QPT.md` derives a narrower direct
QPT argument with a slightly stronger row-count condition. It may replace the
source-QPT premise and avoid arbitrary-key widths, but must be reviewed as a
new variant; it does not change the frozen candidate or this acceptance.
No concrete source parameters, cryptographic runtime, quantum hardness
estimate or resident integration are executed here.
