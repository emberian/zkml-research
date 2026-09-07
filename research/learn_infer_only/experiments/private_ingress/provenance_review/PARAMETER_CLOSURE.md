# Parameter closure of the encrypted-output obstruction

[DERIVED review correction; 2026-09-07] The independent review sharpens the
separating-output condition below to **L > E_i**, including exclusion of
L=E_i. The original reviewed note, code and results are preserved byte for
byte in `parameter_review_original/`; `PARAMETER_REVIEW_COMPLETION.md` and
`parameter_review_completion.json` record the correction and identities.

[DERIVED decision; 2026-09-07] The proposed circuit-size argument does **not**
give an all-parameter impossibility from 2025/330. Its s is the length of a
**current underlying PKE ciphertext on an input message**. It is not the
function description size, function randomness width, output width, function
key length or next-layer ciphertext length. These are separate dimensions in
the source. Increasing the next parameter can therefore evade the earlier
fixed-coin inequality without creating the suggested size contradiction.

[DERIVED stronger conditional result] There is an all-next-parameter
obstruction when the function uses only h effective random bits with
`h < E_i := 2*n*s_i+lambda_i`. A fixed-output test has gap at least `2^-h`,
regardless of how long its encrypted output is. Deterministic PRG stretching
does not help. The literal source proof writes lambda-bit functional coins,
but its definitions permit independent ellR and its PRF definitions permit an
independent output width. This notation issue must not be silently converted
into an unconditional restriction `ellR=lambda` on the stated general game.

[DERIVED remaining route] A coherent fixed-H polynomial sizing family exists
with genuinely longer functional coins and larger next ciphertexts. This
only evades the identified lower bounds. The route still requires a
quantitative **joint** future-package security bound below the current epsilon,
and the separate provenance/mixed-input obligations. “Negligible in the larger
parameter” alone is insufficient for that conclusion.

## 1. Exact source dimensions and the origin of s

[SOURCE: definitions/parameters/construction reread] Datta–Guan–Korb–Sahai,
[(Multi-Input) FE for Randomized Functionalities, Revisited](https://eprint.iacr.org/2025/330),
Definition 4.1, p.21, gives a function with n inputs of ellX bits, ellR random
bits, ellY output bits and an ellF-bit description. Definition 4.2, p.22,
passes all five quantities separately to Setup and quantifies over polynomially
bounded choices. Definition 4.4, p.23, lets the adversary choose their unary
encodings. It states no requirement that ellF, ellR or ellY be at most s.

| Symbol | Actual role in the inspected source |
|---|---|
| [SOURCE] lambda_i | Current PKE security parameter; also lambda_iO in §6.1 |
| [SOURCE] s_i | Length of one current PKE component ciphertext on x_i, §6.1 p.48 |
| [SOURCE] ellX_i | Bit length of each current plaintext slot |
| [SOURCE] ellF_i | Bit length of the randomized function description |
| [SOURCE] ellR_i | Functional randomness width in Definitions 4.1–4.2 |
| [SOURCE] ellY_i | Functional output width |
| [DERIVED] lambda_next, s_next | Parameters/dimensions of the independent encryption called inside F_i |

[SOURCE: reduction read] At the start of Hybrid 2,w,0, p.51, the source
explicitly identifies s with PKE ciphertext length. The index w ranges over
the `2*n` current PKE component ciphertexts, giving `2^(2*n*s)` subhybrids.
The final sum on p.67 cancels this count against per-subhybrid bounds.
Theorem 6.1, p.50, consequently requires
`epsilon_i=2^(-2*n*s_i-lambda_iO)`, and §6.1 sets lambda_iO=lambda_i.
For the two input slots, write `E_i=4*s_i+lambda_i`.

[SOURCE / DERIVED construction dependency] Construction 2, pp.48–49,
encrypts the slot plaintext x_i twice under ordinary PKE. The encryption-key
program E_i checks those encryptions and emits the authentication value; it
does not contain f. The issued function-key program G **does** contain f,
decrypts the inputs and evaluates f. Thus a large next-key literal or a large
next-ciphertext output enlarges G and the issued key. It does not automatically
enlarge the current PKE encryptions of x_i.

[DERIVED valid versus invalid size implications] Perfect PKE correctness
with fixed-length ciphertexts implies `ellX_i <= s_i`: different messages
have disjoint nonempty ciphertext supports. It does not imply
`ellF_i <= s_i`, `ellR_i <= s_i`, `ellY_i <= s_i`, or
`lambda_next <= s_i`. Even under a circuit convention where every output
wire and every used randomness wire contributes to the description size,
there is no source bridge from that description size back to s_i. The
argument therefore does not depend on assuming succinct circuits, unusual
fanout, compressed public keys or omitted output wires.

[DERIVED saved-packet dependency] In the saved candidate, the encrypted
history contains states, openings, observations and semantic authorization
witnesses. It does not contain the entire next FE key or next FE ciphertext.
The public proof relates the state commitment to Step; it does not certify
the full FE ciphertext bytes. Consequently it is consistent to keep the
current plaintext width independent of lambda_next. A changed relation that
carries encryption circuits, ciphertexts or large proofs back into a current
input must have its dimensions audited again. This note does not assume that
every possible provenance design has the saved candidate's dependency graph.

## 2. The lambda-versus-ellR notation issue

[SOURCE] Definitions 3.2–3.3, pp.15–17, explicitly give PRF/PPRF an input
length n and independent output length m. The rMIFE ideal correctness game,
Definition 4.2 p.22, draws ellR fresh bits for each function/input tuple.
Construction 2 computes `r_f=PRF2.Eval(K_f,tuple)` without restoring those
length arguments. Hybrid 2,w,4 and Hybrid 2,w,5, pp.57–58, instead write
`r* <- {0,1}^lambda`. This is the actual text, not an inferred ellR label.

[SOURCE / DERIVED] The same abbreviated section writes PRF.Setup with lambda
and later a lambda-bit PRF key, although §6.1 explicitly assigns enlarged
lambda_PRF1 and lambda_PRF2. Thus taking every displayed lambda as a literal
width does not reconcile all of the section's parameter declarations.
We found no explicit statement identifying ellR with lambda in the inspected
full-text occurrences. This absence is limited to the pinned PDF searched
with `rg` and the cited sections reread with `sed`; no author clarification
was obtained.

[DERIVED explicit parameter completion] The natural well-typed completion is
to set PRF2's output length to ellR, and replace the two uniform r* samplings
by ellR-bit samplings. The current tuple still has length `2*n*s`, so the
subhybrid count is unchanged. Lemma 6.7, p.65, uses punctured PRF2 security to
replace one output by a uniform value of the same length; its argument does
not enumerate those output bits. Function descriptions and hardcoded y*
values remain polynomial-sized under Definition 4.2. No new ellR-dependent
exponential loss appears in the inspected proof steps.

[OPEN source-reading limit] This is a stated parameter completion of the
source syntax/proof, not a new independent verification of the entire
cryptographic reduction or an author-confirmed erratum. If one deliberately
uses the literal lambda-randomness specialization, §3 gives its stronger
obstruction. If one uses the general ellR game with this completion, that
specialization cannot establish an all-parameter refutation. This distinction
is more precise than either assuming ellR is unbounded without accounting
for it, or silently imposing ellR=lambda on the general theorem statement.

## 3. General support tests that do apply

[DERIVED standing premise] Fix accepted challenge inputs for a common F.
Every left output contains a perfectly correct next encryption whose
protected next-state component is a_0; every right output encrypts a
different component a_1. Other payload fields may depend on coins. The next
public key is the same on both sides and is available in f. Therefore the
two first-PKE-component output supports are disjoint. This is the premise
used below; no conclusion is claimed when the next states have overlapping
randomized supports or when both executions can emit the same failure value.

[DERIVED short-coin proposition] If F uses ellR uniform bits, compute
`y*=F(left;0^ellR)` from the exact f and left plaintext advice supplied by
Definition 4.3. Test whether the actual output equals y*. The left probability
is at least `2^-ellR`; the right probability is zero by the disjoint encrypted
state component. Hence `ellR < E_i` rules out compatibility for **every**
choice of next encryption security parameter and output length.

[DERIVED effective-seed strengthening] If F depends only on an h-bit prefix,
or obtains all of its randomness by an efficiently computed expansion of an
h-bit seed, use the output from seed 0 instead. Its mass is at least `2^-h`.
Declaring a longer coin tape, padding an output or expanding a short seed to
lambda_next bits does not make h larger. In particular, a literal
ellR=lambda_i specialization fails because `lambda_i < E_i` for positive n,s_i.

[DERIVED output-collision proposition] There is also an efficient test that
does not search for a most-probable output. A samples a fresh left output
itself, using f and the left advice, and compares its first next-PKE component
to that of the challenged output. If P is the distribution on that s_next-bit
component, the left probability is `sum_c P(c)^2`; the right probability is
zero. Both supports are nonempty, so disjointness gives
`|support(P)| <= 2^s_next-1`. By Cauchy--Schwarz,
`sum_c P(c)^2 >= 1/|support(P)| >= 1/(2^s_next-1) > 2^-s_next`.
Thus `s_next <= E_i` rules out compatibility, including equality,
independently of the number of random bits F declares. More generally, for
any efficiently computed L-bit output projection with nonempty disjoint
left/right supports, the gap is at least `1/(2^L-1) > 2^-L`.

[DERIVED relation to the earlier bound] When rho payload-affecting bits and
lambda_next first-PKE coins are independently uniform, the previous test has
gap at least `2^(-rho-lambda_next)`. The three necessary inequalities merely
to avoid the identified tests are therefore:

```text
effective functional seed length h >= E_i,
next separating ciphertext/projection width L > E_i,
rho + lambda_next >= E_i       # under that independent-coin layout.
```

[DERIVED] Equality in the h or rho+lambda_next lower bound is not a proof
of failure or success: a lower bound equal to epsilon need not violate a
`<= epsilon` condition, and other distinguishers may have a larger advantage.
In contrast, L=E_i fails by the strict collision bound; integer separating
widths must satisfy L>=E_i+1. The next parameter's
numeric value does not guarantee any of these entropy properties if the
encryption algorithm ignores coins or exposes a shorter separating component.

[EXECUTED controls] `parameter_audit.py` checks that an h=3 seed stretched
to 128 bits still has fixed-output mass 1/8, despite a declared 64-bit coin
tape. A separate four-output distribution has left-sample collision 25/32
and cross-world collision zero; its rare fixed left output has mass only
1/8. The same saved distribution now checks the strict projection bound
`25/32 >= 1/3 > 1/4`, which excludes L=E=2. These are finite support
identities. The tuple representations expose
their values and implement no encryption.

## 4. A consistent fixed-H sizing escape

[DERIVED dimension witness] Consider the illustrative ordinary-PKE size
model `s_i=2*lambda_i+M`, with current plaintext width `M=16*k^3`, payload opening
coins `rho=k`, and a polynomial proof-coin budget. Set lambda_0=k and, twice,

```text
lambda_(i+1) = 8*s_i + 2*lambda_i + 2*rho + 1.
ellR_i       = rho + 2*lambda_(i+1) + proof_coins(k).
```

[DERIVED] Then both the corrected partial-event exponent
`rho+lambda_(i+1)` and s_(i+1) exceed E_i; the full fresh coin budget also
exceeds E_i. Next keys, output ciphertexts, proofs and explicit function
descriptions can have larger polynomial lengths. No dimension inequality
from Definitions 4.1–4.2 is violated. This is a sizing model, not a measured
PKE, a cryptographic challenge pair or a proof that any actual distribution
meets epsilon.

[EXECUTED numeric instance] The control takes k=16 and checks:

| Layer i | lambda_i | M | s_i | E_i | lambda_next | s_next | rho+lambda_next |
|---|---:|---:|---:|---:|---:|---:|---:|
| 0 | 16 | 65,536 | 65,568 | 262,288 | 524,609 | 1,114,754 | 524,625 |
| 1 | 524,609 | 65,536 | 1,114,754 | 4,983,625 | 9,967,283 | 20,000,102 | 9,967,299 |

[EXECUTED] With proof_coins=k^3, the respective ellR values are 1,053,330 and
19,938,678. The model reserves a polynomial metadata budget smaller than M
for the public proof/commitment/authorization fields copied into the next
observation plaintext. Outer FE ciphertexts and their authentication tags
are not copied into that plaintext. The script also records explicit polynomial output/description
budgets much larger than s_i. Those budgets are dimensions for the model,
not implementation-size measurements or a claim that they dominate every
possible choice of primitive implementation.

[DERIVED general finite-horizon sizing] For an independently parameterized
PKE whose ciphertext length and relevant algorithm sizes have fixed
polynomial bounds in its security parameter and message width, polynomial
next-parameter enlargement and explicit larger ellR can remain polynomial
in the initial k through any **fixed** number of layers. Composition of
finitely many fixed polynomials is polynomial. One must choose an actual
family with sufficient effective ciphertext entropy/width, not infer it from
an upper size bound or inflate a length by cosmetic padding. A growing
horizon can multiply degrees or constants without a polynomial bound and
is outside this sizing claim.

[DERIVED other primitive parameters] The source already enlarges PRF and
OWF parameters as fixed powers of `2*n*s_i+lambda_i` or
`3*n*s_i+lambda_i`, with fixed hardness exponents. Under the fixed-H sizing
above these remain polynomial. Longer PRF2 output and larger F descriptions
alter polynomial costs; they do not insert ellF or ellY into the enumerated
current PKE tuple. The specified weak-extractability and quantitative
primitive assumptions still must hold for these polynomial circuit families.

## 5. Why a sizing escape is not a compatibility theorem

[SOURCE] Theorem 6.1 assumes CPA-secure PKE. The PKE switches in the proof
use its indistinguishability; the final statement is negligible advantage.
The very small PRF/iO/OWF errors used to pay for the exponential subhybrids
do not by themselves supply an explicit exponentially small bound for the
separate underlying PKE contribution. Nor do they prove security of a
future package correlated with the current function descriptions.

[DERIVED rate counterexample] Let `a(t)=2^(-(log_2 t)^2)`. This is negligible
in t. For every fixed positive integer d, substituting
`t=lambda_current^d` gives exponent `d^2*(log_2 lambda_current)^2`, which is
eventually much smaller than lambda_current and hence smaller than E_i.
Therefore no universally guaranteed polynomial parameter lift converts an
unspecified negligible bound into `<=2^-E_i`. The finite control records this
comparison for several parameters; the asymptotic claim follows because
`lambda/(log lambda)^2` diverges.

[HYPOTHESIS quantitative escape premise] Suppose an actual joint future
package theorem instead gives
`delta(t) <= q(t)*2^(-t^c)` for a fixed c>0 and fixed polynomial q, with the
required same-context/all-replacement challenge relation. A sufficiently
large polynomial t in E_i can then make delta(t) at most `2^-E_i`; for
example `t >= (E_i+1)^(2/c)` eventually dominates both E_i and log q(t).
That would be a real quantitative route around this threshold. The
joint-package theorem, its assumptions and its reduction costs are the
premise; choosing t is the remaining arithmetic.

[EXECUTED conditional numeric control] For the explicitly hypothetical
bound `delta(t) <= t^3*2^-sqrt(t)`, the script chooses `t=(2*E_i)^2` and checks
the conservative integer inequality
`sqrt(t)-3*ceil(log_2 t) >= E_i` at both layers. This is marked hypothetical
in the results. No inspected theorem has been credited with that exact
joint-package bound.

[DERIVED independence from provenance repair] Raising dimensions does not
alter the saved observable-failure gap 1, or repair the dual-mode
current-parent replacement-state counterexample. Conversely, repairing those
guards does not establish the quantitative bound above. The reasons for
failure remain separate, rather than being merged into an unsupported
all-parameter impossibility claim.

## Status and provenance

[REFUTED: proposed size argument] The implication
“F emits a next ciphertext, so s_current bounds lambda_next or F's output
width” is unsupported and contradicted by the source's distinct parameter
roles. No all-parameter encrypted-output impossibility is established by
that argument.

[DERIVED status] Record the stronger **short-effective-randomness** and
**short-separating-output** propositions, the literal lambda-coin
specialization, and the explicit independent-ellR sizing escape. Larger next
parameters remain an unclosed route under a suitable quantitative theorem;
the current source-conditional construction claim is still absent.

[OPEN next] For any subsequent proof attempt, state the PRF2 output width
and actual effective randomness, instantiate the next PKE dimensions without
padding-based entropy claims, and derive the full joint future-package
advantage with all assumptions and polynomial losses exposed. Then compare
that **upper** bound to E_i. The completed lower-bound audit alone cannot
settle that comparison.

[EXECUTED] Run
`python3 research/learn_infer_only/experiments/private_ingress/provenance_review/parameter_audit.py`.
`parameter_results.json` and `parameter_audit.stdout.txt` retain the command,
Python version, program hash and complete controls. No cryptography is
implemented. `parameter_sources.json` pins the reused 2025/330 PDF/extract
hashes, exact read scope, source-text checks and all prior frozen-artifact
checks. Earlier review and dual-mode artifacts remain unchanged.

[EXECUTED accounting] One web search query checked the exact paper title with
randomness/parameter terms; no clarification beyond the public primary
publication records was obtained. This audit used zero Scry SQL/schema,
zero Kagi, zero HTML opens, zero new PDF extracts and zero PDF downloads.
All theorem/algorithm evidence comes from the retained local PDF extract.
