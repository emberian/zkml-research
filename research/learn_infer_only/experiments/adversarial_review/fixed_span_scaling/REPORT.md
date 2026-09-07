# Independent review of the general fixed-span DDH lemma

[DERIVED verdict; 2026-09-07] **Accepted as a conditional classical IND
theorem for the stated fixed-key game.** No blocking error was found in
the general basis sampling, exposed-key distribution, one-direction DDH
transitions, adaptive composition, padded T*k selection, or sampler budget.
The actual 16-by-577 rank and bounded ambient witness also check independently.
Nothing in this review blocks a separate normal correctness/performance
benchmark under that declared scope.

[EXECUTED frozen target] The reviewed `GENERAL_FIXED_SPAN.md` has SHA-256
`5d99740f9f329e0a45f9c45bcd0db684b49f66660db567d81bfc169dbca4edb9`.
`linear_audit.py`, `linear_results.json`, all 16 query files, the public
fixture and the reference equation source are pinned in `results.json`.
Their hashes remained unchanged. This review writes only its owned directory.

## 1. Arbitrary fixed Y and the exposed package

[DERIVED] Work over F_q after the public group and Y are fixed, before the
uniform secret master is sampled. For rank r and k=d-r, the assumptions
`U=[L N]` invertible and `YN=0` imply that

```text
(t,a) uniformly in F_q^r × F_q^k -> s=Lt+Na uniformly in F_q^d,
Ys = YLt.
```

[DERIVED] This proves the full joint law of master, public group elements
and all issued scalar keys, including their correlations. It does not assume
the function keys are independent of the public key. In fact YL has column
rank r, so those scalar keys determine t. The remaining public values along
N are protected only under the stated computational assumption.

[DERIVED] For full-row-rank Y, the displayed pivot construction is correct:
in the pivot/free row order,

```text
U = [ I  -(Y_P)^(-1)Y_F ]
    [ 0         I       ].
```

[DERIVED] It is invertible regardless of any squared norm. The identity
block on the free coordinates makes N full column rank, and YN=0 makes its
columns a basis of the entire kernel. Therefore any admissible difference
has a unique efficient decomposition `x1-x0=Nv`; with this basis, v is just
the difference on the free coordinates. Redundant rows may be removed for
basis construction and restored when computing all original keys YLt.
The rank-zero and k=0 cases are well defined; if k=0, every admissible pair
is identical and the distinguishing gap is zero.

[EXECUTED] An independent finite-field implementation checked **all 890**
two-by-two and two-by-three matrices over F_2 and F_3. Its 20,988 sampling
cases verify bijectivity, exact issued-key values, kernel spanning and the
decomposition above. This includes redundant rows, zero rows and full-column
rank. These checks use public algebra only.

## 2. The DDH transition and adaptive mask composition

[DERIVED] In mask transition ell, the simulator knows t and all a_j except
a_ell. It computes each public coordinate using the supplied `A_ell=g^a`
and the known scalar contributions. All issued keys remain YLt. Thus the
setup has exactly the honest law in either DDH world and has not used any
future message. The shared challenge B is not exposed before the selected
request.

[DERIVED] At that request, earlier masks are fresh uniform elements, the
selected mask is the supplied C, and later masks are `B^(a_j)`, computable
because those exponents are known. This is precisely the adjacent pair of
hybrid distributions with a **shared B**. No independence between the DDH
tuples for different directions is assumed: only one unknown direction and
one DDH challenge are used in any execution of the reduction.

[DERIVED] After all k masks are randomized, condition on the actual prior
view and B. The pair was chosen before these fresh masks. Translating the
joint mask vector by `(g^(-v_j))_j` carries the right ciphertext to the left
ciphertext and preserves its joint uniform law. Every subsequent adaptive
interaction is the same computation on equal distributions. This justifies
`s_(j,k)=1/2`; replacing only one mask generally need not suffice when k>1.

[DERIVED] For request hybrids H_j with the first j answers left, the real
selected challenge satisfies

```text
s_(j,0) = 1/2 + (p_(j-1)-p_j)/2.
```

[DERIVED] The k mask differences telescope to `(p_(j-1)-p_j)/2`, then the
T request differences telescope to `(p_0-p_T)/2`. The padded uniform rank
over T*k transitions therefore defines one uniform DDH distinguisher with
absolute event gap `Delta/(2M)`. It does not choose the largest hybrid gap,
align local signs, or run the adversary T*k times. Setup and all ordinary
answers use the actual transcript in this single run.

[DERIVED] The note now explicitly covers both padded ranks and actual
request ranks that are never reached. Their outputs are fair. The LR
interface's common rejection/output is used on invalid pairs in every
intermediate game, so no endpoint-only admissibility assumption is smuggled
into the proof. Both corrections requested in the 3D review are present.

[EXECUTED nonvacuous k>1 control] An independent k=2, T=3, M=8 toy has
messages depending on the public key, exposed key and actual ciphertext
history, along with public early stopping and a common-abort branch. Its
endpoint hybrid probabilities are

```text
202/729, 10/27, 265/729, 263/729.
```

[EXECUTED] Six actual adjacent mask transitions have both positive and
negative gaps. Their signed sum is `-61/1458`; padding by M=8 gives DDH
gap `61/11664`, exactly the endpoint gap `61/729` divided by 2M=16.
The enumeration includes 972 checks of the public-key simulation using only
one unknown direction, 62,208 unreached cases and 46,845 common-abort cases.
The small group is used for exact identities, with no hardness claim and no
state recovery or extraction procedure.

## 3. Quantitative and sampling details

[DERIVED] The main exact-group-sampling formula is correct:
`Delta <= 2M epsilon_DDH`, with the DDH adversary's actual resources counted.
For polynomial d,m,T and uniform polynomial-time generation of Y/bases, the
mixture and simulation remain polynomial. Matrix algebra and the public-key
simulation must be charged; the potentially O(dk) group-power construction
is a reduction cost, not a measured setup performance result. A simulation
can optimize its known scalar contributions, but the stated upper bound is
conservative and adequate.

[DERIVED minor zero-bound notation] `M<2Tk` implies the displayed strict
`Delta<4Tk epsilon_DDH` when epsilon_DDH is positive. If bounds are allowed
to equal zero, write `Delta<=4Tk epsilon_DDH` for that corollary. The primary
exact `2M` theorem is unaffected. T=0 or k=0 has zero endpoint gap and does
not require a nontrivial selected transition.

[DERIVED] The scalar-draw count is conservative. A selected transition uses
r mask coordinates t, k-1 known a_j, at most k-1 independently randomized
earlier masks, and at most T ordinary-encryption draws. Thus `d+k+T`
bounds the reduction-owned draws, even though only one of T*k transitions
is executed. A rejection cutoff at R trials gives per-draw failure at most
2^-R and per-world coupling error at most `(d+k+T)2^-R`. Applying this
coupling in both DDH worlds yields the note's conservative bound

```text
Delta <= 2M * (epsilon_DDH + 2*delta_samp).
```

[DERIVED] The revised note correctly distinguishes this bounded-bit
correction from ideal/expected-time scalar sampling and from the endpoint
implementation's own sampler. It does not claim constant-time Python or
verified erasure. The same scalar cutoff does not silently bound physical
side channels or an unlimited lifetime adversary.

[EXECUTED] The concrete proof-loss arithmetic is correct: k=561 gives
M=1024 and coefficient 2048 for T=1; T=384 gives T*k=215,424, M=262,144
and coefficient 524,288. Neither coefficient is a numerical DDH security
estimate, and this review ran no larger encrypted benchmark.

## 4. Independent check of the 16-by-577 artifacts

[EXECUTED] A fraction-free Bareiss determinant implementation, separate
from the author's SymPy determinant, gives **-812,032,080** for the first
16 columns. An independent Fraction-based row reduction finds the same
pivots and reconstructs all 561 rational basis columns. Their canonical
top-block hash matches the saved artifact:
`9d2253ecc68b6390fee527f25154d37063947958c29543cd08f7b01933933462`.

[EXECUTED / DERIVED] The determinant is nonzero, smaller in magnitude than
the reference group order q, and coprime to q. Every rational coefficient's
denominator is invertible modulo q. All 561 columns were then independently
checked against the actual integer query matrix modulo that q. With the
source's prime-order-group assumption this gives field rank16 and kernel
dimension561, rather than inferring modular rank solely from rational rank.

[EXECUTED] The saved witness is a nonzero integer vector supported in the
first32 coordinates, with max absolute value3 and squared norm80. Its 16
integer dot products are exactly zero. Adding it to the pinned first public
fixture vector gives range [-22,24], leaves the final bias coordinate
unchanged and preserves all16 integer projection values. No lattice search
was rerun: verification of the supplied public witness is sufficient.

[DERIVED nonvacuity limits] These are three distinct statements:

1. The linear map has a 561-dimensional kernel over the field.
2. There exist two distinct vectors in the declared bounded integer box
   with exactly equal projections; the shifted public fixture gives another
   bounded ambient pair with its bias preserved.
3. There exist two distinct permitted **text encoder outputs** with the
   same projections and the desired semantic/private-input provenance.

[DERIVED] The artifacts establish the first two. They neither establish nor
claim the third. Ambient kernel dimension is not a lower bound on uncertainty
under a given prior, and a linear map with a large kernel may still be
injective on a particular restricted encoder image. No encoder-image
membership or private-state analysis was performed in this review.

[EXECUTED] The public query L1 calculation also reproduces the common
last32/int8 score bound14,219,936 and the proposed baby-step count5,333.
These are arithmetic sizes for a proposed bounded decoder, not an executed
decoder throughput result or a privacy restriction on group-valued reads.

## 5. Meaning of the resulting privacy and closure statement

[DERIVED] Public insertion and inversion of the exact expired ciphertext
preserve the encryption equations for integer window sums. Retained inputs,
snapshots, arbitrary local computations and all derived keys within the
fixed span remain part of the host view. Every paired input must agree on
the full span, including an input subsequently expired from a live queue.
The model does not give selected-query/sign-only release, future independent
key directions, revocation, authenticity or a single continuing history.

[DERIVED] The source setup permits public input encryption after honest
private initialization and erasure of the master. That is the conditional
credential-lifecycle positive; process arguments or a benchmark cannot prove
physical erasure or secrecy of issuer plaintext/coins. Additional setup-
correlated credentials, range proofs, release receipts or trusted services
must be included in a joint game before their transcripts are covered.

[DERIVED] The note's functional limitation is accurate: hidden differences
inside the kernel never change any permitted future fixed-span answer under
these linear updates. Storing Yx directly would reproduce the observable
learner. The cryptographic positive is retention of an encrypted raw
representation with fixed-span IND privacy, not demonstrated private
nonlinear cognition or expanded neural utility.

[SOURCE] The inherited equations and selective theorem were checked in the
prior independent review at
`../fixed_span/REPORT.md`, using ABDP,
[Simple Functional Encryption Schemes for Inner Products](https://eprint.iacr.org/2015/017),
local PDF SHA-256
`353f454857a5ef421ab7b17545b9657f5d192dc0a37f022cca7b71e916f84712`:
Figure2 and DDH definition p.7, Construction3.1 pp.7–8, Theorem3.2 and proof
sketch pp.8–9. This general fixed-basis proof is correctly labeled a new
derived specialization; no adaptive independent-key, simulation, quantum
or malicious-setup theorem is attributed to that source.

## Reproduction and handoff

[EXECUTED] Run from the repository root:

```sh
python3 -B research/learn_infer_only/experiments/adversarial_review/fixed_span_scaling/review.py > research/learn_infer_only/experiments/adversarial_review/fixed_span_scaling/stdout.txt
```

[EXECUTED] `results.json`/`stdout.txt` record exact controls, commands,
Python version, source hash and unchanged inputs. `review_manifest.json`
pins this report and the reused primary source/review evidence. There were
zero searches, PDF downloads/extractions, encrypted benchmark runs, recovery
or extraction experiments. No author's writing main, old negative audit,
shared ledger or companion was run or changed; no commit was made.

[OPEN bounded follow-through] Record independent acceptance and retain the
field/box/encoder-image distinction when reporting any later normal benchmark.
The optional zero-epsilon inequality wording is the only correction noted;
it does not affect the exact theorem, fixture arithmetic or benchmark scope.
