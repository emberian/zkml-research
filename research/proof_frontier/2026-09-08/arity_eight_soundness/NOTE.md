# Arity-eight FRI: the direct curve soundness seam

[DERIVED] The next proof target is **degree-M curve correlated agreement with
bad-scalar bound M·n**, with M=7 for a width-eight fold and M=8 when a fixed
next-height input is injected. Independent binary-round probability bounds do
not apply to the internal challenges β,β²,β⁴. This note does not change the
frozen binary ErrorBudget, sampled theorem, or tower.

## Statement first

[SOURCE] BCIKS20, *Proximity Gaps for Reed-Solomon Codes*, local mirror
`2020/654.pdf`, Theorem6.1, printed p28, and proof §6.1, pp29–30, gives exactly
the needed direct curve statement. For code dimension d and block length n,
its conservative UD condition is θ≤(1−d/n)/2; more than M·n close points on
`u₀+βu₁+…+βᴹu_M` force all M+1 words to agree with codewords on one set of
density at least 1−θ. [Primary paper](https://eprint.iacr.org/2020/654).

[SOURCE] WHIR Theorem4.8, printed p23, restates the geometric generator
`(1,α,…,α^(ℓ−1))` with error `(ℓ−1)n/|F|` in the unique-decoding regime.
Its Lemma4.10 supplies the generic PG-to-mutual-agreement connection.
[Primary paper](https://eprint.iacr.org/2024/1586).

[DERIVED target, not yet a checked theorem] Use existing `reedSolomonCode`,
`hammingDist`, and `AgreesOn`; add no second RS semantics. For field F,
finite ι, injective `dom : ι ↪ F`, naturals M≥1,d≥1,e≥0, and n=cardι:

```lean
-- Target shape; the eventual theorem takes u and A explicitly.
2*e+d ≤ n →
∀ (u : Fin (M+1) → ι → F) (A : Finset F),
  M*n < A.card →
  (∀ z ∈ A, ∃ w ∈ reedSolomonCode dom d,
    hammingDist (fun i => ∑ j, z^j.val * u j i) w ≤ e) →
  ∃ S : Finset ι, n-e ≤ S.card ∧
    ∀ j, ∃ w ∈ reedSolomonCode dom d, AgreesOn S (u j) w
```

[DERIVED] Integer rounding then gives, for `0<θ<(1−d/n)/2`, a geometric
`IsProximityGenerator` instance with error `M*n/|F|`. The probability corollary
has the negation of actual correlated agreement as premise, not an assumed
bad-set bound or a restatement of soundness. For any fixed coefficient family
that lacks CA, the uniform scalar close-event has probability ≤M·n/|F|.

## Actual width-eight and input injection

[SOURCE] Active breadstuffs vendor is
`vendor/plonky3-fri-82cfad73`; upstream revision
`82cfad73cd734d37a0d51953094f970c531817ec`. In `src/two_adic_pcs.rs:284–334`,
the implementation runs adjacent binary arithmetic passes and squares
`current_beta` at line326. Its verifier `fold_row:230–252` is interpolation
at β on the eight fibre points. `src/prover.rs:237–245` adds a new vector at
the folded height multiplied by `β^arity`; `src/verifier.rs:469–479` performs
the matching reduced-opening update. Exact source hashes are in SOURCES.json.

[DERIVED] With the fibre-polynomial decomposition
`f(x)=Σ_(r<8) x^r u_r(x^8)`, the complete width-eight arithmetic is
`F_β(y)=Σ_(r<8) β^r u_r(y)`. It has eight fixed coefficients, hence M=7.
Injection changes it to `F_β(y)+β^8 g(y)`: nine coefficients, hence M=8.
The code comment about maintaining independence is not a statement that β⁸
is statistically independent of β.

[EXECUTED cross-lane] `../p3_folding_transport/RESULTS.json` records independent
pure arithmetic/index checks for this identity, including mixed arities and
injection. That lane owns row-order, bit-reversal, twiddle and coset transport;
this note owns the probability condition. Its complete package is a separate
artifact, not a Lean proof imported here.

[DERIVED] At a fixed prior transcript prefix, u and g must be determined before
the round challenge. They may depend on earlier challenges. The next committed
folded word may depend on this β, as normal sequential timing requires.
Internal β² and β⁴ are deterministic after β: conditioning on that prefix does
not create fresh random challenges for the two later arithmetic passes.

[OPEN execution condition] A byte-level execution bridge must show that the
injected reduced-opening vector is fixed by earlier committed inputs and earlier
PCS randomness before this β. A root appearing before β does not alone prove
this: the opening/resolution and reduction randomness must also be traced.
The frozen root-resolution bridge gives a semantic rootwise word plus a BadRoots
alternative; it does not price that event or establish this new runtime adapter.

[DERIVED folding use] On eight-to-one fibres, common agreement of the eight
component words on n−e folded positions reconstructs a degree<8d word on at
least 8(n−e) source positions. Thus source θ-farness plus the M=7 theorem
bounds the close folded event by 7n/|F|. The same argument works with a fixed
injected g using M=8: CA of all nine words includes CA of the first eight.
It does not require g to be a legal codeword. A joint invariant that also detects
far lower-height inputs still requires a multi-height soundness proof.

[DERIVED exact dimensions] For the frozen actual carrier, |F|=2013265921⁴,
a first width-eight transition would have n=2¹⁷ and d=2¹⁶. The proposed direct
bounds are `7·2^17/2013265921^4` without injection and
`8·2^17/2013265921^4` with a fixed injected vector. Any output radius strictly
between0 and1/4 is in the conservative UD range; source2/5-farness implies
farness at such a smaller radius. These are per-round algebraic bounds, not
new security-bit claims. Neither the frozen nineteen-independent-binary-challenge
experiment nor its query-radius schedule models these batched rounds.

## Finite falsifiers and premise inhabitation

[EXECUTED] `python3 finite_controls.py > RESULTS.json` exits0, using exact
integer arithmetic modulo explicitly prime17 and101. These are finite controls,
not a proof of the general theorem. The script, output and source pins are saved.

[EXECUTED refutation: reusing the affine scalar bound on curves] Over F₁₇,
take D={0,1}, the dimension-one constant code, and v=(0,1). Let
`P(Z)=∏_(r=0)^6 (Z−r)`, and let u_j be its j-th coefficient times v.
Then the curve is P(β)v. Exactly seven challenges yield a codeword, although
n=2. No common agreement set has two positions. At real radius1/4 the close
event is still exact agreement, so the radius is positive and below the
conservative UD threshold. The unscaled n/|F| error is false for this family;
the sourced 7n/|F| bound is consistent. Replacing seven roots by eight gives
the fixed-injection degree-eight control.

[EXECUTED refutation: conditional-cardinality composition] In F₁₇ let the
second-step exceptional set after first challenge a be B(a)={a²}. Every such
set has one element. With independent a,b the event b∈B(a) has probability1/17;
with b=a² it has probability1. The script also records the nonuniform square
and fourth-power marginals. This refutes the proposed inference from binary
bad-set sizes, not FRI soundness.

[EXECUTED refutation: adaptively selected injected word] Keep u₁=v and all
other u_r=0. After β choose `g_β=−β^(−7)v` for β≠0 and g₀=0. Then
`βv+β⁸g_β=0` for all seventeen challenges. All are close, exceeding8n=16,
although u₁ is not a constant codeword. The missing fixed-coefficient premise
is indispensable; the degree-eight theorem does not cover this strategy.

[EXECUTED positive witness] In F₁₀₁, D={0,1,2,3,4}, d=2,e=1, for M=7 and8,
set `p_j(X)=(j+1)+(j+2)X` and change only the evaluation at position0 by
`j²+1`. Every scalar combination differs from its explicit degree<2 polynomial
at at most one position. All101 challenges are good, exceeding35 or40;
2e+d=4≤5, and all coefficients agree on S={1,2,3,4}. This inhabits positive
radius, positive dimension, strict many-good threshold, and common agreement.

## Minimal formal dependency split

[SOURCE existing checked interface] Frozen `formal/full_ud/src/` currently
implements the affine Fin2 case only. `Selvage/FullUDCore.lean:38 fullUDCardCore`
uses `FullUDBivariate.lean:20 bw_bivariate_of_many_close`, which uses
`FullUDInterpolation.lean:154 bw_bounded_kernel_of_many_close` and
`Theory/RSInterpolationKernel.lean:107 bounded_kernel_of_specializations`.
The general `BW_homMatrix` definition already accepts arbitrary ring-valued words.

[DERIVED exact generalization, following BCIKS20 §6.1] Retain that matrix,
replace its input word by `Σ_j C(u_j(i))*Z^j`, and obtain these degrees:

| Object | Degree bound in challenge variable Z |
|---|---:|
| matrix entry in the error-locator block | M |
| maximal minor | M(e+1) |
| error-locator A coefficient | Me |
| numerator B coefficient | M(e+1) |
| quotient at a domain position | M |

[DERIVED] The determinant/root-count and rank proof are the only lower algebra
changes. Polynomial specialization still uses the same error-locator product.
`Theory.PolynomialGluing.polishchuk_spielman` already takes arbitrary bidegree
bounds and is reused intact; its cardinality inequality becomes
`(e+d−1)/n + M(e+1)/|A| < 1`, forced by |A|>Mn and2e+d≤n.
Taking M+1 quotient coefficients yields the existing RS common agreement.

[OPEN formal work assigned] A new degree-parameterized kernel successor is owned
by polynomial_kernel. It keeps `Theory.PolynomialMatrixKernel`, with the
existing degree-one public theorem reduced to a wrapper, and adds
`Source.RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le (M e)`
returning nonzero kernel coefficients of degree≤M·e. No duplicated rank proof.
This lane owns fresh curve BW/PS/CA modules using that successor and the existing
RS definitions. Frozen affine modules and packages remain unchanged. Root owns
selecting the successor in the combined import closure.

## Scope and source search ledger

[OPEN] No direct degree-M curve theorem has been checked in Lean in this note.
No arity-eight adaptive transcript, multi-height invariant, coherent query bound,
Fiat–Shamir/BCS reduction, collision advantage, or changed ErrorBudget is asserted.
The source-backed target closes one algebraic seam when formalized.

[EXECUTED] New-task query counts: three primary-oriented web search queries,
two eprint abstract-page opens, zero Scry SQL/schema calls, zero PDF downloads.
Search results were noisy; the mathematical claim uses inspected local primary
PDFs and pinned source bytes, not search snippets. Older orientation counts are
separate. No field-wide or literature-absence claim is made. Corpus/instrument:
local mirror2020/654 and2024/1586, `pdftotext -layout`; existing notes and Lean/Rust
source files, `rg`/`sed`; finite examples, the saved Python script.
