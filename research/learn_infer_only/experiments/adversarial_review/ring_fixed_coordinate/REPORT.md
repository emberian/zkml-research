# Independent ring fixed-coordinate construction audit

[DERIVED — accepted conditionally] No blocking algebraic or statistical-proof correction was found in the frozen [candidate](../../private_construction/public_setup_pq/ring_candidate/CANDIDATE.md), [ring regularity proof](../../private_construction/public_setup_pq/ring_candidate/RING_REGULARITY.md) and [parameter note](../../private_construction/public_setup_pq/ring_candidate/PARAMETERS.md). The accepted result is a conditional fixed-policy/fixed-coalition construction in the stated ideal sampling model. Its ring counting, Gaussian quotient bound, augmented joint-mask argument and constant-coefficient compression are supported by the source/math audit below. No computational-security endorsement is made.

[DERIVED — exact finite ledger] The public arithmetic witness supports

```
Adv_public < 768 epsilon_RLWE + 2^-168
correctness-tail failure < 2^-203
```

[DERIVED] The first expression leaves the advantage for the exact stated Ring-LWE problem unbounded. It also excludes sampler approximation/cutoff, side channels and implementation discrepancies. The second is a separate coefficient-tail bound for the specified workload. An ideal exact-Gaussian reduction is not automatically a literal worst-case bounded QPT reduction: a finite sampler or cutoff and its distribution/resource accounting must be supplied, or the computational sampling convention must explicitly accommodate ideal/expected-time sampling. The notes already identify this open obligation; this audit does not erase it by accepting the integer inequalities.

## Frozen inputs and source access

| Frozen note | SHA-256 |
| --- | --- |
| `CANDIDATE.md` | `5010b72b024aa7154504a7c0dd0de306fe0068b3af3b33b5026b444c510a0dc2` |
| `RING_REGULARITY.md` | `2926555d5842bb71af7b16caec3eef512a9c7cfea99e877b862bcfea79d30e85` |
| `PARAMETERS.md` | `c23732e366fe5966ddf971c0f69fdf51cec41bee134d0bf3e4da19367631b78d` |
| Author `MANIFEST.json` | `703e824295a40357f44d3a8cfa073ae2f6c1411b24783a83ca1c6e4f7992fbdb` |

[SOURCE] Read the full three notes and public arithmetic script/results. Primary-source inspection used the local pinned extracts of Mera–Karmakar–Marc–Soleimanian [2021/046](/Users/ember/dev/gh/forks/IACR-eprint-mirror/2021/46.pdf), Gaussian definition, Theorem 2, §5 and the Appendix C surjectivity assertion; Stehlé–Steinfeld [2013/004](/Users/ember/dev/gh/forks/IACR-eprint-mirror/2013/004.pdf), π-normalization on printed p.6, Lemmas 2.1/2.4 on p.7 and ideal/low-coordinate counting in Lemma 3.2, pp.15–16; LPR [2013/293](/Users/ember/dev/gh/forks/IACR-eprint-mirror/2013/293.pdf), §2.6 including Definitions 2.20/2.21, Theorem 2.22 and the discrete conversion; and GPV [2007/432](/Users/ember/dev/gh/forks/IACR-eprint-mirror/2007/432.pdf), Corollary 2.8, p.10. The SS p.7 render was independently visually inspected to resolve the infinity-norm smoothing formula. The implementation-paper pins were checked for integrity only; no performance/security theorem from them is endorsed.

[EXECUTED] [source_pins.json](source_pins.json) records exact audit inputs and access levels. The source author's six PDF/extract hashes, frozen scalar reference hash and final artifact manifest were checked. The earlier scalar regularity and hardness results are not dependencies of this review. This lane used no external search, crypto/estimator/attack program, Gaussian sampling, private-state inspection, or companion/source edit.

## Ideal counting and structured ring regularity

[DERIVED] For the power-of-two cyclotomic and completely split prime modulus, the CRT map is a bijection `R_q -> F_q^N`. Uniform entrywise ring matrices therefore induce independent uniform `k×w` matrices in the CRT slots. Surjectivity requires full row rank in every slot, giving exactly

```
rho_rank(k) = 1 - (product_{i=0}^{k-1}(1-q^(i-w)))^N
           <= N sum_{i=0}^{k-1} q^(i-w).
```

[DERIVED] This is a ring-appropriate argument. No claim that coefficient multiplication matrices have independent scalar entries is used. The old source test is insufficient: for a nontrivial CRT idempotent `e`, `a=(1,0,0)` and `u=(1,e,0)` each contain a unit, and `u` is not a ring multiple of `a`, yet the two rows coincide in any slot where `e=0`. This refutes the particular Appendix C sufficient-condition assertion, not the entire paper, its implementation, or Ring-LWE hardness. The new proposal avoids conditioning on that test and explicitly pays the unconditional rank event.

[DERIVED] The short-vector proof correctly classifies a fixed nonzero row tuple `s` by its common vanishing CRT set `S`, of size `v`. For each independent column of the random ring matrix, `A^T s` is uniform on the `N-v` active slots and forced to zero on `S`. The probability of any fixed compatible `w`-tuple is therefore `q^(-w(N-v))`; at most `q^(k(N-v))` choices of `s` are charged. This remains valid for zero divisors and for zero polynomial entries in the resulting tuple.

[DERIVED] A nonzero integral polynomial vanishing in `v` split slots has norm divisible by `q^v`: equivalently, its multiplication matrix modulo `q` has nullity at least `v`, forcing that divisibility of its determinant. The cyclotomic polynomial is irreducible over the rationals, so a nonzero degree-`<N` polynomial has nonzero integral norm. Parseval and AM–GM give `|Norm(t)| <= ||t||_2^N <= (sqrt(N)||t||_infinity)^N`. Consequently no nonzero short polynomial exists once `v >= (1-theta)N` for `B=q^(1-theta)/sqrt(N)`.

[DERIVED] In the remaining ideals, the degree-`v` generator has nonzero constant coefficient. Its multiplication map on degree-`<N-v` multipliers is injective on the lowest `N-v` product coefficients. Thus those low coefficients determine the entire residue polynomial. Since `2B<q`, their allowed integer lifts are unique. The proposal's rounding-safe count

```
(2 ceil(B)-1)^(N-v) <= (2B+1)^(N-v) <= q^((1-theta)(N-v))
```

[DERIVED] follows from `B>=1` and `sqrt(N)>=4`. Unlike a bound with nonintegral `2B` as a literal count, this controls the endpoints explicitly. Zero entries are counted; the entire tuple alone must be nonzero. Summing over vanishing sets and nonzero `s` yields the claimed `min(1,2^N q^(-N theta (w theta-k)))`. The zero tuple `s=0` contributes only `q`-divisible lifts, whose nonzero infinity norm is at least `q>B`. No surjectivity conditioning was smuggled into this argument.

## Gaussian normalization, duality and the joint tuple

[SOURCE/DERIVED] The numerical Gaussian is explicitly `exp(-pi ||z||^2/sigma^2)` on coefficient integers. Its `Nw` independent coefficient law is exactly the lattice Gaussian on `Z^(Nw)` with this parameter. The SS definitions and Lemmas 2.1/2.4 use this convention. The inconsistent-looking width/ρ notation in 2021/046 is not used to transfer numerical widths. No continuous Gaussian density replaces discrete mass modulo `q`.

[DERIVED] Under coefficient Euclidean inner products, `f(X^-1)` is a signed permutation and multiplication by it is the adjoint of multiplication by `f`. Therefore finite-field annihilator duality gives `Lambda_A^*=(1/q)L(iota(A))` even for nonsurjective matrices. Involution preserves the uniform matrix distribution. The short-vector bound gives the stated lower bound on the dual infinity minimum. The visually checked SS Lemma 2.1 does use `1/lambda_1^infinity(Lambda^*)`, so no Euclidean/infinity substitution or missing dimension factor is required.

[DERIVED] SS Lemma 2.4/GPV Corollary 2.8 then bounds the Gaussian quotient distance by `2 delta` when `sigma` exceeds the stated smoothing threshold. The kernel contains `q Z^(Nw)`, hence it is full rank. On the surjective event its quotient is exactly the desired full output ring module. Bad rank or shortness is paid once for the whole shared-matrix experiment. Conditional on a good matrix, independent secret rows admit a product hybrid costing `2h delta`. This establishes the stated joint bound `rho_rank+rho_short+2h delta`.

[DERIVED] Retaining independently sampled recipient rows and their products is valid as a common channel from the retained matrix. A replaced row's secret is not retained with its replaced output. This distinction is essential. The proof does not assert independent CRT components of a short Gaussian, regularity after rare transcript conditioning, or regularity for a matrix selected as a function of those secrets.

## Privacy hybrid and constant-coefficient projection

[DERIVED] The actual setup creates only actual recipients' Gaussian rows and samples missing public ring outputs directly uniformly. The all-row Gaussian master is confined to the comparison experiment. Setup regularity can replace the `d-r` missing rows while retaining all actual recipient credentials, and is paid once per endpoint. Honest independent sampling and fixed registration remain premises; this is not a malicious public-matrix or seeded-matrix theorem.

[DERIVED] For one target challenge, the scalar cancellation shift is `t_i=const(<z_i,e>)`. Its absolute value is bounded by `C=wN BK BE` on the stated coefficient event. Shifting the independent integer flood by this value changes its law by at most `min(1,|t_i|/(2F+1))`, with any subsequent reduction modulo `q` only decreasing statistical distance. Summing over `d` transmitted scalar components and adding key/error tails gives `S`. The shifts may depend on all secret rows and errors; retaining those variables while conditioning on their values justifies the bound without an independence assumption on the shifts.

[DERIVED] After this shift, the target second components are computable from the known comparison rows and the supplied Ring-LWE challenge `c0`, so the reduction requires neither its unknown secret nor its error. Replacing `c0` by independent uniform `u` is precisely the explicitly assumed computational step. At that point, and only at that point, `[A;u]` is an independent uniform two-row ring matrix. Augmented regularity applies to the full pairs `(P_i,<u,z_i>)`, retaining `A,u,Z_J` and exposed products.

[DERIVED] Projecting each second ring output to its constant coefficient is a deterministic map of this full joint distribution. An independent uniform ring output projects to an independent uniform scalar, still independent of the entire first ring output `P_i`. Hence each unexposed retained scalar masks the message coordinate. Exposed coordinates have equal centered `a_i` by the valid-pair condition. This preserves adaptive public-view-dependent messages: the full tuple is replaced before applying the adversary/history channel, rather than asserting uniformity after conditioning on a rare transcript. Classical interactions with a QPT adversary and its independent quantum advice/state are compatible with this statistical data-processing step; no cloning or rewinding is used.

[DERIVED] Other challenge replies in the sequential hybrid use the original public encryption algorithm and fresh independent coins. They can be generated from the retained public tuple and do not need unexposed rows. Comparing both target bits to the same random-mask experiment gives the factor `2T`; the initial setup comparison remains outside that factor. The stated `epsilon_RLWE` must bound the relevant reductions at their actual resources and advice class, with the sampling qualification stated above.

[DERIVED] Constant-coefficient compression preserves correctness as well as this hybrid. Negacyclic multiplication gives `const(bc)=b_0 c_0 - sum_{k=1}^{N-1} b_k c_(N-k)`, so the recipient phase is exactly `Delta a_i+f_i-const(<z_i,e>)`. Discarded ciphertext coefficients do not feed `c0` or any retained scalar. The proof supports the projected algorithm directly; it need not establish a `dN`-output full-ring flooding bound first. Every one of the `d` original message coordinates remains, while `dN` independent plaintext coefficients are not claimed to survive.

## Correctness, nonvacuity and exact arithmetic

[DERIVED] For combinations with integer coefficient L1 norm at most `W`, error is at most `W(F+C)` and the accumulated centered coordinate lies in `[-WX,WX]`. Adjacent actual codepoints are separated by `Delta`; the wraparound gap is `q-2WX Delta >= Delta` because `D>=2WX+1` and `q>=D Delta`. Thus `Delta>2W(F+C)` is sufficient for unique circular nearest-codepoint decoding. Rounding `D v/q` would be a different decoder. Exact expiry cancels the original error; total stream length and allowed live coefficient norm are separate bounds.

[DERIVED] The policy and challenge premises are not intrinsically empty: `Y=[I_r 0]`, `B=I_d` inhabit full row rank and invertibility at the advertised dimensions. For any allowed invertible extension, `B^-1 e_k` with an unexposed coordinate `k` gives a nonzero equal-projection challenge difference from zero. This is an ambient `F_p^d` witness, not a semantic learner-image witness or verification of a particular application policy matrix.

[EXECUTED] The independent [check.py](check.py) verifies the 289-bit prime's order certificate directly: every prime divisor must be `1 mod 2^256`, hence exceed the integer's square root. It also verifies the exact primitive `2N`-root order and prime `p`; no probable-prime library or estimator is used. The smoothing inequality is checked after raising to integer powers, and rank-plus-shortness bounds are exact rationals. All 17 possible coalition sizes pass the statistical ledger, rather than only its endpoints.

[DERIVED/EXECUTED] The Gaussian tail uses its actual normalizer being at least one, then bounds the decreasing discrete tail by its first term and an integral. At the integral threshold `8 sigma`, the resulting `3 sigma exp(-64 pi) < 3 sigma 2^-256` bound justifies the stated union tails. Independent integer/rational checks confirm `C=2^58`, decoder separation, correctness below `2^-203`, and statistical privacy terms below `2^-168`. There was no numerical Gaussian sampling or estimation.

| Independent finite check | Result |
| --- | --- |
| Every `2×3` matrix over `F_5` | 14,880 of 15,625 have rank two; matches the exact product law |
| CRT column images with one/zero common vanishing slots | Uniform on exactly 5/25 image points with 125/25 preimages each |
| Every element of `F_17[T]/(T^4+1)` and all CRT ideals | Low-coordinate injectivity holds for all 83,521 elements and 16 ideals |
| Source-test idempotent | CRT ranks `[2,1,1,1]` despite unit entries and no ring-multiple relation |
| Signed product / involution adjoint | 6,642 constant-product and 26,406 adjoint controls pass |
| Full first output retained, second projected | 125 joint atoms, exactly five preimages each |
| Integer interval translations | 224 exact total-variation controls pass |

[EXECUTED] Command, exit zero and full output are retained in [check.log](check.log) and [results.json](results.json):

```sh
python3 research/learn_infer_only/experiments/adversarial_review/ring_fixed_coordinate/check.py > research/learn_infer_only/experiments/adversarial_review/ring_fixed_coordinate/check.log 2>&1
```

## Costs and decisive remaining hypothesis

[EXECUTED] Recomputed bit-packed costs match the note: 262,721 retained ciphertext residues occupy 9,490,797 bytes at 289 bits each, compared with 94,847,488 bytes for all full-ring components. Public `A` is 9,469,952 bytes and public `P` is 85,377,536 bytes, totaling 94,847,488 bytes. This is the `A,P` table only, excluding policy `B`, parameters and encoding overhead. Compression changes ciphertext costs, not the full public-output table.

[EXECUTED/DERIVED] A strict key-tail event allows 28-bit signed coefficients and 917,504 bytes per recipient, or 14,680,064 bytes for 16 recipients. These are not worst-case storage bounds for an unbounded Gaussian. Inclusive `[-2^27,2^27]` storage needs another bit; the note correctly distinguishes it. Encryption counts are 64 full ring products plus 2,363,392 scalar coefficient products, 262,144 Gaussian coefficients, 577 scalar floods and 4,096 uniform-secret coefficients. A recipient read has 262,144 coefficient products. These counts do not bound NTT implementation cost, arbitrary-precision multiplication, packing overhead, allocator peaks or time.

[OPEN — computational security not accepted] The exact hypothesis is one uniform ring secret of coefficient dimension 4,096, reused in 64 ring samples, with independent coefficient errors of π-width `2^10` modulo the specified 289-bit prime. It is not ordinary LWE with an independent scalar matrix or a 262,144-dimensional independent secret. Exact arithmetic gives `2^-279 < sigma_e/q < 2^-278`; that small relative width is a parameter fact, not a hardness result. Key smoothing width and huge public flooding do not raise the Ring-LWE challenge's error width.

[SOURCE/OPEN] LPR's stated theorem involves its dual ideal, canonical-error convention, sample-count-dependent parameters and a defined asymptotic setting; its discrete conversion also has hypotheses. The `sqrt(N)` coefficient-to-canonical norm factor is necessary geometry, not a complete reduction from that theorem to this finite coefficient-Gaussian instance. No finite approximation-factor/security-level assessment, exact dual/discretization mapping, sampler certificate or estimator output is supplied. Neither source implementation parameters nor previous scalar-LWE results fill this gap.

[DERIVED — disposition] The author and root were notified of the accepted algebra and the explicit computational/sampling qualifications before this review was frozen. No source correction is requested within that scope. No total security bits, practical performance, nonlinear learning, changed policy, malicious registration, adaptive corruption, selected-answer-only release, integrity, or operator isolation follow from this audit.
