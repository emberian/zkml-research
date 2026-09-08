# Explicit joint regularity for the split-ring candidate

[DERIVED, 2026-09-08] This is a ring-specific bound. It does not apply the
ordinary-LWE uniform scalar-matrix lemma to a structured multiplication
matrix. It adapts the ideal/short-vector argument of Mera–Karmakar–Marc–
Soleimanian 2021/046, Theorem 2 and Appendix B, while retaining unconditional
matrices, charging CRT rank failure, and making the elementary counting
rounding explicit.

## 1. Exact distribution and notation

[DERIVED] Let `N≥16` be a power of two, let `q` be a prime with
`q=1 mod 2N`, and set `R=Z[X]/(X^N+1)`, `R_q=R/qR`.
Coefficient vectors use the ordinary Euclidean norm, not the canonical
embedding norm. Draw `A←R_q^(k×w)` independently and uniformly entrywise,
where `w>k≥1`. Let `z∈R^w` have `Nw` independent coefficients with
weight `exp(-π t²/σ²)`. All Gaussian statements below use this convention.

[SOURCE] 2021/046 §2.1 and Appendix B use the CRT isomorphism
`R_q≅F_q^N`. Its Theorem 2 handles `k` ring outputs and conditions the
matrix to be surjective. Its Appendix B Lemma 9 bounds short vectors in a
random row module; its cited source is Stehlé–Steinfeld, EUROCRYPT 2011.
The expanded local version, 2013/004, Lemma 3.2 pp.15–16, supplies the
ideal norm and coefficient-counting argument. We use that argument directly
below and keep the rank-failure event instead of conditioning it away.

[SOURCE convention check] 2021/046 Definition 1 uses an `exp(-x²/(2σ²))`
presentation and also introduces a different `ρ` notation. Therefore no
numeric width from that paper is silently assigned to the present `π`
convention. Stehlé–Steinfeld 2013/004 §2.1, Lemmas 2.1 and 2.4 state the
smoothing and quotient bounds with the `exp(-π||x||²/σ²)` convention.
Those are the numerical Gaussian facts used here. GPV 2007/432 Corollary 2.8
is the original quotient source. No real Gaussian density is substituted for
the folded discrete mass modulo `q`.

## 2. CRT rank failure and the source test seam

[DERIVED exact rank law] Since the CRT map is a bijection, uniform `A`
becomes `N` independent uniform `k×w` matrices over `F_q`. Hence

```text
ρrank(k) = Pr[A:R_q^w→R_q^k is not onto]
         = 1 - [Π_(i=0)^(k-1)(1-q^(i-w))]^N
         ≤ N Σ_(i=0)^(k-1) q^(i-w).
```

[DERIVED] The condition is full row rank in **every** CRT component.
A failure in just one component leaves a nonzero annihilating functional
on the output and makes full uniformity impossible. The above failure is
paid once for the whole joint tuple, not once per recipient or output row.

[SOURCE/REFUTED: sufficient test only] 2021/046 §5 rejects `a` without a
unit component and ciphertext `u` without a unit component or with `u=sa`.
Appendix C p.39 says those conditions make the map `[a;u]` surjective.
That implication is false in a split ring with zero divisors. Let `e` be
any nontrivial CRT idempotent, and take

```text
a=(1,0,0),       u=(1,e,0).
```

[DERIVED counterexample] Both vectors have a unit component; `u` is not
any ring multiple of `a`. Nevertheless, in a CRT component where `e=0`,
the two rows coincide, so the map has rank one. This is a public algebraic
counterexample to the test, not an attack on an implementation. The new
candidate draws `a` and encrypts without these rejection tests, and uses
the exact unconditional rank law above. Its proof does not invoke the
paper's adaptive-key theorem.

## 3. Explicit short-vector bound using ideals

[DERIVED parameters] Choose a real `θ` satisfying

```text
k/w < θ < 1,
B = q^(1-θ)/sqrt(N) ≥ 1,
γ = wθ-k > 0,
ρshort(k) = min(1, 2^N q^(-N θγ)).
```

[DERIVED lattice] Let `L(A)⊂Z^(Nw)` be all coefficient vectors of
`t∈R^w` such that `t=A^T s mod q` for some `s∈R_q^k`, including all
integer lifts. Then

```text
Pr_A[λ1^∞(L(A)) < B] ≤ ρshort(k).
```

[DERIVED proof, common vanishing components] Fix a nonzero tuple
`s=(s1,...,sk)`. Let `S` be the set of CRT components where all `s_i`
vanish, and write `v=|S|`. A vector `t=A^T s` must vanish on `S` in
each of its `w` ring entries. In every other component at least one
`s_i` is nonzero, so, for a fixed compatible `t`, independent uniform
columns of `A` give probability exactly `q^(-w(N-v))`. For fixed `S`
there are at most `q^(k(N-v))` possible tuples `s`. A zero divisor is
thus counted through its actual ideal, rather than treated as a unit.

[SOURCE/DERIVED ideal norm] If a nonzero integral polynomial `t` of degree
below `N` vanishes in `v` of the split components, its principal ideal
is contained in the ideal of index `q^v`. Thus its nonzero integral norm
has absolute value at least `q^v`. Equivalently, reduction modulo `q`
of its multiplication matrix has kernel dimension at least `v`, so the
Smith invariant factors imply `q^v` divides its determinant. Parseval
for the complex roots of `X^N+1` and the arithmetic–geometric mean give

```text
q^v ≤ |Norm(t)| ≤ ||t||2^N ≤ (sqrt(N)||t||∞)^N.
```

[DERIVED] Consequently there is no nonzero such `t` with `||t||∞<B`
when `v≥(1-θ)N`. When `v<(1-θ)N`, write the ideal modulo `q` as
the multiples of the degree-`v` polynomial `h_S` formed by those linear
factors. Its constant coefficient is nonzero. Multiplication by `h_S`
maps the lowest `N-v` coefficients of the multiplier injectively to
the lowest `N-v` coefficients of the product: the corresponding
triangular matrix has nonzero diagonal. Thus an integral polynomial
in this ideal with all coefficients in `(-B,B)` has at most

```text
(2 ceil(B)-1)^(N-v) ≤ (2B+1)^(N-v) ≤ q^((1-θ)(N-v))
```

possibilities. Here `B≥1` and `N≥16` imply `2B+1≤3B≤q^(1-θ)`;
also `2B<q`, so an allowed coefficient has at most one integral lift
of a given residue. This rounding-safe bound includes the zero polynomial
in each entry; only the entire vector `t` is required to be nonzero.

[DERIVED conclusion] Union over at most `2^N` sets `S`, then over
`s` and all `w` entries of `t`. The probability is bounded by

```text
2^N max_(v<(1-θ)N)
    q^[k(N-v)+(1-θ)w(N-v)-w(N-v)]
 = 2^N max_v q^[-γ(N-v)]
 ≤ 2^N q^[-Nθγ].
```

[DERIVED] A tuple `s=0` produces only vectors divisible by `q`, whose
nonzero infinity norm is at least `q>B`; it contributes no short vector.
No conditioning on surjectivity was used in this calculation.

## 4. Smoothing and the complete joint output bound

[DERIVED dual lattice] Let `Λ_A={z∈R^w:Az=0 mod q}` in coefficient
space. The involution `ι(f)=f(X^-1) mod(X^N+1)` is a signed permutation
of coefficients; multiplication by `ι(f)` is the Euclidean adjoint of
multiplication by `f`. Scalar finite-field annihilator duality gives

```text
Λ_A* = (1/q) L(ι(A)).
```

[DERIVED] This identity holds for all `A`, including nonsurjective ones.
Since `ι(A)` is uniform whenever `A` is, the preceding bound gives
`λ1^∞(Λ_A*)≥q^-θ/sqrt(N)` outside an event of probability `ρshort(k)`.

[SOURCE/DERIVED smoothing] Stehlé–Steinfeld 2013/004 Lemma 2.1 gives,
for any full-rank lattice in dimension `D=Nw`,

```text
ηδ(Λ) ≤ sqrt(ln(2D(1+1/δ))/π) / λ1^∞(Λ*).
```

[DERIVED] Thus for `0<δ<1/2`, if

```text
σ ≥ sqrt(N ln(2Nw(1+1/δ))/π) q^θ,
```

the quotient distribution of a Gaussian secret modulo `Λ_A` is within
`2δ` of uniform outside the short-vector event. If `A` is onto,
the quotient is exactly `R_q^k`; otherwise charge `ρrank(k)`.

[DERIVED multiple-row theorem] Independently sample `h` Gaussian rows,
and replace their `k` ring outputs under the same `A` by independent
uniforms. Retain `A` and any other independently sampled secret rows
and their products. The complete joint distributions have distance

```text
δ_h(k) ≤ min(1, ρrank(k)+ρshort(k)+2hδ),       h≥1;
δ_0(k) = 0.
```

[DERIVED proof] Conditional on a good matrix, the product hybrid costs
at most `2hδ`. Bad rank or short-vector events depend only on the
matrix and cost at most their probability for the entire tuple. Other
secret rows and their products are a common randomized channel from the
retained matrix. A replaced row's secret is **not** retained alongside
its newly uniform output. There is no assertion after arbitrary rare
conditioning, grinding or secret-dependent matrix selection.

[DERIVED application] Setup uses `k=1`, `A=a`, and replaces `d-r`
absent public rows while retaining all `r` actual recipients' secrets.
The challenge mask uses `k=2`, `A=[a;u]` with independent uniform
`a,u∈R_q^w`, and replaces `d-j` pairs while retaining only the fixed
coalition's secret rows. Projecting the second ring output to its
constant coefficient preserves the joint bound and produces an independent
uniform scalar mask. The full first ring output remains public.

## 5. Scoped limits

[DERIVED] This result assumes a prime modulus that splits `X^N+1`
completely and independent uniform ring entries. It does not establish
the same formula for ramified rings, unsplit moduli, arbitrary prime
powers, fixed identity blocks, seeded nonuniform matrices, or any
adversarial rejection transcript. Those cases require their own ideal
and distribution analysis. It is a coefficient-Gaussian statement, not
a claim that CRT components of a short Gaussian are independent.

[OPEN] The candidate proof still needs its explicit ordinary QPT Ring-LWE
hypothesis, scalar flooding bound, credential lifecycle, correctness/range
contract and sampling implementation scope. These are separate from the
regularity theorem; a small statistical error does not measure LWE hardness.
