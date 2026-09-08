# Direct polynomial-curve full unique decoding

[EXECUTED] This package proves the degree-M curve extension of the earlier
affine full-UD theorem over the existing `reedSolomonCode`, `hammingDist`,
`AgreesOn`, `CorrelatedAgreement` and `ProximityGenerator` definitions. The
saved final checks and exact axiom census are recorded in `manifest.json`.
Root owns the later combined umbrella build; this package makes no combined
integration claim on its own.

[DERIVED / checked interface] `curveFullUDCardCore` states: for M≥1,d≥1,
2e+d≤n, and more than M·n good scalars of
`Σ_(j=0)^M z^j u_j`, each within e errors of the existing degree<d RS code,
there is one set S of at least n−e positions on which every u_j agrees with
an RS codeword. M=0 is excluded; e=0 is admitted and exercised by
`zero_error_core_fires`.

[EXECUTED] `reedSolomonCode_isGeometricProximityGenerator_fullUD` converts this
integer core to the existing geometric-generator interface at open radius
`0<δ<(1−d/n)/2`, with error `M·n/|F|`.
`hasGeometricMutualCorrelatedAgreement_fullUD` reuses the existing WHIR
PG-to-MCA reduction at the same conservative radius and error.

[EXECUTED] `CurveFriChallenge.lean` exports elementary uniform-probability
statements:

- `curve_uniform_sound`: actual non-CA coefficient family gives error M·n/|F|.
- `arity8_curve_sound`: eight coefficients, one scalar, error7n/|F|.
- `arity8_injected_curve_sound`: `Σ_(r<8)β^r u_r + β^8 g`, error8n/|F|,
  where g is fixed before β. It need not itself be an RS codeword.
- `arity8_injected_fixed_prefix_sound`: u and g may depend on a prior prefix;
  the bound holds for each fixed prefix. This does not establish that a runtime
  provides such a prefix, or that an injected input cannot depend on the current β.

[EXECUTED nonvacuity] F101, length5, degree<2 has positive one-error witnesses
for M=7 and8 with all101 scalars good. Every coefficient word has an actual
changed coordinate and is proved not to be a codeword, using the existing RS
minimum-distance theorem. Legal-word families also inhabit the e=0 branch and
fire the core. An F17, length2, degree<1 example embeds the cubic
`Z(Z−1)(Z−2)` in eight coefficient slots: three good scalars exceed the naive
unscaled n=2 bound while correlated agreement fails. Its radius1/5 is explicitly
proved strictly inside the conservative UD range. The separate note's Python
control uses all seven roots; this Lean control needs only three to refute the
unscaled bound. The note's earlier radius wording is corrected in
`../../arity_eight_soundness/ERRATUM.md` without changing its sealed bytes.

[SOURCE] Mathematical source: BCIKS20, *Proximity Gaps for Reed-Solomon Codes*,
2020/654 Theorem6.1 and §6.1, local mirror only; WHIR2024/1586 Theorem4.8.
See `../../arity_eight_soundness/NOTE.md`, ERRATUM and SOURCES.json for exact
source pins and inspected statements. No new web/Scry queries or PDF downloads
were added during this formalization.

[SOURCE / implementation] BW/Schur/bivariate proof bodies adapt the earlier
Apache-2.0 ArkLib port at commit22dbd4e836c15a21f68889afa69b7130da04abbb.
Existing notices are retained. The original BW matrix and code semantics are
reused. The existing affine specialization lemma supplies the error-locator
certificate for each curve word; the generic PolynomialGluing theorem is
imported unchanged. The degree-M rank proof is supplied by the separate frozen
`polynomial_curve_kernel/` successor, which preserves the old degree-one
public theorem as a wrapper. Its source SHA256 is
`f510b6cc0c648a3583e3eefa49e283b2186add24d2e4df71f3afeb9b06a3fa91`.

[DERIVED dependency details] Matrix entries in the locator block have challenge
degree≤M, maximal minors≤M(e+1), locator coefficients≤Me, numerator
coefficients≤M(e+1). The PS inputs are A:(e,Me), B:(e+d−1,M(e+1));
`|good|>Mn` and2e+d≤n prove its strict ratio bound. The quotient has x-degree
at most d−1 and challenge degree at most M. Taking its coefficient polynomials
produces the common agreement set.

[EXECUTED packaging] `polynomial-curve-full-ud.patch` adds only ten new modules.
It does not replace the affine proof files, the kernel file, or any frozen
carrier/tower/sampling/timing artifacts. Root should select
`polynomial_curve_kernel` instead of the older kernel package, then apply this
additive patch. Proposed umbrella imports are `Selvage.CurveFriChallenge` and
`Selvage.CurveFullUDTeeth`; their imports cover the other eight modules.

[OPEN] There is no actual arity-eight FoldingData/runtime adapter, multi-height
farness invariant, batched coherent-query soundness theorem, challenge sampler
or Fiat–Shamir/BCS bridge here. The scalar is genuinely uniform in the stated
finite-field experiment. The previously frozen nineteen-independent-binary-
challenge budget is not transferred to β,β²,β⁴. No ErrorBudget or security-bit
claim is changed.
