# Independent review of the repaired finite reduction

[DERIVED verdict, 2026-09-08] **Accepted within the stated finite mathematical and conditional QPT scope, after one pre-freeze proof-text correction.** The reviewed `FINITE_THEOREM.md` is the 404-line file with SHA256 `7ae20bc50552283e4688466b966c7e2d1265613f4fb8a49c2909aaeb77bd7bd4`; the author's manifest is SHA256 `2938fd3de8cf77bd80d2a8f2c17109f4d9dc8db8d6563763faf26c4dea435f01`. No further required repair was found. This is an independent source/math review, not a Lean proof or a cryptographic security experiment.

[DERIVED scope] This is a new, explicitly bounded repair of the cited reduction. It does not establish that the literal published sampling recipe works unchanged, nor a concrete cryptographic security level. The ideal distributional comparisons are valid at finite parameters. Turning them into a resource-bounded QPT reduction still requires the stated finite-bit tuple-level sampler discrepancy and resource certificate, together with the exact LWE hypothesis.

## 1. Findings and source displays

[REFUTED: initial draft integrality argument; corrected before freeze] The initial draft claimed `Zb'` was integral. In fact, `b'=Q(b+e')+f` leaves continuous `Zf`, so that intermediate expression need not be integral. The correct identity is

```
h = Z(f+c) = Z(b'+c) - [I_d|0]b.
```

[DERIVED] Since `b'+c` is integral, `Z` is integral, the selected entries of the input lift `b` are integral, and `ZQe'=0`, the hint is integral. The author replaced the incorrect sentence before the pinned freeze. The conclusion and error budget are unchanged. A fixed rational counterexample in `check.py` has `Zb'=5/2` and `h=0`, and verifies the corrected identity.

[SOURCE] I inspected ALS Definition 3, printed p.9, which uses discrete errors `D_(Z,αq)`, and the complete displayed recipe on printed p.22. The latter has continuous balancing width `a sqrt(ξ²I-Q'Q'^T)`, continuous added input noise of width `a`, and discretization width `sqrt(2)aξ`. The locally rendered page confirms these factors. Source: `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/608.pdf`, SHA256 `a7d5c231b70961ea59ca544c91b2392fb35c166c88e42b898640cfdc7dbb94d0`.

[SOURCE] BLPRS pp.6–7 uses `exp(-π||x||²/r²)`, so continuous variance is `r²/(2π)`. Lemma 2.8 gives discrepancy at most `4ε` under `rs/sqrt(r²+s²) ≥ η_ε(Λ)`. Lemma 2.10 gives discrepancy at most `8ε` when its discrete-coset width is at least `η_ε(Λ)`. These were read from the local text and the complete p.7 display. Source: `/Users/ember/paperbin/blprs-classical-hardness-lwe-arxiv-1306.0281.pdf`, SHA256 `1d2b27f2969f59610257cb2498a73a66b2a8ee142780ac6200a45ca9f86dbf9d`.

[DERIVED] Therefore the draft's covariance repair is correct. After the discrete-plus-continuous step, the parameter covariance is `2a²Q'Q'^T`. The printed balancing recipe followed by discretization yields `a²(3ξ²I+Q'Q'^T)`. Multiplying the balancing width by `sqrt(2)` instead gives spherical intermediate width `sqrt(2)aξ` and final discrete width `2aξ`. With `a=1`, `ξ=2`, and `Q=I_3`, the printed and repaired final covariance-parameter diagonals are respectively `[12,13,13]` and `[16,16,16]`; the desired diagonal is `[16,16,16]`. This deterministic exact control concerns parameter covariance, not a sampled distribution. It supports a source-recipe correction; it does not refute every possible proof of the published asymptotic statement.

## 2. Gaussian image, singular values and the gadget

[SOURCE] AR arXiv:1308.2405v2 defines logarithms as base two on p.4; its Gaussian convention uses the same π-normalized width. Definition 3.1 on p.5 requires bounded columns and pairwise orthogonal short integral right-inverse vectors. Theorem 3.2 on p.6 gives image distance `≤2ε` when the least singular value of the width matrix is at least `(1+q1*q2) g_(M-n)(ε)`. Lemma 4.2 on p.8 supplies quality with failure at most `2^-n` under the draft's explicit constants. I inspected the complete p.5, p.6 and p.8 displays, including the square-root boundaries. The exact local source path and hash are in `source-pins.json`.

[DERIVED] Let `V=[v_1|...|v_n]`. Orthogonality and `||v_i||≤q2` imply `||V||op≤q2`; `XV=I` then gives

```
||y||² = <X^T y, V y> ≤ q2 ||X^T y|| ||y||,
s_min(X) ≥ 1/q2.
```

[DERIVED] This directly proves the required lower singular-value bound. No random-matrix net lemma or unquantified spectral constant is needed. The column bound separately gives `||X||op≤||X||F≤sqrt(M)*q1=Amax`.

[DERIVED] The symmetric `S` defined by the singular vectors satisfies `XS²X^T=σ2²I`, `s_min(S)≥σ2/Amax`, and `||S||op≤σ2*q2`. AR's image theorem applies for each fixed quality `X` to that admissible `S(X)`. Conditional independence of all `L` sampled coefficient columns gives the full joint image comparison retaining `X` at cost `2LεI`. It covers every target row simultaneously; a further factor counting recipient rows is not missing.

[DERIVED] The construction tests only the two spectral bounds. Some nonquality matrices may pass those tests, but their image behavior is not silently asserted: their total mass remains covered by the `2^-n` quality-failure term. Quality matrices always pass. Keeping aborts rather than resampling preserves the stated unconditioned comparison.

[SOURCE/DERIVED] AR Lemma 2.1 at dimension `M`, `c=1`, and smoothing error `1/4` yields the factor `(5/3)(sqrt(2πe)e^-π)^M`. Its assumptions follow from the separate `g_M(1/4)` term in `b`. The elementary base is less than `1/2`, giving the strict upper bound `2^(1-M)`. The union bound over `L` columns gives the Frobenius-norm abort term. For a rational sufficient control, `π<22/7`, `π>3`, and `e>8/3` imply its squared base is less than `(44/7)(3/8)^5<1/4`; this rational comparison is checked exactly.

[SOURCE/DERIVED] LPSS p.8 explicitly allows the unrestricted first-row variant; its Theorem 17 proof on p.13 contains the block gadget used here. I inspected that displayed block matrix. The draft transposes consistently: `H[X^T;X2]=[I_n;0]` and `G=H^-T` make the first `n` rows of `G` the desired `[X|X2^T]`. Each factor is an integral permutation/shear with absolute determinant one. Each operator norm is at most one plus the norm of its inserted block, so `||G^-1||op≤(1+Amax)(1+σ2*q2*sqrt(LM))`. This is a separately derived operator-norm bound; LPSS's longest-column norm is not treated as an operator norm. Source: `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2014/494.pdf`, SHA256 `b7715df4acca8bd615c0a8a885d781300f9d80d371cc820da53b9e3004de358d`.

[EXECUTED] A deterministic rectangular fixture with `(n,M,L)=(2,3,4)` checks the exact block product and `|det H|=1`. These finite controls support orientation and constant checks; the general identities above are mathematical derivations.

## 3. Joint information and hybrid accounting

[DERIVED] In the LWE world, choose an integer lift `As+[0;e0]`. The convolution condition is `a/sqrt(2)≥g_(m-d)(εc)`; the repaired balancing noise makes the ideal continuous noise spherical. The discretization condition is `sqrt(2)aξ≥g_m(εr)`. Integer lift changes do not alter the discrete coset or the output modulo `q`. The final hint satisfies `h=Ze` throughout; therefore data processing transfers the Gaussian comparisons jointly to ciphertext and hint. The ideal error is independent of `G,A,s`, even though the hint is intentionally correlated with it.

[DERIVED] In the uniform world, introducing independent `e0` through the exact representation `b=v+[0;e0] mod q` preserves the input law. The integral shift `Qv` drops out of the coset. Conditional on `G`, multiplication by unimodular `Q` preserves uniformity. The resulting uniform term is jointly independent of the generated error and hint. No claim is obtained by conditioning on an observed rare syndrome or successful transcript.

[DERIVED] After the Gaussian conversions, the ideal tuple depends on `G` only through the exposed hint matrix `Z`. Consequently the joint gadget-row replacement, including aborts, is charged once per world. The exact two-world accounting is

| Source of discrepancy | Contribution to distinguishing-gap loss |
|---|---:|
| First-errorless block rank | `2δ3` |
| Entire gadget-row law, including abort | `2δG` |
| Discrete-plus-continuous convolution | `8εc` |
| Final coset discretization | `16εr` |
| Implemented reduction sampler | `2δs` |

[DERIVED] Thus `εred=2δ3+2δG+8εc+16εr+2δs` agrees with the draft. The total-variation convention is the usual factor-one-half convention; advantage is the difference of acceptance probabilities, not a guessing advantage.

[DERIVED row-exposure scope] The setup replacement uses `h=d-r` missing rows and can retain all actual recipient rows. The augmented-mask replacement uses `h=d-j` and retains the coalition's secret rows `Z_J`; other recipient rows' public products can remain in the joint view. It does not retain a replaced row's secret while independently uniformizing that same row's syndrome. Such a stronger claim would fail. The fixed-coalition theorem's stated view respects this distinction.

[DERIVED QPT scope] A common QPT channel cannot increase the trace distance of the classical input states. The single target invocation needs no cloning or rewinding. Any nonuniform advice class must also be permitted by the LWE assumption and independent of fresh setup/secret/challenge coins. Arbitrary separately supplied secret-correlated auxiliary states and superposition interfaces are outside the theorem. Earlier adaptive challenge histories are common channels, rather than additional conditioning assumptions.

## 4. Prime powers and integer constants

[SOURCE/DERIVED] ALS pp.34–35 constructs the first-errorless block by completing a full-rank `d×n` matrix. For `q=p^k`, full row rank modulo `p` is exactly surjectivity over `Z_q` and permits completion to an invertible matrix. The uniform reduction modulo `p` gives

```
δ3 = 1 - product_(i=0)^(d-1)(1-p^(i-n))
   ≤ (p^d-1)/((p-1)p^n).
```

[EXECUTED] I exhaustively checked 5,042 small public matrices across six `(p,k,n,d)` cases, including nonfield moduli 4, 8 and 9. In every case the rank formula matches the exact failure count, and full rank modulo `p` agrees with the image containing every vector of `Z_(p^k)^d`. This does not use the false rule that any nonzero residue difference has a uniform full-ring image.

[DERIVED] The integer certificate is sufficient. `Q1,Q2,A,B,Kbar` each dominate their real-valued counterpart by ceiling inequalities. In particular, `g_(M-n)(λ/(2L))²<LM+LL+κ+3`; `LM+4` dominates both the quarter-smoothing and coefficient-sampler thresholds. Strict `M>30n(Ls+Ln)` preserves the strict AR row-count premise. `ξ≥2Kbar` yields the required strict positive-definiteness margin.

[DERIVED] With `λ=2^-κ`, `κ≥10`, and `n-d≥κ`, all three gadget terms are at most `λ`, so `δG≤3λ`, and the rank term is strictly below `λ`. The convolution and discretizer inequalities have the correct squared widths. Therefore the ideal loss is at most `32λ`, and a separately supplied `δs≤λ` gives `34λ`. At `κ=160`, these are sufficient finite inequalities; they are not an LWE hardness estimate.

[EXECUTED] Independent integer/Fraction computations reproduce every classification in the frozen parameter report:

| Profile | Certificate | Required power of two for `ξ` | Failed original conditions |
|---|---|---:|---|
| Original full-source normalization | fails | `2^50953` | strict `M`, operator norm |
| Original fixed, `n=1024` | fails | `2^153` | operator norm |
| Original fixed, `n=4096` | fails | `2^177` | strict `M`, operator norm |
| Adjusted finite, `n=1024` | passes | `2^153` | none |
| Adjusted finite, `n=4096` | passes | `2^178` | none |

[EXECUTED] All ten setup/mask regularity certificates also pass. The two adjusted rows have base LWE error widths `2^18` and `2^13`. Their LWE dimensions, modulus/noise assumptions and resource requirements remain precisely those stated by the author. Failure of an original row means failure of this sufficient certificate, not a necessary lower bound or refutation of the published asymptotic theorem.

[EXECUTED] For `d=577,r=16,T=384`, the full statistical ledger independently checks as

```
j=0:  Adv_public ≤ 768 εLWE + 1,803,144 / 2^160,
j=16: Adv_public ≤ 768 εLWE + 1,753,992 / 2^160.
```

[DERIVED] Each displayed statistical term is below `2^-139`, conditional on the sampler discrepancy. Setup distance is paid twice overall, while each fresh-challenge hybrid pays twice its reduction and mask losses. The setup term is not multiplied by `T`. These totals do not bound `εLWE`, scheme-sampler discrepancy, correctness failure, or application no-wrap errors.

## 5. What remains unverified

[OPEN] BLPRS Lemma 2.3 supports the ideal discrete Gaussian sampling calls at the stated width thresholds. For anisotropic sampling, the basis `S^-1` has longest Gram–Schmidt vector at most `1/s_min(S)`, so the transformed-lattice invocation is valid. It does not independently certify all finite-bit square roots, covariance decompositions, continuous samples, truncation, spectral decisions, and output-length bounds needed by an implemented QPT reduction. The theorem explicitly leaves the entire classical output tuple's per-world discrepancy `δs` and its polynomial resource bound as obligations. Setting `δs=0` for ideal mathematics alone cannot satisfy those computational obligations.

[OPEN] No concrete sampler, runtime bound, QPT LWE hardness, cryptographic implementation, or correctness-tail workload was verified here. In particular the adjusted 4096 profile changes dimensions and needs a new correctness/cost calculation. No prior frozen theorem or source recipe was silently replaced.

[DERIVED verdict impact] No change to deployed-security claims in `docs/VERDICTS.md` follows. A maintainer may record the new conditional finite repair and the source-formula discrepancy in the relevant §7.8 research discussion; root owns that decision. The accepted contribution is an explicit mathematical loss bound with a clearly unresolved finite-sampler/resource boundary.

[EXECUTED corpus/instruments] Reviewed the four exact primary PDFs and local `pdftotext -layout` extracts pinned in `source-pins.json`, the frozen theorem/parameter/input/output files, and the cited regularity/fixed-coordinate notes. Used local `rg`, text reads, six rendered page inspections, and the independent public-arithmetic script `check.py` (exit 0; command/output in `execution.json`, `stdout.txt`, `results.json`). Web searches, Scry SQL/schema, Kagi, PDF downloads, cryptographic programs, Gaussian sampling, estimators and private runtime accesses: all zero for this review. No field-wide absence claim is made.
