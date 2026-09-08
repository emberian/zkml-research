# Independent finite Gaussian sampler review

[DERIVED verdict, 2026-09-08] **Accepted as a finite uniform-bit sampling specification for the stated product distributions and repaired ring/scalar proof experiments.** The normalization, directed threshold, cutoff, fallback and hybrid-loss arguments are sound. No mathematical correction to the frozen specification is required. This acceptance does not establish an implemented sampler, a concrete CSPRNG, timing security, or the computational Ring-LWE/LWE assumption.

[SOURCE/EXECUTED] Reviewed source: `private_construction/public_setup_pq/finite_sampler/SPEC.md`, SHA-256 `2fef91992b092f93f6023a02b0072008a2f4f46e5601ea8fd71eb8d0972e1576`. Source paths below are relative to `research/learn_infer_only/experiments/`. Exact input hashes, author-result comparisons and output hashes are recorded in `source_pins.json`, `verification.json` and `manifest.json`.

[EXECUTED scope] This review read public mathematical specifications and saved parameter records, and ran deterministic integer/Fraction checks. It drew no random samples and generated no keys or ciphertexts. It ran no sampler, estimator, lattice reduction, cryptographic protocol or timing benchmark. It changed only this review directory. New web searches, Scry calls and PDF downloads: zero. The optional Karney/Falcon orientation paragraphs are not needed by the reference proof and were not independently source-audited here.

## Distribution and normalization

[SOURCE/DERIVED] `SPEC.md:13` defines mass `exp(-πk²/σ²)` for `σ=2^a`, `a≥0`. This is the pi-width convention. Writing the same exponent as `-k²/(2s²)` gives the shape parameter `s=σ/√(2π)`; neither `σ` itself nor a continuous standard-deviation formula is silently substituted for the discrete distribution's exact moments.

[DERIVED] The periodized Gaussian has Fourier coefficients `σ exp(-πσ²j²)`. Absolute convergence of both sums gives

```text
Zσ = σ Σ_j exp(-πσ²j²) ≥ σ.
```

[DERIVED] For the decreasing function `f(x)=exp(-πx²/σ²)` and integer `B=8σ`, the one-sided tail is at most `f(B)+∫_B^∞ f(x)dx`. Since `x/B≥1` in this integral, it is at most `σ² f(B)/(2πB)`. Doubling and dividing by `Zσ≥σ` gives exactly the specification's

```text
Pr[|k|≥8σ] ≤ (2/σ+1/(8π)) exp(-64π) < 3·2^-256.
```

[DERIVED] There is no residual factor of `σ`. The proof only needs `σ≥1`, `π>3` and `ln 2<0.7`; the latter follows from the explicit degree-four positive Taylor lower bound for `exp(0.7)>2`. The new bound is stronger than the earlier ideal-construction notes' valid but loose use of `Zσ≥1`. It does not rewrite those frozen notes.

[SOURCE/DERIVED] `SPEC.md:54` uses exactly `a+4` proposal bits for `[-8σ,8σ)`, and explicitly rejects `-8σ`. The remaining support is the symmetric strict interval `|k|<8σ`. Both the Gaussian fallback zero and the modular/flood fallback values remain inside their declared output ranges. A zero threshold near the cutoff simply removes mass covered by the rounding analysis; no floating-point underflow assumption is involved.

## Directed threshold and finite nonvacuity

[DERIVED] The 80-term Machin sums are exact rational sums before their endpoints are rounded once to the `2^-320` grid (`SPEC.md:75`). The first omitted arctangent term is positive. Thus the interval orientation, including the subtraction of the second arctangent, is correct. Per-term rounded summation would require a different width account, but that is not the specified algorithm.

[EXECUTED] Independent exact arithmetic finds the same grid endpoints as the author's checker; their width is one grid unit, within the declared bound of three. It checks the rational Machin width `<2^-360` and `81!>2^320` without a floating-point acceptance test.

[DERIVED] Multiplying by `k²/(256σ²)<1/4` and outward rounding encloses `z=πk²/(256σ²)` inside `[0,1]`, with width at most four grid units. Induction on the two nonnegative term recurrences encloses `Qz^j/j!`. Clipping an upper term to `Q` is sound because `z≤1`. The signed sum uses lower even/upper odd terms for its lower endpoint, and the reverse for its upper endpoint. Subtracting one grid unit from the lower endpoint pays the even Taylor polynomial's remainder.

[DERIVED] The term-width recurrence `d_j≤(d_(j-1)+4)/j+2` gives `d_j≤8`. The initial exponential interval width is at most `641`; eight monotone directed squarings give at most `(641+2)256-2=164606<2^19` grid units. The exact power is `exp(-256z)=exp(-πk²/σ²)`. Flooring the final lower endpoint to 256 bits therefore loses less than `2^-256+2^-301<2^-255` per weight. This covers every permitted `a,k`, including `a=0` and `k=0`.

[EXECUTED] Twenty-three selected public threshold controls at widths `1,1024,2^25,2^32` include zero, one, central points and the last admissible positive coefficient. The independently computed 96-term exact rational Taylor enclosure, followed by 600-bit directed powers, lies within the specified 320-bit interval in every case. These finite controls support the general proof; they are not an exhaustive proof over all integers or a randomized sampler implementation.

[DERIVED/EXECUTED clarification] The default recurrence produces `Lσ(0)=2^256-1`; the explicitly permitted shortcut gives `2^256`. Both satisfy the stated error contract and yield nonzero central acceptance. A stored 256-bit table must leave the shortcut implicit or special-case zero. The author's `RESULTS.json` explicitly records that interpretation. Without the shortcut, the default thresholds fit the declared 256-bit entries. The finite law is inhabited: for example, at `σ=1`, zero and both signs of one have positive accepted mass.

## Rounded law, cap and output transcript

[DERIVED] Let `Z_S` be ideal mass on the strict support and `E` the mass removed by lower thresholds. The normalized cut law is the convex mixture

```text
P_cut = (1-E/Z_S) P_retained + (E/Z_S) P_removed.
```

[DERIVED] Hence its distance from `P_retained` is at most `E/Z_S`, rather than requiring division by `Z_S-E`. If `E=0`, the laws coincide. The specification's bound `E<M·2^-255` and `Z_S≥σ(1-τ)` gives rounding distance `<64·2^-256` and per-attempt acceptance `α>1/17`.

[DERIVED] For any output value, summing the geometric first-success probabilities through attempt R yields its retained-law probability multiplied by `1-(1-α)^R`. Thus conditioning on success within the cap does not distort the retained law. The complete output law is a mixture with the zero fallback. Its distance from the retained law is at most the cap-failure probability, with no post hoc discarding of failed transcripts. The exact inequality `(17/16)^16>2` proves `(16/17)^4096<2^-256`.

[EXECUTED] An independent exhaustive two-attempt finite-weight control checks this mixture identity on all 16,384 public proposal/acceptance tapes. A separate rational example checks the removed-mass normalization inequality. These exercise the probability argument, not a cryptographic distribution.

[DERIVED] The resulting uniform per-output bound is

```text
ν = 68·2^-256,
TV(finite Gaussian output, ideal Dσ) < ν.
```

[SOURCE/DERIVED] The protected transcript consists of output values and the specified recipient rows, not the private rejection tapes, seeds or running-time observations (`SPEC.md:27`). Independent fresh bits permit sequential product coupling even when subsequent classical messages are adaptive. Applying the same classical-input quantum channel cannot increase trace distance; no new claim about superposition sampling interfaces or leaked execution traces follows.

## Repaired parameters and proof-wide loss

[SOURCE/EXECUTED] The sampler targets the repaired records, not the earlier baseline counts: `ring_candidate/hardness/GRID.json` SHA `de246339b8321791cba308e01ef0f929a42d725e3bbdd7a8b533622a7011031a`, point `ring_joint_repair_16384`, has `N=16384,w=64,σK=2^25`; `alternatives/hardness/REBUILT.json` SHA `b945fd60fa17bbd002f229167b915b10b23733be7db65950fe6a119dbcbe8574`, selected row `n=16384,l=262144`, has `σK=2^32`. Both have error width `2^10`, `d=577,r=16,T=384`. Only their public parameter fields are used; no estimator result is promoted to a security premise.

| Gaussian quantity | Repaired ring | Repaired scalar |
|---|---:|---:|
| Actual 16 recipient rows | 16,777,216 | 4,194,304 |
| All 384 error vectors | 402,653,184 | 100,663,296 |
| `Qactual` | 419,430,400 | 104,857,600 |
| `Qred=(d+T)·dimension` | 1,007,681,536 | 251,920,384 |
| `2Qactual+4TQred` | 1,548,637,700,096 | 387,159,425,024 |

[DERIVED/EXECUTED] These counts match the existing fixed-coordinate proofs: actual setup draws only r secret rows; a computational reduction can sample all d hypothetical rows, simulate the non-target public encryptions, and use the provided challenge without learning its secret/error. Charging T complete error vectors also covers one unnecessary target allowance. Actual finite-to-ideal replacement costs `Qactual·ν` in each of the two bit worlds. Replacing an ideal computational distinguisher by its finite simulation changes both challenge worlds, costing `2Qred·ν`; the original theorem's multiplier `2T` produces `4TQred·ν`. Statistical intermediate distributions can remain ideal mathematical distributions. There is no omitted second-world factor, T-fold actual setup, or assertion that hypothetical absent-row secrets exist in deployment.

[EXECUTED] The combined Gaussian coefficient is `1,935,797,125,120<2^41`, giving additional Gaussian loss `<2^-208`. This is a conservative sum across two separate constructions, not a claim that they form one jointly executed protocol.

[DERIVED/EXECUTED] The uniform-range algorithm has acceptance at least one half and cap error at most `2^-512`; power-of-two ranges accept immediately. We independently count actual uniform draws as `A+(d-r)n+T(n+d)`, using `A=wN` for the ring and `A=ln` for the scalar case. These are respectively 16,753,024 and 4,310,671,744 outputs. The scalar's full `2^32`-entry public matrix is included. Flood widths use 249/250-bit proposal words for repaired exponents 247/248, not the old baseline exponent.

[EXECUTED] A still looser reduction allowance additionally reserves three full d-row uniform arrays and a spare target vector, while charging full A even when it is supplied by the challenge. Its two-world weighted sum is `6,716,480,587,264<2^45`. It dominates the author's sufficient allowance and confirms uniform loss `<2^-467`. Combined independent-bit sampling loss is therefore `<2^-207<2^-192`. The original ideal theorem's statistical error and its computational advantage remain separately charged.

## Strict resources and remaining scope

[DERIVED] Each draw has a strict cap of 4096 attempts and `4096(a+260)` bits. A threshold uses at most 179 integer products plus the specified exact divisions, shifts, sums and comparisons. Of those, 176 have operands at most 321 bits; the initial three depend on the coefficient's bit length. The fixed Machin precomputation is additional finite work. These operations admit bounded polynomial circuits when dimensions and operand lengths are polynomially bounded. The direct algorithm has no table of exponential size in `a` and no unbounded irrational-comparison loop.

| Actual Gaussian workload upper bound | Repaired ring | Repaired scalar |
|---|---:|---:|
| Expected attempts | 7,130,316,800 | 1,782,579,200 |
| Worst-case attempts | 1,717,986,918,400 | 429,496,729,600 |
| Expected integer products | 1,276,326,707,200 | 319,081,676,800 |
| Worst-case integer products | 307,519,658,393,600 | 76,879,914,598,400 |
| Expected bit allowance | 1,929,463,726,080 | 482,865,053,696 |
| Worst-case bit allowance | 464,887,260,119,040 | 116,342,074,114,048 |

[EXECUTED/DERIVED] These exact Gaussian totals match the author. They are upper bounds, not measurements, and exclude the adversary and the protocol's other arithmetic. The separately counted actual uniform-range worst-case bit allowances are 2,474,373,742,592 for the ring and 646,664,854,306,816 for the scalar. Optional threshold tables cost 524,256 bytes for the error width, 17,179,869,152 bytes for the ring key width, and 2,199,023,255,520 bytes for the scalar key width, with the zero-entry convention above. No table was created.

[DERIVED clarification] Every output, including fallback, satisfies the strict key/error coefficient bounds. The flood sampler also stays inside its finite interval. Consequently the abstract finite algorithms satisfy the existing bounded-noise decoding argument for every tape under the declared message/range promises. This is stronger than merely transferring the ideal coefficient-tail correctness event. It does not prove a program's arithmetic or decoder implements those algorithms, and it does not remove the distributional privacy charge.

[OPEN] Fixed precision and caps certify these fixed finite experiments. A general asymptotic negligible-error theorem would need parameters scaled with its security parameter and total polynomial workload. The current polynomial-circuit observation concerns runtime, not that missing asymptotic error statement. The strict cap is distinct from the expectation of at most 17 attempts; early exit still gives value-dependent execution. Padding alone would not prove a side-channel model.

[OPEN] Uniform private bits, their independence and secrecy are explicit premises. A concrete CSPRNG changes the statistical model and needs a separately charged computational assumption at the actual output length and reduction resources, with the same QPT/advice convention. The construction's classical adaptive interface, fixed policy/coalition, and exact small-noise LWE/Ring-LWE assumptions are unchanged. This sampler result supplies no computational-security endorsement or permission to run cryptographic experiments.

## Reproduction

[EXECUTED] Independent command, exit zero with empty stderr; stdout equals `results.json`:

```text
python3 research/learn_infer_only/experiments/adversarial_review/finite_sampler/check.py > research/learn_infer_only/experiments/adversarial_review/finite_sampler/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/finite_sampler/stderr.txt
```

[DERIVED] The source proof and exact finite arithmetic checks support the scope above. No Lean proof, implementation verification or performance result is claimed.
