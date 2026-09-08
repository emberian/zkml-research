# Independent audit of smudged-variant hardness estimates

[DERIVED outcome, 2026-09-08] **Accepted as a bounded heuristic parameter
audit and exact finite arithmetic repair.** The 612,717-byte baseline lacks
support for the modeled target and should remain rejected for implementation.
The selected larger row passes the named retained attack-cost comparisons
and the restricted theorem's finite correctness/statistical conditions. It is
not a certificate of QPT security, an equal-security comparison with ALS, or
authorization to implement either point.

[EXECUTED exact scope] The subject is the frozen
`private_construction/public_setup_pq/alternatives/hardness/` file set pinned
by absolute path, byte count and SHA-256 in this review's `INPUTS.json`.
`review_manifest.json` binds those inputs and all review artifacts. Author
source and results are read only; no author or estimator code was run by this
reviewer. The preceding smudged theorem/review remains unchanged.

[EXECUTED] Primary subject SHA-256 pins:

| File | SHA-256 |
|---|---|
| Author `AUDIT.md` | `53eeea3fc4e11cd03bcc6229ae47b42ddfe98c274acb4af90145eeb085a9fe57` |
| Author `REBUILT.json` | `b945fd60fa17bbd002f229167b915b10b23733be7db65950fe6a119dbcbe8574` |
| Author `MANIFEST.json` | `f3a8047121fb86d310daec4488bcbd1a311a7d269486e15f1e392a24d0c75359` |

## 1. Exact LWE instance, estimator convention, and primes

[SOURCE/DERIVED] The accepted restricted proof assumes ordinary decision
LWE with a uniform secret in `F_q^n`, a uniform unstructured matrix of
`l` rows, and independent centered integer Gaussian errors with mass
`exp(−πz²/1024²)`. The baseline is `n=1024,l=16384`; the selected repair
is `n=16384,l=262144,q=2^292+13`. Recipient width `2^32` and flood radius
`2^244` or `2^248` are different distributions, not substitutions for the
LWE error. These are the proof's unstructured samples, not a ring-LWE proxy.

[SOURCE/EXECUTED] The estimator archive is the exact locally retained
`53da5982597709ba0fdf94ea37a84d822310fd84` snapshot. Its tar SHA-256 is
`d838a23842bbe6d399e3f742847e0df28cc15108369390a159d864225b62c1c3`;
the tar's global commit header agrees. All 25 archived `estimator/` files
match the live snapshot byte-for-byte. The five hashes in every call manifest
and the prior eight-file environment provenance also match. This is an
archived source tree without a nested `.git`; the containing research
repository's HEAD is not its estimator version.

[SOURCE] Exact local estimator pins are under
`he_closure_costs/estimator/runtime/pinned-estimator/estimator/`:
`nd.py:9–34,68–96,227–293,386–402`, `lwe_parameters.py:24–65`,
`lwe_primal.py:228–255,801`, `lwe_dual.py:254–315,692–739`, and
`reduction.py:59–77,262–273,637–676,739–756,963–995`.
The prior environment/source audit and package lock were read for provenance;
no package was installed or modified.

[DERIVED/EXECUTED] The supplied `DiscreteGaussianAlpha(QQ(1024)/q,q)` first
cancels the exact rational `q`, then maps width 1024 to the estimator's
standard-deviation convention `1024/sqrt(2π)≈408.516895131067`.
All 76 retained records agree with that number to their printed precision.
`UniformMod(q)` supplies exactly `q` consecutive integer representatives.
The noise class uses real-valued Gaussian moments/support approximations;
its “standard deviation” is the conventional continuous-width conversion,
not an assertion that this is the exact second moment of the normalized
integer Gaussian. This qualification does not turn these heuristic models
into a distribution-exact attack analysis.

[DERIVED normal form] For `m≥2n`, the pin changes the uniform secret to an
error-distributed secret and reduces the sample count to `m−n`. To see the
map, split off an invertible first `n×n` block `A0` and form
`b1−A1 A0^−1 b0=e1−A1 A0^−1 e0`. The new matrix `−A1 A0^−1` is uniform,
with new secret `e0` and independent errors `e1`. In the uniform comparison,
the transformed response is uniform. The first block's rank failure is below
`1/(q−1)`. Thus baseline normal form has 15,360 samples and the selected
repair has 245,760; neither retains the original sample count after this map.

| [EXECUTED retained Sage proof result] role | Exact modulus |
|---|---|
| Baseline low | `2^288+127` |
| Baseline high | `2^289−493` |
| Selected repair | `2^292+13` |
| Repair sensitivity | `2^293−601` |

[SOURCE/EXECUTED] The retained procedure uses `next_prime(proof=True)`
and `previous_prime()`, followed by `is_prime(proof=True)` for both returned
endpoints. Local Sage10.8 `sage/rings/integer.pyx:5460–5559,6017–6102` was
read: the true proof flag invokes PARI `isprime`, while the false flag uses
`ispseudoprime`; next/previous prime search checks returned candidates.
The exact decimals, offsets, intervals and proof flags match independently.
These are source-backed retained author computations, not independently
rerun primality tests or exported certificates. No power of two is called
prime. The costs use the selected exact prime; testing endpoints does not
establish a hardness minimum over every prime in the interval.

## 2. Call integrity, normalization failures, and operative coverage

[SOURCE/DERIVED] Both primal wrappers normalize internally. Their baseline
uSVP and BDD results are valid outputs of the named heuristic models and
remain in the comparison. The direct public `LWE.dual` wrapper does not
normalize and calls an optimizer whose documented precondition is normalized
input. Therefore every raw dual row in the baseline, repair grid and original
validation is excluded from operative coverage, including finite-looking rows.
Recording a separate `normalized_repr` did not normalize that earlier call.

[SOURCE/EXECUTED] Four explicit low-level beta-2 dual probes reached estimator
code but failed because the bypassed wrapper had not registered `mem` for
`Cost.repeat`. The first six normalization-correction attempts instead failed
before estimator entry at `assert normalized.Xs==normalized.Xe`.
`NoiseDistribution` is a dataclass including vector length: the normalized
secret has 16,384 entries and the error has 245,760. Equal scalar Gaussian
laws do not make those complete objects equal. Both author and reviewer
identified this from the source and preserved traceback; the scalar mapping
itself was correct.

[SOURCE/EXECUTED] The successor `run_normalized_dual_final.py` checks matching
Gaussian class, zero mean and standard deviation, and checks the two lengths
separately before calling the direct dual wrapper with `params.normalize()`.
Its six authorized estimator entries completed. No estimator source changed.
The rejected preflight source and all failed attempts remain separate files.

| [EXECUTED] retained group | Driver attempts | Estimator entries | Operative finite results |
|---|---:|---:|---:|
| Baseline | 24 | 24 | 16 primal |
| Declared four-dimension repair grid | 24 | 24 | 16 primal |
| Declared endpoint/model validation | 12 | 12 | 8 primal |
| Baseline beta-2 probes | 4 | 4 | 0; errors |
| First normalization preflight | 6 | 0 | 0; assertion failures |
| Corrected normalized dual | 6 | 6 | 6 dual |
| Total | **76** | **70** | **46** |

[EXECUTED] There are 66 completed rows and 10 errors, no timeouts. Twenty
completed raw dual rows are excluded. All four `+Infinity` outputs belong
to that excluded set; they prove neither impossibility nor infinite security.
The checker verifies each declared parameter/model/attack Cartesian product,
unique row identities, exact modulus, original and normalized representations,
source pins, START/RESULT log counts, and retained empty stderr. The final
minima contain no raw dual result or failed attempt.

[SOURCE/REPORTED chronology] `REPAIR_GRID.md` records the 24-call grid,
12 validation calls and four beta-2 probes; `CORRECTIVE_CALLS.md` records
the selected-point normalization correction. Root's retained task messages
authorized six actual normalized estimator entries and allowed repairing
the preflight assertions while preserving all attempts. File contents and
row coverage support the declared sets; the review does not promote file
timestamps to a tamper-resistant proof of declaration chronology.

## 3. Results and model limitations

[SOURCE] All primal shape estimates use GSA. `ADPS16(classical)` costs its
core-SVP step as `2^(0.292β)` and `ADPS16(quantum)` as `2^(0.265β)`.
MATZOV uses the explicitly selected `list_decoding-classical` and
`list_decoding-dw` finite models; the latter is a quantum depth-times-width
metric. They are different operation models, not interchangeable hardware
seconds or universal quantum lower bounds. Changing the reduction model
does not quantize every other attack subroutine or cover QPT/qpoly advice.

| [EXECUTED] model | Baseline minimum log2 cost | Selected repair minimum log2 cost | Repair attaining attack / beta |
|---|---:|---:|---|
| MATZOV classical | 43.205449 | 208.327822 | BDD / 617 |
| ADPS16 classical | 11.680000 | 180.456000 | uSVP / 618 |
| ADPS16 quantum core-SVP | 10.600000 | 163.770000 | uSVP / 618 |
| MATZOV quantum depth×width | 47.605591 | 196.614978 | BDD / 617 |

[EXECUTED] Every baseline minimum is uSVP at the optimizer floor `β=40`,
with the same minima at both tested primes. This is a valid modeled floor
result, not a priced optimal LLL attack. In particular the ADPS16 core-only
values omit polynomial/finite costs and are not credible complete wall times.
They nevertheless do not support the proposed modeled threshold. The frozen
conditional theorem is unaffected; its hardness premise was never proved.

[EXECUTED] At the selected low prime, normalized dual costs are respectively
209.837139, 180.748000, 164.035000 and 198.201604, all at `β=619` and
all above the corresponding primal minima. The first grid point `n=8192`
already fails by valid quantum uSVP cost 59.89, so `n=16384` remains the
smallest declared grid dimension passing the tested selected-point comparisons.
At the upper sensitivity prime only the two declared validation models were
checked: minima 179.58 ADPS16 classical and 195.863914 MATZOV quantum
depth×width remain primal; corrected dual is again higher. No unrun all-model
upper-endpoint or continuum claim is inferred.

[SOURCE/DERIVED additional limit] The pin states MATZOV's fitted data cover
block sizes through 1024. The selected row's beta 617–619 is inside that
range; the unused `n=24576` primal grid rows at beta 1060/1062 extrapolate
past it. These larger rows are not needed to justify selection. GSA shape,
finite optimizer search and cost-model assumptions remain heuristic even
inside the fit range. Coverage omits hybrid guessing, dual-hybrid, BKW,
algebraic attacks, alternative shape models, and other current/future methods.

[SOURCE/DERIVED analytic check] The author additionally evaluates the empirical
dual length `1.0219^k q^(1024/k)` using the pinned LLL root-Hermite factor,
without generating a lattice or finding a vector. The retained low-endpoint
formula minimizes at `k=3072`, log2 length 192.0124, about 80 bits below the
sufficient norm ceiling 272. The integer optimum and logged formula costs
recompute. This is evidence under empirical geometry, not a proved algorithmic
upper bound. The deterministic `δ_LLL=3/4` determinant bound instead gives
log2 length about 542.808 at its optimum and fails that sufficient criterion.

[DERIVED conditional analytic statement] If a nonzero dual vector `v` is found
with `σe||v||≤q/64`, MP2011/501 Lemma2.8's exact centered-Gaussian
subgaussian bound shows that testing `|center_q(v^T b)|≤q/8` has gap at
least `3/4−1/q−2exp(−64π)`. The norm condition ensures `v` is nonzero
modulo prime `q`, so the uniform comparison is uniform. The bound proves
the test given such a vector; the empirical length prediction does not prove
the vector-finding premise. No vector or distinguishing experiment was run.

[DERIVED reduction-loss limit] Subtracting `log2(768)=9.5849625…` from a
modeled operation exponent is only informal margin arithmetic. These outputs
do not provide an advantage-versus-work curve for the theorem's loss factor.
In particular an estimated cost at a selected success probability cannot be
converted to certified adjusted QPT security bits by that subtraction.

## 4. Rebuilt finite theorem and storage

[DERIVED/EXECUTED] The repaired row retains
`σK=2^32,σe=2^10,BK=2^35,BL=2^13,d=577,r=16,p=28439893,W=32,T=384`.
Increasing height from `2^14` to `2^18` multiplies `lBKBL` by sixteen.
The corresponding `F=2^248` and prime interval `(2^292,2^293)` increase
flooding and available phase scale together; increasing dimension alone at
the frozen height would not pass the syndrome entropy requirement.

[DERIVED/EXECUTED] With `ε0=2^−192`, the MP/GPV general regularity proof
still has `ηZ<8`, hence `t<2^−29`. At the selected augmented dimension,
`293(n+1)−29l=−2,801,371`, far below the required margin. All four grid
dimensions satisfy the same regularity bound `δ_h<h2^−189`; the rank term
is separately negligible. Reusing the stronger-height simple certificate
would be unjustified, and is not how this bound is obtained.

[DERIVED/EXECUTED] The complete regularity term remains below
`444258/2^189<2^−170`; bounded smudging remains below
`443136/2^183<2^−164`. Repeated Gaussian tails are below `2^−185+2^−216`.
Their exact rational sum is `<2^−163`, still **plus 768 times the exact
uniform-secret QPT-LWE advantage**. Nothing in the heuristic costs supplies
that missing advantage bound against the matched advice class.

[DERIVED/EXECUTED] `D=d(p−1)/2≥2WX+1` and `floor(q/D)>2W(F+lBKBL)`
hold at the selected prime and throughout the stated interval. Independent
checking also bounds the centered phase with
`2WX/D+2WE/q_low<1`. Paying the common key-tail event once and all `T`
error vectors gives ideal correctness failure `<2^−194` for all allowed
combinations. The strict storage event remains `|K_ij|<2^35`; an inclusive
interval would need an extra bit. Private coins, exact or TV-bounded samplers,
fixed honest registration/coalitions and bounded integer closure are unchanged
premises of the previous theorem. Semantic encoder-image nonvacuity is still
separate from its ambient kernel witness.

| [EXECUTED] selected-row arithmetic | Exact count |
|---|---:|
| Ciphertext bytes, bit-packed | 9,622,157 |
| Public `A,P` bytes, bit-packed | 157,649,414,144 |
| Recipient integer key bytes on strict event | 1,179,648 |
| All 16 such keys | 18,874,368 bytes |
| Dense q-matrix/vector scalar products, `Aw` and `Pw` | 4,304,420,864 |
| Coordinate-read scalar products | 262,144 |
| One ciphertext addition's residue operations | 262,721 |
| Live 66 ciphertext bytes | 635,062,362 |
| All 384 ciphertext bytes | 3,694,908,288 |

[DERIVED counting boundary] The dense matrix count is `(l+d)n`; full encoding
also needs the public `F_p` basis transform, `d` scale products `Δa_i`,
additions and sampling. The table does not count them as dense matrix products.
These packed sizes exclude metadata and the separately priced public basis.
No giant matrix was allocated by the checker. The larger repair exceeds the
old restricted ALS `n=1024` row's public-matrix/encoding arithmetic, but those
rows assume different exact LWE problems and cannot be ranked at equal security.

[SOURCE/DERIVED HYL boundary] The author's source-prescription comparison
keeps HYL2025/1613 Theorem3's `l′≥2n log q` and `σK≥sqrt(d)Xl′`, its
equation(7) smudging requirement, and Theorem2's separate base-noise and base-
dimension conversion. The displayed generic sufficient conditions imply
`q/σL≥4d^(5/2)X² λ l l′/ε_pp`. This is a bottleneck of those sufficient
bounds, not a lower bound on all lattice IPFE or every HYL parameter choice.
The direct restricted theorem avoids importing that conversion, and its
estimator dimension is its actual ordinary-LWE dimension.

## 5. Verification and remaining scope

[EXECUTED] The retained checker uses the standard Python library only:

```text
python3 research/learn_infer_only/experiments/adversarial_review/smudged_hardness/check.py > research/learn_infer_only/experiments/adversarial_review/smudged_hardness/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/smudged_hardness/stderr.txt
```

[EXECUTED] `results.json` records PASS, exact coverage, source comparisons,
all independently reconstructed minima, operation/byte counts, finite proof
inequalities and before/after frozen artifact hashes. Existing outputs were
parsed and their displayed logarithms checked; no attack optimizer or sampler
was invoked. All 105 author-manifest links, 20 final minima, 116 rebuilt
parameter fields and 146 displayed logarithms match; stdout matches results
and stderr is empty. No new crypto, lattice reduction, estimator, private-file access,
package change, stopped task, commit or shared-ledger edit occurred. Source
discovery used local `rg` and exact local files; new remote queries 0 and
downloaded PDFs 0. This makes no field-wide absence claim.

[OPEN] The accepted audit supplies a useful bounded heuristic filter and
an exact finite proof-parameter point. Independent attack coverage beyond
the named routines/models, a rigorous computational hardness claim against
the proof's QPT/advice class, concrete sampler/transcript contracts, complete
learner closure and realistic matrix arithmetic costs remain unresolved.
