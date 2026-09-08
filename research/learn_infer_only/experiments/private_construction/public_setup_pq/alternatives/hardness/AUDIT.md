# Actual hardness audit and coupled parameter repair

[DERIVED outcome, 2026-09-08] The frozen 612,717-byte ciphertext point is
heuristically weak and should not be implemented. Its conditional theorem
remains valid; the exact LWE premise was never established. Ordinary dual
geometry already predicts an effective LLL-level distinguisher, and the
pinned primal estimates reach their minimum block-size boundary. A larger
coupled point has substantially higher named modeled costs, at a large
matrix-storage and encryption-work cost. None of these estimates certifies
post-quantum security or rules out unmodeled attacks.

## 1. Exact instance and reproducible primes

[SOURCE] The frozen SMUDGED_FIXED_COORDINATE.md assumes n=1024,
l=16384 uniform-matrix LWE samples, uniform secret in F_q^n, and errors
D_(Z,1024) with mass proportional to exp(−πz²/1024²). These are genuine
unstructured LWE samples in the proof, rather than a scalar proxy for ring
samples. The flood radius2^244 and recipient-key width2^32 are different
distributions and are not the LWE error width.

[SOURCE/EXECUTED] The untouched estimator snapshot is commit
53da5982597709ba0fdf94ea37a84d822310fd84 under the existing
he_closure_costs/estimator/runtime/pinned-estimator. Its nd.py:280–293
implements DiscreteGaussianAlpha(α,q) with stddev=αq/sqrt(2π). We supplied
α=QQ(1024)/q and ND.UniformMod(q), with m=l. This maps to approximately
408.5169 standard deviation, with the exact floating representation retained
in every row. The class uses Gaussian moment/support approximations; this is
not an exact discrete-Gaussian probability engine.

[EXECUTED] Sage10.8 found and proved the following actual primes:

| role | exact prime |
|---|---|
| baseline low | 2^288+127 |
| baseline high | 2^289−493 |
| repair low, selected candidate | 2^292+13 |
| repair high sensitivity | 2^293−601 |

[SOURCE/EXECUTED] `next_prime(proof=True)` found each low endpoint; the
previous prime below each upper power was found, then both endpoints were
checked by `is_prime(proof=True)`. The [Sage documentation](https://doc.sagemath.org/html/en/reference/rings_standard/sage/rings/integer.html#sage.rings.integer.Integer.is_prime)
states that proof=True uses a provable primality test and identifies PARI
isprime as its backend. moduli.json and moduli_repair.json preserve exact
decimal values, procedures, Sage version and elapsed computation time.
Neither power of two is treated as prime. This is a reproducible rigorous
procedure, not a separately exported primality certificate.

## 2. Analytic dual test before estimation

[DERIVED] Select k≥n+1 rows of a uniform F_q^(l×n) matrix A. Its dual
q-ary lattice is Λ={v∈Z^k:v^T A=0 mod q}, of determinant q^n when A
has rank n. Given a nonzero v in that lattice with

    σe ||v||_2 ≤ q/64,

testing whether center_q(v^T b) lies in [−q/8,q/8] distinguishes LWE
from uniform with advantage at least

    3/4 − 1/q − 2 exp(−64π).

[SOURCE/DERIVED proof] MP2011/501 Lemma2.8 p14 says a centered discrete
Gaussian is 0-subgaussian at every width. Therefore <v,e> has tail at
threshold q/8 bounded by 2 exp(−π(q/8)²/(σe²||v||²))≤2 exp(−64π).
The vector has norm<q, so it is nonzero modulo prime q and v^T u is uniform
on F_q for uniform u. The accepted uniform interval contains at most
q/4+1 residues. This proves the stated distinguisher conditional on finding
v. No lattice vector was generated or found in this lane.

[SOURCE/DERIVED heuristic] The pinned reduction.py:59–77 uses empirical
LLL root-Hermite factor δ=1.0219. The standard heuristic dual length is
δ^k q^(n/k), as also documented in lwe_dual.py:42–45. Analytic formula
evaluation for the original n=1024 and q≈2^288 gives an optimal integer
k=3072 and log2 length192.0124, while the sufficient norm ceiling is272.
Thus the modeled length is about80 bits below an already conservative
constant-advantage threshold. The high endpoint gives k=3077, log2 length
192.3454, and80.6546 bits of margin.

[DERIVED limitation] The deterministic δ_LLL=3/4 guarantee instead gives
||b1||≤2^((k−1)/4)q^(n/k). Optimizing that bound yields approximately
2^542.808 at k=1086, which does not prove the sufficient condition. Hence
the weakness conclusion relies on empirical lattice-reduction geometry,
not a theorem that worst-case LLL finds such a vector on this instance.
The pin's LLL cost convention gives k³ when coefficient bit cost is omitted,
or k³ B² with B=288: log2 costs34.755 or51.095 respectively. These are model
arithmetic values, not an executed attack time, and the second includes
more bit-size dependence. analytic_dual.py/json retains every number.

## 3. Estimator contract and integration limits

[SOURCE] Prior he_closure_costs/estimator/AUDIT.md and driver were read.
The existing Sage10.8 environment was reused without package changes or
estimator-source edits. All Sage/cache output was redirected to this lane's
ignored runtime/. The Python driver disables bytecode writes. Named source
hashes, invocation, runtime version and exact input/normalized representations
appear in each result manifest and row.

[SOURCE/DERIVED normal form] lwe_parameters.py:34–65 changes a uniform
secret to an error-distributed secret when m≥2n and subtracts n samples.
Baseline thus normalizes to15360 samples; selected repair to245760. For
prime q this follows by using an invertible first n×n matrix block, moving
its errors into the new secret, and using the remaining samples. The rank
failure of that block is below1/(q−1). It does not justify retaining the
original sample count after the conversion.

[EXECUTED integration discovery] Pinned primal uSVP and BDD normalize
internally (lwe_primal.py:228,801). In contrast, the public LWE.dual wrapper
calls optimize_blocksize directly, whose docstring explicitly requires
normalized input. The initial direct dual calls therefore do not establish
the intended normalized-dual coverage and are excluded from the operative
minima. The originally logged rows remain visible. Their large-n Infinity
results are not evidence that dual attacks are impossible.

[EXECUTED correction] Six corrected normalized dual calls completed in
normalized_dual_final_low/high.jsonl. They pass the per-coordinate Gaussian
checks, use exactly n=16384,m=245760 after normalization, and retain both
before/after parameter records. The final summary excludes all20 initial
raw-dual rows and uses these six corrected rows for the selected point.

[SOURCE named models] All primal runs use GSA. Reduction models are:

- MATZOV(nn='list_decoding-classical'): finite-dimensional classical model.
- ADPS16(mode='classical'): core-SVP term2^(0.292β).
- ADPS16(mode='quantum'): quantum core-SVP term2^(0.265β).
- MATZOV(nn='list_decoding-dw'): quantum list-decoding depth×width model.

[SOURCE] Definitions are pinned reduction.py:637–676,739–756,963–995.
Core-SVP omits polynomial/finite costs present in other models. Substituting
a quantum reduction model does not quantize every other subroutine. The
[estimator's own documentation](https://lattice-estimator.readthedocs.io/en/latest/)
labels its shape and cost predictions heuristic. These are named operation
models, not measured hardware times or proven lower bounds.

[EXECUTED errors] Four explicit beta2 low-level dual probes failed at
Cost.repeat because the driver bypassed the wrapper's registration of the
'mem' cost key. Their exceptions and traces are preserved. No cost was
extracted from those failed calls, and they count against the run budget.
The independent analytic LLL check remains available. The source optimizer's
ordinary dual search starts at beta40 (lwe_dual.py:303), so a floor result
cannot by itself price the cheapest LLL-level option.

[EXECUTED preflight errors and accounting] The first corrective wrapper
mistakenly asserted equality of full Gaussian vector-distribution objects.
Their dimensions differ (16384 versus245760), so six attempts stopped before
entering an estimator routine. The successor checks class, mean, stddev,
and each dimension separately. Both wrappers and all failures are retained.
There are76 driver attempts total:70 estimator entries plus6 pre-estimator
assertion failures. The70 comprise24 baseline,40 initially declared additional
entries (including the4 beta2 errors), and6 root-authorized normalized-dual
entries. No additional parameter grid was run.

## 4. Baseline fails the modeled target

[EXECUTED] All24 baseline calls completed. The following operative minima
use the internally normalized primal calls, over uSVP and BDD. Each occurs
at beta40 and is unchanged at the tested low/high prime endpoints.

| model | smallest log2 modeled cost | attaining attack |
|---|---:|---|
| MATZOV classical | 43.205449 | uSVP |
| ADPS16 classical | 11.680000 | uSVP |
| ADPS16 quantum core-SVP | 10.600000 | uSVP |
| MATZOV quantum depth×width | 47.605591 | uSVP |

[DERIVED] The tiny ADPS16 numbers reflect its core-only formula at the
optimizer floor; they are not credible complete attack wall times. The
analytic dual check and finite-cost models still show that the point does
not support a meaningful128-cost claim. Small statistical proof error and
large absolute n did not establish computational hardness. The prior theorem
is retained as conditional mathematics, while this parameter choice is rejected
for implementation on the tested heuristic evidence.

## 5. Coupled repair grid and finite proof bounds

[EXECUTED] REPAIR_GRID.md was written before outputs. Its24 grid calls
used n∈{8192,16384,20480,24576}, l=262144, q=2^292+13, σe=1024,
with dual/uSVP/BDD in MATZOV classical and ADPS16 quantum core-SVP models.
The selected smallest passing grid n was16384. Twelve declared validation
calls added both endpoint primes under ADPS16 classical and MATZOV quantum
depth×width. The four failed beta2 probes completed the initial40-call
additional budget. Source-contract issues are reported above; no undeclared
parameter search is concealed by the grid.

[DERIVED/EXECUTED] Increasing n alone would fail the fixed-height syndrome
entropy check. Raising the height from2^14 to2^18 also raises the smudging
shift bound sixteenfold, so F increased from2^244 to2^248, and q's lower
power increased from2^288 to2^292. All other ideal distributions stay fixed.
For the selected point:

    n=16384, l=262144, q=2^292+13, σK=2^32, σe=2^10,
    F=2^248, BK=2^35, BL=2^13,
    d=577, r=16, p=28,439,893, W=32, T=384.

[DERIVED/EXECUTED] The proof's general prime-modulus regularity bound uses
ε0=2^−192 and ηZ<8, so t<2^−29. For the augmented matrix,
293(n+1)−29l=−2,801,371. Hence the same δ_h<h2^−189 bound holds.
The smudging total is still below443,136/2^183<2^−164. The repeated tail
charges are below2^−185+2^−216, giving total statistical loss<2^−163.
With E=F+l BK BL and D=d(p−1)/2, the exact integer inequality
floor(q/D)>2WE and D>2WX both pass. The 36-bit key-coordinate size uses
the same strict |K_ij|<2^35 event. REBUILT.json checks all four grid rows.

[DERIVED] These checks rebuild the frozen theorem's finite statistical and
correctness premises. They do not prove LWE hardness or quantify an actual
Gaussian/flood sampler implementation. The fixed coalition, matching advice
class, private encryption coins, public setup transcript, finite integer
closure and semantic nonvacuity limits of the frozen theorem remain intact.

## 6. Modeled repaired costs and physical price

[EXECUTED final operative minima] At the selected exact prime
q=2^292+13, the internally normalized primal runs and corrected normalized
dual runs give the following minima over {uSVP,BDD,dual}:

| model | min log2 modeled cost | attack / beta |
|---|---:|---|
| MATZOV classical | 208.327822 | BDD /617 |
| ADPS16 classical | 180.456000 | uSVP /618 |
| ADPS16 quantum core-SVP | 163.770000 | uSVP /618 |
| MATZOV quantum depth×width | 196.614978 | BDD /617 |

[EXECUTED] Corrected normalized-dual costs at the selected prime are
209.837139 MATZOV classical,180.748000 ADPS16 classical,164.035000 ADPS16
quantum core-SVP, and198.201604 MATZOV quantum depth×width. All are above
the corresponding primal minima, so the weakest named modeled cost remains
163.770000 quantum core-SVP, while the smallest classical model is180.456000.

[EXECUTED endpoint sensitivity] At q=2^293−601, the tested other-model
primal minima are179.580000 ADPS16 classical and195.863914 MATZOV quantum
depth×width. The selected prime is the low one; no unrun all-model upper-
endpoint minimum is claimed. The n8192 row fails with quantum uSVP59.89.
The larger grid rows raise primal costs further while increasing public-key
storage; they are not needed to select the first qualifying declared point.

[SOURCE/EXECUTED limitation] The pinned MATZOV implementation's fit comment
at reduction.py:970–971 states coverage through beta=1024. The selected
point's beta617–619 remains within that fit range. The n24576 grid row uses
beta1060/1062, so its MATZOV numbers extrapolate beyond that stated range;
they are not used to qualify the selected point.

[DERIVED caution] Subtracting log2(768)=9.5849625 from a cost exponent is
only informal margin arithmetic. An estimated cost for99% attack success
does not automatically yield an advantage-versus-work curve for the theorem's
factor768. REBUILT.json records that subtraction transparently but does not
call it a security reduction or certified adjusted security bits.

| [EXECUTED] physical arithmetic at selected point | quantity |
|---|---:|
| ciphertext bytes | 9,622,157 |
| public-key bytes | 157,649,414,144 |
| one recipient key, strict tail event | 1,179,648 bytes |
| all16 recipient keys, same event | 18,874,368 bytes |
| dense q-matrix/vector products for Aw and Pw | 4,304,420,864 |
| additional q-message scale products Δa | 577 |
| coordinate decryption modular products | 262,144 |
| ciphertext-addition residue operations | 262,721 |
| live66 ciphertext bytes | 635,062,362 |
| all384 issued ciphertext bytes | 3,694,908,288 |

[DERIVED] Costs are ideal packed arithmetic, excluding metadata. The dense
product count is exactly (l+d)n for Aw and Pw; the separate Δa term is shown
explicitly. The public F_p basis transform and its B matrix retain the
separately priced original-fixture costs in the frozen parent package. These
counts do not predict latency. The candidate has
far larger public-key and encoding costs than the weak612KB point, and also
exceeds the old restricted-ALS n1024 row's public-key/encoding arithmetic.
Those old rows have different unassessed exact LWE assumptions; this is not
an equal-security performance comparison or a practical deployment claim.

## 7. Why the published HYL recipe is not a cheap relative-error repair

[SOURCE] HYL2025/1613 Theorem3 p27 requires l′≥2n logq and
σK≥sqrt(d)Xl′. Equation(7) p24 includes l BK BL/F≤ε_pp. With the
source BK=sqrt(λ)σK and BL=sqrt(λ)σL, this sufficient prescription requires

    F ≥ λ l σK σL / ε_pp.

[SOURCE/DERIVED] Its generic correctness condition p28, for one block and
Y=1, already requires dF≤floor(q/(dX))/4, even ignoring the additional
Ke term. Combining these source sufficient conditions gives

    q/σL ≥ 4 d² X λ l σK / ε_pp
          ≥ 4 d^(5/2) X² λ l l′ / ε_pp.

[DERIVED scope] This is a bottleneck of satisfying the printed bounds,
not a universal impossibility or lower bound for the construction. Enlarging
l′ to satisfy its missing height premise increases this ratio; it does not
permit larger relative encryption error within that prescription. For the
restricted W-window decoder, the analogous sufficient scaling still includes
2W dX rather than the generic4d²X factor. Increasing σL while holding F,q
fixed breaks the smudging/correctness ledger; increasing them together does
not remove those relative-error obligations.

[SOURCE] The ordinary LWE source premise is stricter still: HYL Theorem2
p26, independently rendered here, has σL=sqrt(σ0²+r²),
σ0>σLWE C sqrt(l) σ1, q/σ1≥sqrt(ln(4n)/π), r≥sqrt(λ), and equation(8).
The source base secret dimension is λ, rather than the public matrix's n.
Its finite C and multi-secret reduction obligations must be retained.
Replacing n in an estimator while ignoring that map would misstate the
source game. The present direct fixed-coordinate proof avoids that source
conversion and uses its exact ordinary-LWE dimension directly.

[DERIVED] The previously demonstrated Table2 height failure therefore is
not cured by simply allocating a taller l′ at unchanged error/flood/modulus.
This bounded analytic comparison found no source-prescription route to a
cheaper, larger-relative-error candidate with all printed premises certified.
It makes no absence claim about other parameter optimizations or papers.

## 8. Remaining work and limits

[EXECUTED/OPEN] The selected point's three named attack paths are complete
in all four declared models at the selected prime. The current estimator
coverage omits hybrid guessing, dual-hybrid, BKW, algebraic attacks, alternative
shape models, and future/unmodeled attacks. Passing these selected cost
models is a useful heuristic filter, not a lower bound against all QPT attacks.

[OPEN] Before any cryptographic implementation: independently review the
rebuilt finite point and estimator integration; specify exact or bounded-error
Gaussian and uniform samplers and their private/public transcripts; price
real matrix arithmetic/storage; preserve the input domain and integer closure
contract. No implementation or lattice-attack execution was begun here.
