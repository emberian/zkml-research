# Fixed-policy ALS costs and finite parameter obligations

[DERIVED outcome, 2026-09-08] No implementation-ready security parameter set is
certified by this tranche. The frozen source-Theorem3 route has a severe
dimension-dependent width cost. The separately reviewed fixed-coordinate proof
removes that exponential factor, but the explicit sizing examples below still
have large matrices and per-input work. The examples have verified finite
correctness and syndrome-regularity inequalities. Source reduction constants,
reduction statistical errors, Gaussian implementation accuracy and the actual
QPT-LWE hardness assumption remain separate unresolved obligations.

[EXECUTED scope] Only public integer arithmetic, source reads, source-page
rendering and hashing were run. No keys, Gaussian samples, ciphertexts, private
fixture values, protocol operation, attack experiment or estimator were run.
The frozen notes/AUDIT.md remains unchanged. All computed values come from
derive_costs.py; results.json, derive_costs.stdout.json and table.md preserve
the outputs. initial_failure.md records a failed first arithmetic assertion.

## Original fixture and exact integer interpretation

[SOURCE] The original designated_span/CONTRACT.md fixes d=577, r=16, two
routes, window W=32 and each signed input coordinate in [−127,127]. Public
crypto/rows.json is the unchanged query matrix. The aggregate public
full_utility/reports/full_003/report.json records T=384 Learn events and
96 Infer events, with 256 expiries. No private per-input material was needed.

[EXECUTED] The recomputed public row L1 norms are

    3185,3320,3188,3343,3061,3374,3348,3499,
    2946,3231,2696,2766,2964,3265,2719,2778.

[DERIVED/EXECUTED] Therefore every allowed integer window score obeys
|Y_i S|≤32·127·||Y_i||_1, with maximum 14,219,936. The smallest prime larger
than twice that maximum is p=28,439,893, verified by integer trial division
through its square root. Thus centered decoding in F_p recovers every promised
integer score. The first 16-column determinant was independently recomputed
by exact Bareiss elimination as −812,032,080; its residue modulo p is
12,724,817, hence nonzero. The public basis can therefore be

    B = [Y; e_17; e_18; ...; e_577].

[DERIVED/EXECUTED] Encoding Bx needs 9,232 dense small-coefficient products,
or 8,600 after skipping zero entries; 7,362 coefficients have absolute value
greater than one. A sparse dot-product implementation uses 8,584 additions
and 561 coordinate copies. All Y coefficients fit signed 8-bit storage,
so implicit B needs only the 9,232-byte Y plus its specified fixed identity
completion, excluding metadata. A large integer lift of B never multiplies
a Gaussian key or encryption error: Bx is reduced modulo p before encoding.

[DERIVED scope] This certifies the original input/range and fixed-score
contract, not privacy on the encoder image. Row rank 16 and ambient dimension
577 do not prove a protected semantic collision. Every recipient still sees
its authorized projection of each retained issued input.

## Exact source constraints and distributions

[SOURCE] ALS 2015/608, §4.2 pp17–18 and Lemmas3–5 pp21–22, with source
plaintext dimension ℓ renamed d. Use q=p^k, Δ=q/p, m=2M, n≥100, d<n.
A∈Z_q^(m×n) is uniform. Each row of Z has M independent centered
D_Z,σ1 entries and M independent D_Z,σ2 entries centered at that row's
canonical unit vector in Z^M. These are Gaussian width parameters for mass
exp(−π(x−c)^2/σ²), not variance parameters. Rows are independent but their
right-half centers differ. Recipient i owns row Z_i, not lift(Y_i)^T Z,
because the fixed policies have been moved to message coordinates.

[SOURCE] The full modular-key prescription printed on p18 is

    K' = (sqrt(d) p)^d,
    σ1 = Θ(sqrt(n log m) · max(sqrt(m),K')),
    σ2 = Θ(n^(7/2) sqrt(m) · max(m,K'^2) · log^(5/2)m),
    α^-1 ≥ d² p³ Bτ · ω(sqrt(log n)),
    q ≥ α^-1 · ω(sqrt(log n)),
    m ≥ 4n log_2 q.

[SOURCE] Bτ bounds each source secret row's Euclidean norm except the stated
negligible tail. The p18 summary also states, with m=Θ(n log q), a reduced LWE
noise rate α'=Ω(α/(n^6 K' log²q log^(5/2)n)) and q≥Ω(sqrt(n)/α'). This
asymptotic summary is not a numerical parameter calculator. We instead retain
the explicit Lemma3/5 map below when normalizing finite examples.

[SOURCE] The actual Lemma4/5 gadget constraints, for m1=m2=M, are

    n≤M≤n^O(1),
    σ1 ≥ Ω(sqrt(M n log M)),
    M ≥ Ω(n log(σ1 n)),
    σ2 ≥ Ω(n^(5/2) sqrt(M) σ1² log^(3/2)(Mσ1)),
    ξ ≥ Ω(sqrt(n M) σ2).

[SOURCE/DERIVED] Lemma3 maps ordinary LWE of secret dimension n−d to the
first-d-are-errorless form in dimension n, with error at most 2^(d−n+1).
Lemma5 maps noise rate β to multi-hint noise rate 2βξ; hence use
β=α/(2ξ), with β≥Ω(sqrt(n)/q). The reduction's base LWE error width is
βq, whereas actual encryption errors have width αq. Those two distributions
cannot be interchanged in a security estimator. Lemmas4–5 also contain
2^−Ω(n) sampling/reduction errors, whose constants are not specified here.

[SOURCE/DERIVED distinct variant] The separately reviewed
../../../adversarial_review/public_setup_pq/FIXED_COORDINATE_QPT.md proves
the fixed-coordinate game directly using the augmented matrix [A_L|v_L].
It uses the Lemma4/5 row distribution with polynomial widths, rather than
Theorem3's arbitrary-key K' prescription. It requires the stronger
M≥2(n+1)log_2q. Its honest public setup and per-input leakage remain the same.
This is a new derived restricted theorem; substituting these smaller widths
into the frozen Theorem3 citation would be unjustified.

## Finite correctness and storage tails

[DERIVED] Write σ_e=αq. An individual coordinate phase has integer error

    ε_i=e1_i−Z_i·e0.

For any scalar combination of original ciphertexts with coefficient L1 norm
at most W, its error is at most W E if each individual |ε_i|≤E.
The strict condition is q>2pWE. Adding the exact original ciphertext and
subtracting it on expiry cancels its error. Freshly encrypting the expired
plaintext would not cancel it. Plaintext offsets add no error but must still
obey the integer score range. General matrix updates, key switching, nonlinear
operations and unlimited coefficient growth are outside this contract.

[DERIVED elementary tail] For σ≥1, integer center c and integer t≥1,
with tσ integer, the discrete Gaussian normalizer is at least one. A decreasing
Gaussian sum and its integral tail give

    Pr[|X−c|≥tσ]
      ≤ 2(1+σ/(2πt)) exp(−πt²)
      ≤ 3σ exp(−πt²).

[DERIVED] For a power-of-two width σ=2^s and at most N scalar samples,
choose t with 4t²≥s+ceil(log_2(3N))+66. Since π>4 ln2, the union tail is
at most 2^−66. This intentionally loose bound avoids a hidden Gaussian-tail
constant or treating a continuous density as discrete mass. Independence is
not needed for this union bound.

[DERIVED] The script uses N_z=d m for secret rows (conservative even though
only r rows are actually sampled), with common t_z based on σ2, and
N_e=T(m+d) for all encryption errors, with t_e based on σ_e. On these events,

    L1 = M t_z(σ1+σ2)+1,
    L2 = ceil(sqrt(M(t_zσ1)^2+M(t_zσ2)^2+2t_zσ2+1)),
    E  = t_e σ_e (1+L1).

[DERIVED/EXECUTED] The +1 and cross-term account for the single unit center.
The total correctness bad-event bound for ideal prescribed Gaussian sampling
is at most 2^−65 over this T=384-input horizon. The script checks q>2pWE
using exact integers. No probabilistic cryptographic experiment is involved.
Gaussian keys have unbounded support; recipient byte counts below are
high-probability sizes on this tail event, not unconditional maximum lengths.
Truncating or rejecting samples to force fixed widths would change the
distribution and requires an additional distance/abort ledger.

## Explicit syndrome regularity, but no total security level

[DERIVED/independently checked] The separate
quantitative_regularity/BOUND.md and RESULTS.json in the adversarial review
lane replace the hidden exponent in ALS Lemma10 with a finite certificate.
They use MP2011/501 Lemma2.4 equation(2.1), GPV2007/432 Corollary2.8/Lemma5.2,
the conventional dual-lattice smoothing definition, and prime-power subgroup
counting. This cost lane independently read those source passages and checked
the expectation-to-distance proof. The bound pays rank failure once for the
joint tuple; it does not assume universal hashing over the field F_q.

[DERIVED certificate] For N=n or n+1 columns, h missing rows, κ≥1, it suffices
that

    M≥N ceil(log_2q)+κ+1,
    σ1²≥ceil(log_2M)+κ+2.

Then the full joint distance, including A and the other independent recipient
rows, is at most 4h·2^−κ. Our script additionally checks the earlier, stronger
Lemma6/9 conditions with 2κ margins, which also pass. It uses κ=160 in all
three examples. The independent review verifies all six (n and n+1) cases.

[DERIVED/EXECUTED] For d577/r16/T384 and worst fixed coalition j=0, the
setup-plus-challenge regularity contribution is at most
1,777,032/2^160 < 2^−139. For j=16 its numerator is 1,727,880. This bounds
only the statistical syndrome terms. The QPT-LWE distinguishing advantage,
Lemma4/5 reduction errors and constants, and sampler implementation accuracy
remain separate; neither this small term nor n alone establishes 128-bit
cryptographic security.

## Computed finite sizing examples

[EXECUTED, normalization only] These examples have n=1024 or n=4096 because
they are convenient explicit dimensions to price, not because a security
estimator selected them. All unspecified lower-bound constants are checked
only against a displayed coefficient-one normalization with base-two logarithms.
That exercise does not determine the source's constants. Powers of two round
widths upward, and q remains an exact power of the independently checked prime.

[DERIVED/EXECUTED full prescription normalization] Compute K'^2=d^d p^(2d)
exactly; log_2K'≈16,933.580465. Round σ1 upward from the displayed source
formula. Round σ2 upward from the maximum of its displayed source formula and
the actual Lemma4 lower expression; their rounded exponents are 33,929 and
33,945 at the final point. This avoids assigning the p18 noise summary the role
of an exact gadget theorem. Set ξ from its normalized Lemma5 expression and
base error width βq from rounded sqrt(n). Select q to satisfy both finite
coordinate correctness and the normalized general source factor
α^-1>d²p³L2 ceil(log_2 n). Iterate m upward to satisfy the dimension/row bounds.
The ceil(log_2n) choice is an explicit member of ω(sqrt(log n)), not the
source's unspecified finite prefactor.

[DERIVED/EXECUTED restricted normalization] Start from the independently
reviewed asymptotic witness σ1=n², σ2=n^8, ξ=n^10 and q≥n^30. Choose the
smallest p-power q≥n^30 and m the next power of two above
4(n+1)ceil(log_2q). At these finite n, σ2=n^8 alone failed the normalized
Lemma4 check; this failed attempt is retained. Raise σ2 and ξ to their
coefficient-one Lemma4/5 floors, then round upward. Choose σ_e as the next
power of two at least q/n^15, so α lies in [n^−15,2n^−15).

[EXECUTED] The exact resulting distributions are:

| Normalization | n−d | q | σ1 | σ2 | ξ | σ_e=αq | βq |
| --- | ---: | --- | --- | --- | --- | --- | --- |
| Full source, n1024 | 447 | p^2748 | 2^16942 | 2^33945 | 2^33964 | 2^33970 | 2^5 |
| Restricted, n1024 | 447 | p^13 | 2^20 | 2^83 | 2^100 | 2^172 | 2^71 |
| Restricted, n4096 | 3519 | p^15 | 2^24 | 2^98 | 2^120 | 2^192 | 2^71 |

[EXECUTED] Generated table.md gives bit-packed sizes in decimal SI units:

| Normalization | q bits | m | Ciphertext | Public A,U | Recipient key* | Products/Encode |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Full source, n1024 | 68,045 | 536,870,912 | 4.57 TB | 4.68 PB | 1.71 TB | 549,756,404,736 |
| Restricted, n1024 | 322 | 2,097,152 | 84.43 MB | 86.46 GB | 14.55 MB | 2,148,074,496 |
| Restricted, n4096 | 372 | 8,388,608 | 390.10 MB | 1.60 TB | 69.21 MB | 34,362,101,760 |

[DERIVED/EXECUTED] *Key sizes use the explicit tail bound. The exact byte
counts and byte-aligned residue alternatives are in results.json. Sizes exclude
framing, hashes, allocator overhead and Gaussian-sampler implementation state.
The public basis adds the 9,232-byte row matrix described above. Plaintext and
source parameters themselves add comparatively small, but unpriced, metadata.

[DERIVED structural counts] A and U hold n(m+d) residues; a ciphertext holds
m+d; recipient registration needs mn modular products per recipient; encryption
needs n(m+d); one coordinate read needs m. A Learn with expiry performs
2(m+d) modular additions/subtractions. Products operate on residues with the
listed q bit lengths; they are not unit-cost CPU instructions. No conversion
from these counts to wall-clock latency is asserted without a benchmark.

[EXECUTED] The restricted n1024 point needs 5,572,617,138 packed bytes for two
live queues plus their accumulators (66 ciphertexts), and 32,422,499,712 bytes
for all 384 original input ciphertexts. Its 384 encryptions require
824,860,606,464 dense modular products. It samples 2,097,729 scalar Gaussians
per encryption. At n4096, live storage is 25,746,408,798 bytes, retained-input
storage 149,797,287,552 bytes, and total encryption products 13,195,047,075,840.
These are storage/work counts only; no objects of these sizes were generated.

[DERIVED] Streaming A can change peak RAM but not its prescribed public byte
volume or the per-encryption matrix work. Replacing independent public A entries
by expansion of a published short seed changes the full setup transcript and
distribution. The current proof does not permit treating such a seed as a free
compression of honest public coins. Ring structure, batching, ciphertext
compression or alternative shorter-secret primitives similarly need a new
source/distribution argument, not just a smaller number in this table.

## Estimator mapping and implementation decision

[SOURCE] Read the existing he_closure_costs/estimator/AUDIT.md, its driver and
pinned estimator nd.py at commit 53da5982597709ba0fdf94ea37a84d822310fd84.
The old BFV estimates used structured ring samples and CBD(20) secrets/errors;
none of their outputs applies here. A future diagnostic for the explicitly
specified LWE assumption would use dimension n−d, modulus p^k, m independent
generic LWE samples, a uniform modular secret, and Gaussian error width βq.
The library's DiscreteGaussianAlpha applies width/(sqrt(2π)) when representing
that noise; this is not an instruction to pass αq as the source error. Its
heuristic attack models do not establish QPT security or FE composition.

[DERIVED decision] No estimator was run: the current finite examples normalize
unresolved source constants and were not selected as a proposed security tuple.
An estimate of such an illustration could be recorded later as a diagnostic,
but cannot calibrate the omitted reduction/sampler errors. The checked finite
correctness and regularity bounds are useful concrete progress; they do not
yet authorize treating any row as an honest security parameter instantiation.

[OPEN next bounded contract] First resolve the Lemma4/5 finite constants and
sample-generation error for the restricted theorem, choose an explicit target
QPT-LWE assumption/error ledger, and reduce or accept the measured structural
costs. Only then propose a bounded implementation with that exact Gaussian law,
public accepted-coin transcript, p/range contract, finite T and W, and resource
budget. This tranche does not propose starting cryptographic execution at a
coefficient-one sizing point. Root owns any adoption, shared-ledger updates and
commits; the frozen construction and stopped tasks remain untouched.
