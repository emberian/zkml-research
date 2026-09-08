# Smudged-instance hardness checkpoint

[DERIVED outcome, 2026-09-08] The frozen 612,717-byte point is heuristically
weak and rejected for implementation; its conditional theorem remains valid.
The coupled repair described in AUDIT.md passes the tested named heuristic
cost models at substantially larger storage and arithmetic cost. No
cryptographic instance or lattice attack was executed. Earlier proof, cost,
review and source notes stay unchanged.

[SOURCE] Reusing the existing untouched lattice-estimator snapshot at
commit53da5982597709ba0fdf94ea37a84d822310fd84 and its Sage10.8 environment.
Prior AUDIT, driver, nd.py, lwe_parameters.py, reduction.py and lwe_dual.py
were inspected. Exact input is uniform F_q^1024 secret, l=16384 independent
samples and integer-Gaussian error width1024; estimator stddev is
1024/sqrt(2π), approximately408.5. Its normalization changes to an
error-distributed secret and consumes1024 samples; that is recorded explicitly.

[DERIVED warning] With root-Hermite factor δ=1.0219 (the pin's empirical
LLL value), a dimension-k q-ary dual vector is modeled at length
δ^k q^(1024/k). At k around3072, this is roughly2^192, far below
q/(64·1024)≈2^272. This is a strong modeled distinguisher condition.
The deterministic worst-case LLL bound does not give that length; do not
describe the empirical shape assumption as a proved attack runtime.

[EXECUTED final point] The selected exact prime is q=2^292+13, proved using
Sage proof=True; n=16384, l=262144, error width 1024, key width 2^32,
flood radius 2^248. REBUILT.json checks correctness, regularity and ideal
statistical loss <2^-163 plus 768 times exact ordinary-LWE advantage. The
smallest retained modeled costs are log2 180.456 classical and 163.77 quantum
core-SVP, with explicit model and coverage limits. These are not certified
QPT security bits or a proved advantage-versus-work curve.

[EXECUTED physical cost] Ideal packed ciphertext: 9,622,157 bytes; public
matrices: 157,649,414,144 bytes; one recipient key on the strict tail event:
1,179,648 bytes. Encryption uses 4,304,420,864 dense q-matrix products plus
577 q-message scale products and the separately priced public F_p basis
transform. Real sampler, arithmetic and storage implementation costs remain
unassessed.

[EXECUTED accounting] All 70 authorized estimator entries are complete:
24 baseline, 40 initial additional, six normalized-dual corrections. Twenty
initial raw-dual rows are excluded for a normalization precondition mismatch;
four beta2 estimator errors are preserved. Six more driver attempts failed
before estimator entry on a vector-dimension assertion, giving 76 driver
attempts total. No Infinity result is used as hardness evidence. Drivers,
before/after normalization records, errors and outputs are retained.

[OPEN next] Independent review of the sealed hardness package, followed by
an explicit finite sampler/transcript contract and realistic matrix-cost
assessment before any implementation. No more estimator calls are scheduled.
