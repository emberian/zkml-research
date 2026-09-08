# Authorized normalization correction

[EXECUTED declaration, 2026-09-08] Root authorized six corrective calls
after the initial40 additional-call budget. No new parameter grid. Run only
the selected n16384,l262144,σe1024 point: normalized dual at low prime
q=2^292+13 in all4 models, and high prime q=2^293−601 in the2 validation
models (ADPS16 classical, MATZOV quantum depth×width).

[SOURCE] The pinned public dual wrapper bypasses the normalize call made
by the primal wrappers/full estimator. The correction supplies
LWE.Parameters(...uniform secret...,m=262144).normalize() explicitly, yielding
the same n16384, Gaussian secret/error stddev1024/sqrt(2π), m=245760.
Each result retains both original and normalized parameter representations.
The original driver and all invalid/raw dual outputs remain unchanged.

[EXECUTED budget] This raises the permitted count to46 additional calls,
plus24 baseline calls. The four beta2 failures remain counted. No lattice
instance, reduction, key, error sample or ciphertext was generated.

[EXECUTED final accounting] All six authorized normalized-dual estimator
entries completed in normalized_dual_final_low/high.jsonl. The earlier
run_normalized_dual.py wrapper made six pre-estimator attempts that failed
because vector-distribution dataclass equality includes differing dimensions.
The final wrapper checks each dimension and the scalar distribution fields
separately. Both wrappers and failure logs are preserved. The complete ledger
is 76 driver attempts, of which 70 entered an estimator routine; the latter
include the four beta2 errors. No extra parameter grid was run.
