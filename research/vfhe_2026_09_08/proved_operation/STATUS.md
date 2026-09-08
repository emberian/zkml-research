# Complete: BFV operation and actual learner-expiry proofs

[EXECUTED] Both complete proofs pass fresh native verification and reject
changed public output claims. The useful-learner event 65 proof covers every
stored NTT slot of both ciphertext components and both RNS primes: 16,384
residue equations. No private learner files were read.

[EXECUTED] Lean owns arithmetic emission and witness production. The owned
portable public-preprocessing PCS adapter fixes the observed independent
verifier transcript mismatch, preserving witness hiding and all FRI settings.
The failed first proof remains at results/proof001/. Accepted proofs are
results/proof002/ and results/expiry_proof001/.

[REPORTED, sibling executed logs retained] Both also pass the shared
JavaScript/WASM verifier with changed-output rejection. REPORT.md and
RESULT.json contain timings, exact artifacts and scope. This package's sources,
binary and accepted artifacts are now frozen for root integration. No further
proof or verification work is planned here; successors use sibling directories.
