# Ring hardness audit checkpoint

[EXECUTED, 2026-09-08] Source/math preparation is complete. The frozen ring
proof and its sealed artifacts remain unchanged. `MODEL_AND_GRID.md` states
the exact uniform-secret and coefficient-Gaussian map, derives a ring
normal form conditional on a unit first sample, and isolates the remaining
generic structured-lattice/GSA modeling assumptions.

[EXECUTED] `prepare_grid.py` exits 0: both N=4096 and N=16384 points pass
joint primality/splitting, smoothing, rank/short-vector, tails, flooding,
decoder and all 17 coalition bounds. `GRID.json` preserves parameters and
costs. All 27 estimator source hashes match the existing pinned archive.

[EXECUTED] Root authorized the predeclared 24-call grid. All 24 entries
completed with zero failures/timeouts, and all 27 source hashes remain
unchanged. The N=4096 baseline fails the named cost filter; the coupled
N=16384 point has minimum log2 modeled cost 167.215 in the quantum
core-SVP model. `AUDIT.md` retains all model and finite-proof limits.
Computational hardness, finite sampler/QPT resources and structured-attack
coverage are not established.

[EXECUTED counts] Exactly 24 estimator entries in one Sage process; zero
cryptographic or attack execution, zero Gaussian draws and zero new network
queries. Independent review is requested before root integrates the result.

[REPORTED parent proof review] The independent frozen ring review accepted
the conditional ideal-sampling mathematics without required correction.
Report: `adversarial_review/ring_fixed_coordinate/REPORT.md`, SHA256
`5183db756af984c34a45f270bd7b33700942b2b9a7989bdd9116e517a5567d18`.
Its computational and bounded-sampler obligations remain explicit.
