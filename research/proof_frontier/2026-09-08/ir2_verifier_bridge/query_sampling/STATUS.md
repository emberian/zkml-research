# Fresh-base query sampling law

[DERIVED] `FiniteModuloSampling.pushforward_exact` proves the arbitrary-predicate law for `p = a*k+1`, every natural `a`, and positive `k`: complete residue cycles contribute `(p−1)/p` times uniform residue probability; the extra representative contributes `1/p` exactly when the predicate accepts zero. `independent_exact` and `independent_bound` give the corresponding q-coordinate power and its upper bound.

[DERIVED] `BabyBearModuloSampling.fresh_bits_exact` specializes this law to the actual existing BabyBear base field for every `ell ≤ 27`. `fresh_bits_independent_bound` proves `(((p−1)/p)*t+1/p)^q` from uniform-index event probability at most `t`. `canonicalEquiv_val` and `sampleBits_mask` identify the canonical integer and its natural bitmask. `actual_zero_bias` proves zero strictly heavier than one when `0 < ell ≤ 27`; both modules include inhabited keystone premises.

[SOURCE] The selected vendor method is `/Users/ember/dev/breadstuffs/vendor/plonky3-challenger-82cfad73/src/duplex_challenger.rs:264`, inspected through line 270. Its body samples a base element then masks its canonical integer. Source fingerprint is in `CHECKS.json`.

[EXECUTED] Both frozen Lean modules pass individual source-stable, warning-free checks with all 20 theorem declarations axiom-pinned. The import-boundary script passes; the scan of these two complete files finds no `sorry`, `native_decide`, or declared axiom. Exact commands, output, and hashes are in `CHECKS.json`.

[OPEN] The probability source is explicitly fresh independent uniform base elements. This theorem supplies no distributional guarantee for Fiat–Shamir challenger outputs. Root owns the actual verifier event adapter, its selected bit height, and the combined integration. Main minidregg and breadstuffs remained read-only.
