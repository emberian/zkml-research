# Query transport status

[EXECUTED] The three additive modules passed individual Lean checks with all 21 theorem declarations covered by `#guard_msgs`-pinned `#print axioms`: `ConsistencyQueryMass`, `ConsistencyCoherentTransport`, and `ConsistencyTransportWitnesses`. All reported dependencies are subsets of `propext`, `Classical.choice`, and `Quot.sound`. The import-boundary script passed. Exact commands, source hashes, exit codes, and output are retained in `checks/`; `MANIFEST.json` identifies the latest checks.

[DERIVED] `BabyBear.consistency_query_exact` proves the requested exact fixed-scalar equality for the existing `Schedule.Accepts firstFifteen` coherent sampler, with the explicit terminal RS-membership premise. Its right side is the actual recursively projected-and-masked terminal consistency mass divided by the actual level-15 cardinality, raised to `q`. See `src/Selvage/ConsistencyCoherentTransport.lean:109`.

[DERIVED] `consistency_mass_source` counts surviving initial source indices through the actual `FoldingData.sq` maps. `sourcePoint_eq_coherent` identifies those maps with the certified natural-order modulo indices. `uniformProb_square` transports the source distribution through the actual first binary square. `uniformProb_all_coordinates` factors the independent coordinates of the shared seed vector; it does not assert independence across rounds.

[DERIVED] `QueryWitnesses.mask_omission_falsifier` proves that the existing far-monomial schedule has strictly positive normalized terminal consistency mass strictly below one. Its legal terminal word, accepting zero seed, and rejecting one seed jointly inhabit the premises. See `src/Selvage/ConsistencyTransportWitnesses.lean:60`.

[OPEN] Root `proof_frontier` owns integration with the weighted scalar bad-event bound and supplied/opening heads. This directory supports its combined patch and does not provide a second integration route. Main `/Users/ember/dev/minidregg` remained read-only; no full build was run by this sublane.
