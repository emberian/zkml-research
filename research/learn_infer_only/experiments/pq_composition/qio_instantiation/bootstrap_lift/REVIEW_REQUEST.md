# Independent review target

[REPORTED / author role] The author is `/root/pq_composition`; no self-review is represented as independent. Root was asked to assign an independent reader. Target bytes:

- `[EXECUTED]` `BOOTSTRAP_LIFT.md`: `ec9f721f2402d31a49a9fd4ee14f978b4cf7474429600710347dc555fe0d9792`.
- `[EXECUTED]` `POINTWISE_CORRECTNESS.md`: `c63e299a31a33617888814d5b4f371cf0f1e25541b4ebaa061e9bc84340d81f2`.

[DERIVED requested checks] The decisive proof obligations are:

1. One-key bit-indexed succinct RE: the function `F_U,c(Pi,x,i,s,b)` is fixed before its setup, all ciphertext hybrids use the one supplied public key/key, and simulation gets only output/metadata.
2. Sublinear encoding composition: outer simulation removes the seed before replacing inner PRG tapes; the short public key and tagged program representation close the common time bound.
3. Tree privacy: the next-level setup is shared between both children; the reduction generates a sibling under the challenged public key and retains the entire future public/CRS package. It does not need next-level secret coins. Equation (6) uses one continuing advice state.
4. Tree correctness: only a fixed-prefix marginal seed/tape distribution is changed; no proof conditions fresh correctness on a known ancestor seed. The all-node union gives equations (7)/(8).
5. The supplement's replacement of perfect FE correctness: one marginal PRF-value failure test per output index gives (C1), outer fresh coins give (C2), composition gives (C3), and the tree uses fresh complete encoding tapes only after its marginal PRG change.
6. Resource/quantifier convention: exact unchanged `q` relies on the stated nonuniform classical-code initialization model; all classical constants and honest work are charged. Uniform envelopes range over each fixed polynomial budget and all allowed advice states.

[OPEN instantiation boundary] The proof assumes a succinct FE public key bounded by `p0(kappa)` under the same uniform parameterization used for recursively described programs. Encryption succinctness alone does not assert that property. The independent base-source lane is checking this parameterization and the actual statistical/correctness rates. An acceptance of the proof under its explicit games is not an acceptance of a LWE-only instantiation or a claim of implemented PQ FE.

[EXECUTED control scope] `controls.py` and `pointwise_controls.py` check finite algebra/compatibility and pin the note hashes. Their results are useful falsifier controls but do not establish cryptographic security. All sources are pinned locally in `audit.json`; query counts remain zero for this tranche.
