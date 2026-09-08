# Inputs and claim provenance

[SOURCE: local primary algorithms, read] `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2021/46.pdf`, Mera–Karmakar–Marc–Soleimanian, §5 pp.21–22; existing layout extract `../ring_candidate/extracts/2021-046.txt` lines 1076–1135. This supplies the noiseless ring-product syntax and explains the source's different adaptive-key proof. This successor does not invoke that proof or its defective surjectivity test.

[SOURCE: local primary definition, read] `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2013/293.pdf`, Lyubashevsky–Peikert–Regev, Definitions 2.20–2.21 and discrete-variant discussion §2.6; existing extract `../ring_candidate/extracts/2013-293.txt` lines 1068–1103. This is ring-distribution context. Its canonical/dual-ideal normalization and worst-case theorem are not a hardness certificate for our fixed power-basis instance.

[SOURCE: frozen local derivations] `../ring_candidate/CANDIDATE.md` §3 and `RING_REGULARITY.md` §§2–4 provide the bare fixed-coordinate hybrid and prime-split structured-ring regularity. `../ring_candidate/hardness/GRID.json` supplies the repaired N=16384 parameters and previously computed finite inequalities. No estimator output is reinterpreted as a proof.

[SOURCE: finite-law specification and implementation] `../finite_sampler/SPEC.md` §§2–5 proves the exact bounded-law error and support. The frozen fast sampler sources and manifest pin the law used by the transport. This successor derives the one-sided finite-key regularity correction directly, rather than importing the earlier broader sampler loss ledger.

[SOURCE: actual seeded chronology, read] `../ring_seed_transport/seed_transport.py` functions `init`, `register`, `finalize`, `encode`, `a_expander`, and the registry/header functions; `../ring_seed_transport/expansion/public_expander.py`, fully read. These determine both public-seed stages, exact canonical addresses, rejection caps, and public recomputation. The frozen manifest is an input anchor; the implementation is untouched.

[DERIVED] The programmable-ROM wrapper, target/table joint distribution, finite-key extension, and new finite theorem are ours. The earlier `designated_span/public_coin_setup/public_seed/PROPOSAL.md` was read as context for finite-tape programming; no DDH theorem or unproved seed-instantiation claim is imported. The child kernel includes its complete independent combinatorial proof.

[EXECUTED] `python3 research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_seed_security_successor/check_ledger.py` performs deterministic exact integer/rational calculations and retains CHECKS.json. Its stdout and the child kernel's exhaustive controls are pinned by the manifest. These are not cryptographic executions.

[EXECUTED query meter] New Scry SQL queries: 0. New web searches: 0. New web opens: 0. New PDF downloads: 0. Local primary PDF hashes and existing extracts only. No private files, Gaussian samples, encryption, estimator or lattice attack execution in this package.
