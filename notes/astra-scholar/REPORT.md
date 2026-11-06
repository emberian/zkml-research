# Astra scholar report

Ember — dark learning remains worth building. My verdict is **keep the MPC custody architecture as the default research direction, but withdraw the present price and privacy closure**. No fork yet satisfies “the mind within never has readable weights on any host” end to end. The harness deliberately holds everything in one process; the desired distributed invariant is still ahead.

[MEASURED] I built and ran four new harness bricks: a ciphertext proof gate with a serialized, witness-hiding Stern reference proof; an independent traffic counter and transcript adversaries; a ring-wide flooding/privacy calculator with key-owner attacks; and a concrete MASCOT preprocessing compiler/inventory. Each has saved results. Large-parameter figures are counts, not N=8192 benchmarks. Claude's elementwise gates, collaborative ZK and handover work remain separate.

[MEASURED/INFERRED] The proof gate matches the actual secret-key BFV encryption relation, including exact scaling, bounded secrets/errors, one integer witness across limbs, pinned public-key setup and complete context. Fiat–Shamir hashes witness commitments before challenges. Tested malformed keys, mixed limbs, changed responses and stale contexts are refused; the old statement-only challenge admits our false-statement forgery. The concrete fallback costs **225.7 Tbit per d=4096 step**, not 6.2 Gbit. I selected the LNS/LaZer route for optimization and supplied its relation compiler; an efficient proof backend and quantum-security reduction are not implemented. The fallback's interactive error is not a complete Fiat–Shamir knowledge-security bound.

[MEASURED/INFERRED] Flooding the first ciphertext component does **not** statistically hide the complete return: the second component distinguishes multipliers almost perfectly information-theoretically. Malformed-key examples recover the multiplier efficiently. For the narrower decrypted-phase simulation, ring dimension, block sums and all returns matter. At d=4096 the current sufficient per-step distance bound is about **2^-14.74**, not 2^-40. N=16384, four 61-bit primes and flooding radius 2^165 can achieve a phase-only **million-step bound below 2^-40** under the stated noise model. Full ciphertext privacy still needs a computational simulation and trustworthy key setup; merely increasing N does not fix it.

[MEASURED/INFERRED] Non-ideal preprocessing overturns §11's parity for the concrete conservative MASCOT backend. At d=4096, including existing online/mask traffic but excluding proofs, HE-MPC costs **14.06 Tbit/step**, FHE(a) **14.88 Tbit**, and modeled FHE(b) **0.914 Tbit**. The dense outer correlations dominate HE-MPC. FHE(b)'s approximately 15.4-fold advantage depends on its unbuilt relinearized schedule and does not settle custody or total cost. The 61-bit statistical budget also fails our sufficient million-step bound. These are backend-specific prices, not lower bounds.

[MEASURED] The original §11 online counts reproduce. The §9 “4.1 Gbit committed” is reconstructed witness volume: three raw share witnesses occupy **12.29 Gbit**, their rate-1/4 encodings **49.15 Gbit**, while the 148-query spine proof payload is approximately **482.42 Mbit**. Those units cannot support one interchangeable size ratio. A fixed-seed MAC cancellation is accepted by the actual code. A valid no-update edge can be replayed. Frozen-transcript and counter/context controls reject these attacks; durable distributed acceptance remains unfinished.

[READ/INFERRED] The welfare page states the boundary plainly: up to two custodians should learn only their shares and permitted outputs under a completed secure protocol; all three can recover the model. FHE gives the host reusable encrypted computation, while the MPC design keeps evaluation inside custody. Authorized outputs can themselves reveal weights. The Lean audit results bound conditional integrity/displacement, not confidentiality or welfare.

The next three bricks:

1. Implement the shorter lattice proof and whole-ciphertext simulation together, with pinned key generation and a full-run security budget.
2. Repair MAC challenge timing, extract a hostile-input verifier, and bind proofs to durable parent/counter/epoch acceptance.
3. Replace scalar-generated dense correlations with authenticated batched HE/OT preprocessing, then integrate Claude's ZK step and re-price equal security levels.

All detailed claims, limitations and runnable evidence are in `notes/astra-scholar/` and the harness's `scholar_` files. VERDICTS and other lanes' files were left untouched.
