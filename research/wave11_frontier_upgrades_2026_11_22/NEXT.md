# Wave 11 Next Steps — From Verified Primitives to Unified System

1. **Retire Bespoke Rust Sumcheck Provers via `SvcsCredibleCompiler`:**
   - Lower real workloads (`qwen35audit` GDN/MLP layers, EVM Stage-0 descriptors, and byte-DFA transducers) directly through `Compiler/SvcsCredibleCompiler.lean` into `SVCS` bundles so bespoke Rust sumcheck implementations can be deleted rather than maintained in parallel.
2. **Close the Native-Verifier Boundary via `obend` (`Core4 -> Lower/Pancake`):**
   - Extract/compile the compact, fixed `SVCS` + Merkle/Datalog + `BaseFold` verifier out of Lean through `obend`'s verified compiler pipeline so runtime verification no longer relies on unverified Rust bound only by conformance vectors.
3. **Upstream `zkhem_v2_closure/dregg_sig_zkhem_v2_selvage_xref.patch` into `~/dev/dregg-sig`:**
   - Once the concurrent session in `~/dev/dregg-sig` commits its staged changes, apply `dregg_sig_zkhem_v2_selvage_xref.patch` (fixing the non-monotone `qrom_work_bits` / `classical_work_bits` binary search, correcting the `bounds.rs:884` `b_cf` comment, and linking `SECURITY.md` V2.0 item 1 to `Selvage/ZkHemV2SoundnessAndPrivacy.lean`).
4. **Oblivious / ZK Wrapper for Merkelized-EDB Gap Proofs & Distributed Custodian Transport:**
   - Wrap sorted-Merkle adjacent-key gap openings (`k_L < q < k_R`) in an oblivious PRF or ZK range-hash proof when neighboring EDB keys must remain hidden from the verifier, and move `dark_gdn_continual` from single-process simulated 3-custodian channels to network-isolated noise-flooded custodian transcripts.
5. **Downstream ML Quality Evaluation of Quantized Gated-DeltaNet Fast-Weight Adaptation:**
   - Measure multi-episode perplexity, factual recall, and post-unlearning retention on `Qwen3.5-0.8B` / `Qwen3.8` benchmarks under the exact integer `B61` + SPDZ quantization regime.
