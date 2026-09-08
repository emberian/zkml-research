# Draft protocol — not frozen executable inputs

[REPORTED] This bounded plan was sent to the coordinator before the pause. It was not implemented or run. The case categories and caps below were fixed in that message; exact coefficient tensors, generator formula and reference code were still missing.

[HYPOTHESIS] Compose the actual public TFHE 1.6.3 routines on u32: `lwe_ciphertext_modulus_switch`, `blind_rotate_karatsuba_assign_mem_optimized`, and `extract_lwe_sample_from_glwe_ciphertext` at monomial 0. Reuse the existing native-u32 arithmetic and decomposition code; do not build another EMA schedule or learner.

[HYPOTHESIS] Planned geometry: two input LWE mask coefficients, GLWE dimension 1, polynomial sizes 8 and 128, decomposition base log 4 and two levels, native u32 modulus. At each size, six finite public cases were planned:

1. All-zero tensors.
2. Body rotation with zero switched mask.
3. One nonzero CMUX step.
4. Two nonzero CMUX steps, sensitive to update order.
5. Modulus-switch rounding boundaries including tie and u32 wrap.
6. Full-width overflow and negacyclic sign cases.

[HYPOTHESIS] The intended independent Python reference uses exact integer arithmetic with explicit reduction modulo 2^32 and schoolbook negacyclic convolution. Wrong update order, wrong negacyclic sign, and wrong rounding should change at least one expected output. These are proposed falsification checks; no expected vectors or successful falsifiers exist yet. Synthetic BSK-shaped tensors would carry no asserted encryption or secret-key relation.

[REPORTED] Original caps, not consumed: at most two compile attempts; 180 seconds cumulative build wall time; 4 GiB aggregate sampled RSS; two build jobs. At most two fresh-process public runs, each 20 seconds and 1 GiB sampled RSS. Target directory must be a new isolated temporary directory, never a shared target. Preserve every failed attempt and pin sources before any future build. No cap escalation is part of this draft.

[OPEN] A future continuation must first freeze the exact tensors, reference, Rust source, Cargo.lock and source pins. A source signature accepting a generic u32 parameter is not a compilation result. A public coefficient calculation is not bootstrap correctness under a generated key, and a finite agreement is not universal Rust or cross-platform refinement.
