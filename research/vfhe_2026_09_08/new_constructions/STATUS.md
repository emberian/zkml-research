# Focused vFHE construction delta

[EXECUTED scope] New lane authorized by root after the completed polynomial-kernel review. Only this directory is writable; companion trees, existing notes and stopped tasks remain untouched.

[SOURCE prior baseline] Read `notes/ring-switching-connectors.md`, `notes/circle-aligned-vfhe.md`, `notes/fhe-scout-verdicts.md`, `notes/ntt-as-gemm.md`, and relevant `docs/VERDICTS.md` passages. Preserve the known distinctions: packing is not elementwise lifting; shared twiddles do not create an NTT relation; BAT needs a preknown operand; modulus/prover alignment and cross-limb provenance are separate obligations.

[EXECUTED completed cycle] A real PCS-enabled matvec proof now uses fused spectral evaluation/quotient generation. Public native arithmetic checks passed; one normal proof returned exit zero, the unchanged verifier accepted, and four decrypted outputs matched. Patch SHA `3ac1aa4ca8e414d5a4703b31b6601113995919f14e925049886d248ba2579443`; see [REPORT.md](REPORT.md) and [implementation/native_command.json](implementation/native_command.json).

[DERIVED exact delta] Cache public matrix NTTs, reuse each input component transform, accumulate Hadamard products before one output inverse, and derive `Y=L−H,Q=H` from `S=L+X^N H`. This replaces the actual source's duplicate full-product and ring-product computation. The Python complementary-coset identity `Q=(D−Y)/2` also passed, but the native port uses the existing length-2N negacyclic backend.

[EXECUTED larger successor] The single larger matched real proof pair and complete native public replay are finished in [scaled/REPORT.md](scaled/REPORT.md): D=4096,64×8192 matrix, whole prove711.650ms→459.557ms (1.5486×), preprocessing plus prove1.4719×, byte-identical full proof files, both fresh replays accepted before64/64 private comparisons. Combined spectral fusion plus shared Y/Q contraction; single baseline-first pair only. Browser consumer work is with independent_review.
