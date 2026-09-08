# Focused vFHE construction delta

[EXECUTED scope] New lane authorized by root after the completed polynomial-kernel review. Only this directory is writable; companion trees, existing notes and stopped tasks remain untouched.

[SOURCE prior baseline] Read `notes/ring-switching-connectors.md`, `notes/circle-aligned-vfhe.md`, `notes/fhe-scout-verdicts.md`, `notes/ntt-as-gemm.md`, and relevant `docs/VERDICTS.md` passages. Preserve the known distinctions: packing is not elementwise lifting; shared twiddles do not create an NTT relation; BAT needs a preknown operand; modulus/prover alignment and cross-limb provenance are separate obligations.

[EXECUTED completed cycle] A real PCS-enabled matvec proof now uses fused spectral evaluation/quotient generation. Public native arithmetic checks passed; one normal proof returned exit zero, the unchanged verifier accepted, and four decrypted outputs matched. Patch SHA `3ac1aa4ca8e414d5a4703b31b6601113995919f14e925049886d248ba2579443`; see [REPORT.md](REPORT.md) and [implementation/native_command.json](implementation/native_command.json).

[DERIVED exact delta] Cache public matrix NTTs, reuse each input component transform, accumulate Hadamard products before one output inverse, and derive `Y=L−H,Q=H` from `S=L+X^N H`. This replaces the actual source's duplicate full-product and ring-product computation. The Python complementary-coset identity `Q=(D−Y)/2` also passed, but the native port uses the existing length-2N negacyclic backend.

[OPEN next authorized cycle] Root requested one materially larger matched unfused/fused proof run and integration with polynomial_gluing's shared `Y/Q` contraction. No native speedup is yet established. Browser replay needs complete proof serialization; independent_review has the exact API and saved-artifact limitation.
