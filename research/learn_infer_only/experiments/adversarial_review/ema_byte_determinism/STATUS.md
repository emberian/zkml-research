# EMA byte determinism audit status

[EXECUTED, 2026-09-08] Complete within the assigned source/public-data scope.
`REPORT.md` separates the executed mismatch, inspected implementation facts,
the timing-selected FFT candidate, and the unresolved causal/runtime questions.

[EXECUTED] Independent parsing confirms the owner's 10,015-byte mismatch only
in ciphertext records 21–23; all framing metadata and 29 other records match.
The three public input hashes match the saved pair. The source archive audit
passes 19 selected files, six prior source pins and three Cargo-locked archives.
The local TFHE build fingerprint lists only `boolean`, with no fixed-Dif4 flag.
The owner failure seal and source-checkpoint hashes are checked.

[SOURCE] The exact feature is `experimental-force_fft_algo_dif4`. An early
informal message called it `fft64-default` before the cfg was read; that name
was inaccurate and was explicitly corrected to root and the runtime lane.
The report and artifacts use only the actual declared feature name.

[EXECUTED] No private files, client keys or plaintext answers were read. No
crypto, decoder, old-run resume, new-run launch, source edit outside this audit
directory, commit, or push was performed. Web/Scry/Kagi queries were zero.

[OPEN] Actual plan identities in the failed pair are unavailable in its saved
logs. Byte inequality does not decide functional correctness. The independent
emitted-runtime lane owns any separately authorized fixed-plan successor.
