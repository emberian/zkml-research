# Packed reader status

[EXECUTED] Complete reader source and a separate native executable are built
under this directory. `PROFILE.json` pins the caller, Rust source, Cargo
manifest, lockfile, and native executable. `SOURCE.json` records the original
reader source and exact new identities and build command.

[EXECUTED] `CHECKS.json` retains successful profile verification, three native
pre-decryption refusals, and all 18 existing linear-profile pins unchanged.
No private read, key generation, or proof execution was launched by this lane.

[SOURCE] `README.md` documents the available command, returned fields, all-slot
repetition check, per-class count bound, zero empty lanes, and full reader
authority. The packed learner and workload owners have been sent the built
binary path and this contract.

[EXECUTED integrated lifecycle] The complete packed lifecycle made five bank reads; all forty bank lanes and exact class sums matched the reference. The later fresh browser query made two bank reads and matched all sixteen bank lanes. See `../../results/packed-matched/RESULT.json` and `../../results/browser-packed/RESULT.json`.

[OPEN] Native parser/NTT, BFV decryption
correctness, trusted counts and caller proof ordering remain explicit external
boundaries; this package does not change the proof producer.
