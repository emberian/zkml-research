# Full unique-decoding port — frozen and checked

[EXECUTED] `full-ud.patch` is complete. SHA256:
`1e7a4c2292766f8b02a80879ef288915d610b67b5c070d8892db8661a8146cb2`.
It adds ten owned modules, 1,992 lines, and 38 theorem/lemma declarations,
all 38 with exact axiom guards. The four dependency modules are the matrix
all-pins successor and the three gluing universe-successor modules.

[EXECUTED] The complete 14-module dependency-ordered exact-byte pass returned
exit code zero for every module; all source hashes stayed unchanged during
the checks. `manifest.json` has `exact_byte_checks_complete: true` and records
all hashes/commands. `logs/freeze-01` through `freeze-14` retain evidence.
Every guarded theorem uses exactly `propext`, `Classical.choice`, `Quot.sound`.

[EXECUTED] The import boundary passes. The patch applies cleanly in a fresh
check tree; resulting bytes match all ten sources. `package.py
--require-complete` rechecks this packaging evidence and the check manifest.

[EXECUTED] The integer full-UD core, probability/MCA/fold heads, existing FRI
tower and whole-opening committed consumers, new-band firing witness and
radius falsifier are checked. See `README.md` for exact covered scope.

[OPEN] Main minidregg was not edited or fully built by this lane. Root owns
combined integration and umbrella wiring. Frozen source must not be edited;
any follow-up is a successor artifact.
