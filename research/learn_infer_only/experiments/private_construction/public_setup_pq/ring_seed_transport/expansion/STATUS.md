# Public expansion status

[EXECUTED] Runtime sources frozen and handed to parent. Cheap deterministic
domain, repeatability, rejection, exhaustion and invalid-input checks pass.
One full public row at N=16384/q289 took 0.0100 seconds; evidence is in
`CHECKS.json` and `RUN.log`, with package hashes in `MANIFEST.json`.

[DERIVED] Canonical independent chunk addresses avoid repeated-prefix XOF
work. Rejection has no modulo bias under ideal independent XOF words, and
cap exhaustion raises without a fallback. Read `SECURITY.md` before making
a construction claim from public seeded expansion.

[OPEN] Direct seeded Ring-LWE/regularity or an appropriate programmable-XOF
proof remains absent here. A revealed seed does not inherit hidden-seed PRG
indistinguishability. Parent owns context binding and fresh setup execution.

[DERIVED correction] Seeded missing rows add another recomputable relation.
Seeded Ring-LWE for `A` alone does not justify replacing such a row by `Z*A`
while retaining its unprogrammed public seed; see `SECURITY.md` for the full
joint simulation/new-direct-proof obligation.
