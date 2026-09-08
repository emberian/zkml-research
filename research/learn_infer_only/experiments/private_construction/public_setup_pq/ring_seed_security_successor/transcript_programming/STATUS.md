# Transcript programming status

[DERIVED] Exact classical finite programming kernel proved in `KERNEL.md`:
overwrite only first-N accepted low words of a fresh ideal capped chunk
table, retain all high/rejected/unused bytes, and preserve abort unchanged.
Uniform independent targets restore the complete uniform table law exactly.

[EXECUTED] One tiny exhaustive model checked 36,864 table/target pairs,
including unused final chunks and high bits. Abort is exactly 13/256 for
every target. Zero-high-bit and zero-unused-tail mutations fail the table-law
test. `CHECKS.json`/`RUN.log` retain the command and output.

[OPEN] Parent full A/missing-row hybrid and chronology, concrete SHAKE256
instantiation and QROM remain outside this kernel. No crypto, estimator,
private-artifact read or frozen-package edit occurred.
