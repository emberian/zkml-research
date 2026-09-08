# Resume

[EXECUTED] Read `MEASUREMENTS.json`, `DESIGN.md` and `MANIFEST.json`; no new
sampler benchmark is needed to establish the recorded result.

[DERIVED] The parent can import `sampling.sampler.GaussianSampler`, and should
pin `sampler.py`, `reference.py`, `proposal_screen.c`, `__init__.py`, the loaded
binary hash, and its rebuild command in each integrated run. Preserve this
source freeze while the parent run executes.

[OPEN] Use the parent's integrated measurements for whole-ring comparisons.
Further native batching or arithmetic changes need their own differential
check; do not edit the frozen baseline or claim constant-time behavior.
