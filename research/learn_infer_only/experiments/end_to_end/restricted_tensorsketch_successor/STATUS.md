[EXECUTED, 2026-09-08 22:47 UTC] The single frozen map fails its predeclared utility gate. Original cached features, one deterministic seed, map and policies were fixed in [POLICY_FREEZE.json](POLICY_FREEZE.json) before `python3 -B evaluate.py > evaluation.stdout 2> evaluation.stderr`. The one paired evaluation exited0 in2.575 seconds. [Exact result](results/RESULT.json), [all predictions](results/predictions.csv).

| Teaching revision | TensorSketch /3,080 | Identical-policy linear /3,080 |
|---:|---:|---:|
|304|1,072|1,246|
|616|1,808|2,194|
|1,232|1,870 (60.7143%)|2,253 (73.1494%)|

[EXECUTED] Final degradation is12.4351 percentage points. The fixed16-query slice remains16/16 at all three checkpoints. All4,334 mapped vectors required neither clipping nor the norm cap; quantization still applies. Registered rows have rank16 and six field-basis roundtrips passed. The retained registry/fixture are public feature artifacts, with no cryptographic setup or keys. There is no nonlinear utility improvement or new privacy evidence.

[SOURCE] [Pham/Pagh, KDD2013, §4.1–4.2 and Algorithm1](https://www.rasmuspagh.net/papers/tensorsketch.pdf): separate CountSketches, circular convolution, decomposable hash/sign maps, and constant-coordinate augmentation. Own source counts: zero web searches, two primary-PDF opens, zero Scry queries. No paper probability bound is applied to this fixed seeded, quantized map. The canonical implementation uses exact integer convolution, not the paper's FFT runtime.

[DERIVED] The declared integer norm cap512 gives absolute score at most32·512²=8,388,608 for total signed weight32, below floor(p/2)=14,219,946. This arithmetic bound is not cryptographic security. No additional algebra-control run was performed.

[REPORTED stop] Root requested architectural reassessment after this result. Unexecuted adapter/control scaffolding was removed; frozen map, policy, source/input pins and outputs are retained. One map, one seed, one paired utility run; zero new model forwards/downloads, crypto runs or private-artifact reads. No tuning or further packaging follows.
