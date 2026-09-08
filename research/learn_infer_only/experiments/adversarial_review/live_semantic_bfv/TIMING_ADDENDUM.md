# Timing attribution correction after the original review seal

[SOURCE correction, 2026-09-08] The author's original coordination packet
misidentified the TFHE worker's 05:56:47 UTC observation as the exact first
Infer-block close. The author's separately sealed `TIMING_ADDENDUM.md` and
`timing_addendum.json` correct that attribution using the worker's public
`end_to_end/private_ema/emitted_long_run/contention.json`, SHA256
`670f57b16ae146116cdf751b226b87962d621ff677331104445c47fae6b71bf4`.
Its retained event-80 checkpoint, identified by that worker as the final Infer
of the block, is **05:56:25.935979 UTC**. Learn81 completes at
05:56:46.718959 UTC; the later observation occurs at 05:56:47 UTC.

[EXECUTED / DERIVED] The live start remains 05:56:48 UTC, with outer wall
27.504062 seconds, as independently checked against the retained start and
command records. It overlapped Learn82 and subsequent work, after the Infer
block. The original independent report's statement that the run started after
the block remains true; the corrected exact time and attribution here take
precedence over the original author's timing sentence. These are shared-load
measurements. Worker acceptance of the overlap remains attributed to the
recorded coordination messages, not an independently reproduced event.

[EXECUTED] The following standard-library-only command exits zero; source,
output and checked public hashes are retained in this directory:

```
python3 -B research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/verify_timing_addendum.py > research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/timing_check.stdout.json
```

It checks the corrected checkpoint objects against the public worker record,
the unchanged live start/wall records, the two-file author correction seal
SHA256 `f1226c40feeab45bdf51554200c9a70f5da4c5ac20410efcef7b6e4c1edf0453`,
and all entries of both preserved original manifests: 67 author files and
17 independent-review files. The original review report and manifest are not
edited. `review_v2.json` and `manifest_v2.json` add this correction to the
preserved result.

[DERIVED disposition] The source and normal-integration acceptance, private
result attribution, public-before-private boundary, output-disclosure and
full-key scope are unchanged. No runtime, model, cryptographic operation,
private read or additional attempt was performed for this timing correction.
