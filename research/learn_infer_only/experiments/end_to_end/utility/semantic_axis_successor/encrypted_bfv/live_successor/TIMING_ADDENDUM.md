# Timing correction to the sealed live result

[SOURCE correction] The sealed coordination.json and REPORT.md treated the
TFHE worker's 05:56:47 UTC observation as its exact Infer-block close. That
was an attribution error in this packet: the observation followed Learn81.
The worker's retained public stdout records event80, the last Infer in that
block, complete at **05:56:25.935979 UTC**; Learn81 completes at
05:56:46.718959 UTC. The exact checkpoints and original message attribution
are retained in [contention.json](../../../../private_ema/emitted_long_run/contention.json),
SHA-256 `670f57b16ae146116cdf751b226b87962d621ff677331104445c47fae6b71bf4`.

[EXECUTED/DERIVED] The live start remains 05:56:48 UTC and its outer interval
27.504062 seconds, as recorded in run_started.json and run.command.json.
It therefore overlapped Learn82 and subsequent work after the Infer block.
No isolated-machine timing claim follows. The worker accepted the overlap;
no pause was requested. The model/BFV outcome, public-before-decryption
ordering and independent checks are unchanged.

[EXECUTED preservation] The original 67-file manifest and all its files stay
byte-identical. This addendum supersedes only the exact block-close timestamp
and its attribution, leaving the original evidence available. Its separate
timing_addendum_manifest.json pins this correction and the original seal.
