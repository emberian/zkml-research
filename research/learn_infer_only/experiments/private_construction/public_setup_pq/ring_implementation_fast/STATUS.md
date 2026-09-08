# Status

[EXECUTED] Native integer Gaussian screening and shared exact FLINT decoding
are integrated. The toy and matched full repaired workloads passed. The full
run took 117.13 seconds versus 265.74 seconds baseline (2.27 x), with 112 matching
designated reads and 19, 922, 944 Gaussian coefficients. Sources stayed unchanged
during execution; the baseline package is untouched. Root owns shared ledgers
and commits.

[EXECUTED] The sampler's contemporaneous million-coefficient benchmarks
measured 10.28 x error-width and 7.23 x key-width speedups with the same law.
The full integrated run measured 5.95 x key-sampling and 5.68 x error-sampling
speedups, 4.32 x all-recipient decoding speedup, and 2.217 GiB peak RSS (+8.8%).
