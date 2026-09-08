[EXECUTED] The requested source integration is complete. Use minidregg-fhe-arithmetic.patch and README.md; the patch already includes the full required off-tree dependency chain, completed query/rotation modules and the selected optimized rescale exporter. All three new-glue checks passed.

[OPEN maintainer action] Apply in the chosen minidregg checkout and run its normal whole-tree integration gate at landing time. Main tree edits are preserved by the one-import hook; the current actual main tree passed read-only git apply --check. No proof/source changes in frozen packages are needed for this proposal.

[OPEN later successor] rescale_compiler_successor was active when this package was assembled and remains excluded. Incorporate it only through its completed replacement patch after its owner/root handoff; do not silently overwrite the sources in this frozen integration package.
