# Rescale compiler layout: actual proof-cost successor

[EXECUTED] Same real32-position batch, same native generic runtime and backend,
smaller proved allocation. The new proof passed fresh verification and changed
output rejection. See `REPORT.md` and `RESULT.json` for exact comparison.

No new Rust source is required: the frozen runtime consumes arbitrary generated
trace widths with the same88-column public prefix. Its build pins remain in
`../proved_rescale_generic/BUILD.json`. The new relation and Lean witness belong
to `../rescale_compiler_successor/`; all outputs here are separate.

The retained commands in `results/*.command.json` are directly replayable into
new output directories. For example, from this directory:

```sh
RAYON_NUM_THREADS=4 ../proved_rescale_generic/target/release/vfhe-proved-rescale-generic prove ../rescale_compiler_successor/artifacts/template_ir2.json ../proved_rescale_generic/results/case001 ../rescale_compiler_successor/artifacts/trace.leu32 NEW_PROOF
RAYON_NUM_THREADS=4 ../proved_rescale_generic/target/release/vfhe-proved-rescale-generic verify ../rescale_compiler_successor/artifacts/template_ir2.json ../proved_rescale_generic/results/case001 NEW_PROOF/proof.bin
```

The old proof was not regenerated. Current scope is32 actual positions,
128 final residues; no fullciphertext or wholelearner claim follows.
