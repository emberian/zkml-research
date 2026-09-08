# Reconstruct the identical comparison witnesses

[EXECUTED packaging] The baseline and cached emitters produced the same complete witness as the frozen query-arithmetic proof. Git stores that public witness once, compressed in the sibling package. Original local traces and all measurements remain untouched.

From the repository root:

```sh
gzip -dc research/vfhe_2026_09_08/query_arithmetic/artifacts/trace.leu32.gz > research/vfhe_2026_09_08/query_emitter_successor/results/baseline001/trace.leu32
cp research/vfhe_2026_09_08/query_emitter_successor/results/baseline001/trace.leu32 research/vfhe_2026_09_08/query_emitter_successor/results/fast001/trace.leu32
```

[SOURCE] `README.md` and the saved result JSON files record the complete-artifact equality and measured emitter comparison.
