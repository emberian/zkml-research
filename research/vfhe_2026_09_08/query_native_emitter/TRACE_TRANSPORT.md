# Exact public witness transport

[EXECUTED packaging] The native full001 witness is byte-identical to the already-proved query witness. The unchanged local raw file is excluded from Git; its compressed transport is stored once in `../query_arithmetic/artifacts/trace.leu32.gz`.

From the repository root:

```sh
gzip -dc research/vfhe_2026_09_08/query_arithmetic/artifacts/trace.leu32.gz > research/vfhe_2026_09_08/query_native_emitter/results/full001/trace.leu32
```

[SOURCE] The existing report/pins record full-byte equality. No emitter or proof was rerun for packaging.
