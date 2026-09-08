# Exact public witness transport

[EXECUTED packaging] The unchanged native event66 witness is carried as `results/event66/trace.leu32.gz`. Restore the original recorded path from the repository root:

```sh
gzip -dc research/vfhe_2026_09_08/update_native_emitter/results/event66/trace.leu32.gz > research/vfhe_2026_09_08/update_native_emitter/results/event66/trace.leu32
```

[SOURCE] The original result records its complete-byte equality to the already-proved event66 trace. This is compression only, with no emitter/proof rerun.
