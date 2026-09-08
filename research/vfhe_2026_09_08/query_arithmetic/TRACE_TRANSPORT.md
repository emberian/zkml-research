# Public witness transport

[EXECUTED packaging] The original complete witness remains unchanged locally. Git carries its gzip transport at `artifacts/trace.leu32.gz` (8,603,809 bytes); the uncompressed witness is 82,214,912 bytes, SHA-256 `8f1d1a0ab009f41756e2164c4a0a833494f1d76ad07992f58b767fb495e78cc5`. This is packaging, not another proof run.

Restore the exact recorded path from the repository root:

```sh
gzip -dc research/vfhe_2026_09_08/query_arithmetic/artifacts/trace.leu32.gz > research/vfhe_2026_09_08/query_arithmetic/artifacts/trace.leu32
```

[SOURCE] The cached-emitter package's retained comparison establishes that its baseline and faster traces are byte-identical to this witness. Those two duplicate raw copies are also excluded from Git; its `TRACE_TRANSPORT.md` gives reconstruction commands. Source/measurement/proof files are unchanged.
