# Reusing the emitted traces

[EXECUTED packaging] The two complete Lean-produced traces are stored in lossless gzip form to keep the repository small. The original uncompressed bytes remain in this workspace and their hashes are recorded by artifact_pins.json. Compression used Python gzip.GzipFile with an empty filename and mtime=0; it does not change the witness.

To use the saved trace without rerunning the Lean producer:

```sh
gzip -dk artifacts/trace.leu32.gz
gzip -dk artifacts_expiry/trace.leu32.gz
```

The runtime consumes the resulting little-endian u32 file. The README also gives the Lean regeneration commands.
