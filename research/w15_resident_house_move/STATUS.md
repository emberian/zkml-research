# Resident house move audit

[EXECUTED] The complete CLI move met the 120 ms median target on M2 Max/APFS at 114.087 ms. The shared hbox/ext4 run measured 168.110 ms. Each had 11 samples. The native hbox integration test passed all 12 refusal cases with 88 native-checked custodian latch steps. The default warnings-as-errors release suite passed 23 tests with four opt-in tests skipped. The native ABI and latency tests were also run explicitly. [Audit log](audit.log) · [Protocol, scope and timing boundaries](../../notes/resident-house-move-protocol-weld.md)

[EXECUTED] The Rust codec and independently rebuilt ELF matched all 21 Lean-generated input/output records. Rust and the ELF agreed on every byte across 4,153 comparisons. Two receipt fixtures crossed the pinned DreggNet verifier boundary in both directions. Reopening the public log recovered the exact package, latch and head. An explicit failed write followed by retry produced one committed epoch. [Fixture generator](lean_vectors.py) · [Billing interop](check_billing.sh)

[DERIVED] The complete journal opening is bounded by 90,976 bytes. The public proof exposes the cursor, counts and a blinded W0 sibling, while private journal data remains with the custodians. Votes authenticate the mesh-domain digest of the 152-byte acknowledged Obend request. Receipt verification covers the exporter's signed transferable backing and reserve arithmetic. The Tulip result covers certified episode IDs and a 16-byte W0 continuity check. [Audited protocol](../../notes/resident-house-move-protocol-weld.md)

[REPORTED] Stage 1 measured 112.792 ms on hbox and 185.249 ms on Mac using a latch-only persistence callback. Those historical measurements describe commit `09630393`. [Original outputs](bench.log)
