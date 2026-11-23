# Next

1. Measure with one disk per custodian (three hosts, or three devices), to see whether the trailing checkpoints really leave the vote path. The single-host runs serialize every flush on one device.
2. Decide whether B should verify the header before publishing. It costs 12.6 ms on hbox, protects only B's liveness, and the log verifies anyway.
3. Pin the 21 Lean vectors' 272-byte expected outputs from a Lean run of `PancakeBeltLatchTest` into this crate, so parity no longer depends on the native ELF being present.
4. Ask DreggNet for a second golden vector (a seat with three credits, one at zero remaining) so drift on their side is also caught here.
5. Decide whether per-provenance counts belong in the public header, or only the cursor.
