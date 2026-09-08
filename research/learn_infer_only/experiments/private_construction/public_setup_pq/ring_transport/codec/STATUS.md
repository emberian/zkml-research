# Codec status

[EXECUTED] Runtime sources frozen and handed to the parent. Five small
roundtrips, fourteen malformed refusals, partial I/O and next-section
preservation passed. One 289-bit public-data benchmark measured 5.80M
values/s packing and 4.46M values/s unpacking plus comparison.

[DERIVED] Raw payloads have exact counts, canonical unsigned ranges and
zero high padding. Header/context binding and signed interpretation remain
parent-owned. Read `DESIGN.md`, `MEASUREMENTS.json` and `MANIFEST.json`.

[EXECUTED] No private artifact reads, payload files, companion writes or
searches. All edits are confined to this codec directory.
