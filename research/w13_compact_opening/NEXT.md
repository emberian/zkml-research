# Remaining research

[EXECUTED] The resident latency and 92,000-byte goals pass for the three-sibling fixture. The current circuit uses paired Keccak rounds and 64-party bit planes. [Measurements, scope and reproduction](../../notes/compact-bitsliced-cshake256-opening.md)

[OPEN] Formalize the two-stage Fiat–Shamir extraction and hiding arguments with explicit primitive and query budgets. The exact split enumeration and the two POLYVAL checks provide the challenge terms. [Implementation](../../native/resident_custody/src/cshake_selective_open.rs)

[OPEN] Connect the selected Minidregg typed codec and receiver to the private circuit’s public wire-image interface. A proof of refinement must cover the canonical encodings, reader prefixes, private early stops and extracted witnesses. The cost at a 260-bit prefix is measured separately from the resident byte circuit. [Private circuit](../../native/resident_custody/src/trie_opening/deployed.rs) · [260-bit proof](full-field.log)
