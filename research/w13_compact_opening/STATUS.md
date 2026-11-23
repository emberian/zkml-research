# Wave 13 lane 1

[EXECUTED] A four-worker release run measured 77,744 median proof bytes for a 64-byte resident cell, with 14.906 s median prove and 6.050 s median verify. The comparison used the same witness and public statement for both backends. [Three fresh samples per backend](bench.log)

[DERIVED] The largest compact proof for this cell is 78,544 bytes. The worst of the 15 bad-preprocessing splits gives 128.222323926 classical challenge bits. The batched construction also checks the independent polynomial-error term against the remaining margin. [Derivation, assumptions and protocol](../../notes/w13-compact-ggm-cshake256-opening.md)

[EXECUTED] The public-branch verifier authenticates the resident projection. The private-prefix circuit checks framed custody and complete answers on canonical wire images with the 219-round backend. The latter accepted a scoped body view and a 260-bit field prefix. Independent Go digests match the private fixture and the public 516-step climb. [Acceptance](acceptance.log) · [Full field proof](full-field.log) · [Independent roots](vectors.log)

[EXECUTED] The current resident implementation supersedes the opening measured above. Its exact parameter ledger, trie branch accounting and release gate are in the [paired-round opening note](../../notes/compact-bitsliced-cshake256-opening.md).
