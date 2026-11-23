# Wave 12 resident custody

[EXECUTED] Seven release tests passed across the durable custodian, restored operator and selective-opening paths. Timing samples, failure boundaries, proof assumptions and the deployed relation are recorded in the [lane note](../../notes/w12-resident-custody-and-cshake-opening.md). The checkout contains the custodian and operator entry points, the library client and the subprocess harness under [resident_custody](../../native/resident_custody/).

[EXECUTED] The independent outer-hash vector used Go 1.24.1. From the repository root, `go run research/wave12_resident_custody/outer_vector.go` printed the following.

```text
outer_frame=30ff01ff2cff44524547472f53544f5245036b7852d67118b7c51346d5ee0e6e0e2a10ef316e4a7501098dc7342683900bdc29ff04ff736561742d01ff
outer_root=228b05975e7fa9d7fe294cb03903b2e7c7069c6d3ff2d3c306d575e1d64c42a7
```

[EXECUTED] The post-suite process check was `ps -axo comm | awk '/l5-zkml\/native\/target\/release\/(custodian_node|resident_operator)$/ {n++} END {print n+0}'`. It printed `0`.
