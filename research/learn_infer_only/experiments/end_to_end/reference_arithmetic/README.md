# Independent public BFV arithmetic check

[EXECUTED] A standard-library-only Python integer/protobuf reference matches
the retained production ciphertext outputs byte for byte. It does not import
or call the production FHE arithmetic. The primary Infer oracle is direct
integer negacyclic multiplication; a different twisted cyclic NTT and a
normalized source-indexed equation model provide additional checks.

| Retained suite | Operations checked | RNS output coefficients | Exact output bytes |
|---|---:|---:|---:|
| Public synthetic `host_runtime/run_001` | 8 Learns, including 4 expiries; 4 Infers | 196608 | 1021236 |
| Public utility `utility_002`, finalized `h0-e0065` | 1 Infer | 16384 | 85103 |

[EXECUTED] Both use N4096, two ciphertext components, moduli
`2199023190017,4398046486529` (83-bit product), and 577 query coordinates.
The host fixture's two queries each have **558/577 nonzero coefficients**;
they are not sparse. The separate actual utility query has **539/577
nonzero coefficients**, 270 positive and 269 negative, with nonzero endpoints.
Its accumulator and output are nonzero public ciphertexts. The two suite
denominators above are kept separate.

[EXECUTED] Authoritative completed records:

- [Host fixture report](results/run_004/report.json) and [execution log](check_004.log).
- [Dense utility report](results/run_003/report.json) and [execution log](check_003.log).
- [Source hash verification](verify_sources.log): 21 read-only source/build
  evidence files rehashed; historical source and copied-binary pins agree.
- [Fixture manifest](fixtures.json): 25 ciphertexts and two public queries,
  retained as gzip files; [utility fixture manifest](utility-fixtures.json):
  two ciphertexts, one public query and a linked public finalization packet.

[SOURCE/DERIVED] [DERIVATION.md](DERIVATION.md) gives the exact wire format,
ordinary polynomial Learn/Infer relation, source primitive-root contract,
bit-reversed odd-root evaluation order, inverse-table identity and scope of
the source equation model. [source-map.json](source-map.json) records exact
paths, lines and hashes. The serialized values are power-basis coefficients
even though the protobuf representation tag says NTT. This is the seam that
makes a direct, independent polynomial oracle possible.

Run from the repository root, choosing unused result directories:

```sh
python3 research/learn_infer_only/experiments/end_to_end/reference_arithmetic/check.py --run run_005
python3 research/learn_infer_only/experiments/end_to_end/reference_arithmetic/check.py --run run_006 --manifest utility-fixtures.json
python3 research/learn_infer_only/experiments/end_to_end/reference_arithmetic/pin_sources.py --verify
```

[EXECUTED] The first two commands need only the retained fixture files and
Python's standard library. Each rehashes its inputs, independently parses
and reproduces their complete bytes, checks all output coefficients, and
records its source and fixture hashes. The last command intentionally needs
the absolute read-only companion/cache sources. `capture_public.py` and
`capture_utility.py` document the original allowlisted capture; replay does
not need the ignored production runtime. No queries were sent to Scry or
other search services.

[OPEN] These are positive samples of public ciphertext arithmetic and byte
correspondence. They are not a universal Rust/compiler refinement, a noise
or decryption proof, an authenticated execution proof, or a privacy result.
The reference does not read secret keys/private vectors, decrypt, rerun the
utility workload, or test extraction/routing attacks. Earlier `run_001` and
`run_002` reports retain development checkpoints; use `run_003`/`run_004`
for the final source and query-support census.

[OPEN: continuation] A subsequent proof effort can connect the source-indexed
modular transform equation to literal native Shoup/Barrett and pointer
semantics, then connect the byte parser to the emitted provenance relation.
This packet supplies exact retained public witnesses and an independent
arithmetic reference for that work; it leaves the frozen BFV certificate
patches and the incomplete operand-provenance lane unchanged.
