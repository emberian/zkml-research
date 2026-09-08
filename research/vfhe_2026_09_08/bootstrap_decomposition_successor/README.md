# Actual first CMUX integer input and signed decomposition

[EXECUTED] One genuine 363,165-byte proof covers all 2,048 native-u32 coefficients of `(X^394−1)*ct0` and their exact TFHE1.6.3 base-1024, two-level signed decomposition. `ct0` is the saved actual initial accumulator after its already-proved body rotation. A fresh consumer verifies the previous modulus-switch proof, the previous complete rotation proof, and this new complete component proof. A changed level-2 digit reaches the unchanged proof verifier and is refused. Results and exact commands are retained in `results/`.

| Measured work | Result |
|---|---:|
| New relation | 2,048 rows ×301 wires;318 arithmetic constraints;3 exact-public tables |
| Lean trace | 2,465,792 bytes |
| Lean-generated template | 62,113 bytes |
| New proof | 363,165 bytes |
| Prove / same-process verify | 403.139292 ms /27.430167 ms |
| Fresh new-component verify | 27.747000 ms |
| Fresh predecessor verifies | 16.335083 ms modulus switch +18.370000 ms rotation |
| Changed-digit verifier refusal | 17.066209 ms, plus accepted predecessors |

[EXECUTED] New proof SHA256: `6993ca1094c7c96d99c3cab01605dc395dd12153aff2ae2b00c25c01a3db9f34`. Template SHA256: `d1306386767a9ec8bdfb9bddf3e0b2f831b352feafdbd3b5e2572baa7aa4c52a`. These are local native timings, not browser measurements or security-bit estimates.

[EXECUTED] Run from this directory with the retained binary, or build this owned crate with `cargo build --release --offline`. The input template is caller-selected; use the pinned template above. All runtime dependencies and the exact binary are recorded in `execution_pins.json`.

```sh
target/release/tfhe-bootstrap-decomposition-proof verify artifacts/template_ir2.json fixtures/normal_001 results/proof001/proof.bin results/replay.json
```

[EXECUTED] `results/verify-001.json` retains the original fresh-process command. `reject-changed` uses the same saved proof and changes only coefficient1536's signed level-2 digit from0 to1, keeping it in range. It reports the actual backend refusal `InvalidOpeningArgument(InvalidPowWitness)`. The consumer reconstructs public tables from canonical decoded ciphertexts and digit bytes; it reads no keys or private artifacts. All proof decoders reject trailing bytes.

[DERIVED] This is a sequential join of three ordinary proof verifications, not a recursive or aggregated proof. The original modulus-switch table binds all806 native LWE words; the reader selects its first nonzero mask row `[0,6878,25207,394]` and verifies the initial body rotation at row805 `[805,56149,55195,862]`. The new proof binds the exact decoded previous output as its input, the same public exponent, all original-index and rotated-index reads, all wrapped differences, and the rounded word and ordered digit offsets.

[SOURCE] The actual core library's fused multiply/subtract helper is crate-private. The one new public intermediate uses its existing public monomial-multiply and wrapping-subtract calls in sequence, which have the same native-u32 relation. The actual existing `SignedDecomposer<u32>` supplies the rounded outputs and ordered level2 then level1 digits. No new keys, encryption, bootstrap, FFT, or external product was run. Native differences contain1,654 zero coefficients,350 coefficients equal to−2^30 modulo2^32, and44 equal to2^30; digits are respectively `(0,0)`, `(0,−256)`, and `(0,256)`.

[EXECUTED] The successful Lean export checks every native row and17 explicit rounding/tie boundary witnesses. The generated source also rejects a changed difference, a changed signed digit, and an out-of-range limb. Kernel theorems quantify over arbitrary assignments and include accepted zero/nonzero/tie witnesses and an inhabited falsifier; the finite checks do not replace those theorems. See `SOURCE_AND_MATH.md`.

[OPEN] This advances only the integer prefix of the first CMUX. It does not prove the bootstrapping-key external product, FFT, torus conversion, later mask iterations, key switch, or complete PBS/AND semantics. The TFHE source/model correspondence, public reader, Lean-to-IR2 serialization and existing proof backend retain their normal implementation trust boundaries. The shared fixed-public-preprocessing backend is reused unchanged; this package establishes no new cryptographic theorem or certified security level.

[EXECUTED provenance limit] The complete source/binary/input inventory was recorded **after** the proof run. The first inventory helper used a nonexistent main-tree `AirSimplify.lean` path; the actual dependency is the retained optimization overlay. The command sequence continued into the successful proof and two consumer runs. The corrected inventory states its actual post-run timestamp; no pre-run inventory claim, hidden reproof, or extra crypto attempt is made. Final input rehash evidence is `results/integrity.json`.
