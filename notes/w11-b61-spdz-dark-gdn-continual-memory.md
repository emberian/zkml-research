# Wave 11 Lane 5 · B61 continual fast weights

[SOURCE] This lane implements one finite-field GDN state with the dimensions of one Qwen3.5-0.8B fast-weight layer. Inputs are synthetic field elements. The Qwen audit runtime separately uses rounded, fixed-point WY products. The lane's reference is the field recurrence below. [Geometry and fixed-point runtime](../native/qwen35audit/src/agent_runner.rs#L1637)

## What the kernel checks

- [DERIVED] A single evaluator can copy its initial ciphertext, evaluate a second query list and produce precisely the honest main transcript. For a threshold trace, the bound is on **accepted crossings**, with epochs in the authorized budget. Honest quorum intersection requires $n+f<2t$. Two signatures among three with one corrupt signer do not imply it. The file gives a split-quorum witness for exactly that case, and a separate theorem assuming unique policy epochs. [Single provider, threshold bound, policy epochs and counterexample](/Users/ember/dev/minidregg/Assurance/DarkB61ContinualGdn.lean:85)
- [DERIVED] With column keys and values, the step is $S' = \gamma S + \beta(v-Sk)k^T$. Its WY representation includes the incoming state in the residual and causal decay in the key factors. Nilpotence of the strictly lower triangular coupling matrix gives a finite, two-sided inverse for $I+L$. The chunk identity holds over commutative rings, including composite-modulus rings. [Constructive inverse](/Users/ember/dev/minidregg/Assurance/DarkB61ContinualGdn.lean:253) · [Stateful equivalence and ZMod specialization](/Users/ember/dev/minidregg/Assurance/DarkB61ContinualGdn.lean:434)
- [DERIVED] Each 64-row slice packs entry $(i,j)$ at degree $128i+j$. The highest product degree is $63\cdot128+127=8191$, so reduction modulo $X^{8192}+1$ preserves every outer-product coefficient. The reverse-key read can wrap into degrees 0 through 126, below the first readout at 127. The packing bijection covers all 262,144 cells with 32 ciphertexts. [Outer product](/Users/ember/dev/minidregg/Assurance/DarkB61ContinualGdn.lean:537) · [Readout and bijection](/Users/ember/dev/minidregg/Assurance/DarkB61ContinualGdn.lean:609)
- [DERIVED] Orthogonal subtraction removes the learned write and preserves the episode's decay. Unit decay throughout the removed episode suffices for literal omission. General WY replay implements literal omission for arbitrary gates and overlapping keys. In a domain, the discrepancy theorem identifies a nonzero coordinate when the later gate, key overlap, update coordinate and later key coordinate are all nonzero. The concrete falsifier uses ZMod 17. [Orthogonal theorem](/Users/ember/dev/minidregg/Assurance/DarkB61ContinualGdn.lean:714) · [Replay and cross term](/Users/ember/dev/minidregg/Assurance/DarkB61ContinualGdn.lean:780)

## What the resident checks

[SOURCE] The harness keeps three custodian objects in one process. An operation carries a hybrid signature quorum, a policy digest, an epoch and a parent commitment. All three in-memory latches must accept. Private state reads use handle admission, masked decryption, noise flooding and the three parties' partial-decryption checks. SPDZ uses the same plaintext field as BFV. Refresh converts depth-one state to shares and re-encrypts it. The reference fixture can explicitly authorize a plaintext audit opening. [Epoch gate](../native/darkvfhe/src/dark_gdn_continual.rs) · [Crossing implementation](../native/darkvfhe/src/dark_gdn.rs#L1509)

[DERIVED] The audit corrected two errors that affected state values. The previous clear and shared inverses omitted the identity diagonal in their first matrix-power multiplication, losing the first subdiagonal even for two steps. Both now solve the triangular system by forward substitution. General replay previously restored checkpoints containing writes that an earlier orthogonal subtraction had removed. Replay now starts before the earliest affected tombstone, preserves its authenticated decay, skips literal omissions and updates retained checkpoints only after verification. The full-size oracle compares the final state against the history consisting of the first episode's decay and the third episode's update. [Resident integration test](../native/darkvfhe/tests/dark_b61_gdn_resident.rs)

[SOURCE] All slice reads, decays and rank updates pass the d-free BEHZ rescale verifier on their hoisted witnesses. The public state bundle opens the canonical Exact-Garner-15 digits for both components of every resulting ciphertext. Version 2 adds three independent public-digit fingerprints, pins the lookup-tree partition and checks the expected WHIR geometry. A separate succinct compute opening is serialized for head zero in the first adaptation. The benchmark counts the bytes returned by each encoder. Internal rescale witnesses, partial-decryption messages and quorum traffic have separate verification paths. [Rescale verifier](../native/darkvfhe/src/cert.rs#L517) · [State prover and verifier](../native/darkvfhe/src/dark_gdn_continual.rs)

[DERIVED] With independent uniform mask coordinates, surjectivity of the GMask transcript map gives TVD zero for its free sumcheck coordinates at fixed challenges and public sum. The state prover uses rejection sampling for these coordinates. For a fixed incorrect public digit matrix, one bilinear fingerprint has failure probability at most $2/p$ with uniform coefficients. Three domain-separated repetitions target roughly 180 bits at a 61-bit prime, under the transcript randomness assumption. The fingerprint output is verified through the same PCS opening. [Mask map](../native/darkvfhe/src/whir_pcs.rs#L204) · [Public-digit binding](../native/darkvfhe/src/dark_gdn_continual.rs#L1283)

[SOURCE] The WHIR estimate comes from the commitment shape. The inherited chunked LogUp samples its challenges once for the entire lookup multiset. The lane now uses four global challenges for the state proof. A single SPDZ MAC check has a field-sized statistical error term. The inherited partial-decryption proof includes unblinded secret-share evaluations, and the simulator generates triples in-process. Durable rollback protection, independent custodian processes and a composed 122-bit security reduction for the entire resident remain open. [WHIR estimator](../native/darkvfhe/src/whir_pcs.rs#L848) · [Shared lookup challenges](../native/darkvfhe/src/logup_gkr.rs#L751) · [Partial-decryption transcript](../native/darkvfhe/src/dark_gdn.rs#L265) · [SPDZ MAC check](../native/darkvfhe/src/dark_gdn.rs#L1396)

[DERIVED] For the fixed rational lookup identity with honest evaluations and poles rejected, the common denominator degree is bounded by the total lookup count plus the table size. At full geometry this is $64\cdot27\cdot8192+2^{20}$. The four-challenge estimate is $4\log_2(p/D)$ bits for degree bound $D$ and independent uniform challenges. This estimate covers the rational identity only. The separate PCS check against the canonical public digits also binds the range-checked values. The orthogonality check opens field nonzero indicators computed by SPDZ exponentiation, so the numeric cross-key inner products stay shared.

## Verification and measurement

[EXECUTED] From the research root, the command below kernel-checked the target with Lean 4.35.0. Output was `898 lines < 950; 0 sorry, 0 axiom, 0 native_decide; 15 #print axioms pins`, `scripts/check-import-boundary.sh passed`, and `0 warnings in 13.98s`. The compiler wrote its object into the research overlay.

```sh
research/wave11_frontier_upgrades_2026_11_22/formal_dark_gdn/build_and_verify.sh --lean-only
```

[EXECUTED] The end-to-end command used the release profile, eight Rayon workers and the lane-specific Cargo target on an Apple M2 Max. Setup took 485.65 ms. Genesis encryption, state proof and verification took 6,446.04 ms. Adaptation wall times include the crossing and proof verification within the API call. The separately timed ciphertext audit and fixture-side input sharing are outside that interval. RSS is the process high-water mark sampled at each operation's return.

```sh
research/wave11_frontier_upgrades_2026_11_22/formal_dark_gdn/build_and_verify.sh --rebuild-lean
```

[EXECUTED] Every weight matched the sequential field oracle after the two writes, after orthogonal subtraction, and after overlapping-key replay following the earlier deletion. The fixture used `t = 2305843009212399617`, two steps in episode zero and one in each of the next two episodes. The last replay includes the earlier tombstone. Each verifier time below is for the public state bundle alone. [Full-size assertions](../native/darkvfhe/tests/dark_b61_gdn_resident.rs#L651)

| Operation | Total ms | Rescale cert verification ms | State proof generation ms | State proof bytes | State proof verification ms | Process peak MiB |
|---|---:|---:|---:|---:|---:|---:|
| Fresh adaptation, two steps | 74,589.87 | 583.39 | 6,267.03 | 479,550 | 70.78 | 6,263.4 |
| Adaptation with refresh, one step | 66,504.11 | 438.70 | 6,769.85 | 478,128 | 72.84 | 6,263.4 |
| Orthogonal subtraction | 8,138.89 | 207.02 | 6,786.78 | 476,803 | 73.53 | 6,263.4 |
| Overlapping-key WY replay | 123,490.86 | 814.04 | 6,206.92 | 480,336 | 71.40 | 6,409.8 |

[EXECUTED] The first update also emitted a **437,866-byte** standalone hoisted compute proof for head zero. The full-state opening verified at a **130.08-bit WHIR** profile. The conditional four-challenge lookup identity estimate was **148.57 bits**. The in-process verifier checks the intermediate certificates separately. The benchmark reports the byte length of each serialized public opening.

<details><summary>[EXECUTED] Captured benchmark output</summary>

```text
Geometry: Qwen3.5-0.8B 16x128x128 = 262,144 fast weights in 32 B61 N=8192 ciphertexts (t = 2305843009212399617)
Setup 3-Custodian Hybrid-PQ + SPDZ + RLK: 485.65 ms | Genesis 32-Ct Encrypt+WHIR: 6446.04 ms (478714 B)
Adapt Ep0 (tau=2 WY, fresh): total=74589.87 ms [read_prove=318.37 ms, spdz+cross=64328.29 ms, adapt_prove=514.52 ms, cert_vfy=583.39 ms, whir_prove=6267.03 ms, whir_vfy=70.78 ms] | state_whir=479550 B | hoisted_whir_head0=437866 B | soundness=(130.08b WHIR, 148.57b LogUp) | peak_rss=6263.4 MiB
Adapt Ep1 (tau=1 + depth-1 refresh): total=66504.11 ms [read_prove=167.53 ms, spdz+cross=29894.17 ms, adapt_prove=464.13 ms, cert_vfy=438.70 ms, whir_prove=6769.85 ms, whir_vfy=72.84 ms] | state_whir=478128 B | peak_rss=6263.4 MiB
W0 Unlearn Mode A (Orthogonal Fast Subtract, 262,144 weights): total=8138.89 ms [exec+prove=1071.51 ms, cert_vfy=207.02 ms, whir_prove=6786.78 ms, whir_vfy=73.53 ms] | proof=476803 B | peak_rss=6263.4 MiB
W0 Unlearn Mode B (Compressed WY Operator Replay, 262,144 weights): total=123490.86 ms [exec+prove=116398.40 ms, cert_vfy=814.04 ms, whir_prove=6206.92 ms, whir_vfy=71.40 ms] | proof=480336 B | peak_rss=6409.8 MiB
```

</details>

[EXECUTED] The final command rebuilt Lean in **11.14 s** with zero warnings. One Rust unit test and all five integration tests passed in release mode. The integration binary took **542.25 s**. Its rejection cases covered a corrupted input MAC, altered signed bytes, stale and over-budget epochs, a unilateral signer, a stale parent, malformed opening geometry, ciphertext/handle substitution, modified sumcheck and lookup data, and trailing proof bytes. The base-field GMask rank checks passed at 39 and 81 for six and thirteen rounds respectively. [Tests and falsifiers](../native/darkvfhe/tests/dark_b61_gdn_resident.rs#L134)

[EXECUTED] **End-to-end exit 1.** The final zero-warning gate counted 12 diagnostics in the unowned `darkproof` crate. Both owned Rust files have `#![deny(warnings)]` and compiled cleanly. The driver keeps dependency diagnostics visible, executes the full suite and fails on the warning count. The diagnostic locations under `native/darkproof/src/` were `handover.rs:191,825`, `middle.rs:444,912,945`, `wire.rs:231,273,280`, `ligero.rs:176`, `run.rs:514,546` and `step.rs:603`. [Verifier script](../research/wave11_frontier_upgrades_2026_11_22/formal_dark_gdn/build_and_verify.sh)

```text
OK: Lean 4.35.0 kernel-verified 1 target module(s) with 0 warnings in 11.14s
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 5 filtered out; finished in 0.00s
test result: ok. 5 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 542.25s

PASS: Lane 5 Lean, release unit test and resident integration suite.
FAIL: zero-warning gate: darkproof=12
```

[SOURCE] Lasagne §7.3, Tables 2 and 3, projects single-core proving for a 16-layer, 2²⁰-gate payload. SizeOpt reports **6.11–12.47 min at 30.00 MB** and TimeOpt **5.17–11.53 min at 45.00 MB**. The abstract's **4–5 min** is for a SIMD payload. The resident measures a multi-threaded, in-process update or deletion and emits a public state opening. The workloads, proof statements and accounting boundaries differ. [Lasagne, ePrint 2026/857, abstract and pp. 31–32](/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026/857.pdf)

[EXECUTED] Kagi: 0, Scry: 0, eprint downloads: 0. The comparison uses the local mirror with `pdftotext -layout`.

[EXECUTED] After retaining the benchmark output above, removed the 759 MiB lane Cargo target created for this run.
