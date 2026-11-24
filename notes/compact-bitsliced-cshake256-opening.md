# Bit-sliced cSHAKE256 selective cell openings

> [DERIVED] The shared bit-plane evaluator now handles framed cells and private trie openings. [Current implementation and measurements](compact-private-trie-and-tulip-crash-continuity.md)

[EXECUTED] A 64-byte resident cell with two four-byte disclosures and a three-sibling world-trie branch proved in **67.229 ms** and verified in **14.367 ms** on an Apple M2 Max with four Rayon workers. Nine fresh proofs had a median length of **89,600 bytes**. The prover and verifier both authenticated the supplied branch inside the timed call. [Release gate](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open.rs)

| Release measurement | Workers | Median proof bytes | Median prove, ms | Median verify, ms |
|---|---:|---:|---:|---:|
| Earlier three-view proof [SOURCE] | 4 | 1,087,552 | 10.281 | 6.396 |
| Earlier compact proof [SOURCE] | 4 | 77,744 | 14,906.409 | 6,049.948 |
| Paired-round proof [EXECUTED] | 4 | 89,600 | 67.229 | 14.367 |
| Paired-round proof [EXECUTED] | 12 | 89,680 | 35.255 | 8.062 |

[DERIVED] At four workers, proving is **221.7× faster** and verification is **421.1× faster** than the earlier compact benchmark. The new median proof is 15.25% larger than that compact proof and 12.14× smaller than the three-view proof. The earlier measurements used the same cell width and disclosure lengths, three samples per backend and empty application context. The current measurement includes world-root verification. [Historical measurements](../research/w13_compact_opening/bench.log)

## How two rounds fit in one checkpoint

[DERIVED] For the first 22 rounds, the witness stores the 1,600-bit state after each pair of rounds. For each five-bit row of the second round’s χ output, write its bits as $a,b,c,d,e$, before iota. The witness also supplies two bits $p=ac$ and $q=ad+be$, with addition over GF(2). Every coordinate of inverse χ is quadratic in these seven bits. For example, its first coordinate is $a+c+e+bc+ad+be+de+qd$. Substituting the hints cancels the two copies of $ad$ and gives the inverse’s cubic term $bde$. The circuit checks both hint equations. The exhaustive row test tries all 32 inputs and all four hint pairs. [Inverse equations and exhaustive test](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open/circuit.rs)

[DERIVED] Each pair checks that inverse χ of the supplied endpoint agrees with the preceding forward χ, iota and linear Keccak layers. Thus a satisfying pair fixes the endpoint from its incoming state. Round 22 (zero-based) uses one further state and round 23 checks the four digest lanes. The blind, cell, cSHAKE prefix, padding, digest and projected bytes enter the same constraint system. The private trace occupies $11(25+10)8+25\cdot8=3,280$ bytes. The 32-byte blind and 64-byte cell bring the masked witness to **3,376 bytes**. [Circuit and native trace test](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open/circuit.rs)

## What runs across parties

[DERIVED] The prover commits masked witnesses and seed vectors before deriving the two POLYVAL keys. A purpose-separated, salted SHAKE128 call on the instance, position and leaf seed produces separate commitment, pad and AES key segments. AES-128 in counter mode expands that private key into the tape. GGM child expansion uses a distinct purpose byte. Rayon distributes the 640 instances. The verifier regenerates 617 complete preprocessing instances and opens 63 parties in each of 23 online instances. [Transcript and prover](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open.rs) · [Seed trees](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open/tree.rs)

[DERIVED] A six-stage butterfly transposes 64 tape words so a single `u64` holds one Keccak bit for all 64 parties. A state contains 25 lanes of 64 such words. Theta XORs column parities, rho rotates plane indices and pi permutes lanes. The online pass evaluates the linear part of the quadratic Beaver check. At public masked operands $a,b$, the party term for operand shares $x_i,y_i$ is $a y_i+b x_i$. Each public bit expands to a word mask. Iota, padding and other public constants enter the clear residual. The aggregate mask supplies the homogeneous quadratic correction. After the inverse transpose, each party’s check bytes and projected mask bytes receive two POLYVAL fingerprints and a secret pad. A differential test compares every party message to scalar polarization, including partial input lanes. [Bit planes](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open/circuit/planes.rs) · [Clear, quadratic and scalar-reference evaluations](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open/circuit.rs)

## Exact one-trial soundness

[SOURCE] Katz, Kolesnikov and Wang, §2.3, Eq. (1), count correct preprocessing instances. Reindexing by the number $k$ of incorrect instances gives the following expression. All $k$ must land in the online subset, and each of the remaining $\tau-k$ online checks must hide its inconsistent party. The supplied $N^{-k}$ exponent gives probability one at $k=0$. [KKW, construction and Eq. (1), local mirror 2018/475](https://eprint.iacr.org/2018/475)

$$
p_k=\frac{\binom{\tau}{k}}{\binom{M}{k}}N^{-(\tau-k)}.
$$

[EXECUTED] With $(N,M,\tau)=(64,640,23)$, exact integer cross multiplication over all 24 splits finds the maximum at $k=14$. The reduced probability is $23/9748679111155310898117152759361193377792$, or **128.316840500 bits** rounded for display. The suggested $(128,352,24)$ and $(128,384,24)$ give 121.103 and 123.947 bits respectively. The Rust test also enumerates every challenge in a smaller game. [Exact arithmetic and checks](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open.rs)

[DERIVED] There are 414 checked 64-bit words plus at most 103 projected bytes, hence at most 214 POLYVAL blocks. Once the masked traces and seed commitments are fixed, two independent field challenges give a batch error bound of $640(214/2^{128})^2$. The unit test adds this bound to the exact maximum and checks the sum against $2^{-128}$ using integers. This is the classical one-trial challenge bound conditional on binding commitments and the ideal challenges. A concrete adaptive Fiat–Shamir or QROM reduction remains open. [Batch ledger](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open.rs)

## Proof bytes and public branch bytes

[DERIVED] A proof has a 96-byte header. Each of 23 online openings contains six 16-byte sibling seeds, a 32-byte hidden commitment, a 32-byte nonce, the 3,376-byte masked witness and a 32-byte Beaver correction. Each subtree on the outer frontier supplies an additional 80 bytes. The 640 active leaves occupy perfect subtrees with 512 and 128 leaves. Enumerating all splits of the 23 hidden leaves between them gives a maximum frontier of 109. The unit test constructs an attaining pattern using bit reversal. The proof bound is **90,880 bytes** for every challenge. [Wire-budget test](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open.rs)

[DERIVED] The benchmark branch adds a 65-byte path and 96 sibling bytes, giving **91,041 bytes** at the proof maximum. The caller supplies the trusted world root and release policy separately. Proof size is independent of branch depth. If separately transporting a full 516-sibling branch, its raw path and digests add 16,577 bytes, for a maximum of **107,457 bytes** including the proof. [Branch verifier](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/trie_opening.rs)

[EXECUTED] The authenticated verifier rejected 15 adversarial cases covering GGM openings, seed commitments, masked round state, inverse χ hints, online broadcast commitments, nonce, preprocessing corrections, offline seeds, a trie sibling, range policy, context transplant, changed answer, truncation and two preflight-bypassed hidden-byte changes. The mixed strategy corrupted 14 preprocessing instances before the final challenge. The suite also exercised the custody release path, multi-block padding boundaries and deployed framed openings. [Adversarial proof tests](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/cshake_selective_open.rs) · [Integration tests](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/tests/resident_house_move_and_cshake_open.rs)

[SOURCE] Resident single-block proofs now use the canonical selective opening module. Proof bytes and local transcript domains changed, so an earlier proof needs regeneration. The two persisted private-store cSHAKE customization strings carry the protocol suffix `/v2` fixed by Minidregg’s `Compiler/PrivateCellRoot.lean:110–111`. Clear and MPC readers share these constants to preserve existing trie and framed-cell roots. [Domain constants and pinned trie vector](https://github.com/emberian/zkml-research/blob/691c42f61a27c92a48ce38fec2630d1b96384b91/native/resident_custody/src/trie_opening.rs)

## Reproduction

[EXECUTED] From `native/`, on macOS 27.2.1 with rustc 1.98.0-nightly (91fe22da8), the following commands exercise the crate and the measured gate. The gate times nine fresh proofs per run and asserts each proof plus the benchmark branch fits 92,000 bytes and that the two latency medians pass.

```sh
export RUSTFLAGS="-D warnings"
cargo test --release -p resident_custody
cargo test --release -p resident_custody exact_cheating_splits -- --nocapture
cargo test --release -p resident_custody authenticated_projection_and_adversarial_openings -- --nocapture
RAYON_NUM_THREADS=4 cargo test --release -p resident_custody authenticated_release_gate -- --ignored --nocapture --test-threads=1
RAYON_NUM_THREADS=12 cargo test --release -p resident_custody authenticated_release_gate -- --ignored --nocapture --test-threads=1
```

[EXECUTED] Release output, in sample order. Times are milliseconds.

| Sample | Bytes, 4 workers | Prove | Verify | Bytes, 12 workers | Prove | Verify |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 89,680 | 67.803 | 14.311 | 89,520 | 34.148 | 8.565 |
| 2 | 89,280 | 67.829 | 14.505 | 89,680 | 33.499 | 7.782 |
| 3 | 89,200 | 68.933 | 14.367 | 89,840 | 35.255 | 8.022 |
| 4 | 89,600 | 67.229 | 14.439 | 89,680 | 35.612 | 7.925 |
| 5 | 89,920 | 66.950 | 14.177 | 90,160 | 34.433 | 7.992 |
| 6 | 89,760 | 66.768 | 14.294 | 90,000 | 34.673 | 8.360 |
| 7 | 89,680 | 67.327 | 14.343 | 89,520 | 36.847 | 8.062 |
| 8 | 88,800 | 66.780 | 14.554 | 89,520 | 39.003 | 8.876 |
| 9 | 89,280 | 67.100 | 14.417 | 89,840 | 39.403 | 13.357 |
