# Compact Boolean cSHAKE openings and private trie answers

[DERIVED] A 64-byte resident opening fits in **78,544 bytes for every challenge**, including the salt, masked-wire root, final challenge digest and every GGM and Merkle opening. The budget covers the serialized ZK proof. The authenticated request also has a public path, sibling digests, root, ranges and answer. The private-store protocol has a different public statement and its own measurements below. [Wire-budget test](../native/resident_custody/src/cshake_selective_open_v2.rs)

## Release measurements

[EXECUTED] Three fresh proofs per backend, on a 64-byte cell, a 32-byte blind and two four-byte projections. Proving includes OS randomness, witness preflight, commitment generation and serialization. Verification starts with the proof bytes. The medians are per column. The compact backend used four Rayon workers on an Apple M2 Max, macOS 27.2.1, rustc 1.98.0-nightly (91fe22da8). [Samples and medians](../research/w13_compact_opening/bench.log)

| Backend | Median bytes | Median prove | Median verify | Worst split, one challenge [DERIVED] |
|---|---:|---:|---:|---:|
| 219-round ZKBoo | 1,087,552 | 10.281 ms | 6.396 ms | 128.1068 bits |
| Batched KKW, 1,024 parties | 77,744 | 14,906.409 ms | 6,049.948 ms | 128.222324 bits |

[DERIVED] The ratio of median proof sizes is 13.99×. The prover processes 4,096 instances of 1,024 parties in each of two passes. The verifier regenerates the preprocessing of 4,082 instances and checks 1,023 opened parties in each of the other 14. Wave 12 already compressed its seeds. At its median, the neighbor’s gate transcripts alone occupied 1,051,200 of 1,087,552 bytes. [Wave 12 measurements and decomposition](w12-resident-custody-and-cshake-opening.md)

## The circuit and the wire budget

[REFUTED: suggested direct χ transcript] A Keccak-f[1600] permutation uses 24 rounds of 25 nonlinear 64-bit words. A direct χ transcript is 38,400 bits or 4,800 bytes. In KKW’s Boolean protocol the hidden online broadcast and the last party’s preprocessing correction normally each cost one bit per AND. The correction is omitted if that last party is hidden. Even one direct transcript for each of 27 executions costs 129,600 bytes. KKW §2.2 describes both costs, and §2.4 Fig. 2 commits the online emulations before the joint challenge. [KKW construction, local 2018/475, pp. 7–12](https://eprint.iacr.org/2018/475)

[DERIVED] The implemented variant commits an **extended witness**. It contains the original 96 bytes and 23 rounds of χ results (4,600 bytes). Given these results, every intermediate χ operand is affine in the extended witness. The last round needs four χ equations for the 32-byte public root. Their outputs follow from that root, the four linear wires and iota. The checked equation for each Boolean multiplication is $xy+z=0$. The projection adds one linear equation per selected bit. Native cSHAKE uses the Wave 12 customization and SP 800-185 padding. Widths 1 through 103 fit one secret rate block. [Circuit](../native/resident_custody/src/cshake_selective_open_v2/circuit.rs)

[DERIVED] Each instance has its own random tape shares for every extended-witness bit and an independent 256-bit pad per party. The first Merkle root binds the seed commitments and the salted masked extended witness of every instance. The public statement, caller context, salt and first root determine two independent 128-bit POLYVAL keys. Write $H$ for the concatenated linear fingerprints. For masked operands $a=x+u, b=y+v, c=z+w$, the prover publishes the aggregate Beaver correction $H(uv)+\bigoplus_i s_i$ when opening that instance. Party $i$'s online message is $s_i+H(a v_i+b u_i+w_i)$, including the appropriate linear projection masks. The XOR of these messages and the correction must equal the fingerprint of the public residual $ab+c$ and the public projection residual. The verifier computes every opened party's message and obtains the remaining one from this equality. The ordered **whole message vector** is committed before selecting the hidden party. [Preprocessing, commitments and verifier](../native/resident_custody/src/cshake_selective_open_v2.rs) · [POLYVAL field and recurrence, RFC 8452 §3](https://www.rfc-editor.org/rfc/rfc8452#section-3)

[DERIVED] The final SHAKE256 challenge binds the first root, the ordered preprocessing commitments and the second Merkle root over online message vectors. Rejection sampling draws a uniform subset without replacement, then an independent uniform party in each selected instance. The salt is fresh 32-byte OS randomness. SHAKE128 expands the 16-byte GGM seeds under distinct tape and child labels, instance IDs and positions. Independent secret transcript nonces hide the masked witness and messages of offline-checked instances even when the verifier has their complete tapes. [Seed trees](../native/resident_custody/src/cshake_selective_open_v2/tree.rs)

[DERIVED] With $F$ maximal offline subtrees the wire cost is
$$
96 + 80 F + 14(160+32+32+4696+32).
$$
Each top subtree carries a 16-byte seed and two 32-byte Merkle hashes. Each online instance carries ten party-tree siblings, one hidden seed commitment, one independent nonce, the masked extended witness and one aggregate correction. For 14 punctures in a depth-12 tree, $F\le 1-14+\sum_{i=0}^{11}\min(2^i,14)=114$. An explicit puncture pattern attains the bound. A full-depth public branch can separately carry $516\times32=16,512$ sibling bytes. [Wire-budget and branch-vector tests](../native/resident_custody/src/cshake_selective_open_v2.rs) · [Public branch](../native/resident_custody/src/trie_opening.rs)

## Soundness and privacy

[REFUTED: supplied cheating-split exponent] With $k$ bad preprocessing instances the proposed expression gives probability one at $k=0$. KKW Eq. (1), reindexed by *bad* instances, gives
$$
p_k=\frac{\binom{\tau}{k}}{\binom{M}{k}}N^{-(\tau-k)}.
$$
All bad instances must land in the online subset. Each of its remaining honest-preprocessing instances must hide the one inconsistent party. With two distinct acceptable hidden-party responses for the same bound message vector and correct preprocessing, every party’s message is checked by at least one response. Their sum then enforces the aggregate equation. More than $\tau$ bad instances give probability zero. [KKW Eq. (1), Thm. 2.2](https://eprint.iacr.org/2018/475)

[EXECUTED] The Rust test computes every split with exact arbitrary-precision integers, selects the maximum by cross multiplication, and checks the 128-bit threshold before taking any logarithms. It also counts every challenge in a toy cut-and-choose game independently. Only the production tuple is available to the prover and verifier. [Exact outputs](../research/w13_compact_opening/acceptance.log)

| $N,M,\tau$ | Worst $k$ | $-\log_2\max_k p_k$ |
|---|---:|---:|
| 1024, 4096, 14 | 11 | 128.222323926 |
| 64, 343, 27 | 22 | 128.062901915 |
| 16, 242, 36 | 23 | 127.018103662 |
| 32, 285, 30 | 22 | 125.796230946 |

[DERIVED] The first challenge matters separately. Condition on binding commitments, with each first-root leaf fixing its masked wires and seed vector. A false extended trace determines a nonzero residual before the batch keys are drawn. For up to $L=296$ fixed-length 16-byte blocks, one POLYVAL evaluation gives a nonzero polynomial of degree at most $L$ in a uniform field element (the fixed field scaling is invertible). Two independent keys give at most $(L/2^{128})^2$. A union over $M$ traces covers all batch failures for that root. The exact integer test checks $M(L/2^{128})^2+\max_k p_k < 2^{-128}$. In a classical random-oracle accounting, $Q_1$ candidate batch queries and $Q_2$ final challenge trials contribute at most $Q_1 M(L/2^{128})^2+Q_2\max_k p_k$, conditional on binding/fixed first messages. Guessing hidden seeds, equivocation or collisions in commitments and the security of the primitives are additional terms. [Exact test](../native/resident_custody/src/cshake_selective_open_v2.rs)

[DERIVED] For an honest online opening in the ideal-tape model, an unrevealed input mask makes the entire masked trace uniform given the opened tapes. The unrevealed independent pad masks the aggregate correction. The hidden message is fixed by the public residual and the other messages. Offline-check openings contain seeds and commitments blinded by a nonce independent of those seeds. The real construction relies on punctured PRG expansion, hiding/binding commitments and the random oracle for the two challenge stages. [Protocol source](../native/resident_custody/src/cshake_selective_open_v2.rs)

[OPEN] This batched variant has a derived classical per-query ledger. A full reduction for adaptive hash queries, extraction, and simulation of the concrete seed-compressed implementation remains open. KKW’s theorem covers its own protocol. No QROM security level was measured or proved here.

## Authenticated answers

[EXECUTED] The resident verifier takes the trusted world root, key path, cell width and authorized ranges. It hashes a tagged leaf carrying the entire canonical 516-bit path and the blinded cell root, then climbs the supplied siblings in the order fixed by that path. The compact proof binds the digest of that complete public context and the entire byte statement. A branch transplanted to another valid root fails. An independent Go computation and a pinned Rust test agree at depth 516. [Verifier](../native/resident_custody/src/trie_opening.rs) · [Independent vectors](../research/w13_compact_opening/vectors.log)

[SOURCE] Minidregg revision `453aba5358786a97a48ec48802e81538947df9e5`, `Kernel/PrivateCellOpening.lean:148` defines `OpeningRel` on a typed store view with private mask, inner digest and one private reveal per reader prefix. `Answers` (line 133) is an iff over the union of the answers. `Shaped` (line 140) bounds early stops to one member. `framed_outerBytes` (line 231) fixes the custody frame. `openingRel_exact` (line 306) assumes a selected canonical codec and a gated store, and allows the named deployed collisions. `honest_rel` (line 362) gives completeness under its stated premises. `Theory/AuthTrieRange.lean:326`, `revealVerify`, recomputes the canonical subtree and climbs verified siblings. These definitions and theorem statements were read directly in the companion tree.

[DERIVED] The private Rust backend specializes that relation to framed custody at the canonical wire-image boundary. The application supplies its trusted layout, the root as 32 little-endian digest bytes, cell ID, version, field scope, and its typed view’s canonical address/value encodings and classifications. It must derive these from the selected codec and `fieldOf`. The verifier derives all paths, content digests, reader prefixes and expected members itself. It rejects duplicate addresses, colliding view paths and out-of-scope entries. For each prefix the following circuit constructs the root of an admissible reveal. [Public plan and wire adapter](../native/resident_custody/src/trie_opening/deployed.rs) · [Private circuit](../native/resident_custody/src/trie_opening/deployed/mpc.rs)

| Public answer at prefix | Witness and check [DERIVED] |
|---|---|
| Two or more members | Rebuild their exact subtree at prefix depth. Climb every sibling. An early stop would violate shape. |
| One member | Start at its public leaf digest. A private monotone run of bits selects the walked depth. Its full path already matches the prefix. |
| Empty | Select empty or a private singleton leaf. A singleton must match every walked bit and differ somewhere in the full requested prefix. Private depth and sibling slots are padded to the public prefix length. |

[DERIVED] Each climb equals **the same private inner digest**. The circuit hashes that digest and the private custody secret with the public frame into the statement root. Every view member must occur under a requested prefix. Reconstructing each subtree from precisely its public answer enforces the reverse inclusion, including overlaps. An early singleton outside an empty answer contributes no view pair. This gives a witness for the framed relation from satisfying circuit wires. All hash calls and Boolean constraints touching those wires run inside the existing 219-round backend. Proof length depends on public shape and the random challenge frontier. The specialized byte interface supports little-endian 256-bit field parameters and u64 versions. [Circuit and proof entry points](../native/resident_custody/src/trie_opening/deployed.rs)

[EXECUTED] The private verifier accepted two visible body entries with a third entry hidden, and an empty view with a private early singleton. It rejected a missing member and a selected leaf claimed as an outside terminal, both with honest-prover preflight bypassed. It also rejected version relabeling. Native circuit checks covered full scope, empty scope, a genuinely empty index, a singleton answer and overlapping body/atom prefixes. The Go fixture independently reproduces the inner and outer digests using cSHAKE and explicitly assembled nodes. These are synthetic canonical-wire inputs. [Private proof measurements](../research/w13_compact_opening/acceptance.log) · [Go computation](../research/w13_compact_opening/vectors.go)

[EXECUTED] A 260-bit code-field prefix with private stop depth produced a 278,548,972-byte proof, verified in 1.493 seconds. The public prefix length fixes the padded number of hash calls. Large circuits replay seeded views after the challenge to bound temporary prover memory. [Full-width field measurement](../research/w13_compact_opening/full-field.log)

[OPEN] The typed Minidregg receiver still needs its production adapter to supply the canonical public wire image. A machine-checked refinement from this Rust evaluator to the Lean predicate and the receiver’s ROM extraction/hiding obligations remain open. The executable relation and the wire-vector tests establish the research prototype’s scope.

## Falsifiers and reproduction

[EXECUTED] The resident test verified an honest opening and rejected changes to the party GGM path, hidden commitment, masked χ bit, transcript nonce, aggregate preprocessing correction, offline master seed, Merkle sibling, byte policy, authenticated context, public answer and proof length. It separately rejected a changed hidden byte with preflight bypassed, then the same invalid witness with eleven deliberately incorrect preprocessing products committed **before** the final challenge. In that last run the bad products cancel the false residual for their online checks. Each remaining instance commits one inconsistent party message to give it exactly one acceptable hidden party. The verifier rejected that mixed strategy. The private blind and a 32-byte hidden canary were also absent as whole substrings in the tested honest proof. [Test implementation](../native/resident_custody/src/cshake_selective_open_v2.rs) · [Release acceptance](../research/w13_compact_opening/acceptance.log)

[EXECUTED] From `native/`, the commands below exercise the verifier and reproduce the measurements. From the repository root, `go run research/w13_compact_opening/vectors.go` reproduces the independent vectors with Go 1.24 or later. [Benchmark output](../research/w13_compact_opening/bench.log) · [Acceptance output](../research/w13_compact_opening/acceptance.log)

```sh
export CARGO_TARGET_DIR=target/w13 RAYON_NUM_THREADS=4 RUSTFLAGS="-D warnings"
cargo test --release -p resident_custody
cargo test --release -p resident_custody release_comparison -- --ignored --nocapture --test-threads=1
cargo test --release -p resident_custody full_field_prefix_proof -- --ignored --nocapture --test-threads=1
```
