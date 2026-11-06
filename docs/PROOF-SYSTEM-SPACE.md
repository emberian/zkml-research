# PROOF-SYSTEM-SPACE: the construction space, where everyone sits, and the empty squares

2026-11-05. Tags: [READ] seen at source; [MEASURED] I ran it; [X] measured by others (cited);
[CLAIM] asserted, unchecked; [INFERRED] derived here. Runnable companion:
`notes/construction-search/space.py` (stdlib; `--calibrate`, `--sensitivity`,
`--point <name>`). Companions: `docs/CERTIFICATES.md`,
`notes/selvage-foundations-critique-2026-11-05.md`, `notes/proof-system-codex-synthesis.md`.

The previous root proposal was called myopic. This map is wide on purpose. I was also told
not to soften findings, so the first section says which of our own beliefs died today.

---

## 0. What the frontier did since August, and what that kills

1. **The "Microsoft Spartan successor" is public, and it has a successor.** BinarySpartan, ePrint
   **2026/1656** (Setty, received 08-11, rev 4 on 09-03): Spartan over GF(2^128), Ligerito,
   Diamond-Posen ring switching, Phalanx SIMD R1CS, Gruen univariate skip. It is **UD-only, no
   PoW, ≤ 2^-102.6**, with 872k BLAKE3/s, 401k SHA-256/s and 287k Keccak-f/s on 12 M4 Max P-cores
   [READ §4]. Then **Magnetar**, ePrint **2026/2423** (10-09): an RV64I zkVM on BinarySpartan +
   **BinaryTwist/BinaryShout** + BinaryRouter. It runs **120 provable bits, UD only, "avoids
   conjectured RS proximity gaps"**, with no Poseidon, at 7.2-12.8M cycles/s, ~600 KiB proofs and
   8-13 ms verify. It claims 24-66× SP1 Hypercube, 12-37× Jolt-Dory and 6-20× Jolt-Akita
   [READ abstract, §6.1]. `notes/binaryspartan-position.md` §0.5 ("could not verify that
   BinarySpartan exists") is **retired**.
2. **Provable-UD-only is now the frontier's reporting standard.** Our deployed IR-v2 reads **UDR
   34** (VERDICTS §2). That is the largest gap between us and the field, and it is a policy choice,
   not physics (§6, critique W1).
3. **FlashProve (Anthropic, 11-02)** is a hash-based commit-and-prove system over Goldilocks with a
   cubic extension, BLAKE2b, ZK Reed-Solomon (rate 0.104), list decoding inside Johnson via BCHKS25
   Thm 4.6 (**proved in Lean**), and LogUp/GKR lookups. Every request is fully proved; the only
   amortization is one 64-column weight-table opening per batch. 18.78 MB proofs, 110 tok/s
   prefill at batch 24 on one H100, Llama-4-Maverick 400B on a 4-bit public conversion
   (re-quantized to |w| ≤ 4095 and base-256 digits: **not native MXFP4/Q4**) [READ, helper digest].
   It has an end-to-end Lean theorem with error `q/2^124 + 2^-101` about a Lean verifier. **It
   exposes no token commitment** (CERTIFICATES §3c).
4. **SASH (Sep)**: Stwo, M31, Blake2s, LogUp and Freivalds. 79.0M committed cells per position
   for Llama-3.1-8B. **The proof system is ~5% of GPU time**: lookup-column generation is 42% and
   base trace 35% [X]. **This kills "the prover is the bottleneck" at frontier scale.** Witness
   generation is, and no tensor core touches it.
5. **TensorZKP (2026/1250)**: BabyBear (`p = 2^31−2^27+1`), challenge field `x^8−11`, 8-bit
   limbs on H100 INT8 tensor cores, HyperPlonk + Brakedown. 2^25 gates in 215 ms; 13.1× (inner
   product) and 36.2× (end to end) over SIMT [READ §7]. **This partially refutes our own VERDICTS
   §4b**, which said BAT "is not free for an MLE fold or a sumcheck round (two runtime witness
   tensors)". The fold `f' = (1−r)f_e + r f_o` has a **known scalar** `r` once it is sampled, so
   BAT applies per round with a fresh 4×4 table. Only the round-polynomial inner products are
   runtime × runtime, and TensorZKP does those as limb GEMMs with deferred reduction. Our §4b's
   **1.26× Amdahl ceiling** was computed for *our AIR prover*, where GEMM-shaped work is 20.8%.
   It does not transfer to a sumcheck-native prover. That ceiling is a statement about our
   architecture, not about tensor cores.
6. **ArkLib** went from 292 to 4 live sorries in two months. It now proves FRI, RS MCA up to
   Johnson, and Binary BaseFold with ring switching. It still has no BCS/FS bridge
   (critique §0.2-0.3).
7. **Also in the space:** holography accumulation (2026/538: stateless PCD for lincheck/
   checkable-subspace SNARKs, with the holographic checks accumulated across steps); Chimera
   (2026/1388: BN254 hybrid GPU sumcheck for Spartan, 7.99× round speedup, **1.27-1.64× end to
   end**, which is the Amdahl lesson again); zkDuel (arXiv 2610.37710: Triton vs CUDA sumcheck
   across 32-256-bit fields); the separation principle for lookup zkML (2026/1390: one-hot/Shout
   per-lookup cost depends only on the access pattern, never on table values); NanoZK
   (arXiv 2603.18046, layerwise sumcheck for LLMs); and Reef (2023/1886: ZK regex **match or
   non-match** over a committed document, which is prior art for absence). The zkVM SoK
   (2026/525) gives a three-layer decomposition (ISA / trace layout / backend), which our
   "statement shape" axis subsumes. Contract-validated benchmarking (2026/1729) compares provers
   only on a hashed, declared public claim. That is CERTIFICATES' law L0 applied to benchmarks,
   and it is the right format for publishing any number in §3.

---

## 1. The axes

| axis | values in the enumerator | notes |
|---|---|---|
| field | BabyBear, KoalaBear, M31, Goldilocks, p61, GF(2^128) tower, lattice ring R_q | limbs per tensor-core mult: 4 (31-bit) or 8 (64-bit); char 2 has no integer MAC |
| PCS | FRI, WHIR, BaseFold-additive, Ligerito, Brakedown, Ajtai (lattice) | the PCS is ~99.8% of in-circuit verifier cost (LEAF-VS-RECURSION) |
| PIOP | AIR, Spartan/CCS, HyperPlonk, GKR | |
| lookup | LogUp, Lasso, Shout (one-hot) | LogUp needs `1/(X−a)` helper columns, i.e. witness generation |
| recursion | none, full, atomic accumulation, holography accumulation, folding | |
| hardware | CPU-SIMD, GPU SIMT, GPU tensor core (INT8 MMA); FPGA/HPU named, unpriced | |
| statement shape | VM, interior AIR, semantic AIR (SASH-measured), boundary-only | 10-1000× between rows; the dominant axis |
| amortization | per-request, commit-then-audit at p = 1%, 0.1% | audit changes the *guarantee*, not only the cost |
| regime (soundness) | UD, Johnson (proved in ArkLib/FlashProve, hypothesis in Selvage), capacity (withdrawn) | |

`space.py` enumerates **76,248 compatible points** [MEASURED] and prints four Pareto fronts.
Compatibility rules are explicit in `compatible()`; for example, LogUp is excluded in char 2.

---

## 2. Where the systems sit

| system | field | PCS | PIOP | lookup | recursion | hw | shape | amort | soundness as reported | formal |
|---|---|---|---|---|---|---|---|---|---|---|
| **Selvage (ours)** | abstract `dom : ι ↪ F` (BabyBear deployed via breadstuffs) | FRI, additive FRI, BaseFold (Lean) | AIR (deployed) + sumcheck (Lean, Rust mirror) | LogUp*, LogUp | proved compiler; deployed plonky3 recursion | CPU | interior AIR, semantic turns | audit theorem (L1, uninstantiated) | **UD 34 / JB 73** deployed | compiler proved; 0/153 deployed |
| **FlashProve** | Goldilocks + cubic | ZK-RS code-switching (CFW 2026/391), rate 0.104 | sumcheck/linear claims, 25 segments | LogUp-GKR, Lasso virtual keys | none | H100 + 24 CPU | integer semantic model | shared weight opening per batch | `q/2^124 + 2^-101`, Johnson, ROM | end-to-end Lean, about a Lean verifier |
| **Stwo / SASH** | M31 circle | circle FRI, blowup 2, 100 q, Blake2s | AIR + 5 sumcheck reductions + Freivalds | LogUp | none | H100 | semantic AIR, 79.0M cells/pos | none | "100 under FRI conjecture" = **~50 JB / ~41.5 UD** [INFERRED] | none |
| **BinarySpartan / Magnetar** | GF(2^128) | Ligerito, UD | Spartan (SIMD R1CS) | BinaryShout/Twist | "efficient recursion" (hash-dominated verifier), not yet measured | 12-core CPU | VM (Magnetar), hash circuits | none | **100 / 120 provable UD** | none |
| **Jolt (2026)** | BN254 (Dory) / lattice (Akita) | Dory / Akita | Spartan | Twist & Shout | Akita recursion WIP | CPU/GPU | VM | none | curve/lattice | none (some Lean of sub-pieces [CLAIM]) |
| **Binius64** | GF(2^128) tower, 64-bit words | FRI-Binius / BaseFold | IronSpartan | — | — | CPU | VM-ish words | none | 96 bits | none |
| **ArkLib** | generic | FRI, Binary BaseFold, (STIR parts) | sumcheck, Spartan parts | — | — | — | library | — | proves FRI, MCA ≤ Johnson | library, 4 sorries |
| **TensorZKP** | BabyBear, x^8−11 | Brakedown | HyperPlonk | perm-check | none | H100 tensor | generic circuits | none | 248-bit challenge field | none |
| **ZK Email** | BN254 | Groth16 / UltraHonk | R1CS / Plonkish | NFA path | none | client CPU | regex path, DKIM | none | knowledge soundness (paper sketch) | none |

---

## 3. What the counts model says (and does not)

From `space.py` [MEASURED by running it; every input is tagged in the file]:

| point | committed cells/pos | field mults/pos | hashes/pos | crypto proxy | total proxy (incl. witgen) |
|---|---:|---:|---:|---:|---:|
| SASH anchor (M31, FRI ρ=½, AIR, LogUp, SIMT, semantic) | 7.90e7 | 3.60e9 | 1.48e7 | 2.1e-3 s | 4.28e-2 s |
| same shape on tensor cores (BabyBear) | 7.90e7 | 3.60e9 | 1.48e7 | 1.5e-3 s | 4.22e-2 s (**1.01×**) |
| **U1 per-request** (BabyBear, WHIR ¼, Spartan/CCS, Shout, tc, boundary-only, MXFP4) | 1.07e7 | 5.63e9 | 4.03e6 | 5.2e-4 s | 3.66e-3 s (**11.7×**) |
| U1 on SIMT instead of tc | 1.07e7 | 5.63e9 | 4.03e6 | 2.3e-3 s | 5.45e-3 s (tc buys **1.49×**) |
| U1 with felt-per-weight instead of MXFP4 | 1.07e7 | 6.20e9 | 4.03e6 | 7.3e-4 s | 3.87e-3 s (MXFP4 buys **1.06×**) |
| **U1 audited at 1%** | (always: hash-only commit of 6.1e6 boundary cells) | 5.63e7 | 4.21e5 | 3.2e-5 s | 6.34e-5 s (**675× SASH**) |
| ours, deployed config, if it proved inference as interior AIR | 3.11e10 | 2.25e13 | 3.11e11 | — | 7.2e3 s |

How to read the table:

- **The ordering of levers matches the FRONTIER-QUEUE Part 1 thesis, now in one unit.** Statement
  shape is ~7-12×. Amortization is ~58× on top (and changes the guarantee). Tensor cores are
  ~1.5× at system level. Native MXFP4 is ~1.06×. Tensor cores are worth 1.01× on SASH's shape,
  because witness generation is 95% of it. **A tensor-core-native field is worth having only
  after the statement shrinks the witness.**
- **Calibration** (`--calibrate`): the crypto proxy is **~29× optimistic** against SASH's measured
  1.3e9 cells/s. Witness generation is *calibrated* (one per-cell constant set so it is 95% of the
  anchor), not modelled. Only ratios on one hardware row mean anything.
- **Sensitivity** (`--sensitivity`): U1 audited moves **≤ 4%** under a 4× change of the
  tensor-core MAC cost, and **~linearly** with boundary committed cells. **The boundary census is
  the number that matters.** It is a derived shape, not an emitted object (inadequacy 3).
- Codex caught two model bugs before this table was printed: SASH lookup cells were counted twice
  (79.0M → 95.6M), and GKR dropped the linear-map sumcheck term (an 8.7× flattery). Both are
  fixed and recorded in the file.

---

## 4. Unoccupied design points

"Unoccupied" means I searched (Kagi, ePrint mirrors, the papers above) and found no system at that
point. It never means nobody has thought of it. **Nearest prior work is named for each.** Costs
are counts from `space.py` or derived in-line.

### U1. Tensor-core-native small prime + Lean-emitted CCS + commit-then-audit + native MXFP4 weights (the asked-for point, priced)

- **Point.** BabyBear (K=4 byte limbs; TensorZKP proves the limb mapping on H100). Round
  polynomials as limb GEMMs and folds as BAT with a known `r`. WHIR at ρ=¼ under Blake2s/Blake3
  (no recursion in audit mode; Poseidon2 only if a wrap is wanted, at 5.7× the crypto cost:
  `U1-poseidon2`). Spartan/CCS **emitted from Lean** (C9 generator: no hand-written constraint).
  Shout one-hot lookups for nonlinearities: no inverse helper columns, so less of the 42%
  lookup-witness phase. Weights committed **once, offline**, in MXFP4 (E2M1 + E8M0/32 =
  4.25 bits/weight, packed 7 per felt). A k=32 block dot is an exact ≤13-bit integer
  (`SELVAGE.md` §5.5, `docs/mx-formats.md`). Per request: a hash-only commitment to boundary
  activations. With probability p, a full proof whose matmul claims land on the weight MLE
  through the shared batch opening (FlashProve's trick), under `AuditSampling.sequential_bound`
  (`E[C] ≤ 1/q`).
- **Price** [MEASURED, model]: per position, always **4.2e5 hash compressions** (the boundary
  commit) and, at p=1%, **5.6e7 expected field mults**. Total proxy is 675× under SASH's shape and
  11.7× under it per-request. In absolute terms divide by the ~29× proxy optimism: about
  **1.8 ms/position audited, 0.1 s/position per-request, on one H100** [INFERRED; a shape, not a
  forecast].
- **Why unoccupied.** TensorZKP is generic circuits with no zkML, no audit, no formal content.
  FlashProve proves every request and re-quantizes away the native format. SASH is per-request.
  Nobody else has a proved audit theorem.
- **Strongest objection** (codex §B1): the audit gives an *expected-loss* guarantee. At p=1% a
  single fraudulent request escapes with probability 0.99. **U1 is governance infrastructure
  (deterrence, bounded expected leakage `b/q`), not per-request correctness**, and a receipt
  must say which it is. The *per-request* U1 is the honest comparator to FlashProve and SASH.
- **Unmeasured term that could kill it:** the MXFP4 unpack/lookup cost inside the proof. Packing
  7 E2M1 per felt makes every weight read an unpack. The model charges 0. First experiment:
  count it in the boundary census.

### U2. Hybrid prime/binary over one byte-level content commitment (inference in a prime field, certificates in GF(2^128))

- **Point.** Inference stays in a small prime (integer MACs). Certificates (DFA, CFG, substring,
  hashes of bytes) run in BinarySpartan/Magnetar-style GF(2^128), where byte and bit relations
  are native. A shared content scheme (CERTIFICATES L4/L5) joins them.
- **Cost driver.** The bridge: hashing the shared bytes in both systems. A 4 KiB window is 64
  BLAKE3 blocks, about **8.96e5 binary constraints** (14k per compression, 2026/1656 §4; codex
  §B2's arithmetic). Against FlashProve the bridge is TK(window): ~33 BLAKE2b compressions,
  0.5-1M constraints.
- **Why unoccupied.** Selvage's `HeteroComposition*` and `VerifierEmbedding` exist in Lean, but
  nobody runs a binary-field certificate prover against a prime-field inference prover.
  `VERDICTS.md` §4c's "binary case must be argued on cryptanalytic surface" is the reason nobody
  wanted binary for the whole thing.
- **Objection** (codex): for short certificates the bridge exceeds the certificate. **That
  pushes the design toward U3.**

### U3. The policy automaton fused into the inference relation's output boundary (codex's improvement on my "certificates as PCS openings")

- **Point.** If we own the inference prover, the output tokens are already a committed witness.
  A DFA/Shout lookup over those same cells certifies the policy, so there is **no second content
  commitment and no bridge**. Absence (CERTIFICATES L3, padded complement) becomes a sub-relation
  of `Produced`.
- **Price** [codex §B8, checked]: a 64-state byte DFA is a 16,384-entry table and 4,096 lookups
  per 4 KiB of output. That is **~4e3 lookup cells against 1.07e7 boundary cells per position**,
  i.e. free. The detokenizer relation (tokens → bytes) is the real cost and is unpriced.
- **My original U3 is partly refuted** (codex §B3): substring-at-position as a batched multilinear
  evaluation still pays an O(n) PCS opening over the whole document (128× the substring for
  32 B in 4 KiB). For a **public position**, Merkle openings (CERTIFICATES L6) are strictly
  cheaper. For a hidden position, use a fused automaton.
- **Why unoccupied.** ZK Email and Reef prove regex over a *separately* hashed document. No
  inference prover exposes its output witness to a policy relation.

### U4. Pay-per-bit lattice folding for autoregressive decode (priced, and it loses at 8B unless block-folded)

- **Point.** Decode is a uniform per-token step, the IVC shape. Neo/SuperNeo (2026/242) gives
  small-field CCS folding with pay-per-bit Ajtai commitments, a good fit for 4/8-bit values.
- **Price.** Nightstream's recursive step is **27,537,894 R1CS rows** [M: `notes/nightstream-
  read.md`, a Lean theorem on their 09-04 branch]. Per token that is 2.6× the 1.07e7-cell
  boundary witness it folds: **1,024 tokens ≈ 2.8e10 rows of recursion overhead** (codex §B4).
  Folding blocks of 128 tokens amortizes this to ~2.1e5 rows/token (codex §B7), which is
  competitive.
- **Why unoccupied.** Lattice folding implementations are research software, and KV growth breaks
  step uniformity; a max-context CCS with masking repairs it at a cost linear in the context.
- **Verdict.** Viable only as **block-folding of teacher-forced replay** (merge with U7).
  Per-token folding is refuted on counts **for sumcheck-based lattice folding**.
  ⚠ ProtogaLattice (ePrint 2026/1317, Balbás-Nitulescu-Plançon) attacks exactly this cost: an
  algebraic (non-sumcheck) folding backbone with fewer RO evaluations and "a smaller verifier
  circuit", 8.13 KB per iteration at 2^30 witnesses [READ abstract]. If its recursive verifier is
  ≲ 1e6 rows, per-token folding re-opens. **The deciding count is that verifier circuit size,
  which the abstract does not give.** Read §§ on the bootstrapping protocol before any U4 work.

### U5. GKR over transformer layers with a small-field hash PCS and tensor-core sumcheck, formally verified

- **Point.** Commit only inputs, weights and lookup data. Every activation is a virtual GKR gate.
- **Price** [MEASURED, model after codex's fix, same hash as U1]: committed cells/pos **4.66e6**
  (2.3× under U1), field mults **5.49e9** (about U1's), total proxy **0.97× U1**. GKR's whole
  advantage is in witness generation (fewer committed cells), and it is small.
- **Nearest.** zkGPT (USENIX Sec '25), zkLLM (CCS '24: tlookup/zkAttn, BLS12-381) and NanoZK
  (layerwise sumcheck) occupy the architecture. **What is unoccupied is the formal layer:
  "GKR/layered circuits exist nowhere in our Lean"** (`SELVAGE.md` §4.5) and nowhere in ArkLib.
  The Lean object is a layered-sumcheck RBR instance our compiler already consumes.
- **Objection.** The win over U1 is in committed cells (witness generation), not field mults.
  Whether GKR's wiring predicate evaluations are tensor-core-shaped is unpriced.

### U6. Proof-carrying prefix/KV DAGs (codex)

- **Point.** Certify a shared prompt prefix once. Requests that extend it carry a certificate of
  `(model, tokenizer, position offset, arithmetic version, KV commitment)` and prove only their
  suffix. This is vLLM prefix caching with proofs, composed by holography accumulation
  (2026/538).
- **Price** [codex §B6]: 100 requests sharing a 4,096-token prefix with 256 new tokens each go
  from 435,200 to 29,696 proved positions, **14.66×**, minus the KV-commitment opening per request
  (attention reads the whole cached KV: ~2·L·d_kv·C ≈ 2·32·1024·4096 = 2.7e8 values per request
  for Llama-3.1-8B's GQA, which is an opening of a committed vector, not a re-proof).
- **Why unoccupied.** Prefix caching is a serving optimization; nobody binds cached KV state to a
  proof. **Falsifier:** change the adapter or position offset and check that the certificate
  refuses; count whether the KV opening exceeds the saved prefill proof.

### U7. Delayed, teacher-forced block replay (codex, merged with U4)

- **Point.** Serve normally. Commit accepted tokens plus sampling randomness. Prove a block of 128
  tokens as **one teacher-forced prefill**, where weights are shared across 128 positions and the
  matmul sumcheck amortizes over B = 128.
- **Price** [codex §B7]: the weight-opening share per token falls from 9.14e7 to 1.71e7
  mult-equivalents (batch 24 → 128). One folding step per block is 2.1e5 rows per token.
- **Why unoccupied.** It needs **bit-exact equivalence of sequential decode and block replay**.
  FlashProve sidesteps this by proving prefill only; SASH proves "4,096+512" as a single trace.
- **Falsifier** (cheap): compare logits, sampling decisions and KV between sequential and
  replayed execution in the integer model. One batch-dependent rounding difference defeats the
  naive equivalence.

### U8. UD-provable leaf at low blowup, low-rate final wrap (the Magnetar rule, applied to our tower)

- **Point.** Setty's §6 sentence: prove the application "at a high rate for speed and the final
  proof at a low rate for size". Our blowup drop (F2) is exactly the leaf half, and our tower
  measurement says it is **×3.21 worse per turn** at the deployed leaf (`LEAF-VS-RECURSION.md`
  corrections; VERDICTS §4c still prints "≈65×", which is stale).
- **The rule** [INFERRED from VERDICTS §4c's three numbers: leaf ÷15.23, wrap cells ×3.268, wrap
  = 26.05× leaf at the deployed point]: with `K = wrap/leaf`, the drop wins iff
  `1/15.23 + 3.268·K < 1 + K`, i.e. **K < 0.41**. Ours is K ≈ 26.9 (the leaf is too small,
  LEAF-VS-RECURSION). A zkML leaf at 2^16-2^20 rows has a wrap that scales with the *child's
  verifier width*, not its height, so K falls roughly in proportion to leaf size.
  **The drop is right for big leaves and wrong for small ones. That is a per-descriptor knob,
  which is what `ir2_config` already says.**
- **Why unoccupied for us.** The measured numbers were never combined into the threshold. For the
  field: SP1/OpenVM raise blowup up the tower (LEAF-VS-RECURSION); nobody publishes the K
  threshold.

### U9. A hash-native binary wrap of FlashProve proofs (verifier-side composition, priced)

- **Point.** Recursively verify a FlashProve proof inside a BinarySpartan-style prover over
  GF(2^128). The verifier is BLAKE2b-dominated (allowance 2^23 32-byte queries [READ
  THEOREM.md:36-41]). That would compress 18.78 MB / 17-21 s CPU verify toward Magnetar's
  ~600 KiB / ~10 ms, and gives our certificates one small object to weld to.
- **Price** [INFERRED]: ≤ 2^22 BLAKE2b compressions. At BinarySpartan's measured BLAKE3 rate
  (872k/s on 12 cores), with BLAKE2b at ~3× BLAKE3 in binary R1CS (64-bit adds), that is
  **~15 s per wrapped proof** of hashing, plus **non-native Goldilocks arithmetic in char 2**
  (unpriced, and probably dominant: every Goldilocks mult is ~4,000 binary constraints as a
  64×64 schoolbook [INFERRED]).
- **Why unoccupied.** FlashProve is 6 days old and unmaintained. **Verdict:** the hash half is
  cheap and the field half is unknown. Count the Goldilocks mults in `cp_verify` (one
  instrumented verify run) before anyone builds it. If it is > 1e8, wrap in a prime field (e.g.
  Goldilocks-native FRI) instead.

### U10. Lookup-witness-free proving as the target (from SASH's 42%)

- **Point.** Since witness generation dominates, choose the lookup argument by **witness-
  generation cost**, not prover-crypto cost. LogUp needs `1/(X−a)` helper columns: a batch
  inversion per lookup, plus a committed column. Shout's one-hot addresses are a pure function of
  the access pattern (2026/1390), so there are no inverses.
- **Price.** In the model, LogUp → Shout cuts boundary-only committed cells **1.54e7 → 1.07e7
  (1.44×)**. Witness generation, calibrated per cell, falls in proportion.
- **Why unoccupied.** Every zkML stack measured so far (SASH, FlashProve, EZKL) uses LogUp-family
  arguments. Jolt/Magnetar use Shout for VMs, not for nonlinearities. 2026/1390 measures depth
  scaling, not witness-generation cost.

---

## 5. Pareto summary (four objectives, `space.py`)

- **A** (per-request: min prover, min verifier hashes, max bits). The front is
  **boundary-only + GKR + Shout + tensor cores** over M31/BabyBear/KoalaBear with WHIR, followed
  by lattice folding and FRI-at-low-rate (verifier-hash minimizers). Field choice among the 31-bit primes is a **null knob**, which agrees with
  VERDICTS §1b's KoalaBear refutation from a different direction.
- **B** (proof bytes). WHIR at low rate, or holography accumulation, wins bytes at ~1.7× prover.
- **C** (audited). The audited fronts are dominated by the always-paid hash-only boundary commit,
  so **the hash choice matters most there** (Blake2s vs Poseidon2 is 5.7× on U1).
- **D** (formalizability first). Only FRI + AIR + LogUp scores 2, because Shout, GKR, WHIR,
  Ligerito and Brakedown have no proved soundness anywhere (ArkLib: FRI, sumcheck, Binary
  BaseFold). **The cheapest formal-2 point (M31 FRI ρ=½, AIR + side sumcheck, LogUp, tc,
  boundary-only) is 3.77e-3 against the front's 3.64e-3 (GKR/WHIR/Shout). Formality costs
  ~1.04× on the prover at the boundary shape.** The formal gap is in *lookups* (Shout) and
  *GKR*, not in the PCS, so the cheapest formal-first lane is the boundary shape on FRI + AIR +
  LogUp, which is what we already have.

---

## 6. F2 (blowup drop + `num_queries` pin): NOT landed. Here is the exact plan.

F2 is **not as cheap as PROGRAM §3 says**, and in its global form it is wrong (U8). Facts
[MEASURED today]:
- `breadstuffs/Cargo.toml:370-373` still pins `plonky3-recursion` at **`fc3c6df`**.
- The pin commit `52e1fab` exists in `~/dev/plonky3-recursion` on branch `update-plonky3-rev`
  and is **contained in no remote branch** (`git branch -r --contains 52e1fab` is empty): it was
  never pushed. That checkout also has uncommitted changes by another lane
  (`circuit-prover/Cargo.toml`, an untracked JSON).
- `circuit/src/descriptor_ir2.rs:7269,7272`: `IR2_FRI_LOG_BLOWUP = 6`,
  `IR2_FRI_NUM_QUERIES = 19`.
- breadstuffs has 54 dirty files on `main` from other lanes.

Landing it means pushing another repo's branch, bumping a shared lock in a tree other lanes are
editing, rotating the IR-v2 VK epoch, re-emitting all 132 goldens and re-genesis (blowup-drop.md
§7). **None of that is a filtered-test, counts-only change. It is ember's flag day.** The plan:

1. **Push `52e1fab`** to `emberian/plonky3-recursion` (ember: outward-facing), after the owner of
   that checkout's dirty `circuit-prover/Cargo.toml` commits or confirms it.
2. **Bump** `breadstuffs/Cargo.toml:370-373` to `52e1fab`. Gate:
   `cargo nextest run -p p3-recursion -E 'test(fri_verifier)'` in the recursion repo, and in
   breadstuffs `cargo nextest run -E 'test(recursion_rejects) | test(num_queries)'` (run
   `--list` first to name the real tests). The falsifier from VERDICTS §2 must reproduce:
   one-query proof → `Err` with the pin, `Ok` with it disarmed.
3. **Also pin `max_log_arity`** (VERDICTS §2: attacker-chosen partition, `log_arity = 0`
   unrejected) **in the same flag day.** Otherwise a two-config world ships a second hole.
4. **Per-descriptor knob, not global**: `ir2_config(desc) → (lb, q, pow)` with
   `(2, 57, 16)` **only for descriptors whose leaf/wrap ratio puts K < 0.41** (U8), i.e. no
   recursion parent or a leaf ≥ about 2^16 rows. Everything recursed at today's leaf size stays
   `(6, 19, 16)`, or moves to `(6, 86, 16)` for UD-100 (W1).
5. **VK epoch.** Check that `recursion_vk_fingerprint` sees `num_queries` (blowup-drop.md §7
   warns it may not). If it does not, add it to the fingerprint *before* two configs coexist.
6. **Counts gate** (no clocks): `ir2_phase_profile::poseidon2_permutation_counts_per_phase` §D2
   must reproduce `217,150 → 14,295` for the switched descriptors, byte-identical across two
   runs, and the tower profile must show the wrap ratio for each switched descriptor below the
   threshold.

---

## 7. First experiment for hbox

**The UD-100 wrap price** (critique W1 + U8, one run, counts only). On hbox under
`swarm-build`, from a detached clone at a pinned SHA, run `recursion_tower_profile` at
`(lb, q, pow) ∈ {(6,19,16), (6,86,16), (2,57,16), (2,148,0)}` and report **wrap cells, in-circuit
`poseidon2_perm` ops, and leaf permutations** per point. That one table decides three things:
whether "adopt provable-UD-100" is affordable in the tower (the 34-bit gap); where K falls for a
real 2^16-row zkML leaf (append that child); and whether F2 lands per-descriptor. It needs no new
code: the harness and the counters exist (`circuit-prove/tests/recursion_tower_profile.rs`).
Filter to that test binary by name; never run the crate suite.
