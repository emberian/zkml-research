# Upstream Code & Soundness Audit of `uiuc-kang-lab/zkTransformer` (CCS 2026)

**Date:** 2026-11-20  
**Lane:** `upstream-audit-pr`  
**Audited Repository:** `https://github.com/uiuc-kang-lab/zkTransformer.git` (`zk_torch_2` crate), base `main` commit `55344d7c37232b4dbe8aa479e139967230d8449b` ([zkTransformer-repo](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo))  
**Audited Paper:** Bing-Jyue Chen, Lilia Tang, and Daniel Kang, *"zkTransformer: Speeding Up Zero-Knowledge Proofs for Transformers Without Accuracy Loss"* (ACM CCS 2026 / `arXiv:2603.19609v1`, pre-extracted at [zkTransformer.txt](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer.txt))  
**Local Fix Branch (not pushed):** `fix/soundness-and-lookup-openings` (`62a8119`, `81e5dd7`) in [zkTransformer-repo](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo)  
**Regression & PoC Suite:** [test_soundness_audit.rs](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/tests/test_soundness_audit.rs) (`[EXECUTED]`)  
**House Rule:** Counts are primary; proof sizes and wall-clock timings are secondary ([SLVG_THOUGHT.md](file:///Users/ember/dev/zkml-research/SLVG_THOUGHT.md) §II.2). Every claim carries its provenance tag (`[SOURCE]`, `[DERIVED]`, `[EXECUTED]`, `[REFUTED: scope]`, `[OPEN]`). Tone is constructive and collaborative: upstream authors are research peers building open artifacts for a shared problem.

---

## 0. Executive Summary

We performed an exhaustive line-by-line soundness and completeness audit of `uiuc-kang-lab/zkTransformer` (`main` @ `55344d7`) across `src/dag/`, `src/basicblock/`, `src/crypto/`, and `src/util/`, cross-referenced against the CCS 2026 paper ([zkTransformer.txt](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer.txt) §§3–6, Appendices D–J).

### Headline Findings

1. **Core `EinSumcheck` Protocol Engine Is Mathematically Sound & Ingenious (`[SOURCE]`, `[EXECUTED]`):**
   - `Einsum::prove` and `Einsum::verify` ([src/basicblock/einsum.rs](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/einsum.rs#L468-L615)) faithfully implement Theorem 3.1's $(F_1, F_{\ge 2}, S)$ index classification, unequal-variable-count partial-sumcheck reduction (`GeneralLinearSumcheckProver`), and factored terminal check $\text{running\_sum} == \widetilde{\mathrm{eq}}(r_{F_{\ge 2}}, s_{F_{\ge 2}}) \cdot \prod_k \tilde{T}_k(\cdot)$ (machine-checked in sibling report [FORMAL_EINSUMCHECK.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/FORMAL_EINSUMCHECK.md)).
   - Likewise, the pairing-based PCS implementations (`KZH2`, `KZH3`, `SparseKZH3` in `src/crypto/polycommit/`) enforce genuine curve pairing equations when invoked.

2. **Six Implementation-Level Soundness & Completeness Bugs Confirmed & Exploited on `main` (`[SOURCE]`, `[EXECUTED]`):**
   - **Bug A — Missing Terminal Sumcheck Evaluations:** `SumcheckVerifier::verify` (`src/crypto/sumcheck/verifier.rs:27-68`) checks only per-round $g_j(0) + g_j(1) = \text{running\_sum}$ and returns `(Some(running_sum), challenges)` for the caller to check against the terminal oracle evaluation. While `Einsum::verify`, `Reducer::verify`, and `Permute::verify` check `running_sum`, `Dag::verify_range` (`src/dag/mod.rs:1241-1270`), `Dag::verify_two_pow` (`src/dag/mod.rs:1427-1428`), and `NonStructuredExp::verify` (`src/basicblock/exp.rs:186-190`) discard `running_sum` and check only `.is_some()`. In addition, `Dag::verify_range` (`line 1250`) omits a length check on `range_bool_proofs`, so setting `bool_proofs = vec![]` bypasses booleanity altogether.
   - **Bug B — Unopened & Partially Uncommitted Sparse Lookup Polynomials (4 Sub-Bugs B1–B4):**
     - **B1 (`0` `SparseKZH3` openings in every benchmark):** `Dag::prove` (`src/dag/mod.rs:854`) snapshots `claims` into `edge_proofs` *before* calling `prove_two_pow` (`line 857`) and `prove_range` (`line 858`), and those functions hardcode `eval: F::zero()` (`lines 1358, 1378, 1480`). Consequently, **`0` `SparseKZH3` opening proofs are generated or verified** in `structured_exp`, `nanogpt`, and `oneshot_gpt2`.
     - **B2 (`74%` of sparse lookup blocks uncommitted):** `Dag::commit` (`src/dag/mod.rs:659`) guards multi-block sparse commitment with `if sparse_commitments[e].is_none()`, committing only `sparse_id == 0` and skipping `sparse_id >= 1` (**`574 / 774 = 74.2%`** of sparse blocks in `nanogpt` and **`1,648 / 2,224 = 74.1%`** in `oneshot_gpt2` were never committed).
     - **B3 (Multi-output `Reducer` & fan-out point bugs):** `Dag::prove` (`line 804`) tags `Reducer` claims with `edge_ids[edge_ids.len() - 1]`, selecting `node.outputs[1]` (sparse `aux` edge) instead of `node.outputs[0]` (dense output) on any 2-output node (`ExpHelper`, `ScaleDown`, `ScaleUp`) with fan-out $> 1$; and `prove_range` (`line 1368`) reads `claims[inp].last()` instead of `node_proofs[n].1[0].point`, mismatching `verify_range` (`line 1192`) on fan-out $> 1$ edges.
     - **B4 (Partial-block table bit-width inflation):** `SparseMLPoly::split_into_blocks` (`src/util/poly.rs:1350`) assigns `table_num_vars = block_size` (`4`) even to narrower final blocks (e.g., `ScaleDown(20, 10)` has `10 = 4 + 4 + 2` bits; `ScaleUp(10, 15)` has `5 = 4 + 1` bits), inflating the allowed range from $[0, 2^{10})$ to $[0, 2^{12})$ (`4×`) and $[0, 2^5)$ to $[0, 2^8)$ (`8×`).
   - **Bug C — Missing Remainder Range Check in `StructuredExp`:** Paper §4.4 (`zkTransformer.txt:522-526`) specifies three constraints for $q = -k \lfloor 2^s \ln 2 \rceil + r$: $k \in [0, 15]$, $|r| \le 2^s \ln 2 / 2$, and linearity. `DagBuilder::exp` (`src/dag/builder.rs:341-350`) omits the $|r|$ bound, allowing a prover to pick $k' = 0$ and $r' = q \ll 0$ so the degree-3 Taylor polynomial underflows negatively (e.g., proving $\exp(-4 \ln 2) = -1519/1024 < 0$ instead of $+64/1024$). We also found an `f32` vs `f64` $\ln 2$ constant mismatch (`src/util/poly.rs:424` vs `src/basicblock/exp.rs:33`) and positive test inputs `0..1024` in `src/bin/structured_exp.rs:55`.
   - **Bug D — Missing Shout Hamming-Weight-1 (`row-sum = 1`) Check in `TwoPow`:** `prove_two_pow` / `verify_two_pow` (`src/dag/mod.rs:1388-1486`) omit both the $\alpha$-shifted table fold $T(k) + \alpha$ (used in `prove_range` to enforce $\sum_k \text{aux}(i, k) = 1$) and standalone booleanity when `self.range` is empty, permitting all-zero rows (`TwoPow = 0`) or multi-one rows (`TwoPow = 32768 + 16384 = 49152`).
   - **Bug E — Fiat-Shamir Transcript Omissions:** `range_proof.middle_claims` and `two_pow_proof.middle_claims` are never absorbed into `Transcript` and are computed *after* squeezing `table_alpha, table_beta, table_gamma` (`src/dag/mod.rs:1290-1292`), enabling an explicit $2\times 2$ linear-system cancellation (`PoC 5`) that proves `NonNegative([-500, -500, -500, -500])` using all-zero `aux` commitments and **genuine** sumchecks. Output, GKR node, and `Reducer` intermediate `Claim.eval`s are likewise omitted from `Transcript`, and `KZH2Commitment` inherits `to_transcript_bytes() -> vec![]` (`src/crypto/polycommit/mod.rs:410`).
   - **Bug F — Broken GKR Claim Chaining & Unbound PCS Openings:** `Dag::verify` (`src/dag/mod.rs:1044-1145`) fails to equate `node_proofs[u].1.last()` to `claims[out][0]` when `claims[out].len() == 1` (skipped because `Reducer` runs only when `len > 1`), fails to equate `NonNegative`/`ZeroCheck` sink claims to initial `claims`, leaves `ChangeShape`/`ScaleDown`/`ScaleUp`/`ExpHelper`/`ClampLower::verify` returning `true` unconditionally, omits input point checks in `Einsum`/`Reducer`/`Permute::verify`, skips opening final DAG output commitments (`should_open`), and never checks `edge_proofs[e].claims == claims[e]` (`PoC 6` forged a `MatMul` output to `9999` and stripped `100%` of `KZH3` openings while `dag.verify` returned `true`).

3. **Constructive PoC Suite & Surgical Fix Branch Verified (`[EXECUTED]`):**
   - On unmodified `main` (`55344d7`), all 6 cheating-prover PoCs in `tests/test_soundness_audit.rs` pass with `dag.verify(...) == true` (`7 passed; 0 failed` in `0.04s`).
   - On `fix/soundness-and-lookup-openings` (`62a8119`, `81e5dd7`), all **65 tests across all 8 Cargo test binaries pass (`0 failed`)**, honest end-to-end `structured_exp`, `nanogpt` (`SEQ_LEN=1`), and `oneshot_gpt2` (`SEQ_LEN=2, VOCAB_SIZE=256`) verify `true`, and every forgery in `tests/test_soundness_audit.rs` rejects (`assert!(!verified)`).

4. **Impact on Published Benchmark Metrics (`[EXECUTED]`):**
   - On unmodified `main`, `nanogpt` (`SEQ_LEN=1`) reproduces Paper Table 4 (`zkTransformer.txt:678-695`) to the byte and millisecond: **`356.33 KB` (`364,886 B`)** proof size, **`0.234s`** online prover time (`0.0606s` input/sparse commit + `0.1730s` prove), and **`0.138s`** verifier time — **with `574 / 774` (`74.2%`) sparse blocks uncommitted and `0` `SparseKZH3` openings**.
   - Once all sparse lookup blocks (`822` blocks in `nanogpt`, `2,368` in `oneshot_gpt2`, `36` in `structured_exp`) are committed and opened via `SparseKZH3` (`1,652` sparse openings in `nanogpt`, `4,760` in `oneshot_gpt2`, `73` in `structured_exp`), proof sizes increase by **`5.14×–9.05×`** (`nanogpt`: `356.33 KB -> 1.79 MB`; `oneshot_gpt2`: `2.66 MB -> 14.02 MB`; `structured_exp`: `28.92 KB -> 261.70 KB`) and verifier time increases by **`6.10×–21.6×`** (`nanogpt`: `0.138s -> 1.452s`; `oneshot_gpt2`: `1.217s -> 7.420s`). This empirically confirms that per-instance `SparseKZH3` pairing openings dominate proof size (`88%–93%`) and verification time (`>99%`) once enabled.

---

## 1. Exhaustive Module & Block Audit Matrix

Every module in `src/crypto/`, `src/basicblock/`, `src/dag/`, and `src/util/` on `main` (`55344d7`) was inspected at source (`[SOURCE]`):

| Module / BasicBlock | `main` Location (`55344d7`) | Audit Status on `main` | Fix Status on `fix/soundness-and-lookup-openings` |
|---|---|---|---|
| `SumcheckVerifier` | [verifier.rs:27-68](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/crypto/sumcheck/verifier.rs#L27-L68) | Checks round consistency $g_j(0)+g_j(1)=\text{sum}$; caller must verify returned `running_sum`. | Preserved API; enforced terminal `running_sum` checks at all callers (**Bug A**). |
| `SparseBoolSumcheckProver` | [linear_prover.rs:455-655](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/crypto/sumcheck/linear_prover.rs#L455-L655) | Hardcoded `final_eval: F::zero()`; assumed boolean entries $\{0,1\}$ during proving. | Added `prove_with_entries` for general sparse field values and exact `term_final_eval` (**Bug A/D**). |
| `KZH2Commit` | [kzh2.rs:103-1083](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/crypto/polycommit/kzh2.rs#L103-L1083) | Pairing equation sound; **omitted `to_transcript_bytes()`** (inherited default `vec![]` at `mod.rs:410`); `assert_eq!` panics on malformed proof vector lengths. | Implemented `KZH2Commitment::to_transcript_bytes()` and non-panicking length guards (**Bug E**). |
| `KZH3Commit` & `SparseKZH3Commit` | [kzh3.rs:406-1136](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/crypto/polycommit/kzh3.rs#L406-L1136), [sparse_kzh3.rs:408-506](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/crypto/polycommit/sparse_kzh3.rs#L408-L506) | Pairing equations and `verify_and_extract` sound (`C`, `C_y`, `d_x`, `f_star` checked); `SparseKZH3` **never invoked** by `Dag` (**Bug B1**); `assert_eq!` panics on malformed lengths. | Wired `SparseKZH3` commit/open/verify across all sparse blocks (**Bug B1/B2**); added non-panicking length guards. |
| `Transcript` & `CryptoField` | [transcript.rs:1-47](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/util/transcript.rs#L1-L47), [poly.rs:72-76](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/util/poly.rs#L72-L76) | Merlin sponge sound; note `ArkFr::from_bytes_le` truncates 64B challenge to 32B (`poly.rs:74`) for icicle compatibility (~$2^{-253}$ bias on BN254). | Documented 32B truncation; restored full Fiat-Shamir claim absorption in `Dag` & `Reducer` (**Bug E**). |
| `Einsum` | [einsum.rs:442-616](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/einsum.rs#L442-L616) | Core sumcheck & terminal product check sound; **did not verify `inp_claim.point`** matched sumcheck challenges + output point (`lines 584-615`). | Added exact `expected_point` verification for every operand `Claim` (**Bug F4**). |
| `Reducer` | [reducer.rs:11-100](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/reducer.rs#L11-L100) | Sumcheck + terminal `running_sum == beta_eq * claim.eval` sound; **omitted claims from `Transcript` before `r_beta`** (`line 22`), **omitted `claims.last().point == challenges`**, and **`Dag::prove:804` tagged wrong output edge on 2-output nodes**. | Absorbed claims before `r_beta`, verified `reduced_claim.point == challenges`, fixed `reducer_edge_ids = vec![node.outputs[0]]` (**Bug B3/E/F4**). |
| `Permute` | [permute.rs:21-128](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/permute.rs#L21-L128) | Permutation sumcheck + terminal `running_sum == perm_eval * inp.eval` sound; **omitted `claims[0].point == challenges` check** (`line 125`). | Added `claims[0].point == challenges` & length checks (**Bug F4**). |
| `Add` / `Sub` | [add.rs:34-225](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/add.rs#L34-L225) | Checked `a.eval ± b.eval == out.eval` and suffix point equality; panicked on wrong claim count. | Added non-panicking `claims.len() == 3` + exact dimension-aware suffix point checks. |
| `ChangeShape` | [shape.rs:9-46](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/shape.rs#L9-L46) | **`verify` returned `true` unconditionally (`line 44`)!** Allowed arbitrary eval/point forgery across reshapes (**PoC 6**). | Enforced `inp.eval == out.eval` and exact zero-prefix / suffix point consistency (**Bug F3**). |
| `ClampLower` & `ZeroCheck` | [clamp.rs:19-112](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/clamp.rs#L19-L112) | `ClampLower::verify` returned `true` without checking `inp.point == out.point`; `ZeroCheck` sink claim unlinked to `claims[inp]` in `Dag::verify`. | Enforced `claims[0].point == claims[1].point` in `ClampLower` and sink-claim equality in `Dag::verify` (**Bug F2/F3**). |
| `ScaleDown` & `ScaleUp` | [scale.rs:12-187](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/scale.rs#L12-L187) | `verify` returned `true` without point check; partial top block inflated to 4 bits (**Bug B4**); architectural mod-$p$ quotient-wrap & `ScaleUp` slack (§5.2). | Enforced `inp.point == out.point` (**Bug F3**) & exact partial-block `this_block_vars` (**Bug B4**); documented mod-$p$ quotient wrap (§5.2). |
| `ExpHelper`, `TwoPow`, `NonStructuredExp` | [exp.rs:24-233](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/exp.rs#L24-L233), [builder.rs:332-400](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/builder.rs#L332-L400) | Missing $|r|$ bound (**Bug C**), missing `TwoPow` row-sum=1 (**Bug D**), missing terminal checks (**Bug A**), `f32` vs `f64` $\ln 2$, `NonStructuredExp` self-referential `expected_sum`. | Fixed all of Bugs A, C, D, `f64` $\ln 2$, `ExpHelper` point check, and `NonStructuredExp` prove/verify. |
| `argmax_check` | [oneshot.rs:89-113](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/oneshot.rs#L89-L113) | Broken by **Bug A** (`NonNegative` accepted forged argmax); also **completeness bug on non-power-of-two `vocab_size`** (`selected[i] - 0 < 0` on zero-padded slots when max logit $< 0$). | Fixed `NonNegative` soundness (**Bug A/B/E/F**) and masked non-pow2 padding in `argmax_check`. |
| `RMSReciprocal`, `DivConst`, `Reciprocal`, `SoftmaxConst`, `SigmoidConst` | [basicblock/llama.rs:12-389](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/llama.rs#L12-L389), [dag/llama.rs:85-443](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/llama.rs#L85-L443) | `DivConst` & `Reciprocal` builder constraints sound; **`SoftmaxConst` omits row-sum check & allocates 4D `[B,H,S,S]`; `SigmoidConst` completely unconstrained; `RMSReciprocal` lacks `NonNeg(r)`** (§5.1). | Documented in §5.1 as model-arithmetization design items (fixing `SoftmaxConst`/`SigmoidConst` alters model DAG topology). |

---

## 2. Detailed Root-Cause Analysis of Bugs A–F (`[SOURCE]`, `[DERIVED]`)

### 2.1 Bug A — Missing Terminal Sumcheck Verification (`Dag::verify_range`, `Dag::verify_two_pow`, `NonStructuredExp::verify`)

- **Source locations (`main` @ `55344d7`):**
  - [src/crypto/sumcheck/verifier.rs:27-68](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/crypto/sumcheck/verifier.rs#L27-L68): `SumcheckVerifier::verify` checks only round-by-round degree and $g_j(0) + g_j(1) = \text{running\_sum}$, returning `(Some(running_sum), challenges)` so the caller can verify `running_sum` against the terminal polynomial evaluation.
  - [src/dag/mod.rs:1240-1270](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/mod.rs#L1240-L1270) (`Dag::verify_range`):
    - Lines `1241-1244`: Calls `sumcheck_verifier.verify(transcript, range_table_proofs[0].round_messages.clone(), table_expected_sum)` and returns `false` only if `verification_result.is_none()`, **discarding `(verification_result, _challenges)`**.
    - Lines `1250-1267`: Iterates `for bool_proof in range_bool_proofs.iter()`, squeezes fresh challenges, checks `verification_result.is_none()` against `F::zero()`, and **never checks `range_bool_proofs.len()`** (an empty `Vec` vacuously passes!).
  - [src/dag/mod.rs:1423-1429](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/mod.rs#L1423-L1429) (`Dag::verify_two_pow`): Ends with `verification_result.is_some()`.
  - [src/basicblock/exp.rs:178-190](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/exp.rs#L178-L190) (`NonStructuredExp::verify`): Computes `expected_sum = round_messages[0][0] + round_messages[0][1]` (tautologically self-referential, never referencing `claims`!) and ends with `verification_result.is_some()`.
- **Consequence (`[DERIVED]`):** For any claimed sum $S^* \in \mathbb{F}$, sending $g_j(X) = S_{j-1}(1 - X)$ at every round satisfies $g_j(0) + g_j(1) = S_{j-1} + 0 = S_{j-1}$ identically without ever touching the witness or table polynomials. Any `NonNegative`, `ScaleDown`, `ScaleUp`, `ExpHelper`, `TwoPow`, or `argmax_check` claim can be forged unconditionally (`PoC 1`).

---

### 2.2 Bug B — Broken Sparse Lookup Commitments, Openings & Multi-Block Decomposition (`B1`–`B4`)

1. **Bug B1 — Zero `SparseKZH3` Openings Generated or Verified (`[SOURCE]`):**
   - In [src/dag/mod.rs:845-858](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/mod.rs#L845-L858):
     ```rust
     for e in 0..self.num_edges {
       edge_proofs.push(EdgeProof {
         claims: if self.should_open(e) { claims[e].clone() } else { vec![] }, // <-- Line 854: BEFORE lookups!
         dense_opening_proof: vec![],
         sparse_opening_proof: vec![],
       });
     }
     let (two_pow_table_proofs, ...) = self.prove_two_pow(witnesses, &mut claims, transcript); // Line 857
     let (range_table_proofs, ...)   = self.prove_range(witnesses, &mut claims, transcript);   // Line 858
     ```
   - Because `claims[sparse_edge]` is still empty at line `854`, `edge_proofs[sparse_edge].claims` is always `vec![]`. The opening loop at lines `896-951` iterates over `edge_proofs[e].claims`, so it produces **zero `SparseKZH3` opening proofs**. Moreover, `prove_range` (`lines 1358, 1378`) and `prove_two_pow` (`line 1480`) push dummy claims with `eval: <F as CryptoField>::zero()` instead of evaluating `aux_poly` at the sumcheck challenge point.
2. **Bug B2 — `74%` of Sparse Lookup Blocks Never Committed (`[SOURCE]`):**
   - In [src/dag/mod.rs:643-665](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/mod.rs#L643-L665), `Dag::commit` loops `for (sparse_id, w) in ws.iter().enumerate()` (`line 643`), but inside the `PolyType::Sparse` arm (`line 659`) writes:
     ```rust
     if sparse_commitments[i].is_none() {
       sparse_commitments[i] = Some(vec![SP::commit(poly, sparse_commit_key)]);
     }
     ```
   - Thus for any multi-block range lookup (e.g., `NonNegative(20)` with `5` blocks, `ScaleDown(30, 15)` with `4` blocks, `ScaleDown(20, 10)` with `3` blocks), **only block `0` (`sparse_id == 0`) was committed**, while blocks `1..num_blocks` (`74.2%` of all sparse blocks in `nanogpt` and `74.1%` in `oneshot_gpt2`) had no commitment at all!
3. **Bug B3 — Multi-Output `Reducer` `edge_id` & Fan-Out Lookup Point Mismatches (`[SOURCE]`):**
   - In [src/dag/mod.rs:804](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/mod.rs#L804), `let reducer_edge_ids = vec![edge_ids[edge_ids.len() - 1]];` passes the **last** element of `edge_ids = [inputs..., outputs...]` to `Reducer::prove`. For a 2-output node (`ExpHelper`, `ScaleDown`, `ScaleUp`, where `outputs = [y_dense, aux_sparse]`), when `y_dense` has fan-out $> 1$ (which happens in `StructuredExp` once remainder range checks also read `r`!), `edge_ids.last()` is `outputs[1]` (`aux_sparse`) rather than `outputs[0]` (`y_dense`)!
   - Similarly, in `prove_range` ([src/dag/mod.rs:1368](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/mod.rs#L1368)), `claims[node.inputs[0]].last()` picks the wrong point whenever `node.inputs[0]` has fan-out $> 1$ (before `Reducer` runs on `node.inputs[0]`), mismatching `verify_range` (`line 1192`, which uses `node_proofs[*n].1[0].point`).
4. **Bug B4 — Partial-Block Bit-Width Inflation in `split_into_blocks` (`[SOURCE]`, `[DERIVED]`):**
   - In [src/util/poly.rs:1328-1353](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/util/poly.rs#L1328-L1353), `SparseMLPoly::split_into_blocks` computes `this_block_vars = remaining.min(block_size)` (`line 1334`), yet constructs `SelectionPolynomial::new(selection.input_num_vars, block_size, block_selection)` (`line 1350`) using `block_size` (`4`) instead of `this_block_vars`!
   - When `rescale_sf = 10` (`ScaleDown(20, 10)`, ubiquitous in every `nanogpt` and `oneshot_gpt2` linear layer), the 3 blocks have radix weights $1, 16, 256$. Giving block 2 four table variables ($[0, 15]$) instead of two ($[0, 3]$) allows $\text{rem} \in [0, 4095]$ instead of $[0, 1023]$, letting a malicious prover bias every `ScaleDown(20, 10)` output by up to **$3$ quantized units** (`PoC 7`) and every `ScaleUp(10, 15)` (`5 = 4 + 1` bits) by up to **$240$ units**.

---

### 2.3 Bug C — Missing Remainder Range Check in `StructuredExp`

- **Paper specification (`[SOURCE]`, [zkTransformer.txt:518-527](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer.txt#L518-L527)):** For fixed-point input $q \le 0$, decompose $q = -k \cdot \lfloor 2^s \ln 2 \rceil + r$ and prove:
  1. $k \in \{0, 1, \dots, 15\}$,
  2. $|r| \le \lfloor 2^s \ln 2 / 2 \rfloor$, and
  3. $q + k \cdot \lfloor 2^s \ln 2 \rceil - r = 0$.
- **Code on `main` (`[SOURCE]`, [src/dag/builder.rs:341-350](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/builder.rs#L341-L350), [src/dag/mod.rs:1221-1228](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/mod.rs#L1221-L1228)):** `DagBuilder::exp` registers `ExpHelper` in `self.range` (which enforces $k = (q - r) \cdot (-L)^{-1} \in [0, 15]$, where $L = \lfloor 2^s \ln 2 \rceil$), then calls `self.scale(r, *SF_LOG, 15)` **without ever bounding $r$**!
- **Exploit (`[DERIVED]`, `[EXECUTED]` in `PoC 3`):** At $s = 10$ ($L = 710$), on honest input $q = -4 L = -2840$ ($\approx -4 \ln 2$, true $\exp \approx 1024/16 = +64$), a cheating prover sets $k' = 0 \in [0, 15]$ and $r' = q = -2840$. Then $(q - r') \cdot (-L)^{-1} = 0 = k'$ passes `ExpHelper`, `TwoPow(0) = 32768` ($= 1.0$ in Q15), and the degree-3 Taylor polynomial evaluates at $r'/2^{10} \approx -2.773$ to **$-1519$ (negative!)**, which `dag.verify` accepts on `main`.
- **Two companion precision/input bugs (`[SOURCE]`):**
  - `get_cached_inverses` ([src/util/poly.rs:424](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/util/poly.rs#L424)) computed `ln2 = 2.0_f32.ln()` (`0.6931472`) whereas `ExpHelper::run` ([src/basicblock/exp.rs:33](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/exp.rs#L33)) computed `2.0_f64.ln()` (`0.6931471805599453`), which diverge in rounded integer $L$ at larger scale factors.
  - [src/bin/structured_exp.rs:55](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/bin/structured_exp.rs#L55) initialized inputs as `(0..1024)` (positive $[0, +1)$) instead of `-(0..1024)` (non-positive), violating `ExpHelper`'s $x \le 0$ precondition (`exp.rs:14`) so that $99.9\%$ of entries had `k = 0` clamped and out-of-domain remainders up to $+1023 > 355$!

---

### 2.4 Bug D — Missing Shout Hamming-Weight-1 (`row-sum = 1`) Check in `TwoPow`

- **Root cause (`[SOURCE]`, [src/dag/mod.rs:1388-1486](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/mod.rs#L1388-L1486)):** Shout's read-checking relation requires each row $i$ of the sparse selector $\text{aux}(i, k) \in \{0, 1\}^{2^m \times 16}$ to have Hamming weight **1**: $\sum_{k=0}^{15} \text{aux}(i, k) = 1$.
  - In `prove_range` (`lines 1326, 1345`), the authors cleverly fold the row-sum check into the table sumcheck by adding random `alpha` to every table entry (`T_range(k) + alpha`), because over BooleanCube $i$, $\sum_k \text{aux}(i, k)(T(k) + \alpha) = m_i + \alpha \iff \sum_k \text{aux}(i, k) = 1$ with overwhelming probability over $\alpha$.
  - In `prove_two_pow` (`lines 1431-1486`) and `verify_two_pow` (`lines 1388-1429`), **both** the `+ alpha` shift (`two_pow_dense(4)` is unshifted!) **and** standalone booleanity (when `self.range` is empty, `two_pow_bool_proofs = vec![]` is ignored by `verify_two_pow`) are missing!
- **Exploit (`[DERIVED]`, `[EXECUTED]` in `PoC 4`):** Setting row $0$ of `aux` to **all zeros** proves `TwoPow = 0` (even though $2^{15-k} \in [1, 32768]$ is strictly positive!), and setting two `1`s at $k=0, 1$ proves `TwoPow = 32768 + 16384 = 49152`!

---

### 2.5 Bug E — Fiat-Shamir Transcript Omissions & Adaptive Linear-System Forgery

- **Source locations (`[SOURCE]`):**
  1. `range_proof.middle_claims` and `two_pow_proof.middle_claims` are never appended to `Transcript`; worse, in `Dag::prove_range` ([src/dag/mod.rs:1290-1324](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/mod.rs#L1290-L1324)), `table_alpha`, `table_beta`, and `table_gamma` are squeezed at lines `1290-1292` *before* `middle_claims` are even computed (`line 1323`)!
  2. `Dag::prove` / `Dag::verify` (`lines 736-858, 1020-1095`) never append DAG sink/output `Claim.eval`s, intermediate multi-input `node_proofs` `Claim.eval`s, or sparse lookup `Claim.eval`s to `Transcript`.
  3. `Reducer::prove` / `Reducer::verify` ([src/basicblock/reducer.rs:22, 65](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/basicblock/reducer.rs#L22)) squeeze `r_beta` before absorbing the `k` input claims being folded.
  4. `KZH2Commitment` ([src/crypto/polycommit/kzh2.rs:103](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/crypto/polycommit/kzh2.rs#L103)) does not override `Commitment::to_transcript_bytes()` ([mod.rs:410](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/crypto/polycommit/mod.rs#L410), which returns `vec![]`!).
- **Constructive Adaptive Forgery (`[DERIVED]`, `[EXECUTED]` in `PoC 5`):** Even if **Bugs A and B were completely fixed** (full terminal sumcheck + `SparseKZH3` openings), omitting `middle_claims` from the transcript before `table_alpha, table_gamma` breaks `NonNegative` completely! Commit to **all-zero** `aux_s = 0` for all blocks $s \in \{0, \dots, B-1\}$. Then the true sumcheck value of $\sum_k \text{aux}_s(r, k)(T(k) + \alpha)$ is identically **$0$**, and booleanity $0 \cdot (0 - 1) = 0$ holds honestly! After squeezing $\alpha, \gamma$, solve the $2 \times 2$ linear system in $(m_0, m_1)$ (setting $m_2 = \dots = m_{B-1} = 0$):
  $$m_0 + 16 m_1 = v_{\text{neg}}, \qquad (m_0 + \alpha)\gamma^0 + (m_1 + \alpha)\gamma^1 + \sum_{s=2}^{B-1} \alpha \gamma^s = 0$$
  $$\implies m_1 = -\frac{v_{\text{neg}} + \alpha \sum_{s=0}^{B-1} \gamma^s}{\gamma - 16}, \qquad m_0 = v_{\text{neg}} - 16 m_1.$$
  Then `eval_acc == v_eval` holds identically AND `table_expected_sum == 0` matches the honest sumcheck on `aux = 0`!

---

### 2.6 Bug F — Broken GKR Claim Chaining & Unbound PCS Openings (`F1`–`F5`)

Inspecting `Dag::verify` ([src/dag/mod.rs:1020-1148](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/dag/mod.rs#L1020-L1148)) revealed five GKR wiring omissions:
- **F1 (Single-consumer output claims unlinked):** At lines `1050-1071`, when `claims[out].len() > 1`, `Reducer` checks that `claims[out]` folds into `local_claims.last()`. When `claims[out].len() == 1` (the overwhelmingly common fan-out-1 case, including every DAG output edge!), `Reducer` is skipped and **`Dag::verify` never checks `local_claims.last() == claims[out][0]`**!
- **F2 (`NonNegative` / `ZeroCheck` sink claims unlinked):** `Dag::prove` copies `claims[inp][0]` into `node_proofs[u]`, and `verify_range` / `verify_zero_check` read `node_proofs[u]`, **never checking `node_proofs[u].1[0] == claims[inp][0]`**!
- **F3 (No-op `BasicBlock::verify`):** `ChangeShape::verify` (`shape.rs:44`), `ScaleDown::verify` (`scale.rs:95`), `ScaleUp::verify` (`scale.rs:185`), `ExpHelper::verify` (`exp.rs:97`), and `ClampLower::verify` (`clamp.rs:69`) all returned `true` without checking `inp.point` or `inp.eval == out.eval`.
- **F4 (Unchecked input claim points):** `Einsum::verify`, `Reducer::verify`, and `Permute::verify` checked `eval` equations without verifying that `inp_claim.point` equaled the sumcheck challenge vector.
- **F5 (Unopened final outputs & unbound `edge_proofs`):** `should_open(e)` (`line 526`) only opened `Role::Constant`, `Role::Input`, and `Role::Auxiliary`, never opening committed final DAG `Role::Output` edges; and lines `1112-1142` iterated over `edge_proofs[e].claims` **without checking `edge_proofs[e].claims == claims[e]`**, allowing a cheating prover to set `edge_proofs[e].claims = vec![]` and strip `100%` of `KZH3` openings (`PoC 6`)!

---

## 3. Constructive PoC Exploit Suite (`[EXECUTED]`)

### 3.1 Execution on Unmodified `main` (`55344d7`)

With `src/` completely untouched on `main` (`55344d7`, plus minimal `ZKTRANSFORMER_CONFIG` path fallback in the test binary), we executed the 7-test PoC suite (`1` honest baseline + `6` cheating-prover exploits across Bugs A–F). Full log saved at [poc_on_main.log](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/poc_on_main.log):

```text
$ cargo +nightly test --release --test test_soundness_audit -- --nocapture
running 7 tests
test test_poc_bug_f_gkr_unlinked_claims_and_stripped_kzh3_openings ... ok
test test_poc_bug_d_shout_zero_hamming_weight_spoofs_two_pow ... ok
test test_poc_bug_e_fiat_shamir_adaptive_middle_claims_forgery ... ok
test test_poc_bug_b_bogus_sparse_commitment_never_opened ... ok
test test_poc_bug_a_forged_argmax_missing_terminal_sumcheck_eval ... ok
test test_audit_honest_argmax_verifies_true ... ok
test test_poc_bug_c_structured_exp_unbounded_remainder_forgery ... ok

test result: ok. 7 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.04s
```

Every single cheating prover (`Bug A` forged argmax token `0` on `[10, 50, 20, 30]`; `Bug B` replaced sparse commitment with empty `SparseMLPoly` and observed `0` sparse openings; `Bug C` forged `exp(-4 ln 2) = -1519 < 0`; `Bug D` forged `TwoPow = 0` via zero Hamming weight; `Bug E` forged `NonNegative([-500; 4])` via $2\times 2$ adaptive `middle_claims` cancellation with genuine sumchecks; `Bug F` forged `MatMul` output `9999` and stripped all `KZH3` openings) was **accepted (`dag.verify == true`) on `main`** (`[EXECUTED]`).

### 3.2 Execution on `fix/soundness-and-lookup-openings` (`81e5dd7`)

On `fix/soundness-and-lookup-openings`, [test_soundness_audit.rs](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/tests/test_soundness_audit.rs) asserts `assert!(verified)` on **4 end-to-end honest circuits** (`Argmax`, `StructuredExp` including half-tie boundaries `-355`/`-354`, standalone `TwoPow`, and `MatMul + ChangeShape`) and `assert!(!verified)` on **7 negative forgery suites** (covering Bugs A–F, weight-0 and weight-2 `TwoPow` rows, block-2 `SparseKZH3` tampering, both sub-attacks of Bug F, and Bug B4 partial-block `ScaleDown(20, 10)` bias). We also repaired all 7 pre-existing unit test files in `tests/` (which failed to compile on `main` due to stale `use zktransformer::...` crate names and old `SparseMLPoly` APIs). Full logs: [poc_on_fix.log](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/poc_on_fix.log), [after_all_tests_quiet.log](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/after_all_tests_quiet.log):

```text
$ cargo +nightly test --release
test_soundness_audit:  11 passed; 0 failed (0.13s)
test_basicblock_add:    8 passed; 0 failed (0.00s)
test_fix_variables:    10 passed; 0 failed (0.00s)
test_kzh2:              4 passed; 0 failed (0.14s)
test_kzh3:              4 passed; 0 failed (0.06s)
test_lagrange_basis:   10 passed; 0 failed (0.00s)
test_linear_sumcheck:  11 passed; 0 failed (0.00s)
test_sd_sumcheck:       7 passed; 0 failed (0.01s)
--------------------------------------------------
TOTAL:                 65 passed; 0 failed
```

---

## 4. Surgical Fix Architecture & Before/After Benchmarks

### 4.1 Summary of Commits on `fix/soundness-and-lookup-openings`

1. **`62a8119`** — `fix: enforce sumcheck terminal checks, sparse lookup openings, and Fiat-Shamir/GKR bindings` (`18` files, `+1058 / -367`):
   - **Terminal sumcheck verification (`src/dag/mod.rs`, `src/util/poly.rs`, `src/crypto/sumcheck/linear_prover.rs`, `src/basicblock/exp.rs`):**
     - Added $O(m)$ `evaluate_range_structured` ($\tilde{T}_{\text{range}}(r) = \sum_{j=0}^{m-1} 2^j r_j$) and $O(1)$ `evaluate_two_pow_structured` ($\tilde{T}_{\text{two\_pow}}(r) = \prod_{j=0}^3 (2^{2^j}(1 - r_j) + r_j)$) in [src/util/poly.rs:1368-1405](file:///Users/ember/.gemini/antigravity-cli/brain/7b8891ea-131f-4759-84a3-a5909e129354/scratch/zkTransformer-repo/src/util/poly.rs#L1368-L1405).
     - Grouped `prove_range` / `verify_range` table sumchecks by exact block table width $m = \text{this\_block\_vars} \in \{1, \dots, 4\}$, verifying `running_sum == folded_aux_eval * (evaluate_range_structured(&r_k) + alpha)` and verifying every booleanity sumcheck (`range_bool_proofs.len() == unique_input_dims.len()`) against $\widetilde{\mathrm{eq}}(r_{\text{eq}}, r_{\text{sc}}) \cdot \sum_j \gamma_j^2 v_j(v_j - 1)$ using authenticated `SparseKZH3` claims.
     - Added `two_pow_alpha` to `prove_two_pow` / `verify_two_pow` (`T_two_pow(k) + alpha`) to enforce Shout Hamming-weight-1 (`row-sum = 1`), plus standalone `two_pow_bool_proofs` verified against `SparseKZH3` claims.
     - Fixed `NonStructuredExp::prove` and `verify` (`src/basicblock/exp.rs:147-215`) to check `expected_sum == out_claim.eval` and terminal `running_sum`.
   - **Complete `SparseKZH3` commitment & opening pipeline (`src/dag/mod.rs`, `src/util/poly.rs`):**
     - Fixed `SparseMLPoly::split_into_blocks` (`poly.rs:1350`) to pass `this_block_vars` instead of `block_size`.
     - Fixed `Dag::commit` (`mod.rs:659`) to push commitments for **all** `sparse_id` blocks (`0..ws.len()`).
     - Fixed `Dag::prove` (`mod.rs:804`) `reducer_edge_ids = vec![node.outputs[0]]` and `prove_range` input point lookup (`node_proofs[*n].1[0].point`).
     - Moved `edge_proofs` population **after** `prove_two_pow` and `prove_range`, populated true `aux_poly` evaluations, enabled `should_open` on committed final `Role::Output` edges, and verified exact `edge_proofs[e].claims == claims[e]` and `sparse_comms.len() == init[e].len()` in `Dag::verify`.
   - **Zero-slack `StructuredExp` remainder range check (`src/dag/builder.rs`, `src/bin/structured_exp.rs`):**
     - Added `add_nonneg_node_with_bits` (`rem_bits = ceil(log2(L))`, `10` bits at $s=10$ vs `20` bits default) enforcing both $r + \lfloor(L-1)/2\rfloor \ge 0$ and $\lfloor L/2 \rfloor - r \ge 0$, which pins $r \in [-\lfloor(L-1)/2\rfloor, \lfloor L/2 \rfloor]$ (`[-354, 355]` at $s=10$, width $710 = L$: **zero boundary slack** and exact completeness on half-way ties!).
     - Fixed `get_cached_inverses` (`poly.rs:424`) to `2.0_f64.ln()`, masked non-pow2 padding in `argmax_check` (`oneshot.rs:107`), and changed `structured_exp.rs` inputs to `-(0..1024)`.
   - **Fiat-Shamir & GKR claim-chaining (`src/dag/mod.rs`, `src/basicblock/*.rs`, `src/crypto/polycommit/*.rs`):**
     - Absorbed output claims, multi-input node claims, `Reducer` input claims, `middle_claims` (before `table_alpha`), and sparse selector evaluations (before booleanity challenges) into `Transcript`, plus `KZH2Commitment::to_transcript_bytes()`.
     - Linked `local_claims.last() == claims[out][0]` when `claims[out].len() == 1`, linked `NonNegative`/`ZeroCheck` sink claims, and enforced point/eval checks in `ChangeShape`, `ScaleDown`, `ScaleUp`, `ExpHelper`, `ClampLower`, `Einsum`, `Reducer`, and `Permute`.
2. **`81e5dd7`** — `test: add soundness audit regression suite and update unit tests` (`8` files, `+1022 / -554`).

---

### 4.2 Before vs. After Benchmark Table (`[EXECUTED]`)

All benchmarks were compiled in `--release` mode on Apple Silicon (`12` Rayon threads, `config.yaml` with `scale_factor_log: 10`, `table_commit_log: 4`, Arkworks BN254 `KZH3` + `SparseKZH3`) using **real cached SRS files** (`0.srs`..`22.srs`). Logs: [before_metrics_exact.txt](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/before_metrics_exact.txt), [after_metrics_exact.txt](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/after_metrics_exact.txt), [before_structured_exp.log](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/before_structured_exp.log), [after_structured_exp.log](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/after_structured_exp.log), [before_nanogpt.log](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/before_nanogpt.log), [after_nanogpt.log](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/after_nanogpt.log), [before_oneshot_gpt2.log](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/before_oneshot_gpt2.log), [after_oneshot_gpt2.log](file:///Users/ember/.gemini/antigravity-cli/brain/b77f54f8-022c-4e1f-bbd0-32160c629f0a/scratch/after_oneshot_gpt2.log).

#### Part A — Structural Commitment & Opening Counts and Exact Proof Sizes (Primary Metrics)

| Metric | `structured_exp` (`N=1024`) Before (`main`) | `structured_exp` (`N=1024`) After (`fix`) | `nanogpt` (`SEQ_LEN=1`) Before (`main` = Table 4) | `nanogpt` (`SEQ_LEN=1`) After (`fix`) | `oneshot_gpt2` (`S=2, V=256`) Before (`main`) | `oneshot_gpt2` (`S=2, V=256`) After (`fix`) |
|---|---:|---:|---:|---:|---:|---:|
| Honest `dag.verify(...)` | `true` | **`true`** | `true` | **`true`** | `true` | **`true`** |
| Forgery PoCs rejected (`7/7`) | `0 / 6` (`false` = 0%) | **`7 / 7` (`100%`)** | `0 / 6` | **`7 / 7` (`100%`)** | `0 / 6` | **`7 / 7` (`100%`)** |
| Total DAG edges | 38 | 45 | 993 | 1,049 | 3,080 | 3,248 |
| Dense `KZH3` commitments | 7 | 9 | 211 | 227 | 704 | 752 |
| Sparse `SparseKZH3` edges | 8 | 10 | 200 | 216 | 576 | 624 |
| Sparse witness blocks (`init`) | 30 | 36 | 774 | 822 | 2,224 | 2,368 |
| **Sparse blocks committed** | **8 / 30 (`26.7%`)** | **36 / 36 (`100%`)** | **200 / 774 (`25.8%`)** | **822 / 822 (`100%`)** | **576 / 2,224 (`25.9%`)** | **2,368 / 2,368 (`100%`)** |
| Dense `KZH3` opening proofs | 6 | 9 | 300 | 317 | 954 | 1,002 |
| **Sparse `SparseKZH3` openings** | **`0`** | **`73`** | **`0`** | **`1,652`** | **`0`** | **`4,760`** |
| **Total proof (`measure_total_proof_size`)** | **29,614 B (`28.92 KB`)** | **267,984 B (`261.70 KB`, `9.05×`)** | **364,886 B (`356.33 KB`)** | **1,876,870 B (`1.79 MB`, `5.14×`)** | **2,791,738 B (`2.66 MB`)** | **14,704,098 B (`14.02 MB`, `5.27×`)** |
| — `sumcheck_proofs` | 10,619 B (`10.37 KB`) | 10,664 B (`10.41 KB`) | 142,091 B (`138.76 KB`) | 142,451 B (`139.11 KB`) | 702,789 B (`686.32 KB`) | 703,869 B (`687.37 KB`) |
| — `opening_proofs` (`KZH3` + `SparseKZH3`) | 8,728 B (`8.52 KB`) | **237,272 B (`231.71 KB`, `27.2×`)** | 160,136 B (`156.38 KB`) | **1,655,280 B (`1.58 MB`, `10.3×`)** | 1,782,416 B (`1.70 MB`) | **13,620,400 B (`12.99 MB`, `7.64×`)** |
| — `range_proof` | 2,976 B (`2.91 KB`) | 10,080 B (`9.84 KB`) | 8,040 B (`7.85 KB`) | 13,344 B (`13.03 KB`) | 10,896 B (`10.64 KB`) | 23,016 B (`22.48 KB`) |
| — `two_pow_proof` | 576 B | 576 B | 576 B | 576 B | 576 B | 576 B |
| — `reducer_proofs` | 6,715 B (`6.56 KB`) | 9,392 B (`9.17 KB`) | 54,043 B (`52.78 KB`) | 65,219 B (`63.69 KB`) | 295,061 B (`288.15 KB`) | 356,237 B (`347.89 KB`) |
| **Full serialized proof** (incl. `Claim`s & `middle_claims`) | 79,718 B (`77.85 KB`) | **370,408 B (`361.73 KB`, `4.65×`)** | 987,662 B (`964.51 KB`) | **3,108,398 B (`2.96 MB`, `3.15×`)** | 5,947,802 B (`5.67 MB`) | **20,324,834 B (`19.38 MB`, `3.42×`)** |

#### Part B — Warm-SRS Wall-Clock Timings (Secondary Metrics, Apple Silicon, 12 Threads)

| Phase (`plonky2::util::timing`) | `structured_exp` Before | `structured_exp` After | `nanogpt` (`SEQ_LEN=1`) Before | `nanogpt` (`SEQ_LEN=1`) After | `oneshot_gpt2` (`S=2, V=256`) Before | `oneshot_gpt2` (`S=2, V=256`) After |
|---|---:|---:|---:|---:|---:|---:|
| Total `commit` (constants + inputs + sparse) | 0.0278s | 0.0673s (`2.42×`) | 0.1919s | 0.3996s (`2.08×`) | 118.3298s | 139.6320s (`1.18×`) |
| — Constant weight/mask commit (`offline`) | 0.0052s | 0.0089s | 0.1313s | 0.1462s | ~116.8s | ~117.0s |
| — Input + sparse witness commit (`online`) | 0.0226s | 0.0584s (`2.58×`) | 0.0606s | 0.2534s (`4.18×`) | ~1.5s | ~22.6s |
| Total `prove` (`GKR` + lookups + openings) | 0.0265s | 0.1576s (`5.95×`) | 0.1730s | 0.6408s (`3.70×`) | 6.7347s | 15.0485s (`2.23×`) |
| — `prove two_pow` | 0.0007s | 0.0002s | 0.0014s | 0.0003s | 0.0190s | 0.0125s |
| — `prove range` | 0.0104s | 0.0246s | 0.0376s | 0.0267s | 1.1052s | 1.2734s |
| — **`provide opening proofs`** | **0.0010s** | **0.1132s (`113×`)** | **0.0363s** | **0.4994s (`13.8×`)** | **3.0978s** | **11.1306s (`3.59×`)** |
| Online prover (`parse_timing.py`: online commit + prove) | 0.0491s | 0.2160s (`4.40×`) | **0.2336s** *(Table 4: `0.23s`)* | **0.8942s (`3.83×`)** | ~8.2s | ~37.6s |
| **Total `verify`** | **0.0081s** | **0.1752s (`21.6×`)** | **0.1384s** *(Table 4: `0.13s`)* | **1.4519s (`10.5×`)** | **1.2174s** | **7.4204s (`6.10×`)** |
| — `verify two_pow and range` (PIOP) | 0.076ms | 0.233ms | 0.728ms | 1.749ms | ~4.5ms | ~9.8ms |
| — **`verify irreducible edges` (PCS openings)** | **7.658ms** | **174.36ms (`22.8×`)** | **132.83ms** | **1,443.59ms (`10.9×`)** | **~1.20s** | **~7.39s (`6.16×`)** |

> [!IMPORTANT]
> **Why proof size & verification time jump by `5×–10×`:** Notice in Part A that `sumcheck_proofs` grows by `< 0.3%` (`138.76 KB -> 139.11 KB` on NanoGPT) and `range_proof` grows by only `5 KB`. Almost **100% of the increase** comes from `opening_proofs` (`156.38 KB -> 1.58 MB` on NanoGPT; `1.70 MB -> 12.99 MB` on GPT-2 Small), because each `SparseKZH3` opening proof carries `d_x` ($\mathbb{G}_1$), `C_y` ($\mathbb{G}_1$), an IPA vector, and `f_star`, and each block requires **two** evaluations (one at the table sumcheck challenge and one at the booleanity sumcheck challenge). Batching/folding `SparseKZH3` openings across shared points or adopting helper-free LogUp-GKR / `Rank1ProdExp` (see [EXP_AND_GQA_PRICING.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/EXP_AND_GQA_PRICING.md)) is the natural path to recover compact proofs soundly.

---

## 5. Additional Model-Arithmetization & Specification Findings

Beyond Bugs A–F (which we repaired directly in `fix/soundness-and-lookup-openings` without altering existing model DAG public interfaces), our audit identified five architectural/specification items that upstream maintainers and downstream users should be aware of:

1. **Unconstrained `SoftmaxConst` & `SigmoidConst` Advice and `RMSReciprocal` Sign Ambiguity (`[SOURCE]`):**
   - **Softmax (`src/basicblock/llama.rs:225-315`, `src/dag/gpt2.rs:133-139`, `src/dag/llama.rs:439-443`):** `SoftmaxConst::verify` returns `true`, and both `gpt2_attention` and `llama_attention` omit the $\sum_j \exp(s_j + c) \approx 2^s$ constraint (`// Soundness check (sum ≈ SF) belongs in a later pass.`, with no pass implementing it). Furthermore, `SoftmaxConst::run` (`basicblock/llama.rs:239`) allocates a 4D advice tensor `[B, H, S, S]` instead of row-broadcast `[B, H, S, 1]`, allowing independent per-entry shifts $c_{b,h,s,t}$ unless reshaped to `[B, H, S, 1]`. (Cross-ref [SEAM_AND_PRIOR_ART.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/SEAM_AND_PRIOR_ART.md) §0.4, including Zamir's Theorem 1 exposure on approximate $\sum \approx 1$ tolerances.)
   - **Sigmoid in GELU / SiLU (`src/basicblock/llama.rs:318-389`, `src/dag/builder.rs:289-330`):** `SigmoidConst` supplies advice $c$ claiming $\exp((x+c)/2^s) = \sigma(x/2^s)$ (`builder.rs:301` checks only $x + c \le 0$), with **no reciprocal / $(1 + \exp(-x)) \cdot y \approx 2^s$ constraint** binding $c$ to $x$.
   - **RMSNorm sign flip (`src/dag/llama.rs:85-100, 360-375`):** `llama_rms_norm` constrains $x_{\text{mean}} \cdot r^2 \in [2^s - 512, 2^s + 512]$ without `add_nonneg_node(r)`, permitting $-r$ (negating the entire normalized activation vector!).
2. **`ScaleDown` Mod-$p$ Uncommitted Quotient Wrap & `ScaleUp` Remainder Slack (`[SOURCE]`, `[DERIVED]`):**
   - **Quotient wrap (`src/dag/mod.rs:624, 1203-1210`, `src/basicblock/scale.rs:41-96`):** Intermediate dense `Role::Output` edges are not PCS-committed (`should_commit` returns `false` when consumed downstream), and `ScaleDown` range-checks only $\text{rem}_i = x_i - 2^{\Delta s} y_i + 2^{\Delta s - 1} \in [0, 2^{\Delta s})$ in $\mathbb{F}_p$ without bounding $y_i \in [-2^B, 2^B)$ in $\mathbb{Z}$. Shifting $\text{rem}_i \mapsto \text{rem}_i + \delta$ allows $y'_i \equiv y_i - \delta \cdot 2^{-\Delta s} \pmod p$; in `StructuredExp`, multiplying `exp_r` ($\Delta s = 15$) by `two_pow = 2^15` ($k = 0$) cancels $2^{-15} \pmod p$ into an exact integer perturbation $-\delta$! (Cross-ref [EXP_AND_GQA_PRICING.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/EXP_AND_GQA_PRICING.md) §1.2.)
   - **`ScaleUp` slack (`src/basicblock/scale.rs:134-145`, `src/dag/mod.rs:1211-1218`):** `ScaleUp` checks $2^{\Delta s} x_i - y_i + 2^{\Delta s - 1} \in [0, 2^{\Delta s})$ instead of enforcing exact $y_i = 2^{\Delta s} x_i$ directly via scalar multiplication in GKR (which requires **zero** sparse lookups and zero slack!).
3. **`ClampLower` $-14 \ln 2$ Tail Floor at Long Context (`[SOURCE]`, `[EXECUTED]`):**
   - `DagBuilder::exp` (`src/dag/builder.rs:129`) clamps inputs at $-C = -\lfloor 14 \ln 2 \cdot 2^s \rceil$, leaving $\exp(-C) \approx 2^{-14}$ (`2` ULPs in Q15) on causal-masked or negative-tail tokens rather than $0$ (`20.14%` Softmax denominator bias at $L = 4096$; cross-ref [EXP_AND_GQA_PRICING.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/EXP_AND_GQA_PRICING.md) §0).
4. **Proof-Size Wrapper Exclusions & Config Scale Factor (`[SOURCE]`):**
   - `extract_lookup_proof_only` (`src/dag/mod.rs:204-213`) strips `middle_claims` and `extract_sumcheck_proofs_only` (`lines 290-303`) strips intermediate `Claim` structs before calling `measure_total_proof_size` (explaining the difference between `1.79 MB` and `2.96 MB` on repaired `nanogpt` in Table 4.2A).
   - Repo `config.yaml` sets `scale_factor_log: 10` ($2^{10} = 1024$), whereas Paper §6.2 (`zkTransformer.txt:634`) describes $s = 15$.
5. **Paper Lemma 3.2 Soundness Formula (`[REFUTED: Lemma 3.2 formula (m+1)*v/|F|]`):**
   - Paper Lemma 3.2 (`zkTransformer.txt:370-388`) omits the outer Schwartz–Zippel term $(\mu_L + \mu_R + \mu_S)/|\mathbb{F}|$ and uses $v = \max_t |\mathcal{I}_t|$ instead of the actual sumcheck round count $\mu_S + \kappa$ (repaired and machine-checked in Lean 4 in [FORMAL_EINSUMCHECK.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/FORMAL_EINSUMCHECK.md) §1.3).

---

## 6. Proposed Folds for `docs/VERDICTS.md` (Not Edited In Place)

Per `AGENTS.md`, we do not edit `docs/VERDICTS.md` directly. Maintainer fold summary:
1. **`zkTransformer` (`uiuc-kang-lab/zkTransformer`, CCS 2026) artifact audit (`[SOURCE]`, `[EXECUTED]`):** Record that while `EinSumcheck` (`src/basicblock/einsum.rs`) and `KZH3`/`SparseKZH3` (`src/crypto/polycommit/`) are algebraically sound, `main` (`55344d7`) had six implementation soundness bugs (missing terminal sumcheck checks in `verify_range`/`verify_two_pow`, `74.2%` uncommitted sparse blocks + `0` `SparseKZH3` openings in `Dag::commit`/`Dag::prove`, missing $|r|$ bound in `StructuredExp`, missing Shout Hamming-weight-1 check in `TwoPow`, unabsorbed `middle_claims` in Fiat-Shamir, and unlinked fan-out-1 GKR claims). Consequently, Paper Table 4's `356.33 KB` / `0.23s` / `0.13s` NanoGPT numbers omitted `SparseKZH3` openings; with our verified surgical fix (`fix/soundness-and-lookup-openings`), NanoGPT (`SEQ_LEN=1`) measures **`1.79 MB` (`5.14×`), `0.894s` online prove (`3.83×`), and `1.452s` verify (`10.5×`)**.
2. **Model-level advice constraints (`[SOURCE]`):** Record that `SoftmaxConst` (`4D` advice without row-sum constraint) and `SigmoidConst` (unconstrained advice) in `zkTransformer` `main` require wiring reciprocal/normalization constraints (or exact integer Softmax as in `gptoss-int v0` to avoid Zamir's Theorem 1 slack).

---

## 7. Ready-to-File Upstream GitHub Issue & Pull Request Drafts

### 7.1 Draft GitHub Issue for `uiuc-kang-lab/zkTransformer`

**Title:** Soundness & completeness fixes for lookup sumcheck terminal checks, `SparseKZH3` openings, `StructuredExp` remainder bounds, and GKR/Fiat-Shamir claim binding

**Body:**
> Hi @bingjyuechen, @liliatang, @ddkang — congratulations on the CCS 2026 paper (`zkTransformer`) and thank you for open-sourcing the full Rust implementation! The `EinSumcheck` index-partitioning design (`F_1`, `F_{>=2}`, `S`) and unequal-variable-count sumcheck reduction in `src/basicblock/einsum.rs` are very clean.
>
> While studying the paper and running end-to-end experiments against `main` (`55344d7`), we noticed a set of implementation bugs in the lookup, `StructuredExp`, Fiat-Shamir, and DAG verification paths that currently cause `Dag::verify` to skip terminal checks and `SparseKZH3` openings (and break `Reducer` / `argmax_check` completeness in edge cases). We put together a self-contained regression test suite (`tests/test_soundness_audit.rs`) and a clean fix branch (`fix/soundness-and-lookup-openings`) where all 65 unit/integration tests and end-to-end `structured_exp`, `nanogpt`, and `oneshot_gpt2` binaries pass.
>
> ### Summary of Issues Found on `main` (`55344d7`)
>
> 1. **Missing terminal sumcheck verification (`src/dag/mod.rs:1241-1270, 1427-1428`, `src/basicblock/exp.rs:186-190`):**
>    `SumcheckVerifier::verify` checks per-round `msg[0] + msg[1] == running_sum` and returns `(Some(running_sum), challenges)` for the caller to verify against the terminal evaluation (as `Einsum::verify`, `Reducer::verify`, and `Permute::verify` do). However, `Dag::verify_range`, `Dag::verify_two_pow`, and `NonStructuredExp::verify` only checked `verification_result.is_some()`, and `verify_range` (`line 1250`) did not check `range_bool_proofs.len()`.
> 2. **Sparse lookup commitments & `SparseKZH3` openings (`src/dag/mod.rs:659, 804, 854-858, 1358, 1368, 1378, 1480`, `src/util/poly.rs:1350`):**
>    - In `Dag::prove` (`line 854`), `edge_proofs` copied `claims` *before* `prove_two_pow` (`line 857`) and `prove_range` (`line 858`) pushed their selector claims (which also had placeholder `eval: F::zero()`), resulting in `0` `SparseKZH3` opening proofs being emitted or checked.
>    - In `Dag::commit` (`line 659`), `if sparse_commitments[i].is_none()` committed only `sparse_id == 0` and skipped `sparse_id >= 1` on multi-block range decompositions.
>    - In `SparseMLPoly::split_into_blocks` (`src/util/poly.rs:1350`), `SelectionPolynomial::new` passed `block_size` (`4`) instead of `this_block_vars` on narrower final blocks (e.g. `ScaleDown(20, 10)` where `10 = 4 + 4 + 2`).
>    - In `Dag::prove` (`line 804`), `reducer_edge_ids = vec![edge_ids[edge_ids.len() - 1]]` selected `node.outputs[1]` (sparse `aux`) instead of `node.outputs[0]` on 2-output nodes (`ExpHelper`, `ScaleDown`, `ScaleUp`) with fan-out > 1, and `prove_range` (`line 1368`) used `claims[inp].last()` instead of `node_proofs[*n].1[0].point`.
> 3. **Missing `|r| <= 2^s ln 2 / 2` remainder range check in `StructuredExp` (`src/dag/builder.rs:341-350`):**
>    Paper §4.4 specifies bounding `|r| <= 2^s ln 2 / 2` alongside `k in [0, 15]`, which was not yet wired in `DagBuilder::exp`. Also aligned `get_cached_inverses` (`src/util/poly.rs:424`) from `2.0_f32.ln()` to `2.0_f64.ln()` (matching `exp.rs:33`) and updated `src/bin/structured_exp.rs:55` to feed non-positive inputs `-(0..1024)`.
> 4. **Shout Hamming-weight-1 (`row-sum == 1`) & booleanity in `TwoPow` (`src/dag/mod.rs:1388-1486`):**
>    Added `two_pow_alpha` (`T_two_pow(k) + alpha`) to `prove_two_pow` / `verify_two_pow` (matching `prove_range`'s `+ alpha` technique) so all-zero or multi-one selector rows cannot pass, plus standalone booleanity verification when `self.range` is empty.
> 5. **Fiat-Shamir transcript bindings & GKR claim chaining (`src/dag/mod.rs`, `src/basicblock/*.rs`, `src/crypto/polycommit/kzh2.rs`):**
>    - Absorbed `middle_claims` into `Transcript` *before* squeezing `table_alpha`, `table_beta`, `table_gamma` (preventing adaptive linear cancellation across blocks), along with output, node, `Reducer`, and sparse selector claim evaluations and `KZH2Commitment::to_transcript_bytes()`.
>    - Linked `local_claims.last() == claims[out][0]` when `claims[out].len() == 1`, linked `NonNegative`/`ZeroCheck` sink claims, added input point/eval checks in `ChangeShape`, `ScaleDown`, `ScaleUp`, `ExpHelper`, `ClampLower`, `Einsum`, `Reducer`, and `Permute`, opened committed final `Role::Output` edges, and verified `edge_proofs[e].claims == claims[e]`.
>
> *(Follow-up design note for future work: `SoftmaxConst` in `src/basicblock/llama.rs:239` currently allocates `[B, H, S, S]` without the `sum ≈ SF` constraint noted in `src/dag/llama.rs:440`, and `SigmoidConst` has no reciprocity check yet; we left model-level advice blocks untouched in this PR to keep the diff surgical.)*
>
> We have a clean PR ready with these fixes and `tests/test_soundness_audit.rs` — happy to open it or adjust anything to match your preferred conventions!

---

### 7.2 Draft Pull Request Description for `fix/soundness-and-lookup-openings`

**Title:** `fix: enforce lookup sumcheck terminal checks, SparseKZH3 openings, StructuredExp remainder bounds, and Fiat-Shamir/GKR claim bindings`

**Body:**
> ## Summary
> This PR resolves six soundness and completeness issues across the lookup, `StructuredExp`, Fiat-Shamir transcript, and GKR DAG verification paths, repairs the existing unit tests under `tests/`, and adds an 11-test regression suite (`tests/test_soundness_audit.rs`).
>
> ## Key Changes
> - **Lookup terminal sumcheck verification (`src/dag/mod.rs`, `src/util/poly.rs`, `src/crypto/sumcheck/linear_prover.rs`, `src/basicblock/exp.rs`):**
>   - Group `Range` table sumchecks by exact block bit-width (`this_block_vars`) and verify terminal `running_sum` against `folded_aux_eval * (evaluate_range_structured(&r_k) + alpha)` in $O(\log N)$ field ops.
>   - Verify `SparseBoolSumcheckProver` terminal evaluations against authenticated `SparseKZH3` opening evaluations (`\widetilde{eq}(r_eq, r_sc) * \sum_j \gamma_j^2 v_j (v_j - 1)`) and enforce exact booleanity proof counts.
>   - Enforce Shout Hamming-weight-1 (`row-sum == 1`) in `TwoPow` via `two_pow_alpha`-shifted table folding (`evaluate_two_pow_structured(&r_k) + alpha`) plus standalone `TwoPow` booleanity sumchecks.
>   - Fix `NonStructuredExp::prove` / `verify` expected sum and terminal evaluation check.
> - **Multi-block `SparseKZH3` commitments & openings (`src/dag/mod.rs`, `src/util/poly.rs`):**
>   - Preserve exact final-block `this_block_vars` in `SparseMLPoly::split_into_blocks` (fixing partial-block bit-width inflation on e.g. `ScaleDown(20, 10)` and `ScaleUp(10, 15)`).
>   - Commit all `sparse_id` blocks in `Dag::commit` (removing `if sparse_commitments[i].is_none()` early skip).
>   - Fix `Reducer` `edge_id` selection on 2-output nodes (`node.outputs[0]` instead of `edge_ids.last()`) and fan-out input point selection in `prove_range`.
>   - Populate `edge_proofs` *after* `prove_two_pow` and `prove_range` with true `SparseMLPoly` evaluations, open final `Role::Output` commitments, and verify `edge_proofs[e].claims == claims[e]` on all committed edges.
> - **`StructuredExp` & `argmax_check` (`src/dag/builder.rs`, `src/dag/oneshot.rs`, `src/bin/structured_exp.rs`):**
>   - Add zero-slack remainder range bounds `r in [-floor((L - 1) / 2), floor(L / 2)]` (`L = round(2^s ln 2)`) via `add_nonneg_node_with_bits`.
>   - Align `get_cached_inverses` to `2.0_f64.ln()`, mask non-power-of-two padding in `argmax_check`, and use non-positive inputs `-(0..1024)` in `src/bin/structured_exp.rs`.
> - **Fiat-Shamir & GKR claim binding (`src/dag/mod.rs`, `src/basicblock/*.rs`, `src/crypto/polycommit/*.rs`):**
>   - Absorb output, multi-input GKR, `Reducer`, `middle_claims`, and sparse lookup `Claim.eval`s into `Transcript` before squeezing downstream challenges; implement `KZH2Commitment::to_transcript_bytes()`.
>   - Enforce GKR fan-out-1 output claim linking, `NonNegative`/`ZeroCheck` sink claim linking, and input point/eval checks across `ChangeShape`, `ScaleDown`, `ScaleUp`, `ExpHelper`, `ClampLower`, `Einsum`, `Reducer`, and `Permute`.
>
> ## Verification & Benchmarks
> - `cargo +nightly test --release`: **65 passed, 0 failed** across all 8 test suites (including 4 end-to-end honest circuits and 7 negative forgery regression suites in `tests/test_soundness_audit.rs`).
> - End-to-end release binaries with real BN254 SRS (`config.yaml`, `SF_LOG=10`, 12 threads):
>   - `structured_exp`: `verified: true` (`36/36` sparse blocks committed, `73` `SparseKZH3` openings, `261.70 KB`).
>   - `SEQ_LEN=1 nanogpt`: `verified: true` (`822/822` sparse blocks committed, `1,652` `SparseKZH3` openings, `1.79 MB`, `0.64s` prove, `1.45s` verify).
>   - `SEQ_LEN=2 PROMPT_LEN=1 VOCAB_SIZE=256 SKIP_AUTOREGRESSIVE=1 oneshot_gpt2`: `verified: true` (`2,368/2,368` sparse blocks committed, `4,760` `SparseKZH3` openings, `14.02 MB`, `15.05s` prove, `7.42s` verify).
