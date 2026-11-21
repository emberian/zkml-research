# Decision — `zktransformer_2026_11_20`

1. **ADOPT `EinSumcheck` (`F_1 / F_{>=2} / S` multilinear contraction compiler) into `minidregg` and our `catgrad` lowering pass:**
   - Ready-to-apply Lean 4 patch: [formal/minidregg-einsumcheck.patch](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/formal/minidregg-einsumcheck.patch) (`0 sorry`, `0 axiom`).
   - Primary targets for `gptoss-int v0`:
     - **Un-repeated GQA** (`tgrd,ngd -> tgrn` and `tgrn,ngd -> tgrd`, `F_1` intra-group query index, `F_{\ge 2} = \{g\}` 3-bit KV group): `8×` attention sumcheck multiplication reduction (`12 -> 9` rounds) with zero KV replication.
     - **Native MXFP4 3-operand `EinSumcheck`** (`ikb,jkb,jk -> ij`): eliminates offline weight dequantization, runs at exact univariate round degrees `(2^5, 3^7, 3^{\log_2 N})` under `b -> k -> j` (fitting landed cubic sumcheck), and cuts `gpt-oss-20b` MoE committed felts by `1.94×` (`5.49–6.82×` bits vs 29-bit dequantized spec window; `2.46–3.06×` bits like-for-like vs measured spread).

2. **REJECT `StructuredExp` for our stack (`0 / 25` grid points):**
   - Keep `gptoss-int v0`'s direct exact integer `EXP_TAB` (`2,840` entries, padded to $4,096$, $b = 12$) backed by helper-free fraction-tree LogUp-GKR (**D1b**, `5×` fewer committed cells than committed-inverse **D1a**) over prime fields, or 4-bit `BinaryShout` (**D2_w4**) over binary tower fields.
   - Reserve 1-rescale `Rank1ProdExp` (`(15, 15) -> 15` hi-lo subtable decomposition) only for small batch counts below $m^*(15) \approx 8,032$ cells on BabyBear (or wide tables $b \ge 20$).

3. **UPSTREAM CONTRIBUTION FILED:**
   - Opened Issue `https://github.com/uiuc-kang-lab/zkTransformer/issues/1` and Pull Request `https://github.com/uiuc-kang-lab/zkTransformer/pull/2` on `uiuc-kang-lab/zkTransformer` with all core verifier, lookup-opening, `ClampLower` advice-commitment, and PCS `VerifierKey` fixes (`67/67` tests passing, `structured_exp` / `nonstructured_exp` / `nanogpt` verified end-to-end).
