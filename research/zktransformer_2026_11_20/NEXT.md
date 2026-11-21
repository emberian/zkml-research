# Next Steps — `zktransformer_2026_11_20`

1. **Fold Lean `EinSumcheck` Artifact into `minidregg` (Maintainer Action):**
   - Apply [formal/minidregg-einsumcheck.patch](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/formal/minidregg-einsumcheck.patch) cleanly to `/Users/ember/dev/minidregg` (`git apply --check` verified `rc = 0`) and wire `Theory.ZkmlEinsum` and `Assurance.ZkmlEinSumcheck` into `minidregg`'s root build targets.
   - Extend `Theory/ZkmlTensorOps.lean` (`TOp`) with a certified lowering pass to `EinsumContractionSpec` covering un-repeated GQA (`tgrd,ngd -> tgrn`, `tgrn,ngd -> tgrd`) and native MXFP4 3-operand block-scaled matmul (`ikb,jkb,jk -> ij`).

2. **Benchmark `(2^5, 3^7, 3^{\log_2 N})` MXFP4 `EinSumcheck` & Un-Repeated GQA in `breadstuffs`:**
   - Implement the $b \to k \to j$ variable-elimination schedule for native MXFP4 `ikb,jkb,jk -> ij` (`SEAM_AND_PRIOR_ART.md` §5.2), which halves the $N \cdot K_{\text{blk}} \cdot 32$ `Q` bookkeeping array in 5 degree-2 rounds before the 7 degree-3 $k$-rounds and $\log_2 N$ degree-3 $j$-rounds, and compare wall-clock prover throughput + BaseFold/WHIR commitment memory against dequantized `(Wh, Wl)` 2-limb matmul.
   - Implement un-repeated GQA (`F_1` intra-group query head binding, `F_{\ge 2} = \{g\}` 3-bit shared KV group) for `gpt-oss-20b` (`EXP_AND_GQA_PRICING.md` §3).

3. **Nonlinear Lookup Implementation Choice for `gptoss-int v0`:**
   - Keep `gptoss-int v0`'s direct 4,096-entry exact integer `EXP_TAB` ($b = 12$) backed by helper-free fraction-tree LogUp-GKR (**D1b**, `5×` fewer committed cells than committed-inverse **D1a**) over prime fields or 4-bit `BinaryShout` (**D2_w4**) over binary tower fields.
   - Reserve `Rank1ProdExp` (`(15, 15)` hi-lo outer-product subtable decomposition) only for single-layer / short-context regimes ($m < m^*(b)$) or wider fixed-point domains ($b \ge 20$). Do **not** adopt `StructuredExp`.

4. **Fold Approved Verdicts into `docs/VERDICTS.md` (Maintainer Action):**
   - Review the proposed folds in [notes/zktransformer-verdicts.md](file:///Users/ember/dev/zkml-research/notes/zktransformer-verdicts.md) (§1 Zamir/Hollow-LLM case study, §3 native MXFP4 & GQA `EinSumcheck`, §5 `Rank1ProdExp` & `StructuredExp` lookup pricing ledger).
