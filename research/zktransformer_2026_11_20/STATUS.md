# Status — `zktransformer_2026_11_20`

**State:** COMPLETE (2026-11-20)  
**Consolidated Evidence Note:** [notes/zktransformer-verdicts.md](file:///Users/ember/dev/zkml-research/notes/zktransformer-verdicts.md)

## Upstream Contributions (`uiuc-kang-lab/zkTransformer`)

- **Fork Branch:** `https://github.com/emberian/zkTransformer/tree/fix/soundness-and-lookup-openings`
- **Upstream Issue:** `https://github.com/uiuc-kang-lab/zkTransformer/issues/1`
- **Upstream Pull Request:** `https://github.com/uiuc-kang-lab/zkTransformer/pull/2`

## Completed Artifacts in `research/zktransformer_2026_11_20/`

1. **Lean 4 Machine-Checked `EinSumcheck` Formalization (`lean-einsumcheck`):**
   - [FORMAL_EINSUMCHECK.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/FORMAL_EINSUMCHECK.md)
   - [formal/Theory/ZkmlEinsum.lean](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/formal/Theory/ZkmlEinsum.lean) (`0 sorry`, `0 axiom`, `17` `#guard_msgs` pins)
   - [formal/Assurance/ZkmlEinSumcheck.lean](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/formal/Assurance/ZkmlEinSumcheck.lean) (`0 sorry`, `0 axiom`, `28` `#guard_msgs` pins)
   - [formal/minidregg-einsumcheck.patch](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/formal/minidregg-einsumcheck.patch) (`git -C /Users/ember/dev/minidregg apply --check` passed `rc = 0`)
2. **Deterministic `exp` Subtable & GQA Pricing (`exp-subtable-lab`):**
   - [EXP_AND_GQA_PRICING.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/EXP_AND_GQA_PRICING.md)
   - [experiments/exp_pricing.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/exp_pricing.py), [experiments/rank1_prod_exp.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/rank1_prod_exp.py), [experiments/einsum_gqa_counts.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/einsum_gqa_counts.py) (+ CSV/JSON outputs)
3. **`catgrad` Lowering Seam, Native MXFP4 `(2^5, 3^7, 3^{\log_2 N})` `EinSumcheck` & Prior Art (`catgrad-lit-seam`):**
   - [SEAM_AND_PRIOR_ART.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/SEAM_AND_PRIOR_ART.md)
   - [experiments/verify_seam_and_mxfp4.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/verify_seam_and_mxfp4.py)
4. **Upstream Code Audit & Cross-Family Peer Reviews:**
   - [UPSTREAM_AUDIT.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/UPSTREAM_AUDIT.md) *(initial lane report; superseded on cross-family corrections C1/C2/M1/Lemma-3.2 framing by [notes/zktransformer-verdicts.md](file:///Users/ember/dev/zkml-research/notes/zktransformer-verdicts.md))*
   - [CROSSFAMILY_REVIEW_CODEX_ASTRA.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/CROSSFAMILY_REVIEW_CODEX_ASTRA.md) (`codex` `gpt-6.2-astra`)
   - [CROSSFAMILY_REVIEW_CLAUDE_FABLE.md](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/CROSSFAMILY_REVIEW_CLAUDE_FABLE.md) (`claude` `claude-fable-5-2`)
