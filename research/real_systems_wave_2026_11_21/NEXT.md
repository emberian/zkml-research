# NEXT — `real_systems_wave_2026_11_21`

## Immediate Follow-Up Priorities

1. **Interactive End-to-End Verifiable Local Agent Daemon (`Qwen3.8-27B` Metal + `U1` Stream + `policy_transducer` + `prove_private_cert`):**
   - Wire `/opt/homebrew/bin/llama-server` (`Qwen3.8-27B-UD-Q4_K_XL.gguf` at `16.75 GiB` RSS on M2 Max) directly to `minidregg/prover`'s `StreamingRedactor` + `CompiledByteLl1Parser` + `prove_private_cert` and `native/qwen35audit`'s `U1` boundary commitment stream (`29–43 µs/tok`), emitting a single verifiable receipt bundle for every local tool-call turn.
2. **Multi-Round `WHIR` Folding on Leaf Receipts (`darkvfhe` & `qwen35audit`):**
   - Replace 1-step Ligero row evaluation (`4.5 MiB` in `qwen35audit` at `t_cols=208`; `2.55–22.21 MiB` in `darkvfhe` at `t_cols=312`) with 2–3 `WHIR` folding rounds + `GMask` univariate sumcheck masking to compress leaf proofs below `500 KiB`–`1.5 MiB` with full sumcheck-round HVZK.
3. **Algebraic `Tower256` Transition Quotient + `BinaryShout` Lookup in `Tower256PrivateContentCert`:**
   - Upgrade `PrivateReceipt` from `2 + stepQueries` Fiat–Shamir step openings (`((L-1)/L)^q` soundness) to an algebraic `Tower256` transition quotient + `BinaryShout` delta lookup before additive FRI, achieving `2^-100` transition soundness with zero single-byte step disclosure (`docs/LEAF-PROVER-DECISION.md` §6.2).
4. **Homomorphic `GDN` Outer-Product State Update in `darkvfhe::dark_gdn`:**
   - Update `Enc_pk(S_t)` directly in BFV via hoisted outer-product + `relinearize_ct3` so the 3-custodian `Dark-GDN` resident avoids the per-turn `S2E` crossing (`6` ciphertexts) and `~3 s` offline state PCS refresh.
5. **Maintainer Folds into `docs/VERDICTS.md` & `docs/LEAF-PROVER-DECISION.md`:**
   - Fold the proposed verdict updates from all 5 Wave-6 notes (`notes/{verified-ast-extraction-and-redaction-transducers,tower256-private-content-certificates,darkvfhe-succinct-pcs-and-custodian-gdn,real-qwen35-pretrained-zk-audit,sota-2026-hardware-fit-model-selection}.md`), including mandatory per-head `u_scale[h]` on pretrained GDN (`38×` KL gain), `8 -> 0` (`-0.0`) nibble canonicalization for `MXFP4`, and `8`-bit power-of-two GCD scale normalization for `NVFP4` `F8_E4M3` lifts.
