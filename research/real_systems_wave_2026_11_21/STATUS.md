# STATUS — `real_systems_wave_2026_11_21`

**Completed:** 2026-11-21
**Standard:** Zero toys, zero placeholders — real pretrained `Qwen3.8-Flash-Next` (`FP8` / `NVFP4-CSF` / `MLX-4bit`), `Qwen3.8-27B` (live Apple Metal `llama-cli` v0.9.0 + real `MXFP4`/`NVFP4` safetensors), and 24-layer `Qwen3.5-0.8B` execution; real succinct 128-bit `Ext3` and `BabyBear Ext4` Coset-RS/Ligero PCS proofs; real private-witness `Tower256` `cSHAKE256` receipts across `.accept`, `.count`, `.bound`; and Lean-4.35.0-proved LL(1) AST extraction + secret-redaction transducers.

## Completed Lanes (`5/5` `Carbon` Top-Level Workers + `7` `Neon` Audit/Research Helpers)

| Lane | Worker (+ `Neon` Helpers) | Verified Deliverables | Status |
|---|---|---|---|
| **1. Verified LL(1) Parse-to-AST Extraction & Deterministic Secret-Redaction Transducer** | `mini-ast-transducer` (`transducer-neon-audit`) | `minidregg/Theory/VerifiedAstTransducer.lean` (`1,970L`, `12` pins) · `minidregg/Compiler/PolicyAstTransducerEmit.lean` (`507L`, `8` pins) · `minidregg/prover/src/policy_transducer.rs` (`1,984L`) · `notes/verified-ast-extraction-and-redaction-transducers.md` | **DONE** (`exit 0`, `4/4` conformance + `532 MB/s` redact) |
| **2. Private-Witness Succinct `Tower256` Content Certificates (`.accept`, `.count`, `.bound`)** | `mini-tower256-zkcert` (`zkcert-neon-audit`) | `minidregg/Compiler/Tower256PrivateContentCert.lean` (`1,951L`, `13` pins) · `Compiler/Tower256PrivateCertConformance.lean` (`128L`, `1` pin) · `minidregg/prover/src/tower256_private_cert.rs` (`2,609L`) · `src/bin/prove_private_cert.rs` · `notes/tower256-private-content-certificates.md` | **DONE** (`exit 0`, `51.4 ms` prove / `1.04 ms` verify @ `4 KiB`, `0` `>=6B` leaks) |
| **3. Succinct 128-Bit Coset-NTT PCS for `HoistedB61` & 3-Custodian Dark `GDN` + `vPIR` Engine** | `darkvfhe-succinct-gdn` (`pcs-gdn-neon-audit`) | `native/darkvfhe/src/{succinct_pcs,dark_gdn,cert}.rs` · `src/bin/dark_resident_bench.rs` · `tests/succinct_pcs_and_dark_gdn.rs` · `notes/darkvfhe-succinct-pcs-and-custodian-gdn.md` | **DONE** (`exit 0`, `12/12` suites, `56.6x` wire cut, 4-turn `max|diff|=0` 3-custodian `GDN+vPIR`) |
| **4. Real Pretrained `Qwen3.5-0.8B` (`24L`) + `Qwen3.8-Flash-Next` (`FP8`/`NVFP4`/`MLX-4bit`) & Native `Ext4` `U1` Auditor** | `real-qwen35-zk-audit` (`qwen35-neon-eval`, `qwen38fn-neon-slice`) | `experiments/real_qwen35_gdn_eval.py` · `native/qwen35audit/` (`Ext4` Gruen + `SuccinctExt4Pcs` + `U1` + ZK `Absent` DFA) · `notes/real-qwen35-pretrained-zk-audit.md` | **DONE** (`exit 0`, `FP8 KL = 0.00555 nats`, `5/5` Rust tests, `6/6` attacks refused) |
| **5. Nov-2026 Hardware-Fit SOTA Model Selection (`<= 96 GiB`) & Live Apple Metal Run** | `sota-hw-model-hunter` (`scry-hf-models`, `scry-community-sota`) | `experiments/sota_2026_hw_fit_and_live_run.py` · cached `Qwen3.8-27B-UD-Q4_K_XL.gguf` (`17.66 GB`, `80.8–111.0 tok/s` prefill / `7.3–8.2 tok/s` decode @ `16.75 GiB` RSS) · `notes/sota-2026-hardware-fit-model-selection.md` | **DONE** (`exit 0`, E2E Metal -> `RewriteCert` -> LL(1) AST) |

## Consolidated Metered Search Ledger (`AGENTS.md` Compliance)
- **`scry.py` (`research.py scry`):** `39` executed SQL queries + `3` `schema` calls (`1` coordinator + `2` `sota-hw-model-hunter`)
- **`kagi.py` (`research.py kagi`):** `8` queries (`2` coordinator + `6` `scry-community-sota`)
- **`eprint.iacr.org` direct PDF downloads:** `0` (strict zero-download compliance)
