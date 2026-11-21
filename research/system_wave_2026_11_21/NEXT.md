# NEXT — `system_wave_2026_11_21`

## 1. Ready-to-Land Maintainer Folds & Follow-Ups

1. **`docs/VERDICTS.md` Proposed Maintainer Folds (`AGENTS.md` Rule):**
   - **§3 & §7.5 (`vFHE` / `Hole B`):** Record `HoistedB61` + `Exact-Garner-15` flipping `FHE vs MPC` at `d = 4096` (`21.50–25.08 Gbit` strict `digits61` vs `31.50 Gbit` MPC at `9.5×` smaller wire), mechanized in both `minidregg` (`Theory/BfvHoistedRescale.lean`) and `breadstuffs` (`Bfv/ScaleLiftRefinement.lean`), and benchmarked in native Rust (`native/darkvfhe`: `118.1 ms` warm `d=4096` FHE matvec, `1.75–2.23 s` full `HoistedB61+D1b` prove, `24.55 ms` succinct verify, `8.00 s/step` `Hoist(b, τ=64)` SGD, `3.91 s` `Dark-vPIR`).
   - **§3 & §5 (`Qwen3.8-Flash-Next`):** Record `75%` `Gated DeltaNet` (`O(1)` `0.211 GiB` state, depth-1 crossing, `1.514 ms`/layer native Rust `Gruen` WY prove), `25%` `QSA` (`K = 2048`, BabyBear `C3/C5` Top-`K_B` traps), `97 × GR` (`max|R| <= 140`, FP8-safe), `51.2B` PLE (`Poseidon2 Merkle` / `2P-DPF`), and the E2E 4-layer integer block cryptographic prover (`qwen38_int_block_e2e_prover.py`, `0.9893` 4L `cos_sim`, `7/7` forged transcripts rejected).
   - **§9 (`Selvage` W4 & `CERTIFICATES.md`):** Mark `Selvage` W4 (`AdvOpeningScheme` + `ContentScheme`) and `CERTIFICATES.md` `P1`–`P9` mechanized across `minidregg` (`Selvage/ContentCertificate.lean`, `Assurance/CertificateComposition.lean`, `2,508` lines) and `breadstuffs` (`PaddedAbsence.lean`, `AttestedAutomatonWeld8Closure.lean`).

2. **Next High-Value Engineering Milestones:**
   - **Wire `darkvfhe` into `darkproof` WHIR/Ligero PCS (`native/`):** Replace `darkvfhe`'s SHA-256 column-root oracle seam with `darkproof::pcs::PcsParty` coset LDE openings to emit end-to-end custodian wire bundles in `darktrain` / `darkdeploy`.
   - **Demo Prototype ("Zero-Leak Repo Auditor" / "Dark Hermes" Chunk Runner):** Connect `minidregg/prover` (`gruen_einsum` + `deltanet_wy` lifted to `field6.rs` / `Ext4`) with real `Qwen/Qwen3.8-Flash-Next-FP8` shard weights + `ContentCertificate` (`Produced ∘ Absent ∘ FormOK`) receipts.
   - **Post-Mirror-Sync `PRISM` (`ePrint 2026/1956`) Read:** Once `/Users/ember/dev/gh/forks/IACR-eprint-mirror/` syncs past `2026/1861`, evaluate composing `PRISM`'s MF-PCS with `HoistedB61`'s `128` group certificates.
