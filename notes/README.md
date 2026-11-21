# notes/ — what is in here and how to read it

**Start with `docs/VERDICTS.md`.** It is the single current-truth file: what we
believe now, in final form, no history, no ⚠ markers. Open questions are its §7.

> **The rule: where a note and VERDICTS disagree, VERDICTS wins and the note is
> history.** Notes are *evidence* — what a lane measured, derived, or read at
> source. VERDICTS is the *conclusion*. Cite a note for its measurement; cite
> VERDICTS for what we think.

**When a note is wrong, the fix is ordering, not deletion.** Current truth goes
at the top, superseded reasoning stays below it, and every measurement is kept —
a refuted claim with its refutation attached is how we stop re-deriving it. If a
file's *central* claim dies, it moves to `archive/` rather than being edited into
something it never said.

---

## The five things that were contradicting each other, and where they now live

| question | answer | files that hold it |
|---|---|---|
| **Is the prover hash-bound?** | ⚑ **OPEN.** Derived 94% at lb=6, measured 19–40% at ρ=1/2. One profiling run settles it. VERDICTS §7.1 | `prover-floor.md` (derived side), `fast-systems-recon.md` (measured side) — both lead with the contradiction |
| **Which field?** | **BabyBear deployed, both trees. KoalaBear recommended and UNEXECUTED.** Never "our KoalaBear parameters" | `field-choice-verdict.md`, `hash-verdict.md`, `koalabear-limb*.md` |
| **"Conjectured 130"?** | **CBR-shaped, from a regime deleted upstream. Never quote it.** Ours is UDR 34 / JBR 73 | `two-regime-calculator.md`, `grey-lit-corrections.md` §4 |
| **The `fold_add` ratio** | **= B, PROVER-SIDE ONLY**, and deployed B is **4** (4.2×), not 512 | `fold-as-opening-verdict.md`, `fold-as-opening.md` §0 |
| **eprint 2026/1390** | A **lookup-specific restricted-model separation** — *not* a general Ω(m) commitment floor. The floor we hold is the `Ω(\|w\|)` extraction argument | `boundary-statements.md` §2.5(b), `virtualization-verdict.md` §4 |

## Evidence — what each file measured

**Prover cost and proof-system design**
- `prover-floor.md` — the cost function per committed felt; sumcheck is 2–17% of prover time; lb=6 is 2.9× off the optimum
- `fast-systems-recon.md` — six systems read at source, hashing/LDE timed here; the base→ext 2.95× cliff; our soundness posture against five production systems
- `boundary-statements.md` + `virtualization-verdict.md` — the exchange rate: one committed base felt ≈ 3,120 mults at lb=4, 12,331 at lb=6; virtualizing one ≈ 40/layer
- `two-regime-calculator.md` — the regime in the type, 22 theorems, 0 sorry; the CBR withdrawal
- `multilinear-pcs-landscape.md` + `multilinear-pcs-verdict.md` — the seam is one `RbrKnowledgeSoundness` instance; route is BaseFold at RS
- `gkr-substrate-design.md` + `gkr-substrate-findings.md` — the Lean-authored substrate design; our proximity leg has no query-count term
- `fold-as-opening.md` + `fold-as-opening-verdict.md` — built and measured; three of four briefed numbers wrong
- `formalization-frontier.md` — ArkLib measured: 416 sorry-tainted declarations, 133 security results
- `avigad-stwo-verdict.md` — the StarkWare/Avigad formalization is the twin, and carries a real theorem anyway
- `lookup-ram-verdicts.md` — the lookup/RAM frontier, both halves; the three-member one-hot law (Twist/Shout is closed to our stack, by its authors)
- `spain-celer-verdicts.md`, `ozaki-limbs-verdict.md` — read at source, both rejected as imports with the reason kept
- `field-choice-verdict.md`, `hash-verdict.md`, `field-recursion-evidence.md`, `koalabear-limb*.md`, `poseidon2-audit-verdict.md` — the field/hash campaign
- `grey-lit-corrections.md` — five of our verdicts refuted from outside the eprint corpus
- `sis-lattice-verdict.md`, `two-ladder-composition.md`, `shared-arithmetic.md`, `system-primitives.md`, `joint-representation.md` — adjacent design threads

**FHE / vFHE**
- `h2-verdict.md` — measured both directions: 109-bit joint prime is a net loss, 61-bit wins, costs one depth level
- `coeff-matmul-landed.md` — built: 12 bits/matmul split-sign, depth 2 after, 466 µs at 512×31
- `fhe-core-theory.md` — the secret is CBD(20); the honest security ledger
- `kpz-noop-and-the-model-gap.md` — the KPZ fix is a no-op, derived and measured
- `fhe-scout-verdicts.md` — the FHE frontier scan with its coverage gaps named
- `hpu-seam-study.md` — 162,770 lines of Zama SystemVerilog read; the ring is ℤ/2⁶⁴
- `ring-hash-design.md`, `ring-hash-cryptanalysis.md`, `ring-hash-{build,tau}-verdict.md`, `ring-hash-scripts/` — build it, τ=2; FS 52% → 4%
- `vfhe-hoisted-certificate-breakthrough.md` (+ `research/vfhe_sota_2026_11_21/experiments/vfhe_hoisted_b61_and_pir.py`) — `HoistedB61` (`6,144 -> 128` hoisted sum-before-rescale matvec certs + fused `d`-free polynomial identity + `Direct-20` / zero-slack `Exact-Garner-15` canonical lifts + `τ=64` temporal outer-product hoisting w/ exact SPDZ bilinear correction): slashes `d=4096` matvec certs `25.3×–34.2×` (`601.4×–151,936×` on dark `vPIR`), fits in existing `k=5` primes (`7.65×` smaller rounding noise), and **flips `FHE vs MPC` at `d=4096`** (`Hoist-FHE(b, τ=64)` = `11.08 Gbit` packed / `21.50–25.08 Gbit` strict `digits61` vs `31.50 Gbit` MPC at `9.5×` smaller wire; `Inference-Only vFHEML` = `3.73 Gbit` packed / `10.78 Gbit` `digits61` at `17.7×` smaller wire); audits `Laminate` (`2025/2285`), `Lasagne` (`2026/857`), `Zama` (`2026/1127`), `Quasar` (`2026/1839`), `LatticeBlindFold` (`2026/1857`), `YPIR` (`2024/270`), `SandwichPIR` (`2026/1816`)
- `native-hoisted-b61-rust-benchmarks.md` (+ `native/darkvfhe/`) — multithreaded (`rayon`) native Rust `HoistedB61` + 61-bit `D1b` LogUp-GKR (`FastPrime61` Crandall reduction, stack `U576/U192` Knuth-D BEHZ division, dual negacyclic/cyclic `O(N log N)` ring-quotient extraction, `Direct-20` & `Exact-Garner-15` prepacked lifts; `6/6` test & falsifier suites pass): `51×–54×` faster prove & `71×–973×` faster verify than Python at `N=8192`; `d=4096` (`2,048 -> 32` blocks) FHE drops `3,825.7 -> 118.09 ms` warm (`32.4×`, `17,343 blks/s`), full `HoistedB61+D1b` prove `1.75 s` (`Direct-20`) / `2.23 s` (`Exact-Garner-15`), succinct verify `24.55 ms`; 2L `vFHEML` `2.84 s` prove, `Hoist(b, τ=64)` `8.00 s/step`, `Dark-vPIR` (`V=151,936`) `3.91 s` (`19,454 blks/s`)
- `darkvfhe-succinct-pcs-and-custodian-gdn.md` (+ `native/darkvfhe/src/{succinct_pcs,dark_gdn,cert}.rs`, `src/bin/dark_resident_bench.rs`) — closes `native-hoisted-b61-rust-benchmarks.md` §4 #1 with a real 128-bit `Ext3` Coset-NTT RS/Ligero matrix PCS (`HoistedSuccinctBundle` `DVFHEPC1`, `blow=4, t_cols=312` -> `129.5b` Ligero / `211.6b` UD / `>164b` `Ext3` soundness, zero-witness standalone verify: `2.55 MiB` / `62.2 ms` at `d=64`, `22.21 MiB` / `251.9 ms` at `d=4096` = `56.6×` smaller than `1,258 MiB` witness + saves `805 MiB` `Enc(W)`) and executes a 4-turn bit-exact (`max|diff|=0`) 3-custodian threshold-BFV + SPDZ encrypted `Qwen3.8` `Gated DeltaNet + Dark-vPIR` resident at `N=8192` (`E=2^111.0`, `>40b` full-poly TVD, hard `C8` zero-decryption-oracle gate + succinct `R_PD`, `6/6` attacks refused)

**zkML**
- `moe-router-binding.md` (+ `-cost.py`) — router binding must be zero-knowledge; expert selections recover 91% of tokens
- `ml-systems-corrections.md`, `kv-cache-correction.md` — append-dominant KV is true of the computation, false of serving
- `ml-to-crypto-mappings.md`, `speedup-ledger.md` — the mapping tricks and every measured speedup in one place
- `float-in-zk-three-regimes.md` — the three regimes; ⚠ its bf16 framing is superseded
- `zkml-landscape.md`, `zkml-integration-architecture.md`, `catgrad-seam.md` — the open position, and where the pillar lives
- `attestable-calibration.md` — the overhead number is a baseline choice, not a measurement
- `audit-sampling-prior-art.md`, `audit-theorem-statement.md`, `impl-readiness.md` — the audit game: prior art, the Lean spec, and what is mechanically verified
- `zkqmc-read.md` — eprint 2022/1007 read in full (2026-09-04): a prover-held quasi-random shift is `BeaconRefutation` (ε_beacon = p, q ≤ 0), a warden-secret shift is learned from ≈ ℓ/log₂(1/p) observed fires; trap for audit selection, real-but-off-axis for the paper's own claim
- `rank1-gradient-check.md` — a linear layer's gradient is CHECKED, not proved: the MLE of an outer product factors, so no sumcheck round at all; Lean-authored, measured at 4096×4096, and honest that it removes the n² proof but not the n² commitment
- `zktransformer-verdicts.md` (+ `research/zktransformer_2026_11_20/`) — `zkTransformer` (CCS 2026) read & audited at source with cross-family review (`gpt-6.2-astra` + `claude-fable-5-2`), upstream Issue + PR filed: ADOPT `EinSumcheck` (`minidregg-einsumcheck.patch`, 0 `sorry`; un-repeated GQA cuts attention sumcheck muls 8×; native MXFP4 `ikb,jkb,jk->ij` runs at degrees `(2^5, 3^7, 3^log N)` and cuts MoE committed felts 1.94×), REJECT `StructuredExp` (0/25 grid points vs `Rank1ProdExp` / helper-free D1b LogUp-GKR); 9 implementation soundness/completeness bugs (`0` `SparseKZH3` openings, `74%` uncommitted sparse blocks, unbound `ClampLower` advice, PCS `VerifierKey` bypass) proved & repaired
- `einsum-speedup-wave.md` (+ `research/speedup_wave_2026_11_21/experiments/einsum_turbo_pricing.py`) — next-gen `EinSumcheck` on `gptoss-int v0`: Gruen `{0,∞}` `eq`-factoring (`4.75×` GQA SC speedup vs `zkTransformer`, `18/25` quadratic rounds on MXFP4 `gate_up`); `b->j->k` tensor-factored delayed block-bind (`l_0=5`) + 7-bucket 0-mul E2M1 Horner (`16.4×` smaller `Ext4` buffer, `12.65×` padded / `18.36×` active BabyBear mul speedup; generic Toom-Cook `SVO` `l_0>=3` refuted on BabyBear); `W=128` block-windowed sliding GQA + zero-commitment `step_β` carry chain (`32.8×` at `T=4096`, `130.5×` at `T=16384` per sliding layer, `3.84×–4.01×` 24L); Active-4 MoE coupon-collector curve (`8.00× -> 2.41× -> 8.26×`) + 24L folding (`1,704 -> 11` sumchecks, `152×` transcript cut)
- `qaren-and-gptoss-nonlin-speedups.md` (+ `.../gptoss_nonlin_and_qaren_pricing.py`) — closes `AGENDA.md:111` (`Qāren` `2026/347` rejected: `24×–333×` primitive cell blowup, `2,240×–165,777×` Mod-PCS blowup, + 4 constructive completeness/soundness bugs verified by PoC; hold repaired `Lagrange-Check` for `vFHE`); cuts `gptoss-int v0` 24L non-arithmetic wall `2.07×–2.24×` (`2.57×–3.15×` vs bit-blast, `-105.63B` cells / `-119.41B` lookups at `T=4096`), 9/9 SHA-256 intermediate digests bit-identical on real `gpt-oss-20b` weights (dead clamps `layer.py:227,256,258-hi,260` alone save `-28.14B` cells)
- `trace-packing-and-zk-whir.md` (+ `.../trace_packing_and_zk_pricing.py`) — Frigo & shelat (`2026/2770`) `GF(2^128)` trace bit-plucker + Hilbert-90 ZK (`0` quad gates, `127L+2` pads, `0` extra rounds, `2^-128` error) composed with Bloemen `Blo26` Thm 5 (`H=Tr`); catches odd-char sign bug in `2026/2770` `Remark 4.5` & refutes binomial `KoalaBear Ext5` (`X^5+X+4`); refutes 31-bit multi-challenge LogUp (`c=12–15`, `2.6×` worse) while verifying 64-bit Goldilocks + `k_s=3` skip (`1.05×–1.72×`); `ProveKit v2` subdomain projection `π(x)` (`930.9×` table NTT cut) & `<0.6%` ZK-WHIR (`CFW26`/`ProveKit v2`)
- `qwen38-next-zkml-vfheml-architecture.md` (+ `research/vfhe_sota_2026_11_21/experiments/qwen38_next_zk_vfhe_pricing.py`) — source-exact `Qwen3.8-Flash-Next` (`arXiv:2608.30320`, `125.74B` `512E Top-10+1` MoE `A6.04B` + `51.20B` Layer-2 N-gram PLE + `2.71B` MTP): `75%` `Gated DeltaNet` (`36L`) verifies chunkwise WY `(I+L)[U|W]=RHS` in 1 flat deg-2 Gruen `EinSumcheck` (`0` GKR layers, `0` invs, `0` `T^2` `EXP`s) & runs `O(1)`-state (`0.211 GiB` thru `1M`) depth-1 `vFHEML`; `25%` `QSA` (`12L`) cuts softmax `850×–3,401×` (`K=2048`) with 2 verified BabyBear Top-`K_B` traps (`B1a` `τ<2^30` bottom-`k` wrap, `B1b` `ReLU=0` ties); `97` 4-branch `GR` bounds residuals (`max|R|=139.2` FP8-safe, `0` Sinkhorn); refutes naive `D1b` on `51.2B` PLE (`576,891×` ZK P2-Merkle gain, `~1,250×` `2P-DPF` upload gain vs `YPIR`); beats `gpt-oss-20b` per token for all `T>=64K` (`2.57×–10.8×` at `256K–1M`)
- `lean-vfhe-deltanet-gruen.md` (+ `research/vfhe_sota_2026_11_21/formal/minidregg-vfhe-deltanet-gruen.patch`) — 3 kernel-verified `minidregg` Lean 4 modules (`1,451` lines, `0 sorry`, `0 axiom`, `33` `#print axioms` pins): `Theory/BfvHoistedRescale.lean` (hoisted `sumMulPhase` `+1` vs `+K` rounding, `K=64` `fheRs4096` margin, mis-decrypt gap witness, & `VERDICTS.md` §7.5 `Hole B` `HoistedRescaleCert` iff/uniqueness + `Q=31,t=4` mod-`Q` alias tooth), `Theory/ZkmlDeltaNet.lean` (`Qwen3.8-Next` `GDN` Householder equivalence + nilpotent `neumannInv` chunkwise WY `(1+L)U=V` over any `CommRing` incl. `ZMod 16`), & `Assurance/ZkmlGruenSumcheck.lean` (`Gruen` `{0,∞}` `eqLinPoly` split, `r=0` fn.23 tooth, Mode-2 `<=2/|F|` soundness, `F_7` 3-root unstripped forgery, & Jolt `#1474` double-strip tooth)
- `minidregg-gruen-deltanet-native-seam.md` (+ `minidregg/Compiler/{GruenEinSumcheck,DeltaNetWy}Conformance.lean`, `minidregg/prover/src/{gruen_einsum,deltanet_wy}.rs`) — closes `minidregg`'s Lean-to-Rust conformance seam (`27` `#print axioms` pins, `[AddCommGroup R]` type-enforced 0-mul `e2m1Horner`, interior `z_1=0` `ZeroEqFallback` & `α_1=0` WY vectors): `Gruen` `{0,∞}` Mode-2 achieves `11.7×–11.8×` round / `5.5×–5.8×` full-prove speedup vs `sumcheck.rs` (`48.4×–50.6×` / `15.5×–17.7×` BabyBear-specialized), `5.60×` MXFP4 delayed-bind Horner speedup, and `1.514 ms` (`1.842 ms/tok` w/ WY solve) on a full `Qwen3.8-Flash-Next` GDN layer
- `lean-content-certificates-and-binding.md` (+ `minidregg/Selvage/ContentCertificate.lean`, `minidregg/Assurance/CertificateComposition.lean`) — 2 kernel-verified `minidregg` Lean 4 modules (`2,508` lines, `0 sorry`, `42` `#print axioms` pins, `Neon`-audited against ATLAS Law-2 vacuity) mechanizing `CERTIFICATES.md` `P1`–`P8` / `L0`–`L6` (`ContentScheme`, Tier-1 `substringAt_of_openings`, Brzozowski `absent_iff_padded_complement` + `"xPx"` trap, `cert_and` + fractional `bindAdv=1/2` witness & necessity tooth, `BoundDfaStmt` splice separation, `cert_allRecords` `N·ε + mmrBindAdv + bindAdv`, `cert_produced_weld` + `TK` tooth, `cert_mapScheme`, `Pred.evalWith` bridge) and closing `Selvage` W4 (`AdvOpeningScheme`)
- `qwen38-e2e-prover-and-breadstuffs-closures.md` (+ `.../qwen38_int_block_e2e_prover.py`, `.../breadstuffs-holeb-dfa-weld8.patch`, `DARK-LEARNING` §24) — executes a 4-layer integer `Qwen3.8-Flash-Next` repeating block (`3 GDN + 1 QSA + 8 GR + 4×512E MXFP4 MoE + 16-prime SplitMix64 PLE`, `0.9893` 4L `cos_sim`) with 6 real Fiat–Shamir / FHE+SPDZ provers & verifiers (`7/7` planted forged proofs rejected), and closes `breadstuffs` `BFVScaleLiftRefinement` (`Bfv` `113 -> 176` clean theorems), `Dregg2` `P4`/`P6` (`PaddedAbsence`), and chip-generic 8-lane `AttestedAutomatonWeld8` (`P9`)
- `verified-ast-extraction-and-redaction-transducers.md` (+ `minidregg/Theory/VerifiedAstTransducer.lean`, `minidregg/Compiler/PolicyAstTransducerEmit.lean`, `minidregg/prover/src/policy_transducer.rs`) — closes ambiguous CFG tool-call splice (`ambigMiniJsonCfg_splice_attack`) and secret-in-CoT sanitization across Lean 4.35.0 (`2,477` lines, `0 sorry`, `20` `#print axioms` pins: `attrReplay_unique_of_ll1`, 139-rule `miniJsonCfg_is_ll1`, `SafeReplacement` `redactBytes_scrubs_padded_complement`, `rewrite_and_extract_sound_or_collision`) and `--release` Rust (`ExactNat` `>=2^64` safe, `301–532 MB/s` batch & `258–373 MB/s` `O(N)` streaming redact, `24–35 MB/s` compiled LL(1) AST extraction, `14.26 ms` `4 KiB` `2× cSHAKE256` `RewriteCert`)
- `tower256-private-content-certificates.md` (+ `minidregg/Compiler/Tower256PrivateContentCert.lean`, `minidregg/prover/src/tower256_private_cert.rs`, `src/bin/prove_private_cert.rs`) — upgrades `Tower256ContentCert.lean` from `.accept`-only `fullDisclosure` to private-witness salted `Tower256` + `cSHAKE256` receipts across `.accept`, `.count`, and `.bound` (`2,079` Lean lines, `14` `#print axioms` pins: `saltedRoot_eq_or_collision`, `unopened_salted_leaf_rom_prob_eq`, `maskedCubeRoot_prob_eq`, `checkPrivate_sound_or_collision`, `step_sampling_miss_prob_eq`); native LCH Additive-NTT + L1 Fan–Paar + `CShake256Core` midstates (`73.3×` speedup) prove `1/4/16 KiB` secrets-bearing docs in `13.7 / 51.4 / 210.5 ms`, verify in `0.80–1.27 ms` (`30–47 KiB`), with `0` leaked `>=6B` slices
- `real-qwen35-pretrained-zk-audit.md` (+ `native/qwen35audit/`, `.../real_qwen35_gdn_eval.py`) — executes real 24L pretrained `Qwen/Qwen3.5-0.8B-Base` (`18 GDN + 6 GQA`, `0` WY errors on `23.59M` cells; per-head `u_scale[h]` cures `beta ≈ 10^-3` underflow for `38×` KL gain -> `FP8 KL = 0.00555 nats` / `98.12%` Top-1, `Mixed-MXFP4 KL = 0.06385 nats` / `91.25%` Top-1) and HTTP-Range `L0..L3` of real `Qwen/Qwen3.8-Flash-Next-FP8` + `NVFP4-CSF` (`20.1 dB` experts + `31.5 dB` `MXFP8` GDN -> `25.53 dB` 4L `MXFP4-MoE`) + `MLX-4bit`; native `BabyBear Ext4` (`103.5b` UD) `qwen35audit` runs `29.4–42.8 µs/tok` `U1` stream, `550.1 ms` prove / `55.3 ms` verify on `Qwen3.5` `GDN+SwiGLU` + 0-cleartext ZK `Absent("sk-...")`, and `1,613.4 ms` / `44.0 ms` on real `Qwen3.8` `H_v=48` WY + `512E` `MXFP4` (`6/6` attacks rejected)
- `sota-2026-hardware-fit-model-selection.md` (+ `.../sota_2026_hw_fit_and_live_run.py`) — systematic Nov-2026 Scry/Kagi hardware-fit survey (`39` Scry SQL + `6` Kagi) & `zkML`/`vFHEML` pricing for `96 GiB` M2 Max: crowns `Qwen/Qwen3.8-27B` (`17.66 GB` `UD-Q4_K_XL`, `LCBv6 90.3%`, `SWE-V 77.8%`) as `#1 <=25 GB` resident target (pulled & executed live on Metal at `80.8–111.0 tok/s` prefill, `7.3–8.2 tok/s` decode, `16.75 GiB` RSS + E2E `cSHAKE256` `RewriteCert` + LL(1) AST), `Qwen/Qwen3.6-35B-A3B` (`38.55B` BB muls) as `#1` fast MoE, and `Qwen/Qwen3.8-Flash-Next` (`83.62 GB` w/ `mmap` PLE, `83.34B` BB muls @ `256K`) as `#1` full-`96 GiB` target; catches `3.96%` `-0.0` (`0b1000`) nibbles in shipped MLX `MXFP4` and `NVFP4` `F8_E4M3` BabyBear overflow cured by `8`-bit GCD scale shift

**Deltas, 2026-11-21** (Sept 5 → Nov 21 sweep):
`proximity-and-hw-delta-2026-11.md` (+ `.../beyond_johnson_repricing.py`) — reprices 480 `(field, n, ρ, tgt, pow)` cells against `DKT26` (`2026/2056`), `Gabizon` (`2026/2048`), `Jeronimo` (`2609.05870`), & `better.codes` (`69.45b` PR `#644`): `q=19` stays retired (`78b` asymp); `DKT26` Thm 5.12 proves `O_ρ(n/η_0^3)` Johnson MCA in **every** char (`+7.0–14.8b` over `BCHKS25`, shipped in `Plonky3 #2282`); positive-order beyond-Johnson locks out char 2 (`0/192`), fails unground on `BabyBear^4` (`0/96`), passes `14/96` on `KoalaBear^5` (`100b`), and passes `90/96` on `Goldilocks^3` (`u=2` OOD mandatory); `2611.17042` A100 roofline (sumcheck int-issue bound, LogUp barrier bound) + `BenX` STARK refutation + `Plonky3 v0.8.0` binary WHIR.

**Deltas, 2026-09-04** (what moved outside since 08-18, each with corpus+instrument):
`proximity-delta-2026-09-04.md` (BCSS25's personal communications are 2026/532 and
2025/2110; Plonky3 labels our 130 "legacy"; nothing moves UDR 34 / JBR 73),
`systems-delta-2026-09-04.md` (PR #1982 merged; leanVM v0.10 binary+BLAKE2s;
BinarySpartan v4; Jolt to lattice PCS; Plonky3 v0.7.0 has GKR), `formal-delta-2026-09-04.md`
(ArkLib 416→314 tainted, statements admitted not absent; better.codes; VCVio Merkle extractability),
`hash-delta-2026-09-04.md` (no hash verdict moves; 2026/1792's compression-mode trail
window is 16 ≥ R_P=13 at our Merkle internal node — cost at our prime uncomputed;
1760 is a rules artefact and a design rule), `eprint-delta-2026-09-04.md` (all 142
ids 1719–1861 triaged: 19 relevant, 19 maybe; 1838 FS-on-program-generated-instances
is a new requirement for the EVM route; 1835 k-tree regime missing from BRIEF 3),
`nst-1792-at-our-node.md` (+ `gsr-scripts/nst_1792.py`) — 1792's cost model reproduced
58/58 + 21/21 with no fitted constant, then evaluated at our Merkle node: ≥ 2^511.9,
R_P=20 changes nothing at the floor; the binding quantity is d=8 × the p−2 cap, not R_P.

**Algebra candidates, 2026-09-04** (the joint-algebra question, `swarm/ASTRA-ALGEBRA-PROMPT.md`):
`circle-aligned-vfhe.md` (+ `circle-scripts/circle_m31.py`) — M31's negacyclic NTT and the
circle STARK share one twiddle table exactly, and it buys nothing: the BFV relation is
coefficient-domain; cosmetic. `galois-ring-stack.md` (+ `galois-scripts/`) — Z/2^64 as one
algebra is a trap: residue-field soundness (1/64 per challenge bit), local ring so challenge
sets have size ≤ 2, T-function hashes (preimage kill test ran); by-products: q = 2^64−257 is
load-bearing, rescale at power-of-two q is a shift. `inert-cyclotomic-tower.md` (+
`galois-scripts/inert_tower.py`) — the Φ_{3⁸} tower dissolves the residue-field obstruction and
dies on dense GR(2⁶⁴,162) proof messages (270–480× per mult); by-product: commit-to-the-ciphertext
at 5.5×. `astra-algebra-read.md` — the adversarial read of the external model's answer: what it
corrected in us, what we priced, what it got wrong. `exceptional-set-lean.md` — the
Lean side (minidregg `Theory/ExceptionalSetLocalRing.lean`, `Theory/CyclotomicExceptionalSet.lean`):
exceptional sets ⟺ injective residues over any local hom into a field, the ceiling |A| ≤ |residue
field|, fixed-weight sets over (ZMod n)[X]/(f) for p | n | pᵉ via `AdjoinRoot`, counting C(deg f, h)
over any monic f, conductor 6561 proved; teeth on ZMod 4 and (ZMod 4)[X]/(X²+1). `lova-neo-rmfe-read.md` (+
`galois-scripts/rmfe_toy.py`) — Lova read at source (q = 2^64, unstructured SIS, t = 330,
16–47 MB/fold: the unstructured PQ fold is outside VERDICTS §3c's 4–50× band); Neo now has
implementations (Nightstream) but still no verifier constraint count; RMFE toy verified,
rates 0.279 at D = 2. `nightstream-read.md` — Nightstream's Lean audited at main and tip: 5,621
theorems, 0 sorry, 185 native_decide, a paper twin plus R1CS layout, no FS/BCS/depth theorem; the
recursive step costs 27,537,894 rows by their own theorem; "both legs" stands. `dual-mode-ideal-quotient-gate.md` (+ `ring-hash-scripts/ideal_quotient_gate.py`)
— the CRT-slot congruence gate on both full modes at the real modulus: both escape; σ₃₁ is the
Frobenius; the τ=2 cost row is mis-counted. `descriptor-reader-scout.md` — what d55ef32/b297c7d
deleted and why (quoted), the emit→consume map (the Stage-0 descriptor JSON has no consumer),
the lawful build brief (Lean witness fill + exhibits; generated-glue reader; p3 as throwaway
oracle), and the blocker: `GateMleExt6.lean:246 CommittedTerminal` has no realizer.
`unit-witness-census.md` — every soundness/knowledge/extraction declaration in Selvage classified K/S/U/H
with consumers: the genuine extractors are never wired into any `RbrKnowledgeSoundness.extract`, the deployed
2⁻⁵⁵ sums only (S)/CR bounds, the IVC tower's `KnowledgeSound` has identity extractors and zero consumers;
top-3 upgrades named with exact statement changes. `fold-extractor-upgrade.md` — upgrade 3 resolved
the other way: FoldRoundBound is false for every extractor (zero-absorb attack, proved at toy and
production); the carried-witness reduction has error 0 at the cost of succinctness and half the capacity.

**The learn/infer-only resident (2026-09-06)** — `swarm/astra-handoff/` holds the external
handoff + our companion; `streaming-fe-credential-audit.md` — the SFE writer state IS the inner
master secret: appending and reading are the same credential (dissertation §3.2 = GKS23 §6.2,
derived path reproduced); not a theorem break, a structural mismatch with the host-appends model.
`pre-constrained-encryption-read.md` — PCE is one-hop: sPCE fixes every function at setup, the learn
chain dies at hop two; delegating PCE with closure needs general-circuit constraints = iO (the paper
says so); the extractor warning confirmed and sharpened; DARK-TRAINING §6 reclassified to tier-C custody.
`private-trace-lemma.md` — minidregg `Theory/PrivateTrace.lean`: trace privacy from a preserved relation
(no axioms), the byte toy honest (equal HIGH bit), +1 as the preservation falsifier, recovery in 8 decided
by kernel and 7 insufficient for every policy. `release-gate-routing.md` — minidregg
`Assurance/ReleaseGateRouting.lean`: an unbound release gate determines the state; a binding gate
releases only public information; the kernel's Settlement is one by type; at Stage 0 the descriptor
forces Z and the receipt is bound evidence (binds, does not hide).

**Sweeps and corpora** — `mirror-mine-2026-08.md`, `inspiration-sweep{,-cc,-pl}.md`,
`inspiration-verdicts.md`, `vacuity-prior-art.md`. Each names its corpus AND its
instrument; absence claims are only as good as those two lines.

**Method and process** — `soundness-theater-correction.md`, `the-absence-problem.md`,
`missed-threads.md`, `context-window-compositions.md`, `window-review-2026-08-13.md`,
`what-remains.md`, `kpz-noop-and-the-model-gap.md` §"model gap". Keep as-is; they are
about how the work went, not what is true.

## archive/

**History, not truth. Do not cite it.** Files whose central claim died, kept
whole with their reasoning and measurements, each labelled with what replaced
it. `archive/README.md` is the table.
