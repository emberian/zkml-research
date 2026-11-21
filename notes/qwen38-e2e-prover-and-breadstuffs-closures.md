# End-to-End Integer `Qwen3.8-Flash-Next` Cryptographic Prover & `breadstuffs` Metatheory Closures (`Hole B`, `P4`, `P6`, `P9`)

**Date:** 2026-11-21 · **Lane:** `bread-qwen38-e2e` (Worker 4, `system_wave_2026_11_21`)
**Executable Artifacts (`[EXECUTED]`):**
- **Lean 4.35.0 Overlay & Patch (`breadstuffs/metatheory`):** [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/system_wave_2026_11_21/formal_bread/build_and_verify.sh) (`8.41s`, `exit 0`) · [breadstuffs-holeb-dfa-weld8.patch](file:///Users/ember/dev/zkml-research/research/system_wave_2026_11_21/formal_bread/breadstuffs-holeb-dfa-weld8.patch) (`git -C /Users/ember/dev/breadstuffs apply --check` exits `0`; `/Users/ember/dev/breadstuffs` untouched)
- **End-to-End Integer `Qwen3.8-Flash-Next` Prover & Verifier:** [qwen38_int_block_e2e_prover.py](file:///Users/ember/dev/zkml-research/research/system_wave_2026_11_21/experiments/qwen38_int_block_e2e_prover.py) (`21.45s`, `exit 0`, `7/7` forged transcripts rejected)
- **Custody Decision Addendum:** [DARK-LEARNING-SCHEME-DECISION.md §24 Addendum](file:///Users/ember/dev/zkml-research/docs/DARK-LEARNING-SCHEME-DECISION.md#L1943-L1994)

---

## 0. Executive Verdicts

1. **`breadstuffs` Metatheory Closures (`VERDICTS.md` §7.5 `BFVScaleLiftRefinement` + `CERTIFICATES.md` `P4`, `P6`, `P9`):** `[DERIVED]` `[EXECUTED]`
   Four Lean 4.35.0 modules (`1,603` new lines across `Bfv/ScaleLiftRefinement.lean`, `Dregg2/Crypto/Deriv/PaddedAbsence.lean`, `Dregg2/Circuit/Emit/AttestedAutomatonWeld8Closure.lean`, plus `Bfv.lean` bumping `#assert_namespace_axioms Bfv` from `113 -> 176` clean theorems) are kernel-verified with **`0 sorry`, `0` custom `axiom`, `0 native_decide`, `0 #guard`**, `37` `#assert_all_clean` pins, and `32` `#guard_msgs`-pinned `#print axioms` checks:
   - **`VERDICTS.md` §7.5 (`Hole B` / `BFVScaleLiftRefinement`):** Proves `ediv_add_half_eq_rescale` (`⌊(t z + ⌊Q/2⌋)/Q⌋ = Bfv.rescale t Q z` for **all** `Q > 0`, odd and even), `BFVScaleLiftRefinement` over `breadstuffs`'s actual `Bfv.Rn`, `Bfv.negaMul`, `Bfv.RnsCt`, `Bfv.LimbMulRel`, and `Bfv.perLimb_pins_modProd`, the ring bridge `hoistedRescaleCert_refines_negaMul_sum` (`P_sum = ∑_c toPoly (a_c) * toPoly (b_c)`), hoisted `sumMulPhase_noise_le` (`+1` vs `+K` rounding slack, `K = 64` `fheRs4096` margin), and both integer and polynomial `Q = 31, t = 4` (`1·1 = 1` vs `2·16 = 32 ≡ 1 mod 31`) falsifiers.
   - **`CERTIFICATES.md` `P4`, `P6`, & `P9`:** Proves `absent_iff_padded_complement` + `whole_word_complement_is_not_absence` over `Dregg2`'s real `PredRE`/`derives`/`Matches` (`P4`); proves instance-level `splice_verifierKernel_separation` (`spliceUnboundKernel` fires `dfa_verify_sound` while no `DfaBoundVerifierKernel` sharing that record-ignoring `verify` can inhabit `extractable`) and composes `P6 ∘ P4` in `dfa_bound_padded_absence_or_collides`; and proves chip-generic (`∀ S8 : Heap8Scheme`) 8-lane root & completion-lane pinning modulo `MapRootColl` plus the arm-for-arm `DescriptorIR2` `.mapOp -> holdsAt8` equivalence `satisfied2_repointed_iff_lanes8` (`P9`, leaving all 43 legacy `DescriptorIR2` consumers green).
2. **End-to-End Integer `Qwen3.8-Flash-Next` 4-Layer Repeating Block + Real Fiat–Shamir Provers & Verifiers:** `[DERIVED]` `[EXECUTED]`
   Closes `[OPEN]` #3 of [qwen38-next-zkml-vfheml-architecture.md](file:///Users/ember/dev/zkml-research/notes/qwen38-next-zkml-vfheml-architecture.md#L131) by executing a complete bit-exact integer-quantized (`MXFP4` E2M1 + `FP8` E4M3 + `INT16/32` accumulators) `Qwen3.8-Flash-Next` 4-layer repeating block (`3 × GDN + 1 × QSA + 8 × 4-branch GR + 4 × 512E Top-10+1 MXFP4 MoE + Layer-2 16-prime SplitMix64 PLE`) coupled to **six real, zero-shared-state SHA-256 Fiat–Shamir / FHE+SPDZ cryptographic provers and verifiers**:
   - **Quantization Fidelity (`[EXECUTED]`):** Single `GDN` (`3:1` GVA, `w_conv=4`, `L2Norm`, WY `C=16/64`) achieves **`cos_sim = 0.99919` (`27.8 dB` SNR, `261` INT16 ULP)** vs dequantized-weight FP32 (`0.99717` / `22.4 dB` vs raw unquantized FP32); Layer-2 16-prime SplitMix64 PLE hits **`0.99942` (`29.3 dB`)**; across all **9 sequential subblock stages** (`3 GDN + 1 QSA + 8 GR + 4 × 512E MXFP4 MoE + PLE`), the end-to-end 4-layer integer block maintains **`cos_sim = 0.98928` (`16.6 dB` SNR)** vs dequantized-weight FP32 and **`0.97802` (`13.6 dB`)** vs raw unquantized FP32.
   - **Real Cryptographic Proving & `7 / 7` Falsifier Refusal (`[EXECUTED]`):** Verifies `12` `C=16` + `3` `C=64` BabyBear/`Ext4` **Gruen `{0, ∞}` Mode-2 `EinSumcheck`** proofs across all 3 GDN layers (`0` prover inversions, including `r_u = 0` deterministic completeness fallback), `12` **`MXFP4` delayed-bind MoE** Gruen Mode-2 proofs (`ikb,jkb,jk -> ij`, including `r_j = 0` fallback), `45` **`QSA` `C3 + C5` Threshold Top-$K_B$** queries proved inside a depth-`16` **Helper-Free `D1b` Projective Fraction-Tree LogUp-GKR** cubic sumcheck (`0` helper columns, surviving forced `B1b` `ReLU == 0` ties), `1,024` **dual SHA-256 + width-16 BabyBear `Poseidon2-8` Merkle openings** (`zkML`) and **16-head 2-server SPDZ-authenticated `BGI16` PRG-tree `DPF` evaluations** (`vFHEML`) on the SplitMix64 PLE tables, and **2 parallel depth-1 `HoistedB61` (`Exact-Garner-15` + fused `d`-free) encrypted `GDN` state reads** on `bfv_ref.BFV`. All **`7 / 7` planted adversarial forgeries** are deterministically rejected.
3. **`DARK-LEARNING-SCHEME-DECISION.md` §24 Addendum Landed:** `[DERIVED]` `[EXECUTED]`
   Appends a self-contained §24 Addendum ([lines 1943–2015](file:///Users/ember/dev/zkml-research/docs/DARK-LEARNING-SCHEME-DECISION.md#L1943-L1994), preserving §§1–24.5 intact) recording how `HoistedB61` (`6,144 -> 128` matvec certs + fused `d`-free identity + `Direct-20`/`Exact-Garner-15` + `τ = 64` temporal flush) flips `Hoisted-FHE(b, τ=64)` (`21.50–25.08 Gbit` strict `digits61` w/ §20.2 ZKPoPK; `11.08 Gbit` packed) and `Inference-Only vFHEML` (`10.78 Gbit` `digits61`) strictly below pure `SPDZ MPC` (`31.50 Gbit` / `12.89 Gbit`) at $d = 4096$ while keeping `9.5×–19.9×` smaller online wire.

---

## 1. `breadstuffs/metatheory` Audit & Kernel-Verified Closures (`Lean 4.35.0`)

### 1.1 Ground-Truth Audit of `/Users/ember/dev/breadstuffs/metatheory` (`[SOURCE]`, `[EXECUTED]`)

Inspecting `breadstuffs` @ `f45ef0ba5` revealed two important baseline facts before authoring:
1. **Toolchain vs Prebuilt `.olean` Cache:** `metatheory/lean-toolchain` and `.lake/packages/mathlib` sit on `leanprover/lean4:v4.35.0`, whereas `metatheory/.lake/build/lib/lean/` still held `4.30.0`-header `.olean`s for part of `Dregg2` and `Bfv`. [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/system_wave_2026_11_21/formal_bread/build_and_verify.sh) inspects `.olean` magic headers, symlinks `4.35.0` artifacts, and compiles the 134-module dependency cone into `formal_bread/build/` in parallel without touching `/Users/ember/dev/breadstuffs`.
2. **Nov 5–6 Partial Landings vs Open Gaps:** `Dregg2/Crypto/Dfa.lean` had already added `BoundStatement` and `dfa_bound_identifies_record_or_collides`, and `Dregg2/Circuit/Emit/AttestedAutomatonLanes8.lean` had added `MapOp.holdsAt8` / `Satisfied2Lanes8` with `weld_completion_lanes_not_free` proved **only at `constChip`**. Meanwhile, **`BFVScaleLiftRefinement` (`VERDICTS.md` §7.5)** and **`P4` (`absent_iff_padded_complement`)** were completely absent, **`P6`'s instance-level `DfaVerifierKernel` separation** and **`P6 ∘ P4` composition** were missing, and **`P9` lacked chip-generic (`∀ S8`) 8-lane uniqueness and the explicit `DescriptorIR2` repointing equivalence**.

### 1.2 Module-by-Module Theorem & Falsifier Ledger (`[DERIVED]`, `[EXECUTED]`)

| Module (`formal_bread/`) | Lines | Clean Pins | Key Theorems & Constructive Falsifier Teeth |
|---|---:|---:|---|
| [Bfv/ScaleLiftRefinement.lean](file:///Users/ember/dev/zkml-research/research/system_wave_2026_11_21/formal_bread/Bfv/ScaleLiftRefinement.lean) + [Bfv.lean](file:///Users/ember/dev/zkml-research/research/system_wave_2026_11_21/formal_bread/Bfv.lean) | 855 + 78 | `16` + `176` ns | `ediv_add_half_eq_rescale` (`L58`, all `Q > 0`); `intScaleCert_iff` (`L84`); **`BFVScaleLiftRefinement`** (`L128`) + witness (`L170`); `hoistedRescaleCert_iff`/`_unique` (`L259, L352`); **`hoistedRescaleCert_refines_negaMul_sum`** (`L449`); `sumMulPhase_noise_le` (`L539`), `deployed_hoisted64_margin_holds` (`L656`), `eager_vs_hoisted_rounding_gap` (`L676`); **`bfvScaleLiftRefinement_modQ_falsifier`** (`L699`, `1·1=1` vs `2·16=32` on `Rn 1`) & `holeB_modQ_alias_falsifier` (`L737`). |
| [Dregg2/Crypto/Deriv/PaddedAbsence.lean](file:///Users/ember/dev/zkml-research/research/system_wave_2026_11_21/formal_bread/Dregg2/Crypto/Deriv/PaddedAbsence.lean) | 403 | `12` | **`slice_eq_factor_iff`** (`L59`, holds unconditionally for all `i, j : ℕ`); `derives_any_true` & `derives_star_any` (`L73, L76` across all `Value` constructors); **`absent_iff_padded_complement`** (`L105`) & `absent_matches_iff_padded_complement` (`L118`); **`whole_word_complement_is_not_absence`** (`L131`); **`splice_verifierKernel_separation`** (`L185`); **`dfa_bound_padded_absence_or_collides`** (`L270`) + witness (`L338`). |
| [Dregg2/Circuit/Emit/AttestedAutomatonWeld8Closure.lean](file:///Users/ember/dev/zkml-research/research/system_wave_2026_11_21/formal_bread/Dregg2/Circuit/Emit/AttestedAutomatonWeld8Closure.lean) | 345 | `9` | **`weld8_canonical_root_pins_all_8_lanes`** (`L61`); **`weld8_completion_lanes_unique_at_canonical_heap`** (`L74`, `∀ S8`); **`weld8_two_runs_same_pubRoot_collides`** (`L113`, floor-free `MapRootColl`); `weld8_completion_lanes_not_free_of_unattained_lane` (`L157`); **`satisfied2_repointed_iff_lanes8`** (`L235`) + witness (`L274`) + `satisfied2_repointed_refutes_completion_lanes_free` (`L287`). |

```text
$ bash research/system_wave_2026_11_21/formal_bread/build_and_verify.sh
OK: syntax hygiene check (0 sorry, 0 axiom, 0 native_decide, 0 #guard; #print axioms + #assert_all_clean pinned)
  [LOCAL  4.83s] (1/4) Dregg2.Crypto.Deriv.PaddedAbsence -> rc=0              (#assert_all_clean: 12 keystones)
  [LOCAL  5.88s] (2/4) Bfv.ScaleLiftRefinement -> rc=0                         (#assert_all_clean: 16 keystones)
  [LOCAL  7.59s] (3/4) Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure -> rc=0 (#assert_all_clean: 9 keystones)
  [LOCAL  2.53s] (4/4) Bfv -> rc=0                                             (#assert_namespace_axioms Bfv: 176 theorems)
OK: Kernel-verified all 4 local modules cleanly in 8.41s
OK: git -C /Users/ember/dev/breadstuffs apply --check breadstuffs-holeb-dfa-weld8.patch
OK: /Users/ember/dev/breadstuffs target paths untouched (read-only discipline verified)
```

---

## 2. End-to-End Integer `Qwen3.8-Flash-Next` 4-Layer Block & Real Prover/Verifier Suite

### 2.1 Architecture, Integer Quantization Fidelity, & Division-Free WY Bridge (`[DERIVED]`, `[EXECUTED]`)

[qwen38_int_block_e2e_prover.py](file:///Users/ember/dev/zkml-research/research/system_wave_2026_11_21/experiments/qwen38_int_block_e2e_prover.py) instantiates one complete 4-layer `Qwen3.8-Flash-Next` hybrid block (`T = 64, d = 64`) preserving every structural invariant of `arXiv:2608.30320` and `modeling_qwen4_exp.py`:
- **`3 × GDN` (`3:1` GVA `H_k=2, H_v=6`, `d_k=d_v=16`, `w_conv=4`, sigmoid out-gate):** Solves quantized chunkwise WY for **both `C = 16` (`4` chunks) and `C = 64` (`1` chunk)** via forward substitution with exact Euclidean remainder $0 \le R_{\text{rem}}[h,i,k] < M_{\text{wy}} = 4096$:
  $$\sum_{j=0}^{C-1} \tilde{L}_{h,i,j} \, UW_{h,j,k} = M_{\text{wy}}\bigl(RHS_{h,i,k} - UW_{h,i,k}\bigr) + \lfloor M_{\text{wy}}/2\rfloor - R_{\text{rem}}[h,i,k],$$
  which holds **over $\mathbb{Z}$ with zero BabyBear wraparound** (`max |RHS_M| < 10^7 ≪ p_BB / 4`) and reduces to **one flat degree-2 Gruen `{0, ∞}` Mode-2 `EinSumcheck`** (`0` prover `Ext4` inversions!). Over BabyBear as an exact `CommRing` (with forced $\alpha_{29,4} = 0$), `C = 16`, `C = 64`, and sequential GDN match with **`max |diff| == 0`**.
- **`1 × QSA` (`12:1` GQA `H_q=12, H_kv=1`, `PRoPE(8)` + `AvgPool r=4` 4Q/1KV `ReLU` Indexer, `K_B=4`):** Evaluates `ReLU` block scoring with `0` `EXP_TAB` lookups, injects exact `ReLU == 0` score ties at $t = 63$ (`B1b`), and proves all `45` active Top-$K_B$ queries via `C3` tie-breaking + `C5` $2 \times 15$-bit $\tau_i$ decomposition inside a **depth-`16` Helper-Free `D1b` Projective Fraction-Tree LogUp-GKR** cubic sumcheck.
- **`8 × 4-Branch GR` + `4 × 512E Top-10+1 MXFP4 MoE` + `Layer-2 16-Prime SplitMix64 PLE`:** Runs all `512` routed + `1` shared experts per MoE layer in `MXFP4` E2M1 (`[-12..12]/2` × `UE8M0` block scale per `B=32` elements) with monotone `softmax(top-10(logits))` (`10` vs `512` `EXP`s), plus Layer-2 SplitMix64 (`mults = [23703573157769, 20109073645365, 8052911324071]`, `EOS = 248044` reset at $t = 21$, dilated `conv1d(k=4, d=3)`) across 16 prime tables (`1031..1123`).

| 4-Layer Block Stage (`T = 64, d = 64`) | vs Dequantized-Weight FP32 (`cos_sim` / `SNR` / `max_ulp`) | vs Raw Unquantized FP32 (`cos_sim` / `SNR`) |
|---|---|---|
| `L0: GDN #1` (`3:1` GVA, WY `C=16 & C=64`) | **`0.999193`** / **`27.8 dB`** / `261` | **`0.997173`** / `22.4 dB` |
| `L0: 512E Top-10+1 MXFP4 MoE + GR` | **`0.999175`** / **`27.7 dB`** / `280` | **`0.996728`** / `21.8 dB` |
| `L1: Layer-2 16-Prime SplitMix64 PLE` | **`0.999418`** / **`29.3 dB`** / `281` | **`0.997556`** / `23.1 dB` |
| `L1: GDN #2` + `512E MXFP4 MoE + GR` | **`0.994327`** / `19.4 dB` / `1,883` | **`0.987988`** / `16.2 dB` |
| `L2: GDN #3` + `512E MXFP4 MoE + GR` | **`0.989746`** / `16.8 dB` / `2,000` | **`0.978935`** / `13.7 dB` |
| **`L3: QSA #1` + `512E MXFP4 MoE + GR` (Final E2E)** | **`0.989276`** / **`16.6 dB`** / `2,660` | **`0.978022`** / **`13.6 dB`** |

### 2.2 Executed Cryptographic Sub-Verifiers & `7 / 7` Soundness Falsifier Ledger (`[EXECUTED]`)

Every verifier below reconstructs its SHA-256 Fiat–Shamir transcript independently from public commitments and proof messages (`0` shared RNG/witness state):

| Sub-Protocol (`zkML` / `vFHEML`) | Honest Proof Load Verified | Planted Adversarial Falsifier (`7 / 7` Rejected) | Exact Verifier Rejection Gate |
|---|---|---|---|
| **1a. `GDN` WY `Gruen` `{0, ∞}` Mode-2 `EinSumcheck`** | `12 × (C=16)` + `3 × (C=64)` proofs (`0` invs; `r_h[0]=0` fallback tested on `GDN #2`) | **`F1`:** Mutated `UW` cell + tampered round-0 `{q_0(0), q_0(∞)}` message | **`REJECTED`:** `terminal sigma != L_eval * UW_eval` |
| **1b. `MXFP4` Delayed-Bind MoE `Gruen` Mode-2** | `12` `ikb,jkb,jk->ij` proofs (`j->b->k`, `S` delayed past `b`; `r_j[0]=0` fallback tested) | **`F2`:** Forged expert output `Y` + tampered Phase-`B` `{q_b(0), q_b(∞)}` poly | **`REJECTED`:** `Phase-K cubic sum check failed at round 0` |
| **2a. `QSA` `C3 + C5` Threshold Top-$K_B$** | `45` causal Top-$K_B$ queries (`ReLU == 0` ties at $t=63$ handled cleanly via `C3`) | **`F3`:** `B1a` wraparound $\tau = 8\cdot 2^{27} + 15$ (`1073741839`) forging bottom-$k$ (passes if `C5` disabled!) | **`REJECTED`:** `query 0: C5 tau 15-bit limb reconstruction failed (tau=1073741839)` |
| **2b. Helper-Free `D1b` Fraction-Tree LogUp-GKR** | Depth-`16` (`65,536`-leaf) projective fraction tree (`0` helper cols, `16` cubic GKR layers) | **`F4`:** Out-of-range limb `2^15 = 32768` + zeroed `root_N = 0` header | **`REJECTED`:** `D1b root split check failed` |
| **3a. `PLE` `zkML` SHA-256 + `Poseidon2-8` Merkle** | `64 × 16 = 1,024` dual openings (`x^7` width-16 BabyBear Poseidon2 + `EOS=248044` reset) | **`F5`:** Post-`EOS` token-22 head-8 embedding shifted by `+1` | **`REJECTED`:** `token 22 head 8: SHA-256 Merkle root mismatch` |
| **3b. `PLE` `vFHEML` 2-Server `BGI16` `DPF`** | `16` prime-head full-domain PRG-tree evaluations w/ embedded `[1, mac_key]` SPDZ tag | **`F6`:** Malicious Server 1 shifts head-3 response share by `+1` | **`REJECTED`:** `SPDZ-DPF MAC check failed on PLE prime head 3!` |
| **4. `HoistedB61` Depth-1 Encrypted `GDN` Step** | `2` parallel multi-block `bfv_ref` reads ($\bm{S}^\top\bm{k}_t, \bm{S}^\top\bm{q}_t$, `4->2` hoisted `Exact-Garner-15` certs) | **`F7`:** `Hole B` forged BEHZ quotient `y_forge = y + 1` with matching output handle & `y_lifts` | **`REJECTED`:** `fused hoisted rescale identity fails in F_p (row 0, comp 0)` |

---

## 3. Provenance, Unverified Scope (`[OPEN]`), & Proposed Maintainer Folds

- **Corpus & Metered Search Disclosure:** `0` `eprint.iacr.org` fetches, `0` Scry queries, `0` Kagi queries in this lane (builds directly on local `breadstuffs` @ `f45ef0ba5`, `dark_learning_2026_11_06`, and `vfhe_sota_2026_11_21` search ledgers).
- **Unverified Scope (`[OPEN]`):** (1) Full `125.7B + 51.2B` `Qwen3.8-Flash-Next` checkpoint perplexity under `INT16/MXFP4/FP8` fixed-point execution (`~180–360 GB` weights not downloaded); (2) whole-tree `43`-consumer migration of shared `DescriptorIR2.MapOp.holdsAt` in `breadstuffs` (kept non-breaking via `Satisfied2Repointed ↔ Satisfied2Lanes8`).
- **Proposed Folds (Do Not Edit `docs/VERDICTS.md` Directly):**
  1. **`docs/VERDICTS.md` §7.5 (`line 1647`):** Mark `BFVScaleLiftRefinement` closed in both `minidregg` (`Theory/BfvHoistedRescale.lean`) and `breadstuffs` (`Bfv/ScaleLiftRefinement.lean` via `breadstuffs-holeb-dfa-weld8.patch`).
  2. **`docs/CERTIFICATES.md` §0.1, §0.3, §5 (`P4`, `P6`, `P9`):** Record `Dregg2/Crypto/Deriv/PaddedAbsence.lean` (`P4` + instance-level `P6` separation + `P6 ∘ P4` bridge) and `Dregg2/Circuit/Emit/AttestedAutomatonWeld8Closure.lean` (chip-generic 8-lane root uniqueness + `DescriptorIR2` repointing equivalence).
