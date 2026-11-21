# Succinct 128-Bit Coset-NTT Matrix PCS (`HoistedSuccinctBundle`) and 3-Custodian Threshold-BFV + SPDZ Encrypted `Qwen3.8` `Gated DeltaNet` + `Dark-vPIR` Resident

**Date:** 2026-11-21 · **Lane:** `darkvfhe-succinct-gdn` (`real_systems_wave_2026_11_21`, Worker 3)  
**Crate:** [`native/darkvfhe/`](../native/darkvfhe/) (`src/{succinct_pcs,dark_gdn,cert,lib}.rs`, `src/bin/dark_resident_bench.rs`, `tests/succinct_pcs_and_dark_gdn.rs`)  
**Companion Evidence:** [`notes/native-hoisted-b61-rust-benchmarks.md`](native-hoisted-b61-rust-benchmarks.md) · [`notes/vfhe-hoisted-certificate-breakthrough.md`](vfhe-hoisted-certificate-breakthrough.md) · [`notes/qwen38-next-zkml-vfheml-architecture.md`](qwen38-next-zkml-vfheml-architecture.md) · [`BfvHoistedRescale.lean`](../research/vfhe_sota_2026_11_21/formal/Theory/BfvHoistedRescale.lean) · [`native/darkproof/src/{pcs,ligero,spdz}.rs`](../native/darkproof/src/)

**Claim tags (`AGENTS.md`):** `[EXECUTED]` compiled & run in `--release` on this machine · `[DERIVED]` exact algebra/probability · `[SOURCE]` inspected at named path:line · `[OPEN]` unverified boundary.

---

## 0. Executive Verdicts (Closing `[OPEN]` #1 of `native-hoisted-b61-rust-benchmarks.md` + Real 3-Custodian Resident)

[`notes/native-hoisted-b61-rust-benchmarks.md`](native-hoisted-b61-rust-benchmarks.md) (§4 #1) left replacing the Wave-5 SHA-256 column-hash oracle with a genuinely succinct 128-bit PCS on the custodian wire — and executing an end-to-end threshold-custodian encrypted `Qwen3.8` `Gated DeltaNet` + `Dark-vPIR` resident — as `[OPEN]`. Wave-6 closes both in [`native/darkvfhe/`](../native/darkvfhe/) with zero toys or oracles:

1. **Real 128-Bit Succinct Coset-NTT Reed–Solomon / Ligero Matrix PCS (`succinct_pcs.rs` + `cert.rs`, `[DERIVED]`, `[EXECUTED]`):**
   - Commits the entire online `HoistedB61` witness (`b_lifts`, `y_lifts`, `s_lifts`, 4-limb $w=20$ `K_res` quotients, and `2^{20}` `ProveKit v2` multiplicities) **once** over $\mathbb{F}_{p_0}$ ($p_0 = 2^{61}-376831$), derives witness-bound Fiat–Shamir challenges from the real salted SHA-256 Merkle PCS root, and discharges **both** all 8-prime `HoistedB61` polynomial evaluations (`Direct-20` & `Exact-Garner-15`) **and** the `D1b` LogUp-GKR terminal multilinear leaf claims `(z_w, z_tab)` against that **same PCS root** `[DERIVED, EXECUTED]`.
   - **Provable $\ge 128$-Bit Soundness:** At `blow = 4` (`rate = 1/4`) and `t_cols = 312` distinct column openings, column proximity achieves **`129.49` bits** under classical [AHIV17] Ligero third-distance ($\delta = 1/4$) and **`211.56` bits** under [BCIKS20] Unique Decoding ($\delta = 3/8$), while true cubic extension arithmetic $\mathbb{F}_{p_0^3}$ ($|\mathbb{F}_{p_0^3}| > 2^{182.99}$) raises sumcheck/RLC/proximity algebraic soundness from $\sim 44$–$60$ bits (base field) to **`> 164` bits** `[DERIVED]`.
   - **Concrete Wire Compression & Zero-Witness Verification (`N = 8192`, 12-core Apple M2 Max):** Self-contained `HoistedSuccinctBundle::to_bytes()` (`DVFHEPC1` wire format, including `persistent_a` PCS opening so **zero** weight ciphertexts are re-sent) measures **`2,613.8 KiB` (`2.55 MiB`, verify `62.2 ms`)** at $d = 64$, **`3,638.9 KiB` (`3.55 MiB`, verify `76.7–121.8 ms`)** at $d = 256$, **`7,120.7–8,370.6 KiB` (`6.95–8.17 MiB`, verify `94.7–96.3 ms`)** at $d = 1024$, and **`22,745.4–22,746.3 KiB` (`22.21 MiB`, verify `251.9–295.4 ms`)** at $d = 4096$ (`2,048 -> 32` blocks) — a **`56.6×` wire reduction** vs Wave-5's `1,258 MiB` full witness (`+ 805 MiB` `Enc(W)` saved) `[EXECUTED]`.
2. **Real 3-Custodian Threshold-BFV + SPDZ Encrypted `Qwen3.8` `Gated DeltaNet` + `Dark-vPIR` Resident (`dark_gdn.rs`, `[DERIVED]`, `[EXECUTED]`):**
   - Implements **3-of-3 distributed BFV key generation** ($s = s_0 + s_1 + s_2$, **zero party ever holds $s$**), pairwise oblivious ring-OLE relinearization shares $[s^2]_i$, long-term custodian PCS key commitments (`key_pcs_root`), succinct ZK partial-decryption proofs (`PdSuccinctProof` for `R_PD` smudging range $|e_i|_\infty \le E \approx 2^{111.0}$ and ciphertext handle binding), a **hard `C8` zero-decryption-oracle gate** (`verified_handles` checked *before* computing/releasing any partial decryption share), and **3-party SPDZ MAC-authenticated crossings** ($\alpha = \alpha_0 + \alpha_1 + \alpha_2$, commit-then-open `sigma` check) `[DERIVED, EXECUTED]`.
   - Across **4 consecutive stateful turns** at deployed **$N = 8192$, $d_k = d_v = 128$ (`Qwen3.8` GDN head width), `V = 256` encrypted `Dark-vPIR` table** (including $\alpha_t = 0$ state reset), the resident matches cleartext `GDN` over $\mathbb{Z}_t$ **bit-for-bit (`max |diff| = 0` on every turn)** in **`2.72–4.29 s` host prove + `4.37–5.78 s` 3-custodian `C8` verify/`E2S`/SPDZ + `2.84–7.00 s` `S2E` state PCS refresh** (`7.66 MiB` total succinct proofs/turn) `[EXECUTED]`.

---

## 1. Mathematical Construction & Soundness Ledger (`succinct_pcs.rs`, `cert.rs`, `dark_gdn.rs`)

### 1.1 Cubic-Extension Coset-NTT Matrix PCS & Blinding (`succinct_pcs.rs:76-418, 923-1398`)

- **Field & Coset Code (`[DERIVED]`, `[SOURCE: darkproof/src/pcs.rs:58-97, ligero.rs:21-98]`):** For any 61-bit Crandall prime $p = 2^{61} - \delta$, `Ext3Field::new` deterministically selects the lexicographically smallest $(c_0, c_1)$ passing Rabin's irreducibility test ($\gcd(u^p - u, f) = 1$ and $u^{p^3} \equiv u \pmod{u^3 - c_1 u - c_0}$), yielding $\mathbb{F}_{p^3}$ of order $> 2^{182.99}$ (`succinct_pcs.rs:88-115`, verified across all 9 primes in `ext3_irreducibility_and_inverses_across_all_primes`). Rows of width $W = C + \text{hide}$ ($C = 2^{m_c}$, $\text{hide} = t_{\text{cols}} = 312$) are evaluated on disjoint multiplicative cosets $z^t \langle \omega_{2^k} \rangle$ at blowup `blow = 4` (`npts = 4 W`) via parallel `rayon` radix-2 NTTs (`succinct_pcs.rs:235-302, 1484-1561`) and committed into a salted SHA-256 column Merkle tree with deduplicated multiproofs (`succinct_pcs.rs:509-649`).
- **Unified `Ext3` Sumcheck + Proximity Folding (`[DERIVED]`):** `open_slot_claims` batches arbitrary `SlotLinearClaim`s with $\beta \in \mathbb{F}_{p_0^3}$, runs $m_c + m_r$ quadratic sumcheck rounds over $\mathbb{F}_{p_0^3}$ (with Round 0 folded directly against base-field `u64` entries in `self.ext`, halving peak `Ext3` RAM), emits degree-$< W$ row combinations `u_eval(X)` ($\text{eq}(z_{\text{row}})$) and `u_prox(X)` ($\gamma^r$ RLC), and opens $t_{\text{cols}} = 312$ distinct columns.
- **Soundness & ZK Blinding Ledger (`[DERIVED]`, cross-audited by `pcs-gdn-neon-audit`):**
  - **Algebraic Soundness (`> 164` bits):** Batching (`|claims| / p_0^3`), quadratic sumcheck ($2(m_c + m_r) / p_0^3$), and degree-$< W$ proximity RLC ($R / p_0^3$) sum to $< 2^{-164}$ soundness error at $m_r + m_c \le 30$.
  - **Column Proximity (`129.5` bits Ligero / `211.6` bits UD):** At rate $\rho = W / (4W) = 1/4$, $(1 - (1-\rho)/3)^{312} = (3/4)^{312} = 2^{-129.49} < 2^{-128}$ ([AHIV17] third-distance) and $(1 - (1-\rho)/2)^{312} = (5/8)^{312} = 2^{-211.56}$ ([BCIKS20] correlated agreement).
  - **Witness-Independent Column Openings:** `hide = t_cols = 312` uniform tail coefficients per row ensure any $t_{\text{cols}}$ opened evaluation columns are $t_{\text{cols}}$-wise uniform over $\mathbb{F}_{p_0}$ (Vandermonde invertibility on coset points), `3` proximity-mask rows (`1, u, u^2` basis) make `u_prox` uniform over $\mathbb{F}_{p_0^3}^W$, and `4` uniform data-blinding rows blind `u_eval[0..C]` whenever $z_{\text{row}} \notin \{0,1\}^{m_r}$ (`test_hvzk_zero_witness_leakage_on_opened_columns`). *(Adding `darkproof::gmask::GMask` univariate sumcheck masking to hide intermediate sumcheck round polynomials themselves is noted in §4 `[OPEN]`.)*

### 1.2 Single-Matrix 8-Prime Cross-Field Evaluation Without Wrap (`cert.rs:1140-2380`)

- **Non-Wrapping 21-Bit Chunked Sub-Sums (`[DERIVED]`):** All digit columns $d_{m,j}$ (`Direct-20` or `Exact-Garner-15`), 4-limb $w=20$ `K_res` quotients (with coefficient $j = N-1$ fixed to `0` and verified against `r0_deg_n1[N-1] = 0`, enforcing $\deg K < N-1$ per [`BfvHoistedRescale.lean:388-428`](../research/vfhe_sota_2026_11_21/formal/Theory/BfvHoistedRescale.lean)), and `mults[0..2^20]` live in **one** $\mathbb{F}_{p_0}$ PCS matrix. `D1b` LogUp-GKR proves $d_{m,j} \in [0, 2^{20}) \subset \mathbb{Z}$; in `Exact-Garner-15`, the 9 affine-linear lookups per limb enforce $T_i \in [0, 2^{20})$ where $2^{20} T_i = 2^{20}\Sigma_{\text{pos}} - \Delta_i - d_0 - 2^{20}(d_1+d_2+d_3) + v_0$ satisfies $|2^{20} T_i| < 2^{41} \ll p_0/2$, forcing exact integer equality and boolean carry $c_i \in \{0,1\}$ (`cert.rs:1168-1233`).
- For primes $p_\ell$ ($\ell \in \{1..7\}$), splitting each public weight $W^{(\ell)}_{m,j} = (\gamma_{m,\ell} r_{\text{FS},\ell}^j) \bmod p_\ell \in [0, 2^{61})$ into three 21-bit chunks $W_0 + 2^{21} W_1 + 2^{42} W_2$ produces exact integer sub-sums $0 \le S_b = \sum_{m,j} d_{m,j} W_{m,j,b} \le 15 \cdot 8192 \cdot (2^{20}-1)(2^{21}-1) \approx 2^{57.93} < p_0 \approx 2^{61}$ — **zero modular wraparound**, folded with Fiat–Shamir $\tau_{\text{sub}}$ into `21` `SlotLinearClaim`s alongside `D1b` GKR's `(z_w, z_tab)` leaf claims (`cert.rs:1707-1806, 2130-2203`).

### 1.3 3-Custodian Threshold-BFV, `C8` Gate, Succinct `R_PD`, & Depth-1 `Qwen3.8` `GDN` (`dark_gdn.rs`)

- **Zero-`sk` Ceremony & Smudging Bound (`dark_gdn.rs:110-335`, `[DERIVED]`):** Custodians $i \in \{0,1,2\}$ sample ternary $s_i \in \{-1,0,1\}^N$ locally, aggregate $b_{\text{pk}} = -(a_{\text{pk}}\sum_i s_i + \sum_i e_{\text{pk},i}) \bmod Q$, generate $[s^2]_i$ via pairwise masked ring-OLE without reconstructing $s$, and commit $s_i + 1 \in \{0,1,2\}$ into persistent `key_pcs_root` with verified `D1b` `[0, 3)` range proofs. At $N = 8192$ ($Q/(2t) \approx 2^{121.00}$), smudging bound $E = \lfloor (Q/(2t))/1024 \rfloor \approx 2^{111.0}$ keeps $3E + |e_{\text{ct}}| \approx 2^{112.58} \ll Q/(2t)$ (`8.42` bits decryption margin) while bounding full-polynomial statistical TVD by $N|e_{\text{ct}}|/(2E) \approx 2^{13}\cdot 2^{58}/2^{112} = 2^{-41.0}$ (`> 40` bits full-ring drowning).
- **Hard `C8` Gate + Succinct ZK `R_PD` + SPDZ Crossing (`dark_gdn.rs:348-765`, `[DERIVED]`, `[SOURCE: e2s_proof.py, crossing_wire.py]`):** Each custodian maintains `verified_handles: HashSet<[u8; 32]>`; `partial_decrypt_ct2_checked` / `ct3_checked` aborts with `"C8 ABORT"` *before* touching $s_i$ if `ct_handle` was not produced by a verified `HoistedSuccinctBundle`. Every released partial decryption $d_i = c_1 s_i + e_i \pmod Q$ (or $c_1 s_i + c_2 [s^2]_i + e_i$) carries a `PdSuccinctProof` proving $|e_i|_\infty \le E$ (`6` $w=20$ digits) and $d_i$ consistency against `key_pcs_root` across all 3 `Q`-limbs (`dark_gdn.rs:436-578`). At the `GDN` crossing (`dark_gdn.rs:845-1035`), the host proves `Dark-vPIR` ($x_t = E^\top e_{\text{tok}}$) and depth-1 parallel reads $m_k = S_{t-1}^\top k_t$, $m_q = S_{t-1}^\top q_t$ (`notes/qwen38-next-zkml-vfheml-architecture.md` §3.1); the 3 custodians verify all 3 succinct bundles, run dealerless `(Enc_pk(R), [R])` `E2S` into $\mathbb{Z}_t$ SPDZ shares, evaluate $u_t = v_t - \alpha_t m_k$, $S_t = \alpha_t S_{t-1} + \beta_t k_t u_t^\top$, and $y_t = \alpha_t m_q + \beta_t \langle k_t, q_t\rangle u_t$ via authenticated Beaver triples, verify commit-then-open `spdz_mac_check`, and refresh `Enc_pk(S_t^T)` via `S2E` + offline PCS range check.

---

## 2. Executed Correctness & Adversarial Attack Ledger (`tests/succinct_pcs_and_dark_gdn.rs`)

Command (`[EXECUTED]`, `0` compiler warnings in `darkvfhe`; `5/5` unit + `3/3` Wave-5 + `4/4` Wave-6 suites pass):
```sh
cd /Users/ember/dev/zkml-research/native && \
  CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-darkvfhe2 cargo test --release -p darkvfhe
```

| Test / Adversarial Attack (`tests/succinct_pcs_and_dark_gdn.rs`) | Security Property / Soundness Seam | Outcome (`[EXECUTED]`) |
|---|---|---|
| `test_succinct_pcs_bundle_roundtrip_and_deployed_n8192` | `to_bytes` / `from_bytes` + zero-witness standalone verify (`Direct-20` & `Exact-Garner-15`, persistent & non-persistent `A`, $N \in \{64, 8192\}$) | **PASS** |
| `test_hvzk_zero_witness_leakage_on_opened_columns` | All-zero witness produces `100%` non-zero masked `opened_cols` & `u_eval[0..C]` | **PASS** |
| `test_multi_turn_3_custodian_dark_gdn_and_pir_bit_exact` | 5 stateful 3-custodian `GDN + Dark-vPIR` turns (incl. $\alpha_t = 0$ reset) vs cleartext $\mathbb{Z}_t$ | **PASS** (`0` bit diffs) |
| **Attack 1 (`1-cell PCS witness / column / eval mutation`)** | Mutate `opened_cols[3][2] += 1` or `p0_poly_evals[0] += 1` in serialized bundle | **REFUSED** (`Merkle` / `PCS`) |
| **Attack 2 (`Forged Merkle multiproof sibling / salt`)** | Flip 1 bit in `multiproof.siblings[0]` or `multiproof.salts[0]` | **REFUSED** (`root mismatch`) |
| **Attack 3 (`Forged Exact-Garner-15 boundary u + Q`)** | Non-power-of-two strip alias $u' = 42 + Q \in [Q, 2^{183})$ ($r_2 \ge q_2$, $T_2 = p_0 - 1$) | **REFUSED** (`D1b` balance) |
| **Attack 4 (`Hole B quotient shift y_0[0] + 1`)** | Mod-$Q$-preserving output shift forging BEHZ rounded quotient | **REFUSED** (`Bp` rescale) |
| **Attack 5 (`Corrupted custodian SPDZ MAC`)** | Tamper Party 1 share/MAC before `spdz_open_batch` + `spdz_mac_check` | **REFUSED** (`MAC check FAILED`) |
| **Attack 6 (`Unverified E2S -> C8 abort` + `R_PD` forgeries)** | Unverified handle `e2s_ct3`, tampered proof ingest, `unrelated_boundary_shares`, `offset_partial` | **REFUSED** (`C8 ABORT` before share release; `R_PD` rejected) |

---

## 3. Real `--release` Benchmarks at Deployed `N = 8192` (12-Core Apple M2 Max)

Command (`[EXECUTED]`, exits `0` in `373.17s` under concurrent multi-worker swarm load on M2 Max):
```sh
cd /Users/ember/dev/zkml-research/native && \
  CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-darkvfhe2 cargo run --release -p darkvfhe --bin dark_resident_bench
```

### 3.1 Standalone 128-Bit `HoistedSuccinctBundle` Scaling (`N = 8192`, Persistent `Enc(W)`, `0` Witness Access)

| Width `d` | Mode | Blocks (`In->Out`) | Online PCS Shape (`2^{m_r}×2^{m_c}`) | PCS Commit (`ms`) | PCS+`D1b` Open (`ms`)\* | Total Online Prove (`ms`) | **Standalone Verify (`ms`)** | **Serialized Proof (`KiB` / `MiB`)** | Soundness (`UD / Lig` bits) |
|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `64` | `Direct-20` | `1 -> 1` | `256 × 16384` | `240.31` | `704.84` | `964.52` | **`62.18`** (`38.2` idle) | **`2,613.75` (`2.55 MiB`)** | `211.6 / 129.5` |
| `64` | `Exact-Garner-15` | `1 -> 1` | `256 × 16384` | `249.34` | `999.63` | `1,269.05` | **`81.11`** (`39.2` idle) | **`2,616.67` (`2.56 MiB`)** | `211.6 / 129.5` |
| `256` | `Direct-20` | `8 -> 2` | `512 × 16384` | `395.04` | `1,824.95` | `2,257.45` | **`121.78`** (`46.4` idle) | **`3,638.92` (`3.55 MiB`)** | `211.6 / 129.5` |
| `256` | `Exact-Garner-15` | `8 -> 2` | `512 × 16384` | `370.78` | `2,058.74` | `2,471.47` | **`76.65`** (`54.4` idle) | **`3,638.86` (`3.55 MiB`)** | `211.6 / 129.5` |
| `1024` | `Direct-20` | `128 -> 8` | `512 × 32768` | `710.60` | `3,696.11` | `4,522.09` | **`94.73`** | **`7,120.68` (`6.95 MiB`)** | `211.6 / 129.5` |
| `1024` | `Exact-Garner-15` | `128 -> 8` | `1024 × 32768` | `1,055.71` | `6,310.23` | `7,554.14` | **`96.26`** | **`8,370.64` (`8.17 MiB`)** | `211.6 / 129.5` |
| **`4096`** | `Direct-20` | **`2048 -> 32`** | `1024 × 65536` | `2,520.20` | `64,996.19` | `68,129.59` | **`295.41`** (`234.4` idle) | **`22,745.37` (`22.21 MiB`)** | `211.6 / 129.5` |
| **`4096`** | `Exact-Garner-15` | **`2048 -> 32`** | `1024 × 65536` | `1,915.21` | `51,392.36` | `53,856.98` | **`251.85`** (`241.3` idle) | **`22,746.32` (`22.21 MiB`)** | `211.6 / 129.5` |

*\*Note:* Both `Open (ms)` and `Serialized Proof` include opening **both** the online `witness_pcs` (`~6.1 MiB` at $d=4096$) **and** the persistent `Enc(W)` `a_pcs` (`4096 × 131072 = 5.37 × 10^8` cells, `~16.1 MiB`), so custodians verify `Enc(W)` against its 32-byte `a_pcs_root` without receiving `805 MiB` of weight ciphertexts `[EXECUTED]`.

### 3.2 3-Custodian Encrypted `Qwen3.8` `Gated DeltaNet` (`d_k = d_v = 128`) + `Dark-vPIR` (`V = 256`, `N = 8192`)

- **Setup & Genesis (`[EXECUTED]`):** 3-of-3 Threshold-BFV + SPDZ ceremony (`0` party holds `sk` or `alpha`, $E = 2^{111.0}$) = **`221.29 ms`**; Resident genesis (`Enc_pk(E)` `[256×128]` + `Enc_pk(S_0^T)` `[128×128]` + 3-custodian offline PCS range verify) = **`916.36 ms`**.

| Turn (`tok`, `α_t`, `β_t`) | Match vs Cleartext `GDN` (`Z_t`) | Host Prove (`PIR + m_k + m_q`, `ms`) | 3-Custodian `C8` Verify + `E2S`/`R_PD` + SPDZ (`ms`) | State `S2E` + PCS Refresh (`ms`) | Succinct Proofs (`PIR / m_k / m_q`, `KiB`) |
|---|---|---:|---:|---:|---:|
| **Turn 0** (`17`, `3`, `2`) | **`BIT-EXACT (max|diff| = 0)`** | `4,083.9` | `5,015.2` | `2,871.8` | `2,618.0 / 2,614.9 / 2,614.3` |
| **Turn 1** (`142`, `5`, `4`) | **`BIT-EXACT (max|diff| = 0)`** | `2,955.9` | `4,371.0` | `3,165.2` | `2,617.1 / 2,615.9 / 2,615.2` |
| **Turn 2** (`255`, **`0`**, `7`) | **`BIT-EXACT (max|diff| = 0)`** | `2,718.7` | `5,783.9` | `6,997.1` | `2,617.5 / 2,616.7 / 2,615.4` |
| **Turn 3** (`64`, `9`, `3`) | **`BIT-EXACT (max|diff| = 0)`** | `4,293.3` | `5,178.7` | `2,836.1` | `2,617.4 / 2,614.7 / 2,615.9` |

**4-Turn Totals (`[EXECUTED]`):** `133,632` Beaver triples (`33,408/turn`) · `20` checked `E2S` crossings · `24` `S2E` crossings · Peak RSS = `37,756.2 MiB`.

---

## 4. Remaining `[OPEN]` Boundaries & Proposed Maintainer Folds

- **Remaining `[OPEN]` Boundaries:**
  1. **Sumcheck-Round `GMask` Transcript HVZK + Multi-Round WHIR Folding (`[OPEN]`):** `succinct_pcs` already makes opened columns, `u_prox`, and `u_eval[0..C]` witness-independent via `hide = 312` tail masks + `3` proximity + `4` data blinding rows; adding univariate sumcheck round masking (`darkproof::gmask::GMask`) closes full transcript-level HVZK across the quadratic sumcheck polynomials, and replacing 1-step Ligero row evaluation (`6 × W` `Ext3` scalars) with 2–3 WHIR folding rounds will shrink $d = 4096$ bundles from `22.2 MiB` toward `< 2 MiB`.
  2. **Homomorphic State Update Avoiding Per-Turn `S2E` State Re-Commit (`[OPEN]`):** Updating `Enc_pk(S_t)` directly in BFV via hoisted outer-product + `relinearize_ct3` eliminates the per-turn `S2E` crossing (`6` cts) + offline state PCS refresh (`~3–4 s`).
- **Proposed Folds (`docs/VERDICTS.md` Untouched):**
  - **[`docs/VERDICTS.md`](../docs/VERDICTS.md) §3 & §7.5:** Mark [`native-hoisted-b61-rust-benchmarks.md`](native-hoisted-b61-rust-benchmarks.md) §4 #1 (`Succinct PCS Wire Closure`) **CLOSED** by `native/darkvfhe/{succinct_pcs,cert,dark_gdn}.rs`: `2.55 MiB` (`d=64`) to `22.21 MiB` (`d=4096`) 128-bit `Ext3` Coset-NTT Matrix PCS bundles (`129.5b` Ligero / `211.6b` UD, `62–295 ms` zero-witness verify) and 4-turn bit-exact 3-custodian `Qwen3.8` `Gated DeltaNet + Dark-vPIR` execution at $N = 8192$.
