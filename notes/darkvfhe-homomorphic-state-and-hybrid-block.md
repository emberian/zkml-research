# Homomorphic-State `Dark-GDN` & Full 3-Custodian Encrypted `Qwen3.8` Hybrid Block (`N = 8192`)

**Status:** Current evidence (`2026-11-21`). Closes `[OPEN]` #2 of `notes/darkvfhe-succinct-pcs-and-custodian-gdn.md` (§4 #2) in native multithreaded Rust (`native/darkvfhe/src/dark_block.rs`, `src/bin/dark_block_bench.rs`, `tests/homomorphic_gdn_and_block.rs`).

## 0. Executive Summary & Proposed `docs/VERDICTS.md` Fold

1. **Multi-Turn BFV Noise Law & `[REFUTED: unrefreshed depth >= 2 ct*ct at log2 Q = 183, log2 t = 61]` (`[DERIVED]` + `[EXECUTED]`):** Including canonical-embedding $s^L$-correlation ($\mathbb{E}[|\hat{s}|^{2m}] = m!(2N)^m \implies C_L = L!(L+2)/2$, verified within $\le 0.04\text{b}$ of 30-key $N=8192$ Monte Carlo) with per-hop factor $M = t^2 N(2N+1)/12$ and $2^{-40}$ Gaussian union bound $8.652\sigma$, Wave-6's $t_{61} = 2^{61}-1294335$ ($\log_2(Q/(2t_{61})) = 121.00\text{b}$) grows by $73.71\text{b/turn}$, reaching $2^{161.48}\text{b} \gg 2^{121.00}\text{b}$ (`-40.49b`) at depth $L = 2$. Pairing the deployed `(Qp, Bp)` (`log2 Q = 183`, `log2(QB) = 488`, `E = 2^{111}-1`) with the 33-bit Blum prime $t_{32} = 4{,}355{,}803{,}843$ ($\log_2 t = 32.020$, $t \equiv 3 \pmod 4$, $Q_{8192} \bmod t = 730$) lowers hop growth to **`44.73b/turn`** against a **`149.98b`** decryption ceiling, unlocking **`R_refresh(correctness) = 3`** (`2` pure in-BFV homomorphic state updates per `1` noise-reset crossing, `max |diff| = 0` across all turns) while explicitly distinguishing **`R_refresh(>40b TVD) = 1`** at `log2 Q = 183` (`TVD = 2^{-40.6}` at $L=1$; `>40b` TVD at $L=2,3$ requires widening `Qp` by +1..2 61-bit primes).
2. **In-BFV Homomorphic `GDN` State Update (`HomomorphicGdnState`, `[EXECUTED]`):** Replaces Wave-6's per-turn `E2S + 32,768-triple SPDZ outer product + full-matrix S2E + PersistentGridPcs re-commit` with **zero-`sk` 3-custodian threshold `RelinearizationKey` setup (`2.63 s` at $N=8192$)** and **2 sparse `S2E` ciphertexts** (`Enc_{pk}(\alpha_t X^0)` + strided `Enc_{pk}(\sum_r \beta_t u_{t,r} X^{r d_c})`, encrypting `129` slots instead of `16,384` matrix slots = **`127x` fewer state `S2E` slots**, **`0` state `E2S` `R_PD` proofs**, and **`0` state PCS re-commits**). At deployed $N = 8192, d_k = d_v = 128$ (`RAYON_NUM_THREADS=4`, interleaved head-to-head), `FusedHoistedK2 + relinearize_ct3` cuts state update latency from `3,871.8 ms/turn` to **`2,758.5 ms/turn` (`1.40x` faster; `1.49x–1.54x` per pure turn, `2.17x` at 16 threads)** and cuts 4-turn Beaver triples **`3.8x`** (`133,632 -> 35,328`), with empirical state phase noise `57.32b` (`Turn+1`) and `101.93b` (`Turn+2`) matching the analytical $2^{-40}$ bound (`59.09b`, `103.52b`) within `1.8b`.
3. **Full 3-Custodian Encrypted `Qwen3.8` Hybrid Block (`EncryptedQwenHybridBlock`, `[EXECUTED]`):** Chains `Dark-vPIR -> SPDZ Blum-RMSNorm -> HoistedB61 (q,k,v,z,\alpha,\beta) + Homomorphic-State GDN + Qwen3NextRMSNormGated + W_out -> SPDZ Blum-RMSNorm -> Oblivious Private-Router Top-2 SwiGLU MoE` (`E \in \{8, 16\}`) at deployed $N = 8192$ (`46.53–47.94 s/turn`, `6.75 GiB` peak RSS) with **`max |diff| = 0`** against cleartext `Qwen3.8` over $\mathbb{F}_t$, **zero cleartext weights/activations**, **zero leaked MoE expert IDs** (closing the `91%` token-recovery channel of `notes/moe-router-binding.md` §1.1), OS `/dev/urandom` CSPRNG + 3-party secret-shared SPDZ masks, atomic `StagedStateUpdate` commit, and **`7/7` refused adversarial attacks + `4/4` cross-audit regressions**.
4. **Proposed `docs/VERDICTS.md` Fold (§3 / §7):** Record `darkvfhe::dark_block` as closing stateful in-BFV `GDN` updates (`R_refresh = 3` correctness / `R_refresh = 1` `>40b` TVD at `log2 Q = 183, t = 4,355,803,843`) and end-to-end 3-custodian `Qwen3.8` hybrid-block execution (`0` expert-ID leakage).

---

## 1. Multi-Turn BFV Noise Recurrence, Blum Prime $t_{32}$, & `R_refresh` Cadence

- **Exact $s^L$-Correlated Variance (`[DERIVED]`):** Under 3-party setup $s = s_0 + s_1 + s_2$ ($\text{Var}(s_j) = 2$), fresh public-key noise has $\sigma_{S_0}^2 = 96N + 24$ and 3-party `S2E` has $\sigma_{\text{S2E}}^2 = 3\sigma_{S_0}^2$. Because $\tilde{m} = m + t I(X)$ has $I(X) \approx c_1 s / Q$ ($\text{Var}(I_j) = N/6$), $L$ sequential multiplications accumulate $s^L$ whose canonical-embedding moments satisfy $\mathbb{E}[|\hat{s}(\zeta)|^{2m}] \approx m!(2N)^m$, yielding combinatorial correlation factor $C_L = L!(L+2)/2$ and per-hop multiplier $M = t^2 N(2N+1)/12$:
  $$\text{Var}(e_{\text{read}}^{(L)}) \approx K_{\text{blk}} M^L (\sigma_{S_0}^2 + 3\sigma_{\text{S2E}}^2) C_L \quad (L \ge 2), \qquad \|e\|_{\infty, 2^{-40}} = 8.652\,\sigma.$$
- **Blum Prime Selection & `darkstep` Barrett Invariant (`[DERIVED]` + `[SOURCE]`: `native/darkstep/src/arith.rs:132,157`):** `Modulus::new(q)` computes `mu = ((1u128 << 122) / q) as u64`, which wraps `u64` when $q < 2^{58}$, while `Modulus::reduce(x)` sets `qhat = x >> 60 = 0` whenever $x = (Q \bmod t)\cdot m < 2^{60}$. Selecting $t_{32} = 4{,}355{,}803{,}843$ ($2^{32} + 60{,}836{,}547$, prime, $t \equiv 3 \pmod 4$, $Q_{8192} \bmod t_{32} = 730$, and $t_{32, N=64} = 4{,}303{,}819{,}103$ with $Q_{64} \bmod t = 492$) guarantees $(Q \bmod t)\cdot m < 2^{42} \ll 2^{60}$ (**zero `u64` truncation** and `< 365` loop ticks in `Rns::encode_round` without modifying `darkstep`).

| Profile (`N = 8192, log2 Q = 183, E = 2^111 - 1`) | Turn / Depth $L$ | Analytical $\|e_S\|_{2^{-40}}$ | Empirical $\|e_S\|_{\infty}$ | Analytical $\|e_{\text{read}}\|_{2^{-40}}$ | Margin vs $Q/(2t)-3E$ | Full-Ring TVD | Verdict |
|---|---:|---:|---:|---:|---:|---:|---|
| Wave-6 $t_{61} = 2^{61}-1294335$ (`[EXECUTED]`) | Turn+0 ($L=1$) | `13.70b` | — | `87.41b` | `+33.59b` | `2^-11.6` | Safe (`R_refresh = 1`) |
| Wave-6 $t_{61} = 2^{61}-1294335$ (`[REFUTED: L>=2]`) | Turn+1 ($L=2$) | `88.07b` | — | `161.48b` | **`-40.49b`** | `2^+62.5` | **Overflows $Q/(2t)$** |
| Blum $t_{32} = 4{,}355{,}803{,}843$ (`[EXECUTED]`) | Turn+0 ($L=1$) | `13.70b` | `12.52b` | `58.43b` | **`+91.55b`** | **`2^-40.6`** | **Safe + `>40b` TVD** |
| Blum $t_{32} = 4{,}355{,}803{,}843$ (`[EXECUTED]`) | Turn+1 ($L=2$) | `59.09b` | **`57.32–57.63b`** | `103.52b` | **`+46.46b`** | `2^+4.5` | **Bit-exact (`max|diff|=0`)** |
| Blum $t_{32} = 4{,}355{,}803{,}843$ (`[EXECUTED]`) | Turn+2 ($L=3$) | `103.52b` | **`101.93b`** | `148.20b` | **`+1.78b`** | `2^+49.2` | **Bit-exact (`R_refresh = 3`)** |
| Blum $t_{32} = 4{,}355{,}803{,}843$ (`[DERIVED]`) | Turn+3 ($L=4$) | `148.20b` | — | `193.06b` | `-43.08b` | `2^+94.1` | Refresh required |

---

## 2. Threshold `RelinearizationKey` Ceremony & Ring Slot Algebra (`HomomorphicGdnState`)

- **Zero-`sk` 3-Custodian `RLK` Ceremony (`setup_threshold_cluster_with_rlk`, `[DERIVED]` + `[EXECUTED]`):** On the 4-prime basis $(q_0, q_1, q_2, b_0)$ with gadget $P_{\text{ks}} = b_0 \approx 2^{61}$ and $2^{60m}$ limbs ($m \in \{0..3\}$), each custodian $i \in \{0,1,2\}$ computes $b_i^{(m)} = -a^{(m)} s_i + P_{\text{ks}} 2^{60m} s_i^{(2)} + e_i^{(m)}$ from its local $(s_i, s_i^{(2)})$ (`pairwise_ring_ole_2sisj`) without ever reconstructing $s$ or $s^2$, verified consistent with `cluster.pub_key.b_coeff`. Every relinearization passes `verify_and_ingest_relinearized_ct` (`C8` handle check + canonical RNS bounds + deterministic `relinearize_ct3` equality).
- **Exact Negacyclic Outer-Product Slot Packing (`[DERIVED]`):** Packing each $d_r \times d_c$ ($128 \times 64 = 8192$) block of $S_{t-1}^\top$ at $X^{r d_c + c}$:
  1. Constant monomial $P_\alpha(X) = \alpha_t X^0$ scales every slot of $S_{t-1}^\top$ with **zero** negacyclic wrap.
  2. Strided $P_u(X) = \sum_{r=0}^{d_r-1} (\beta_t u_{t,r}) X^{r d_c}$ times contiguous $P_k(X) = \sum_{c=0}^{d_c-1} k_{t,c} X^c$ has degree $\le (d_r - 1)d_c + (d_c - 1) = d_r d_c - 1 = 8191 < N$, landing $(\beta_t u_{t,r}) k_{t,c}$ at $X^{r d_c + c}$ with **zero slot collisions and zero mod-$(X^N+1)$ wrap**.
  3. Subsequent reads $S_t^\top \cdot k_{\text{rev}}$ extract slots $r d_c + (d_c - 1) \ge 63$, while wrap terms reach degree at most $(N-1) + (d_c - 1) - N = 62 < 63$ (**zero interference**).
  4. Both `TwoMulRelinearizeSum` (`2` `HoistedSuccinctBundle`s + `2` `relinearize_ct3` + `verify_and_ingest_ct2_sum`) and `FusedHoistedK2` (`K_blk = 2` sum-before-rescale + `1` `relinearize_ct3`, `2x` smaller update proof) are implemented and verified bit-exact across 6 turns (including $\alpha_t = 0$ reset).

---

## 3. Oblivious 3-Party SPDZ Crossings & Private-Router Top-2 SwiGLU MoE

1. **Sign-Unambiguous Blum-Prime `RMSNorm` (`spdz_rmsnorm_checked`, `[DERIVED]` + `[EXECUTED]`):** Since $t \equiv 3 \pmod 4$, $|Q_t| = (t-1)/2$ is odd, so $y \mapsto y^{(t+1)/4} \bmod t$ is the unique positive square-root homomorphism on $Q_t = (\mathbb{F}_t^*)^2$ with $((c^2)^2)^{(t+1)/4} = +c^2$ identically (**zero $\pm 1$ sign ambiguity**). The 3 custodians jointly sample secret `[c] = [c_0][c_1][c_2]` and `[\sigma] = [s_0][s_1][s_2]` from independent `/dev/urandom` streams, open uniform $u = \sigma c^4 s_{\text{ms}} \in \mathbb{F}_t^*$ and run `spdz_mac_check` **before** zero-branching (blocking active rushing custodians from shifting $u \to 0$), recover $[\chi], [r_{\text{inv}}]$, and enforce blinded $([\chi]-1)([\chi]+1) = 0 \land [\chi][s_{\text{ms}}][r_{\text{inv}}]^2 - 1 = 0 \land (c_{\text{qr}}^2 r_{\text{inv}})^{(t-1)/2} = 1$ (`r_inv ∈ Q_t`, rejecting $-r_{\text{inv}}$) + `spdz_mac_check`.
2. **Zero-Leakage Private-Router Top-2 MoE (`spdz_private_router_top2`, `[DERIVED]` + `[EXECUTED]`, closing `notes/moe-router-binding.md` §1.1):**
   - Decomposes each secret logit $[l_e] \in [0, t)$ into 33 exact integer bits via a 3-party XOR `edaBit` ($r = r^{(0)} \oplus r^{(1)} \oplus r^{(2)} < t$, unknown to $\le 2$ custodians) + dual 33-bit ripple-carry adders + MUX + booleanity/reconstruction check + `spdz_mac_check`.
   - Appends the 4-bit `C3` tie-breaker $(E - 1 - e)$ (`notes/moe-router-binding.md` §2.3), runs $\binom{E}{2}$ 37-bit pairwise comparisons, evaluates degree-$(E-1)$ Lagrange indicators at ranks `0` and `1`, verifies `C1` booleanity, `C2` sum-to-1, and Top-2 disjointness ($e_{0,j} e_{1,j} = 0$), and normalizes gates via 3-party Bar-Ilan–Beaver inversion (with verified `denom == 0 -> [1/2, 1/2]` fallback so $g_0 + g_1 \equiv 1 \pmod t$ unconditionally).
   - Emits encrypted 1-hot selectors $\text{Enc}_{pk}(e_{\text{sel}}^{(0)}), \text{Enc}_{pk}(e_{\text{sel}}^{(1)})$ and Kronecker-gated activations $\text{Enc}_{pk}(e_{\text{sel}}^{(r)} \otimes h_{1,\text{norm}})$ against horizontally stacked `[W_gate; W_up]` and fused `W_down` (`verify_and_ingest_pinned_persistent_bundle` pinning each layer's `a_pcs_root` + `Qp` limbs). The host's ciphertext dimensions and RLWE distributions are **100% invariant** to which Top-2 experts fired.

---

## 4. `[EXECUTED]` Benchmarks (`N = 8192`) & Adversarial Falsifiers

**Commands (`exit 0`, zero `darkvfhe` warnings):**
```sh
cd /Users/ember/dev/zkml-research/native
RAYON_NUM_THREADS=4 CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-darkblock \
  cargo test --release -p darkvfhe --test homomorphic_gdn_and_block
RAYON_NUM_THREADS=4 CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-darkblock \
  cargo run --release -p darkvfhe --bin dark_block_bench
```

| Workload @ Deployed `N = 8192, t = 4,355,803,843` (`RAYON_NUM_THREADS=4`) | State Update / Turn | End-to-End / Turn | 4-Turn / 3-Turn Crossings & Wire | Accuracy & Leakage |
|---|---:|---:|---|---:|
| **Wave-6 `DarkGdnResident`** (`d_k=d_v=128, V=256`, per-turn `S2E` + PCS refresh) | `3,871.8 ms` | `13,506.8 ms` | `133,632` triples, `20` E2S, `24` S2E (`16,384` state slots/turn) | `max\|diff\| = 0` |
| **Upgraded `HomomorphicDarkGdnResident`** (`FusedHoistedK2`, `R_refresh = 3`) | **`2,758.5 ms` pure (`1.40x`; `1.54x` peak, `2.17x` @ 16T)** / `2,867.9 ms` amort (`1.35x`) | **`12,316.9 ms` (`1.10x`)** | **`35,328` triples (`3.8x` fewer)**, `14` E2S, `2` sparse state S2E (`129` slots, `2.09 MiB` prf) | `max\|diff\| = 0` |
| **Full `EncryptedQwenHybridBlock`** (`V=256, d=128, E=8 Top-2, d_ff=64`, Genesis `6.42 s`) | `2,579.9–2,615.9 ms` pure / `3,307.5 ms` reset | **`46,533.6–47,935.2 ms`** (`Host 23.7 s`, `Cust+SPDZ 23.7 s`) | `69,028` triples (`3` turns), `41` E2S, `168` S2E, `9–10` bundles (`26.83–28.93 MiB`), `6.75 GiB` RSS | **`max\|diff\| = 0`, `0` leaked expert IDs** (`[4,6]`, `[4,0]`, `[3,2]`) |

- **Adversarial & Cross-Audit Suite (`4/4` test suites PASS in `747.91 s`, `5/5` `--lib` unit tests PASS in `0.58 s`):**
  - **Attacks 1–7 (`[EXECUTED]`):** (1) Unverified `Ct3` relin (`C8 ABORT`) & +1 limb-forged relinearized `Ct`; (2) Unverified router/state `E2S` oracle probe (`C8 ABORT` before share release); (3) `HoistedSuccinctBundle` Hole-B quotient shift & PCS column mutation on state update; (4) `R_PD` cross-ciphertext replay & `partial_rns` tamper; (5) Forged `RMSNorm` `r_inv` quadratic witness & SPDZ MAC tamper; (6) Non-boolean `[2, t-1, 0..]` (`C1`), duplicate-expert (`disjointness`), and all-zero capacity-drop (`C2`) MoE selectors; (7) Cross-layer persistent-matrix swap (`W_gdn_out <-> W_router` equal-shape `a_pcs_root` pin).
  - **Cross-Audit Regressions (`#112`, `[EXECUTED]`):** OS `/dev/urandom` ciphertext handle freshness on identical genesis state; rejection of `refresh_cadence > R_refresh_correctness`; exact `denom == 0 (mod t)` sum-of-two-squares router vector satisfying $g_0 + g_1 \equiv 1 \pmod t$ in both cleartext and 3-party SPDZ; and transactional `StagedStateUpdate` rollback before `open_verified_output`.

## 5. Remaining `[OPEN]` Boundaries

1. **Compose `WhirPcs61` (`GMask61`) into `EncryptedQwenHybridBlock` (`[OPEN]`):** Swapping `DVFHEPC1` Ligero openings (`26.83–28.93 MiB`/turn across `9–10` bundles) onto `whir_pcs.rs` (`~77x` smaller openings) will shrink full hybrid-block per-turn proof wire below `~400 KiB`.
2. **Widened `Qp` (`4–5` 61-bit primes, `log2 Q = 244–305`) for Multi-Turn `>40b` TVD (`[OPEN]`):** Adding +1..2 `Qp` primes lifts $E \approx 2^{172..233}$ so `R_refresh(>40b TVD)` matches `R_refresh(correctness) >= 3` without per-turn smudging resets.
3. **Distributed Ceremony & Turn-Tagged Handle Admission (`[OPEN]`):** `setup_threshold_cluster_with_rlk` simulates the 3-custodian RLK/SPDZ setup from a single harness seed (`R1-4`) and admits verified ciphertext handles into a set without per-turn/role epoch tags (`R1-6`); production deployment requires interactive pairwise Ring-OLE keygen and turn-scoped custodian handle staging.
