# Native Multithreaded Rust (`darkvfhe`) `HoistedB61` Engine, `D1b` LogUp-GKR Prover/Verifier, and `N = 8192` Wall-Clock Benchmarks

**Date:** 2026-11-21 · **Lane:** `native-hoist61-rs` (`system_wave_2026_11_21`, Worker 1)  
**Crate:** [`native/darkvfhe/`](../native/darkvfhe/) (`Cargo.toml`, `src/{lib,bigint,rns_hoist,digits,logup_gkr,cert}.rs`, `src/bin/bench_hoist61.rs`, `tests/correctness_and_falsifiers.rs`)  
**Companion Evidence:** [`notes/vfhe-hoisted-certificate-breakthrough.md`](vfhe-hoisted-certificate-breakthrough.md) · [`vfhe_hoisted_b61_and_pir.py`](../research/vfhe_sota_2026_11_21/experiments/vfhe_hoisted_b61_and_pir.py) · [`BfvHoistedRescale.lean`](../research/vfhe_sota_2026_11_21/formal/Theory/BfvHoistedRescale.lean) · [`AirSumcheckCubic.lean`](/Users/ember/dev/minidregg/Assurance/AirSumcheckCubic.lean)

**Claim tags (`AGENTS.md`):** `[EXECUTED]` measured/tested in `native/darkvfhe` on this machine · `[DERIVED]` exact algebra/arithmetic · `[SOURCE]` read at named repo/paper location · `[OPEN]` unverified boundary.

---

## 0. Executive Verdicts (Closing `[OPEN]` Boundary #2 of `vfhe-hoisted-certificate-breakthrough.md`)

[`notes/vfhe-hoisted-certificate-breakthrough.md`](vfhe-hoisted-certificate-breakthrough.md) (§4.2 #2) left native multithreaded Rust wall-clock execution of `HoistedB61` + 61-bit `D1b` LogUp-GKR at $N = 8192$ as its #1 `[OPEN]` engineering boundary. Building and `--release`-benchmarking **`darkvfhe`** on a 12-core Apple M2 Max (`96 GB` RAM, `rustc 1.98.0-nightly`) closes it end-to-end:

1. **`51×–54×` Prover & `71×–973×` Verifier Speedup over Python at Deployed `N = 8192` (`[EXECUTED]`):**
   On a 1-block (`R=1, K=1`) `N = 8192` product ($\log_2 Q = 183, \log_2(Q B) = 488$), `vfhe_hoisted_b61_and_pir.py` takes **`10,744.9 ms` build + `1,497.6 ms` verify (`Direct-20`)** and **`12,097.5 ms` build + `1,916.8 ms` verify (`Exact-Garner-15`)** *without* `D1b` GKR trees `[EXECUTED: M2 Max Python 3]`. Native `darkvfhe` *including* full 61-bit `D1b` LogUp-GKR (`999,424`–`1,916,928` lookups + `2^{20}` `ProveKit v2` table tree) proves in **`200.51 ms` (`Direct-20`, `53.6×` faster)** / **`236.98 ms` (`Exact-Garner-15`, `51.0×` faster)** and verifies in **`21.15–25.16 ms` full (`70.8×–76.2×` faster)** or **`1.54 ms` succinct (`973×` faster)** `[EXECUTED]`.
2. **`d = 4096, N = 8192` Forward Block Matvec (`2,048 -> 32` Blocks) in `118.1 ms` FHE / `1.75 s` Full `HoistedB61+D1b` Prover / `24.5 ms` Succinct Verifier (`[EXECUTED]`):**
   Hoisting `32 × 64 = 2,048` encrypted blocks into `32` row-group rescales cuts FHE execution **`6.08×` cold (`3,825.7 -> 629.2 ms`)** and **`32.4×` warm (`3,825.7 -> 118.09 ms`, `17,343 blocks/s`)**, shrinks zero-error BEHZ rounding noise **`8.12×` (`66,571 -> 8,201`)** at $N = 8192, K = 64$, proves all `2,048` blocks (`~32M` `D1b` lookups) in **`1,753.7 ms` (`Direct-20`)** / **`2,230.6 ms` (`Exact-Garner-15`, `+27%` for zero-slack `[0, Q-1]`)**, and verifies in **`726.5 ms` (full `805 MiB` ciphertext SHA-256 + MLE openings)** or **`24.55 ms` (succinct PCS-oracle verifier)** `[EXECUTED]`.
3. **End-to-End Deployed System Regimes at `d = 4096, N = 8192` (`[EXECUTED]`):**
   - **`vFHEML` 2-Layer Inference (`4,096 -> 64` hoisted cts, persistent `Enc(W)`):** **`2.84 s` online prove**, **`1.78 s` full verify** (`~49.1 ms` succinct), `1.984 Gbit` (`w=20`) / `4.477 Gbit` (`digits61`), `1,611.4 KiB` `D1b` GKR proof.
   - **`Hoist(b, τ = 64)` Exact Dense SGD (`6,144 -> 128` matvec certs + `τ = 64` temporal outer-product flush):** **`8.00 s` total amortized host FHE + `HoistedB61` prover wall-clock per step** (`6.03 s` 3-matvec prove + `1.74 s` unrescaled outer NTT accumulation + `185.3 ms/step` amortized BEHZ rescale & `P_ks = b_0` RNS-gadget relinearization flush).
   - **`Dark-vPIR` (`V = 151,936, d = 4096`, `75,968 -> 32` hoisted cts, fits `k = 5`):** **`3.91 s` (`19,453.9 blocks/s`)** across all `75,968` encrypted blocks (`14.94B` 61-bit MACs) + `1.46 s` shared query NTT (`2,374` cts); online query lift (`47,480` digit polys) + Row-0 `HoistedB61+D1b` prove = **`19.17 s`**, verify = **`3.24 s`**, peak RSS = **`16.75 GiB` (`17,155.5 MiB`)**.

---

## 1. Algorithmic & Systems Architecture of `native/darkvfhe`

1. **Zero-Allocation Stack CRT & Exact BEHZ Division ([`bigint.rs`](../native/darkvfhe/src/bigint.rs), `[DERIVED]`, `[EXECUTED]`):**
   - Every deployed prime $p_l \in Q_p \cup B_p \cup \{t\}$ has Crandall form $p_l = 2^{61} - \delta_l$ with $\delta_l < 2^{22}$ (`Qp = [2^61-376831, 2^61-573439, 2^61-999423]`, `t = 2^61-1294335`, `Bp = [2^61-2031615, ..., 2^61-3178495]`), enabling hardware-division-free `u128 -> u64` reduction (`FastPrime61::red128`) in two 61-bit shifts/muls and one conditional subtraction (`lib.rs:51-61`).
   - Input base extension $Q_p \to Q_p \cup B_p$ (`lift_q_to_8limbs_and_u`) uses 3-limb `[u64; 3]` Garner mixed radix, and post-NTT tensor reconstruction (`behz_rescale_from_8limbs`) uses 8-limb Garner into stack `[u64; 9]` (`576` bits) + normalized Knuth-D division `divrem_u576_by_u192`, matching `num_bigint::BigInt::div_mod_floor` bit-for-bit across `2,000` randomized 384-bit signed tests (`bigint::tests::divrem_and_behz_match_bigint_exact`, `0` heap allocations per coefficient).
2. **`O(N log N)` Dual Negacyclic/Cyclic Quotient Extraction & 32-Way Lazy `u128` MAC ([`rns_hoist.rs`](../native/darkvfhe/src/rns_hoist.rs), `[DERIVED]`, `[EXECUTED]`):**
   - Because $32 \times 2 \times (2^{61}-1)^2 < 2^{128}-1$, `accumulate_row_limb` accumulates 32 blocks of $(a_0 b_0,\, a_0 b_1 + a_1 b_0,\, a_1 b_1)$ in `u128` before a single `red128` fold (`2` reductions total for $K = 64$).
   - Instead of $O(N^2)$ schoolbook or Kronecker big-int multiplication to obtain the degree-$< N-1$ ring quotient $K_{k,p}^{(r)}(X)$ in $P_{k,\text{sum}}^{(r)}(X) = D_k^{(r)}(X) + (X^N+1)K_k^{(r)}(X)$, `HoistedEngine` pairs `darkstep::ntt::Ntt` ($D \equiv P \bmod (X^N+1)$) with `CyclicNtt` ($C \equiv P \bmod (X^N-1)$ using $\omega_N = \psi_0^2$) and recovers $K_{k,p}^{(r)} = (C - D) \cdot 2^{-1} \bmod p$ in $O(N \log N)$, with built-in top-degree invariant $C_{N-1} = D_{N-1}$ (`rns_hoist.rs:582-599`).
   - `RelinearizationKey` & `relinearize_ct3` (`rns_hoist.rs:178-255, 636-698`) extract 10 $w=20$ digits of $c_2 \in [0, Q)$, group triples into four 60-bit gadget limbs $g_0 \dots g_3$, multiply in the 4-prime $(q_0, q_1, q_2, b_0)$ NTT domain, and modulus-switch $P_{\text{ks}} = b_0$ with `>100` bits of noise headroom.
3. **Prime-Independent Digit Prepacking & Unconstrained-`F_p` Narrowed-Top Soundness ([`digits.rs`](../native/darkvfhe/src/digits.rs), [`cert.rs`](../native/darkvfhe/src/cert.rs), `[DERIVED]`, `[EXECUTED]`):**
   - Prepacking `Direct-20` columns into `(lo100, hi83)` `u128` pairs and `Exact-Garner-15` columns into `(r0, r1, r2)` `u128` triples *once* outside the 8-prime loop cuts multi-prime polynomial evaluation work by **`~10×`** while preserving exact algebraic identity over $\mathbb{Z}$ and $\mathbb{F}_p$.
   - **Soundness catch sealed (`digits.rs:146-160, 290-332`):** Checking *only* $2^{17} d_9 \in [0, 2^{20})$ in $\mathbb{F}_p$ against an unconstrained $\mathbb{F}_p$ witness would admit $d_9 = 2^{-17}\cdot 5 \bmod p \notin \mathbb{Z}_{<8}$ via mod-$p$ inverse wrap. `darkvfhe` emits *both* $d_{\text{top}} \in [0, 2^{20})$ and shifted complement $d_{\text{top}} + (2^{20} - 2^{\text{top\_bits}}) \in [0, 2^{20})$ (where $d_{\text{top}} < 2^{20} \implies d_{\text{top}} + 2^{20} - 2^k < 2^{21} \ll p$, preventing wraparound), plus `Exact-Garner-15`'s linear boundary complement $T_i \bmod p$.
4. **Forked-Subtranscript Parallel `D1b` LogUp-GKR + $O(\log M)$ Selector Verifier ([`logup_gkr.rs`](../native/darkvfhe/src/logup_gkr.rs), `[DERIVED]`, `[EXECUTED]`):**
   - Forking deterministic witness-bound subtranscripts per $2^{18}$ chunk (`FsTranscript::fork_sub`) runs degree-3 `cubicForm` GKR sumchecks across all 12 cores simultaneously while dropping per-tree layer buffers immediately (`O(\text{threads}\cdot 2^{18})` bounded L2/RAM footprint).
   - At the leaves, the verifier evaluates the $[0, 2^{20})$ table identity $\tilde{\text{id}}(z) = \sum_{b=0}^{19} 2^b z_b$ in **`20` muls** and the non-power-of-two active prefix selector $\widetilde{\text{sel}}_{[0, M)}(z)$ in **$O(\log M)$ muls** via binary subcube decomposition (`eval_prefix_selector_le`, `logup_gkr.rs:212-238`).

---

## 2. Executed Correctness, Python Cross-Check, & Adversarial Falsifier Ledger

Command (`[EXECUTED]`, `0` warnings in `darkvfhe`, `6/6` test suites pass in `1.68s`):
```sh
cd /Users/ember/dev/zkml-research/native && \
  CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-darkvfhe cargo test --release -p darkvfhe
```

| Test / Adversarial Falsifier (`tests/correctness_and_falsifiers.rs`) | Target Invariant | Outcome (`[EXECUTED]`) |
|---|---|---|
| `divrem_and_behz_match_bigint_exact` (`2,000` 384b cases) | Stack `U576 / U192` + 8-limb Garner vs `BigInt::div_mod_floor` | **PASS** (`0` bit discrepancies) |
| `test_python_vs_rust_cross_check_bit_exact` (spawns `python3`) | Bit-exact match vs `vfhe_hoisted_b61_and_pir.py` (`Qp, Bp, t`, `out_cts`, `Direct-20`, `Exact-Garner-15`, `K_res`) | **PASS** (100% bit-identical) |
| `test_bit_exact_decryption_rounding_noise_relin_and_tau_outer` | `N ∈ {128, 8192}, K = 64` decrypt + rounding drop (`66,571 -> 8,201 = 8.12×`) + `P_ks=b_0` relin + `τ = 8` outer flush | **PASS** (bit-exact `mod t`) |
| **Falsifier 1 (`Hole B` mod-$Q$ alias)** | `Q=31, t=4` (`z=32 ≡ 1`) & full `HoistedB61` `y_0[0] + 1` mod-$Q$-preserving forgery | Mod-$Q$ **ACCEPTS**; `HoistedB61` **REFUSES** (`Bp` check) |
| **Falsifier 2 (`Attack F-FS`, Astra E5)** | Adaptive quotient shift forging decrypted plaintext at predictable statement-only $r_{\text{FS},p}$ | Legacy FS **ACCEPTS**; `HoistedB61` **REFUSES** |
| **Falsifier 3 (`Attack F-Boundary`, Astra E4/E7)** | Non-power-of-two strip alias $u' = 42 + Q \in [Q, 2^{183})$ (`r_2 >= q_2`) | `< 2^{183}` **ACCEPTS**; `Exact-Garner-15` & `D1b` **REFUSE** |
| **Falsifier 4 (`wrong_quotient`, `mixed_limbs`, `stale_parent`, `wrong_delta`)** | Full-RNS `SHA-256` handle + cross-limb opening + output binding (`Hole A`) | **`4 / 4` REFUSED** |
| **Falsifier 5 (Out-of-range digit `2^{20}` vs pure `D1b` LogUp-GKR)** | `D1b` rational root balance (`BatchedC3` & `MonolithicC4`) with `direct_digit_check = false` | **REFUSED** (`rational sum balance failed`) |

---

## 3. Real `--release` Wall-Clock Benchmarks (`N = 8192`, 12-Core Apple M2 Max)

Command (`[EXECUTED]`, exits `0` in `77.88s`):
```sh
cd /Users/ember/dev/zkml-research/native && \
  CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-darkvfhe cargo run --release -p darkvfhe --bin bench_hoist61
```

### 3.1 Forward Block Matvec Scaling (`d ∈ {64, 256, 1024, 4096}`, `N = 8192`, `8 × 61b` Primes)

| Width `d` | Blocks (`In -> Out`) | `Eager` FHE (`ms`) | `Hoist` Cold (`ms`) | **`Hoist` Warm (`ms`)** | **`Prove` `Direct-20` (`ms`)** | **`Prove` `Exact-Garner-15` (`ms`)** | `Verify` Full (`ms`) | **`Verify` Succinct (`ms`)** | Peak RSS (`MiB`) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `64` | `1 -> 1` | `18.49` | `17.53` | **`15.08`** | **`180.42`** | **`209.80`** | `19.53` | **`1.539`** | `452.7` |
| `256` | `8 -> 2` | `31.85` | `20.25` | **`15.17`** | **`222.63`** | **`253.80`** | `25.29` | **`2.732`** | `816.4` |
| `1024` | `128 -> 8` | `237.83` | `63.14` (`3.8×`) | **`23.16` (`10.3×`)** | **`470.45`** | **`703.95`** | `74.14` | **`5.605`** | `1,854.5` |
| **`4096`** | **`2048 -> 32`** | `3,825.70` | **`629.15` (`6.1×`)** | **`118.09` (`32.4×`)** | **`1,753.73`** | **`2,230.61`** | `726.54` | **`24.546`** | `10,822.9` |

### 3.2 1-Block Cold `N = 8192` Baseline Comparison (Rust `darkvfhe` + `D1b` GKR vs Python `vfhe_hoisted_b61_and_pir.py`)

| Configuration (`N = 8192, R = 1, K = 1`, Cold Inputs) | Prover (`ms`) | Full Verify (`ms`) | `D1b` Lookups | `D1b` GKR Proof (`KiB`) | Cert (`w=20` / `digits61`) | Speedup vs Python (Prove / Verify) |
|---|---:|---:|---:|---:|---|---:|
| Python `vfhe_hoisted_b61_and_pir.py` (`Direct-20`, no GKR) | `10,744.90` | `1,497.60` | *(direct loop)* | — | `51.31` / `131.92 Mbit` | `1.0×` / `1.0×` |
| Python `vfhe_hoisted_b61_and_pir.py` (`Exact-Garner-15`, no GKR) | `12,097.50` | `1,916.80` | *(direct loop)* | — | `57.05` / `149.41 Mbit` | `1.0×` / `1.0×` |
| **Rust `darkvfhe` `Direct-20 + D1b(c=3, 2^18)`** | **`200.51`** | **`21.15`** (`1.54` succ) | `999,424` | **`34.09 KiB`** | `51.31` / `131.92 Mbit` | **`53.6×` / `70.8×` (`973×` succ)** |
| **Rust `darkvfhe` `Exact-Garner-15 + D1b(c=3, 2^18)`** | **`236.98`** | **`25.16`** | `1,916,928` | **`59.62 KiB`** | `57.05` / `149.41 Mbit` | **`51.0×` / `76.2×`** |
| **Rust `darkvfhe` `Exact-Garner-15 + D1b(c=4, monolithic)`** | **`379.07`** | **`27.81`** | `1,916,928` | **`17.84 KiB`** | `57.05` / `149.41 Mbit` | **`31.9×` / `68.9×` (`3.34×` smaller GKR)** |

### 3.3 End-to-End System Regimes at `d = 4096, N = 8192` (`[EXECUTED]`)

| Deployed Regime (`d = 4096, N = 8192`) | Hoisted Reduction | Measured Native Wall-Clock Breakdown (12-Core M2 Max) | Online `ct×ct` Cert (`w=20` / `digits61`) |
|---|---|---|---|
| **`vFHEML` 2-Layer Inference** (`W1 x`, `W2 h`; persistent `Enc(W)` offline `1,430.4 ms`/layer) | `4,096 -> 64` cts | **`2,839.23 ms` (`2.84 s`) online prove** · `1,776.65 ms` full verify (`~49.1 ms` succinct) · `1,611.4 KiB` GKR | **`1.984 Gbit` / `4.477 Gbit`** (full step `3.73` / `10.78 Gbit` < 2L-MPC `12.89 Gbit`) |
| **`Hoist(b, τ = 64)` Exact Dense SGD** (`3` matvecs + `τ=64` outer NTT acc + flush/relin) | `6,144 -> 128` matvec + `64×` outer | `6,034.52 ms` 3-matvec prove + `1,735.99 ms` 1-step outer NTT acc (`4,096` blks) + `11,858.40 ms / 64 = 185.29 ms` flush+relin = **`8,000.49 ms` (`8.00 s`) / step** | **`11.08 Gbit` packed / `21.50 Gbit` `digits61` w/ §20.2 ZKPoPK** (`0.68×` MPC `31.50 Gbit`!) |
| **`Dark-vPIR` Encrypted Embedding** (`V = 151,936, d = 4096`, `k = 5`, $2^{451} < 2^{488}$) | `75,968 -> 32` cts (`601.4×` cert) | `1,460.07 ms` query NTT (`2,374` cts) + **`3,905.03 ms` (`19,453.9 blks/s`)** full `75,968`-blk FHE matvec · `19,166.74 ms` query-lift+Row-0 prove · `3,235.65 ms` verify · `17,155.5 MiB` peak RSS | **`8.58 Gbit` (`w=20`) / `25.37 Gbit` (`digits61`)** (down from `15,260.7 Gbit`!) |

---

## 4. Remaining `[OPEN]` Boundaries & Proposed Maintainer Folds

- **Remaining `[OPEN]` Boundaries:**
  1. **Composing `darkvfhe` with `darkproof` Coset/WHIR PCS Openings (`[OPEN]`):** `darkvfhe` currently hashes witness columns into a SHA-256 commitment root (`compute_witness_root`) and measures both full-opening (`726.5 ms`) and PCS-oracle (`24.55 ms`) verification; wiring `darkproof::pcs::PcsParty` / WHIR LDE commitments onto the `HoistedWitness` digit columns will realize the full succinct proof byte budget on the custodian wire.
  2. **Post-Cutoff `PRISM` (`ePrint 2026/1956`) Full-PDF Audit (`[OPEN]`):** Remains above local mirror cutoff `2026/1861` (`0` `eprint.iacr.org` requests made).
- **Proposed Folds (Maintainer Fold Only — `VERDICTS.md` Untouched):**
  - **[`docs/VERDICTS.md`](../docs/VERDICTS.md) §3 & §7.5:** Mark [`vfhe-hoisted-certificate-breakthrough.md`](vfhe-hoisted-certificate-breakthrough.md) §4.2 #2 (`Rust Wall-Clock Prover Timing`) **CLOSED** by `native/darkvfhe`: `1.75 s` (`Direct-20`) / `2.23 s` (`Exact-Garner-15`) per `d = 4096` (`2,048 -> 32`) `N = 8192` matvec with 61-bit `D1b` LogUp-GKR (`24.55 ms` succinct verify), `8.00 s/step` amortized host FHE+prove for `Hoist(b, τ=64)` exact dense SGD, and `3.91 s` (`19,454 blocks/s`) FHE execution on `75,968`-block `Dark-vPIR`.
  - **[`docs/DARK-LEARNING-SCHEME-DECISION.md`](../docs/DARK-LEARNING-SCHEME-DECISION.md) §24:** Cross-reference `native/darkvfhe` (`notes/native-hoisted-b61-rust-benchmarks.md`) for concrete M2 Max wall-clock timings alongside the §24 Gbit/wire tables.
