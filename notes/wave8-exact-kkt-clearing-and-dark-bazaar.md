# Wave 8 — Quarried `FHQPB001` Exact SDD/KKT Certificates & `NoSingleViewer >= 2` `DarkBazaar` Clearing

**Search Ledger:** `Scry: 0`, `Kagi: 0`, `eprint.iacr.org downloads: 0` (local companion/donor audit only).

## 1. Donor Audit & Vulnerability Closure

- `[SOURCE]` `breadstuffs/fhir/src/qp_certificate.rs:1-420` & `breadstuffs/metatheory/Market/{SddPsd.lean,CertQp.lean,QpCertificateBundle.lean}` define the `FHSDD001` row-diagonal-dominance checker and `FHQPB001` primal-dual KKT bundle, requiring an entry-for-entry Matrix Pin between the admitted PSD witness and the KKT Hessian `Q` (`tooth_matrix_pin_omitted_unsound`).
- `[SOURCE]` `breadstuffs/starbridge-apps/privacy-voting/tests/tally_forgery.rs:1-62` demonstrates an unproved BFV ballot forging `1,000,000` votes in a single ciphertext (`[REFUTED: unproved BFV intake]`: homomorphic addition preserves privacy only if ciphertext plaintext ranges are proved at intake).
- `[SOURCE]` `breadstuffs/dreggnet-market/src/lib.rs:696-750` (`do_settle` / `reveal_bid`) reveals individual limit orders in cleartext prior to clearing (`[REFUTED: commit-reveal individual opening]`: leaks losing/unfilled institutional order curves).
- `[SOURCE]` `obend/lean/Obend/{Judge/Clearing.lean,Judge/Netting.lean,Crypto/DarkBazaar.lean}` specify `NoSingleViewer >= 2` batch-only opening and multilateral settlement conservation, leaving concrete lattice instantiation open.

## 2. Lean `v4.35.0` Formalization (`Theory/ExactKktClearingCert.lean`)

- `[EXECUTED]` Kernel-verified [ExactKktClearingCert.lean](file:///Users/ember/dev/minidregg/Theory/ExactKktClearingCert.lean) (`906` lines `< 950`, Lean `v4.35.0` with `-DwarningAsError=true`, `0` warnings in `3.98 s`, `0 sorry`, `0` custom `axiom`, `0 native_decide`, `0 #guard`, `21` `#guard_msgs`-pinned `#print axioms` within `{propext, Classical.choice, Quot.sound}`; `scripts/check-import-boundary.sh` passed):
  - **Part A (`O(|E|)` SDD-to-PSD):** Proved `sddFactor_quadForm_eq`, `sddFactor_implies_psd` (`Q = ∑ w_e b_e b_eᵀ + diag(d)` with `w_e ≥ 0, d_i ≥ 0` certifies `∀ x : Fin n → ℚ, 0 ≤ xᵀ Q x` with `0` square roots or floats), `scaled_dd_implies_psd`, executable `FHSDD001` `checkSddRowDomInt_implies_psd`, plus falsifier teeth `tooth_negative_edge_weight_not_psd` and `tooth_indefinite2_refused_and_not_psd`.
  - **Part B (`FHQPB001` KKT Global Optimality):** Proved `primal_sub_dual_eq_compGap` (`p* - d* = compGap`), `lagrangian_weak_duality`, `kkt_bounded_gap_global_optimal` (`p* - d* ≤ ε` certifies `f(x*) ≤ f(y) + ε` for every feasible `y`), `kkt_complementary_slackness_exact_optimal`, executable division-free `ℤ` `checkFhqpb001BundleInt_sound`, plus `tooth_matrix_pin_omitted_unsound`, `tooth_wrong_sign_dual_rejected`, and `tooth_gap_exceeded_rejected`.
  - **Part C (Multilateral Netting & Joint Keystone):** Proved `sum_netBalance_eq_zero` (`0` value creation), `checkMultilateralNetting_sound`, `fhqpb001_clearing_and_netting_keystone`, inhabited `clearing_and_netting_joint_witness` (`280 → 50` gross volume, `82.1%` compression), plus `tooth_value_creation_leg_refused` and `tooth_exposure_inflation_refused`.

## 3. Native Rust Engine (`darkvfhe::dark_clearing`) & Benchmarks

- `[DERIVED]` **Wrap-Free 3-Prime BFV `WhirPcs61` Submission Proof (`DBWHIR61`):** Over `params_n8192_homo()` (`N = 8192`, `log2 Q = 183`, Blum prime `t = 4,355,803,843`, `Q mod t = 730`), for all `m_j ∈ [0, 65535]`, `2 · (Q mod t) · m_j < t`, so `Rns::encode_round(m_j)[k] = (Δ_k · m_j) mod q_k` with zero rounding carry. Splitting `(B_k, A_k, Δ_k, q_k, c_{0,k}, c_{1,k})` at `2^38` with quotient `w_{b,k} ∈ [-2^18, 3·2^18)` and carry `carry_{b,k} = low_num / 2^38 = -high_num` (`|carry| ≤ 147,455 < 2^18` honest; `|Low_res| ≤ 4.53 × 10^17 < p_0/2` and `|High_res| ≤ 7.22 × 10^12 < p_0/2` adversarial) binds all three 61-bit RNS primes inside `WhirCommittedPcs61` (`192` queries = `130.1b` `[BCIKS20]` UD / `185.3b` `[DKT26]` MCA, `GMask61` HVZK, `0` unblinded witness evaluations) + `D1b` `LogUpGkrProof` (`MonolithicC4` with CSPRNG lookup blinding).
- `[DERIVED]` **Dealerless `NoSingleViewer >= 2` $t$-of-$n$ Threshold BFV:** Shamir keygen over `R_Q` cleared by `L_fact = (n - 1)!` (`gcd((n - 1)!, t) = 1` for `n ≤ 16`) with `2^110` smudging noise (`> 70b` TVD drowning, `> 20b` decryption margin below `Q/(2t) ≈ 2^149.98`), per-custodian `C8` `HandleRole` gate (forbidding individual ciphertext decryption even by `≥ t` custodians), voter/bidder nullifier deduplication, and strictly monotonic `epoch_latch`.
- `[EXECUTED]` Command: [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/wave8_forward_extrapolation_2026_11_21/formal_kkt/build_and_verify.sh) (`exit 0`, `0` warnings under `#![deny(warnings)]` + `-D warnings` on [dark_clearing.rs](file:///Users/ember/dev/zkml-research/native/darkvfhe/src/dark_clearing.rs) and [dark_bazaar_kkt.rs](file:///Users/ember/dev/zkml-research/native/darkvfhe/tests/dark_bazaar_kkt.rs)):

| Workload (`--release`, Apple Silicon) | Prover / Solver | Verifier | Wire Size | Outcome |
| :--- | ---: | ---: | ---: | :--- |
| `FHQPB001` 4-tick SDD-Laplacian Call-Auction (`n = 8, meq = 1`) | `< 1 ms` | `10 µs` | `1,868 B` | `[EXECUTED]` `comp_gap = 0` (`p* = d*`) |
| `DBNET001` 5-Party Multilateral Netting (`6 → 3` legs) | `< 50 µs` | `1 µs` | `232 B` | `[EXECUTED]` `1,500 → 80` vol (`94.7%` saved) |
| `DarkBazaar` `N = 8192` Single-Bidder `DBWHIR61` Proof | `668.66 ms` | `12.28 ms` | `353,092 B` | `[EXECUTED]` `130.1b` UD, `0` leaked evals |
| `DarkBazaar` `N = 8192` 3-Bidder `2-of-3` Epoch Clearing | — | `47.50 ms` | — | `[EXECUTED]` Aggregate-only opening + KKT |
| Private `{0,1}` Tally `N = 8192` 4-Voter `3-of-4` Epoch | — | `63.80 ms` | — | `[EXECUTED]` `10^6` & `-1 mod t` forgery killed |

## 4. Remaining `[OPEN]` Boundaries

- `[OPEN]` Recursive/aggregated batch folding across `M >> 100` concurrent `DBWHIR61` bidder proofs (currently verified linearly at `12.28 ms` per bidder, `~81` bidders/s single-node) can fold `M` `WhirPcs61` openings via a shared `mc` cascade.
- `[OPEN]` Cross-chain atomic settlement execution of `DBNET001` net legs against `obend-lightclients` proven foreign holdings (`VerifiedEthHeader` / `VerifiedCometHeader` ICS-23 envelopes) awaits Phase-3 Starbridge escrow wiring.
