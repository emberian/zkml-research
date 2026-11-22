# Wearable SHE Organ #3: Belief Circles, Picosecond ToF Co-Presence & `IConfluent` AR Overlay Merge

**Status:** `[VERIFIED]` Lean `v4.35.0` kernel proofs + `[EXECUTED]` byte-exact Rust `--release` conformance, adversarial regressions & microbenchmarks (`2026-11-21`).
**Owned Artifacts:**
- Lean `v4.35.0`: `/Users/ember/dev/minidregg/Assurance/WearableBeliefCircle.lean` (`943` lines, `0 sorry`, `0` custom `axiom`, `0 native_decide`, `16` `#guard_msgs`-pinned `#print axioms`, `0` warnings).
- Rust engine & tests: `/Users/ember/dev/minidregg/prover/src/belief_circle.rs` (`#![deny(warnings)]`), `/Users/ember/dev/minidregg/prover/tests/wearable_belief_circle.rs`, `/Users/ember/dev/minidregg/prover/testdata/belief_circle_conformance.json` (`9,305 B`, Lean-authored).
- Verifier harness: `research/wave9_wearable_she_2026_11_21/formal_belief_circle/build_and_verify.sh`.

---

## 1. Physical Co-Presence: `Hancke–Kuhn` / `dregg_distance_tdc` Picosecond ToF Gate

- `[SOURCE]` Silicon timing anchor from `/Users/ember/dev/qsag/hardware/gf180mcu/rtl/dregg_distance_tdc.sv` & `README.md`: 64-round rapid-bit responder (`u_lock` single-shot challenge lock preventing dual read of `r0[i]`/`r1[i]`), 32-tap Vernier TDC (`450 ps` slow tap − `220 ps` fast tap = `230 ps/tap`), post-SPEF rapid-bit pad-to-pad turnaround floor `t_proc_min = 3,990 ps`.
- `[VERIFIED]` Exact SI speed-of-light arithmetic (`c = 299,792,458 pm/ps`, `1 mm = 10^9 pm`, zero floating point): for `d_max = 3,000 mm` (`3.0 m` room radius), `dreggBeliefTofParams_deadline` proves `maxRoundTimePs = 24,003 ps`.
- `[VERIFIED]` **`tof_accepts_implies_within_radius`** & **`wormhole_relay_deterministically_rejected`**: if `verifyTofSession` accepts and any round satisfies `CausallyConstrained t_proc_min dActualMm Δt` (`Δt ≥ t_proc_min + 2·d/c`), then `dActualMm ≤ d_max`; any honest/wormhole relay with `dActualMm > d_max` is deterministically rejected (`.err (.tofTimeout _)`).
- `[VERIFIED]` **Exact Combinatorial Mafia-Fraud Bounds:**
  - **`hancke_kuhn_mafia_fraud_exact_count`** & **`hancke_kuhn_mafia_fraud_reject_count`**: against single-shot-lock hardware, every `k`-round pre-ask strategy wins on exact `3^k` of `4^k` `(challenge, hiddenBit)` pairs (rejected with probability `1 - (3/4)^k`).
  - **`hancke_kuhn_security_margins`**: `k = 64` (1 `dregg_distance_tdc` run) gives `3^64 · 9.9×10^7 < 4^64`; `k = 128` (2 chained runs, default belief-circle gate) gives `(3/4)^128 < 2^-53 < 10^-15`.
  - **`blind_precommit_exact_count`**: fixed `k`-bit pre-committed guess matches `1` of `2^k` targets (`1 - (1/2)^k`).
- `[VERIFIED]` **`#tooth` Falsifiers:** `tooth_wormhole_relay_5m_rejected` (`5,000 mm`, `37,347 ps` → `.tofTimeout 0`), `tooth_below_turnaround_floor_rejected` (`3,989 ps` → `.belowTurnaroundFloor 0`), and `tooth_precommit_early_bit_caught_and_lock_load_bearing` (proving `u_lock` omission collapses `(3/4)^2 = 9/16` to `16/16`).

---

## 2. Traffic-Analysis-Free Belief-Circle Transport (`Theory.Channel` Composition)

- `[VERIFIED]` **`circle_rf_trace_independent_of_activity`**: composes `Theory.Channel.Domain.observable_trace_depends_only_on_membership` and `cell_size_exact` over `WearableActivity` (`idle` / `jittQuery` / `arHazardReticle` / `overlayPatch`). Under `PayloadHidden` and constant emission (`designEmission`), passive room RF sniffers (`wireTick`), relays, operators, witnesses, and non-recipient members observe identical packet sizes (`256 B` at `P1`, `1,024 B` at `P2`) and identical traces regardless of wearer activity.
- `[VERIFIED]` **`circle_member_presence_hidden`**: composes `member_view_independent_of_presence` under `designPolicy` (`RelayFills` + `ConstantFanout` + `FillHidden`), hiding peer regular-tick silence from non-recipient circle members.
- `[VERIFIED]` **`#tooth` Falsifiers:** `tooth_event_driven_rf_leaks_hazard` and `tooth_unsealed_cell_leaks_hazard` demonstrate concrete wire-trace distinguishability when constant emission or sealing is dropped.
- `[EXECUTED]` Concrete `cSHAKE256` counter-mode stream + 16 B encrypt-then-MAC `P1`/`P2` regular and duty (`tick = 0`, 160 B public VRF/roots) cells match Lean byte-for-byte in `belief_circle_conformance.json`.

---

## 3. Scoped AR Overlay Merge (`PqSelectiveBiscuit` + ToF + `Theory.Confluence`)

- `[VERIFIED]` **`admitCircleUpdate_sound`**, **`overlay_drops_out_of_range_relay`**, **`overlay_drops_revoked_credential`**: every admitted `SpatialEntry` carries a verified `PqSelectiveBiscuit` token (`CAP-01/10/12`, `circleWriteRight = 0x01`, ancestor-cone revocation checked via `revoke_ancestor_kills_cone`) AND an accepted ToF co-presence transcript (`≤ d_max`).
- `[VERIFIED]` **`overlay_allAdmitted_iconfluent`** & **`overlay_zero_round_convergence`**: `AllAdmitted` over `OverlayState := Finset SpatialEntry` (`⊔ = ∪`) is `Theory.Confluence.IConfluent`, giving `0`-round BFT convergence across arbitrary delivery permutations, duplicates, and partition heals; `converged_overlay_renders_identical_viewNode` links merged states to `LightClientAndViewLens.ViewNode` AR reticles (`diff = .keep`).
- `[VERIFIED]` **`tooth_maxOneReticle_not_iconfluent`** vs **`witness_reticle_floor_coordination_free`**: cardinality ceilings (`card ≤ 1`) break `IConfluent` (`bounded_breaks`), while grow-only floors (`monotone_free`) stay coordination-free.

---

## 4. `[EXECUTED]` Conformance, Adversarial Regressions & `--release` Benchmarks

Command: `research/wave9_wearable_she_2026_11_21/formal_belief_circle/build_and_verify.sh` (`exit 0`, `0` warnings).

| Verification Gate | Result | Measured Cost / Evidence |
|---|---|---|
| Lean `v4.35.0` kernel check + import boundary | **PASS (`0` warnings)** | `943` lines, `16` `#guard_msgs` axiom pins, `2.60 s` target verify |
| Byte-exact Lean → Rust conformance (`9,305 B` JSON) | **PASS (`100%` match)** | 128-rd ToF `r0`/`r1`/`chal`/`resp`, `P1`/`P2` regular+duty cells, 3-wearer CRDT root |
| Unit + 8 adversarial tests (`adv_01..adv_08`) | **12 / 12 PASS** | `0/256` pre-ask mafia fraud (`u_lock`), 5 m wormhole, `< 3,990 ps` floor, cell replay/bitflip, forged/revoked creds, partition heal |
| `128`-round ToF session verify (`--release`) | **PASS** | **`0.105 µs/op`** (`50,000` ops in `5.27 ms`) |
| `1,024 B` `P2` `cSHAKE256` seal + MAC + open | **PASS** | **`49.24 µs/op`** (`2,000` ops in `98.49 ms`, `> 4,000×` faster than `5 Hz` `P2`) |
| `64+64` `IConfluent` CRDT join + `state_root` | **PASS** | **`12.49 µs/op`** (`1,000` ops in `12.49 ms`, `0` BFT rounds) |

## 5. Honest Residual Scope (`[OPEN]`)
- Physical RF front-end multipath/clock-jitter calibration beyond the deterministic `dregg_distance_tdc` silicon floor (`3,990 ps`, `230 ps` Vernier step) and hardware-in-the-loop UWB/optical impulse transceiver integration remain outside this formal/software assurance slice.
- `Theory.Channel` sealing (`PayloadHidden`/`FillHidden`) is composed via its standard reduction boundary; `cSHAKE256` PRF/IND-CPA security is computational, not information-theoretic.
