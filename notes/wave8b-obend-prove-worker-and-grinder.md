# Wave-8B Quarry: `obend-prove-worker` — Off-Lock Bounded `ProveService<I, O>` & Deterministic `c = 1/4` `windowed_find_map_first` Grinder

**Date:** 2026-11-21 · **Lane:** `w8b-obend-prove-worker` (`Phase 1` `crates/obend-prove-worker`) · **Metered search ledger:** `Scry: 0, Kagi: 0, eprint.iacr.org: 0` `[EXECUTED]`

## 1. Scope & Donor Provenance

- `[SOURCE]` **Worker-pool donors:** [prove_pool.rs](file:///Users/ember/dev/breadstuffs/node/src/prove_pool.rs#L6-L52) (off-lock bounded MPSC closing the `F-DOS-1` 5-minute inline `state.write()` wedge) and [dreggnet-prove-service/src/lib.rs](file:///Users/ember/dev/breadstuffs/dreggnet-prove-service/src/lib.rs#L94-L407) (`ProveService<I, O>`, whose `HashMap` status table retained terminal jobs forever — only removing on enqueue failure at lines 269/277 — and whose `MatchProveService` wrapped `prove_tug_match` / `win_leaf` `20-15-5=0` mannequin `B2`). See [MASTER_REVIVAL_ALIGNMENT.md](file:///Users/ember/dev/zkml-research/research/breadstuffs_revival_2026_11_21/MASTER_REVIVAL_ALIGNMENT.md#L371) & [§4.2 Phase 1](file:///Users/ember/dev/zkml-research/research/breadstuffs_revival_2026_11_21/MASTER_REVIVAL_ALIGNMENT.md#L468).
- `[SOURCE]` **Grinder donor:** [grinding_challenger.rs](file:///Users/ember/dev/breadstuffs/vendor/plonky3-challenger-82cfad73/src/grinding_challenger.rs#L114-L200) (`GRIND_WINDOW_C_NUM/DEN = 1/4`, `GRIND_WINDOW_MIN_UNITS = 64`, `GRIND_TASKS_PER_WORKER = 8`, `default_grind_window`, `windowed_find_map_first`). See [MASTER_REVIVAL_ALIGNMENT.md](file:///Users/ember/dev/zkml-research/research/breadstuffs_revival_2026_11_21/MASTER_REVIVAL_ALIGNMENT.md#L423).
- `[DERIVED]` Zero external dependencies, pure `std` Rust (`#![forbid(unsafe_code)]`), zero `dreggnet-game-board` / `prove_tug_match` (`B2` burned), zero `rayon` / `plonky3` fork dependency.

## 2. Landed `obend` Phase-1 Crate (`crates/obend-prove-worker`)

`[EXECUTED]` Committed on `revival-obend-prove-worker` at **`e762fc917c06851b2e8ed3dfa2dd8fa0b6298a80`** (`6` files, `+2,535` lines; wired into workspace `Cargo.toml`):

| File | LOC | Delivered Capability & Hardening Invariants |
|---|---:|---|
| `Cargo.toml` / `src/lib.rs` | `9` / `42` | Pure-`std`, `#![forbid(unsafe_code)]` Phase-1 workspace crate re-exporting `service` and `grinder`. |
| `src/service.rs` | `1,267` | Generic off-lock `ProveService<I, O>`: (1) bounded `queue_depth` failing fast with `EnqueueError::QueueFull` without blocking callers; (2) bounded `Done`/`Failed`/`Cancelled` tombstones (`max_retained_settled`) evicted via deterministic monotonic-tick LRU (`BTreeMap<u64, JobId>`) + optional wall-clock TTL (`BTreeMap<(Instant, u64), JobId>`) with synchronized `dedup_index` cleanup so every map stays `O(queue_depth + workers + max_retained_settled)`; (3) direct per-waiter `WaiterSlot` rendezvous so blocked `wait(id)` calls never lose results even at `max_retained_settled == 0`; (4) monotonic `cancel_stale_epoch` immediately evicting stale queued jobs (freeing queue slots), flipping cooperative `CancelToken`s on stale in-flight jobs, discarding stale completions as `JobStatus::Cancelled`, and rejecting future stale admissions with `EnqueueError::StaleEpoch`; (5) idempotent `enqueue_with_id` (`JobId`) and `enqueue_dedup` (`[u8; 32]`) returning existing `Queued`/`Proving`/`Done` handles without consuming queue capacity or re-running the backend; (6) panic-isolated workers (`catch_unwind`). |
| `src/grinder.rs` | `440` | Pure `std::thread::scope` `c = 1/4` `windowed_find_map_first` (`default_grind_window`, `windowed_find_map_first_with_threads`, `windowed_find_map_first_indexed`, `windowed_find_map_first_cancellable`): contiguous ascending windows eagerly split into `workers * 8` atomic chunks with `best_unit: AtomicU64` upper-bound pruning strictly above discovered hits while exhaustively scanning every unit `< best_unit`, guaranteeing bit-exact `1T == NT` lowest-unit determinism across `1..=32` threads and any window `>= 1`. Includes pure-Rust FIPS 180-4 SHA-256 (`obend-pow-grind-v1`) `grind_pow` / `grind_pow_cancellable` / `verify_pow`. |
| `tests/prove_worker.rs` | `776` | `17` integration/adversarial tests covering off-lock concurrency, `QueueFull` backpressure, `10,000`-job bounded eviction (`<= 64` retained across `jobs`, `lru_order`, `ttl_order`, `dedup_index`), deterministic LRU recency touch, TTL pruning, `max_retained == 0` waiter safety, `JobId` + `[u8; 32]` deduplication, `cancel_stale_epoch` (cancellable & plain backends), `cancel_job`, panic isolation, NIST SHA-256 KAT, `1T == 2T == 4T == 8T == 16T == 32T` PoW parity (including deployed `16`-bit `window = 16_384`), adversarial slow-low-thread / fast-high-thread tooth, and end-to-end cancellable PoW proving. |

## 3. Verification Gates (`[EXECUTED]`)

- **Remote `hbox` release build & test (zero macOS builds):**
  `SWARM_MEM_MAX=12G timeout --kill-after=10s 600s env RUSTFLAGS="-D warnings" cargo test --release -p obend-prove-worker`
  → `exit 0`, `0` warnings, compiled in `1.27s`, **`17/17` tests passed in `2.26s`** (`0` ignored, `0` failed). Remote scratch `~/.cache/obb-worktrees/w8b-prover` removed and verified absent.
- **Local `obb lint`:**
  `/Users/ember/dev/obebuilder/target/release/obb lint --repo "$WT" --json`
  → `exit 0`, **`0` findings** on `crates/obend-prove-worker` (`total_findings=510`, unchanged from base `17f4be53`).
- `[OPEN]` Wiring `obend-prove-worker`'s `ProveService` and `windowed_find_map_first` into `WhirExt4` / `WhirPcs61` epoch batch proving and `minidregg` challengers belongs to Phase 3 proof-spine integration.
