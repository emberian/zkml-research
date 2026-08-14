# Per-phase profile of a real IR-v2 proof — measured 2026-08-13

**One line:** the deployed IR-v2 prover is **hash-bound at every feasible blowup**. `hash/arith`
is `1.01` at `b=3` and rises to `1.86` at `b=8`; **there is no crossover inside the feasible set**,
because `b=2` does not exist for this circuit. And ~25% of a *deployed* prove is a phase nobody had
named — the PoW grind — whose random draw is what produced the "measured optimum at lb=4".

Harness: `breadstuffs/circuit/tests/ir2_phase_profile.rs` (§A–§F below are its test names),
landed as breadstuffs `7aa61862f`. No deployed constant, config or type moves.
Raw logs: `scratchpad/emb-{A,B,D}-final.log`, `emb-phaseC2.log`, `emb-phaseF.log`.

⚠ Shared-tree note: the one-line `tracing-subscriber` dev-dep this harness needs was swept into a
concurrent lane's commit `5a1b7e358` by `git commit --only`'s path granularity (it guards other
*files*, not other *hunks* of a hot shared file). It is in HEAD and correct; only the attribution
is wrong, and history is not being rewritten to fix that.

---

## 0. Method, and what it cannot see

**Instrument: plonky3's own `tracing` spans.** Every phase is already `#[instrument]`ed upstream
(rev `82cfad73`; `p3-fri`/`p3-challenger` are the vendored copies). The harness installs a
`tracing_subscriber::Layer` that accumulates **self time keyed by the full span path**
(`prove_batch>FRI prover>commit phase>build merkle tree`), then classifies paths into phases.
Keying by path, not by name, is load-bearing: `build merkle tree` occurs both under the main
commits and under the FRI commit phase.

Nothing upstream was patched and no timer was added to a hot loop.

**Second instrument, independent of the first: an exact Poseidon2 permutation counter.**
`descriptor_ir2::prove_vm_descriptor2_for_config` is generic over `SC`, so the same real proof runs
under a config whose only difference is a counting permutation. Counts are exact and
hardware-free. (Its *timings* are meaningless — a global `fetch_add` per permutation — and are not
reported.)

**Third: a Poseidon2 rate micro-benchmark**, to convert counts into ms and check the classifier
from outside. It closes to within 10% (§5).

### Blind spots — stated, not hedged

1. **Un-instrumented code is invisible as a phase.** `Pcs::commit` carries no span, so the
   bit-reversal and `to_row_major_matrix` copies between the LDE and the Merkle build land in
   `prove_batch`'s own self time. That is the `prove residual` row: 0.4–0.6 ms, ~0.5%. Small here,
   but it is real work, not error.
2. **Span busy time is wall clock on the entering thread.** With rayon *inside* an instrumented
   function, the span measures elapsed time for the parallel section, not CPU-seconds. **Every
   number below is `RAYON_NUM_THREADS=1`** — it measures *work*, which is also the right unit for a
   silicon argument. The multithreaded run on this box was unusable: it measured `lb=7` as *faster*
   than `lb=6`.
3. **No field-multiplication counts.** A BabyBear multiply is inlined with no hook. The arithmetic
   side is measured in time only; only the hashing side has an exact op count.
4. **The estimator is a per-phase minimum over reps, and does not sum to any observed prove time.**
   Under preemption each phase is inflated independently, so the fastest *whole* run is not the run
   in which any given phase was cleanest.
5. **The box is heavily shared.** Apple M2 Max, 12 cores, 96 GB, 36 login sessions, **load average
   16–95 throughout** (other agents' cargo/rustc/python). Absolute ms run ~1.5–2× a quiet machine.
   **The ratios are the deliverable; the absolute ms are not.** N = 21 for §A/§B, 9 for §F.
6. **One workload family.** The deployed IR-v2 descriptor batch. §6 adds the trace-height axis on a
   second real descriptor, but the recursion/leaf-wrap tower (h = 2^20) is not measured here.

---

## 1. ⚑ `b = 2` is not in the feasible set

The deployed IR-v2 batch carries an inline degree-7 Poseidon2 S-box, so
`log_blowup ≥ ⌈log₂(7−1)⌉ = 3`. At `lb=2` the config builder does **not** refuse; it returns a
config that produces a proof failing its own self-verify:

```
lb=2 q=19: IR v2 batch self-verify failed: OodEvaluationMismatch { index: Some(1) }
```

(index 1 = the poseidon2-chip table.) So the requested `b ∈ {2,4,6}` sweep starts at 3, and the
measured range below is `b = 3..8`. `create_config_with_fri` accepting an unprovable blowup and
failing 60 ms later at OOD is a footgun worth a refusal.

---

## 2. The per-phase table — fixed `q = 19`, `pow = 0`, single-threaded, per-phase min of 21

`q` and `pow` are held fixed so the *only* moving knob is `b`. (At the deployed `pow=16` the grind
is a random draw of 0.04–41 ms — larger than the entire Merkle term — see §4.)

| phase (ms) | b=3 | b=4 | b=5 | b=6 | b=7 | b=8 | ratio/rung |
|---|---:|---:|---:|---:|---:|---:|---|
| LDE commit *(arith)* | 0.750 | 1.604 | 4.392 | 7.710 | 16.647 | 27.277 | ≈2× |
| LDE quotient-eval *(arith)* | 1.445 | 3.357 | 6.109 | 12.925 | 26.416 | 44.331 | ≈2× |
| **Merkle-commit *(hash)*** | **4.696** | **9.579** | **21.479** | **42.509** | **81.578** | **148.305** | **≈2×** |
| quotient eval *(arith)* | 1.135 | 1.161 | 1.360 | 1.283 | 1.305 | 1.168 | **1.0×** |
| lookup perm *(arith)* | 0.211 | 0.207 | 0.237 | 0.246 | 0.239 | 0.234 | **1.0×** |
| FRI fold *(arith)* | 0.032 | 0.041 | 0.054 | 0.072 | 0.123 | 0.181 | ≈1.4× |
| FRI fold Merkle *(hash)* | 0.166 | 0.296 | 0.621 | 1.198 | 2.225 | 3.909 | ≈1.9× |
| query/open phase | 0.049 | 0.056 | 0.064 | 0.068 | 0.073 | 0.071 | **1.0×** |
| open arith (quotient reduce) | 1.229 | 1.472 | 2.320 | 3.545 | 5.463 | 8.714 | ≈1.5× |
| prove residual (unspanned) | 0.405 | 0.409 | 0.485 | 0.485 | 0.522 | 0.493 | 1.0× |
| **prove total** | **10.33** | **19.77** | **37.29** | **72.09** | **135.05** | **236.87** | |
| verifier (standalone) | 4.221 | 4.446 | 5.176 | 5.167 | 5.189 | 4.700 | **1.0×** |

Three phases are `Θ(2^b)` (both LDEs, both Merkles). Four are flat in `b` (quotient evaluation,
lookup permutation, the query phase, the residual). **The query/opening phase is 0.05–0.07 ms —
essentially free on the prover side**, because `MerkleTreeMmcs::open_batch` copies stored sibling
digests and does no hashing; the query-phase hashing is the *verifier's*.

Note also that **`LDE quotient-eval` is consistently ~1.7× `LDE commit`**. That is
`get_evaluations_on_domain` taking its slow path (iDFT the committed LDE back to coefficients, then
coset-DFT onto the quotient domain) rather than truncating. It is the largest single arithmetic
term at every blowup and looks like a live optimisation target.

---

## 3. ⚑ The crossover: there isn't one in range — it sits at `b ≈ 2.9`, just under the floor

hash = Merkle-commit + FRI-fold Merkle. arith = both LDEs + quotient + lookup + fold + open-arith.

| b | blowup | hash ms | arith ms | **hash/arith** | hash % of prove |
|---:|---:|---:|---:|---:|---:|
| 3 | 8 | 4.863 | 4.801 | **1.013** | 47% |
| 4 | 16 | 9.875 | 7.842 | **1.259** | 50% |
| 5 | 32 | 22.100 | 14.472 | **1.527** | 59% |
| 6 | 64 | 43.707 | 25.781 | **1.695** | 61% |
| 7 | 128 | 83.803 | 50.194 | **1.670** | 62% |
| 8 | 256 | 152.214 | 81.904 | **1.858** | 64% |

**Hashing and arithmetic are already at parity at the lowest feasible blowup, and hashing wins
everywhere above it.** The crossover `hash = arith` extrapolates to `b ≈ 2.9` — below the
degree-7 feasibility floor of 3. There is no operating point of this circuit that is
arithmetic-bound.

*Why the ratio rises at all when both terms are `Θ(2^b)`:* the LDE amortises **one** iDFT of the
base trace across all `2^b` coset DFTs, so it carries a blowup-independent component; the Merkle
build carries none. The two `Θ(2^b)` terms therefore diverge slowly rather than staying parallel.

### This dissolves the 94%-vs-19–40% disagreement, but not the way the model predicted

`PHASES-AND-TENSOR.md` §1 expected the two lanes to be reading opposite ends of a *crossover*: LDE
dominant at low blowup, hashing dominant at high. **Measured, hashing is dominant at both ends**
(47% of prove at `b=3`, 64% at `b=8`) — the swing across the whole feasible blowup range is 1.01 →
1.86, a factor of 1.8, not a sign change. Whatever produced "19–40% hash at ρ=1/2" was measuring a
different object (a different circuit shape, or a multithreaded wall clock, or an aggregate that
included the grind and the self-verify). The blowup knob **moves the mixture, but it never flips
it.**

---

## 4. ⚑ The phase nobody named: the PoW grind is ~25% of a deployed prove, and it is a random draw

`query_proof_of_work_bits = 16` (deployed). `GrindingChallenger::grind` searches for a witness whose
absorbed transcript samples 16 zero bits. Exactly measured at the deployed point: **47,917
scalar-equivalent Poseidon2 permutations = 11,979 SIMD calls** (it is *packed*: 4 candidate
witnesses per permutation). That is **8.2 ms of a 69.0 ms prove**, and it depends on **neither the
blowup nor the trace** — only on which witness index the Fiat–Shamir transcript happens to land on.

Its draw across the parity ladder, one run:

| (lb, q) | (3,38) | (4,29) | (5,23) | (6,19) | (7,17) | (8,15) |
|---|---:|---:|---:|---:|---:|---:|
| grind ms | **40.8** | 10.1 | **0.04** | 8.2 | 31.9 | 40.0 |

Expected value ≈ `2^16 / 4 lanes × 758 ns ≈ 12 ms`, exponentially distributed with a heavy tail —
so a ~1000× spread across points is ordinary, not anomalous. **Any single-number prove time at
`pow=16` contains this draw.**

---

## 5. ⚑ The "measured optimum blowup at lb=4" is REFUTED — it is a grind draw

`docs/reference/FRI-PARAM-FRONTIER.md` §1b reports the security-parity ladder as
`29 / 20 / 32 / 58 / 101 / 183 ms` for `lb = 3..8`, with a **minimum at lb=4** and lb=3
anomalously above it. Reproduced here at `pow=16` (single-threaded, contended box, min of 21):

| (lb,q) | prove ms | self-verify ms | **published-equivalent** | published |
|---|---:|---:|---:|---:|
| (3,38) | 51.0 | 7.2 | 58.2 | 29 |
| (4,29) | 29.6 | 6.7 | **36.2** | **20** |
| (5,23) | 35.4 | 5.2 | 40.6 | 32 |
| (6,19) | 69.0 | 4.5 | 73.5 | 58 |
| (7,17) | 149.4 | 4.1 | 153.6 | 101 |
| (8,15) | 334.9 | 4.2 | 339.1 | 183 |

**Same shape reproduced** (lb=4 minimum, lb=3 high, then monotone up); absolute scale ~1.6–1.9×
because this run is single-threaded on a load-40 box.

Now the same ladder with **the grind removed and nothing else changed** (`pow=0`):

| (lb,q) | (3,38) | (4,29) | (5,23) | (6,19) | (7,17) | (8,15) |
|---|---:|---:|---:|---:|---:|---:|
| prove ms | **14.9** | 20.3 | 34.9 | 67.9 | 120.6 | 243.3 |

**Strictly monotone increasing. The lb=4 minimum vanishes and lb=3 becomes the fastest by 1.4×.**
The published lb=3 point paid a 40.8 ms grind draw against lb=4's 10.1 ms; that difference — 30 ms
of coin flip — is the whole of the reported optimum. **The measured optimum is the lowest feasible
blowup, `lb=3`**, and prove time is monotone in `b` thereafter.

Two further corrections to how that grid should be read:

* **The published `prove` column includes a full `verify_batch` self-verify.**
  `descriptor_ir2.rs` runs one unconditionally (`check`), 4.1–8.6 ms. Prove-only and
  published-equivalent are both given above.
* **Proof bytes were re-measured and agree with the published trend**: 220,874 → 122,298 B across
  lb=3..8 (`rmp-serde`; the published table is postcard, hence the offset).

---

## 6. The second axis, and it is not the one the model expected: trace height

The deployed transfer descriptor's committed matrices are **width 2–386, height 8–64** (read off
the `dims` fields the DFT spans already carry; §C). `log₂ h` multiplies the LDE term and not the
Merkle term, so the *a priori* expectation is that a taller trace shifts the mixture toward
arithmetic. **It does not.**

`pasta-fpmul-sound` (190 declared → 694 committed columns, row-local AIR so an honest block cycles
to any height), fixed `q=19`, `pow=0`, heights `2^6 … 2^12`:

| log₂ h | 6 | 8 | 10 | 12 |
|---|---:|---:|---:|---:|
| hash/arith at **lb=3** | 1.51 | 2.53 | 2.74 | **2.81** |
| hash/arith at **lb=6** | 6.23 | 7.54 | 7.07 | **6.85** |

⚠ This sweep ran at load average 85–95; treat the magnitudes as soft. The **direction** is not soft:
hashing's share is flat-to-rising in trace height, never falling.

The mechanism: the Merkle **leaf** hash is a `PaddingFreeSponge` over the whole committed row, so it
costs `⌈w/8⌉` permutations per row and scales as `w·h·2^b` — the *same* shape as the LDE. The
`log h` factor that should favour arithmetic is swamped by the per-permutation cost. A wide table
makes this *worse*, not better: at 694 columns the ratio is 2.8–6.9, against 1.0–1.7 for the
386-column transfer batch.

**So "wider/taller traces will make it arithmetic-bound" is false for this implementation.**

---

## 7. Op counts, and an independent check on the whole table

Exact scalar-equivalent Poseidon2 permutations (counting config, `q=19`):

| phase | b=3 | b=4 | b=5 | b=6 | b=7 | b=6, pow=16 |
|---|---:|---:|---:|---:|---:|---:|
| Merkle-commit | 26,493 | 52,989 | 105,981 | 211,965 | 423,933 | 211,965 |
| FRI fold Merkle | 549 | 1,101 | 2,205 | 4,413 | 8,829 | 4,413 |
| open arith (challenger sampling) | 736 | 736 | 736 | 736 | 736 | 736 |
| **PoW grind** | 0 | 0 | 0 | 0 | 0 | **47,917** |
| verifier (self-verify) | 3,698 | 3,812 | 3,926 | 4,040 | 4,154 | 4,040 |
| **total** | **31,512** | **58,674** | **112,884** | **221,190** | **437,688** | **269,106** |
| of which SIMD calls | 6,756 | 13,518 | 27,042 | 54,090 | 108,186 | 66,069 |

Merkle permutations double *exactly* per blowup rung (`2n − 3`), which is the cleanest confirmation
in the whole run that the classifier is attributing correctly.

**Cross-check from outside the span table.** Poseidon2 rate on this box (min of 4,000 windows ×
512 permutations, throughput-bound over independent states): scalar **938 ns/perm**, packed×4
**758 ns/call = 189 ns/lane**, SIMD factor **4.95×**.

| predicted from counts × rate | measured by spans |
|---|---|
| Merkle at b=6: 216,378 scalar-equiv ÷ 4 × 758 ns = **41.0 ms** | **37–43 ms** |
| grind at pow=16: 11,979 packed calls × 758 ns = **9.1 ms** | **8.2 ms** |

Both close within 10%. Two independent instruments agreeing is the reason to believe the phase
split rather than the classifier's plausibility.

⚑ Recording one trap: **the grind is SIMD-packed**, 4 candidate witnesses per permutation. Assuming
it is scalar makes this cross-check appear to fail by 6× and would have been read as a broken
classifier.

---

## 8. The verifier — hash-dominated, and leaving a 5× on the floor

Standalone verify, single-threaded, min of 21:

| | b=3 | b=4 | b=5 | b=6 | b=7 | b=8 |
|---|---:|---:|---:|---:|---:|---:|
| verify ms (fixed q=19) | 4.22 | 4.45 | 5.18 | 5.17 | 5.19 | 4.70 |
| **% of prove+verify** | **29.0%** | 18.4% | 12.2% | 6.7% | 3.7% | 1.9% |
| verify ms (parity ladder, q falls) | 7.40 | 6.36 | 5.45 | 4.50 | 4.25 | 4.26 |
| % of prove+verify (parity) | 12.7% | 17.7% | 13.3% | 6.1% | 2.8% | 1.3% |
| permutations | 3,698 | 3,812 | 3,926 | 4,040 | 4,154 | — |

**Verify time is flat in blowup at fixed `q`** — it is a function of query count and Merkle path
length, not of the prover's LDE work. Its variation on the parity ladder tracks `q` (38→15)
exactly as `FRI-PARAM-FRONTIER` reports.

**⚑ The verifier's permutations are 100% SCALAR, and the prover's are 100% packed.** Measured, not
inferred — §D reports the scalar/packed split per phase:

| at b=6 | scalar-equivalent perms | of which SCALAR |
|---|---:|---:|
| prover Merkle-commit | 211,965 | **9** |
| prover FRI-fold Merkle | 4,413 | **9** |
| PoW grind | 47,917 | **1** |
| **verifier** | **4,040** | **4,040** |

So the verifier's 4,040 permutations run at the scalar rate (938 ns) rather than the packed lane
rate (189 ns): **≈3.8 ms of a 5.17 ms verify, or ~73%.** The "verification is hashing" reading is
confirmed — hash-dominated, though not ~100%; the remaining ~1.4 ms is path walking, extension-field
arithmetic and constraint evaluation at the OOD point.

**And that is a concrete, unclaimed 5×.** The verifier checks 19 independent query paths one node
at a time while the exact same `Poseidon2BabyBear<16>` on the same box does 4 lanes per call for the
prover. Batching the query paths across SIMD lanes would take verify hashing from ~3.8 ms toward
~0.8 ms — **verify from 5.2 ms to ~2.2 ms**, at every grid point, with no soundness or wire change.
(Whether p3's `MerkleTreeMmcs::verify_batch` can be lane-batched without a fork is not established
here; the headroom is.)

⚠ The 73% is *derived* (measured count × measured rate), not read off a span: the verifier's
internals carry no sub-spans at this rev. The count and the rate are each measured; the product is
the inference. It is the one figure here I would want a second instrument on.

## 9. What this decides

* **Silicon target, and the Amdahl ceiling is now a number.** The dominant engine is **Poseidon2,
  at every feasible blowup**, by 1.0–1.9× over *all* field arithmetic combined — and at the deployed
  knobs a further ~25% of the prove is a PoW grind that is also Poseidon2. The **NTT/GEMM-shaped**
  phase is only the two LDE rows:

  | | b=3 | b=4 | b=5 | b=6 | b=7 | b=8 | **deployed (6,19,pow16)** |
  |---|---:|---:|---:|---:|---:|---:|---:|
  | LDE share of prove | 21.2% | 25.1% | 28.2% | 28.6% | 31.9% | 30.2% | **20.8%** |
  | Amdahl ceiling if NTT were free | 1.27× | 1.33× | 1.39× | 1.40× | 1.47× | 1.43× | **1.26×** |

  So a *perfect* NTT accelerator — infinite speedup, zero transfer cost — buys **1.26× at the
  deployed point** and never more than 1.47× anywhere in the feasible range. The MLE-fold engine is
  smaller still (`FRI fold` is 0.03–0.18 ms, under 0.1% of prove). **The tensor-core thesis is
  aimed at a fifth of this workload.** That is a real reason to prefer a Poseidon2 engine, or to
  run this measurement on the recursion/leaf-wrap tower (h = 2^20, where `log h` is 3× larger)
  before choosing silicon — but it is not an argument that GEMM work is worthless, only that on
  *this* circuit it is capped at 1.26×.
* **The blowup knob.** Prove time is monotone increasing in `b` once the grind is removed. Nothing
  in the *time* column argues for `lb=6`; the argument for it is proof bytes (122–221 KiB across the
  ladder) and the soundness ledger. **`lb=3` is 4.6× faster to prove than the deployed `lb=6`** at
  parity, and 1.8× larger on the wire.
* **The verifier leaves a 5x on the floor.** Its permutations are 100% scalar where the prover's
  are 100% packed (measured, §8). Lane-batching the 19 query paths takes verify from ~5.2 ms toward
  ~2.2 ms with no soundness or wire change.
* **The grind is the cheapest win on the table.** 8–41 ms per proof, ~25% of a deployed prove, for
  16 bits that the Lean ledger prices as one additive term. Whether those 16 bits are worth a
  quarter of the prover is a soundness-budget question, not a performance one — but until now the
  cost was not in any grid.
* **Do not read a prove-time optimum off a `pow>0` grid.** Every such column contains an
  exponentially-distributed draw with mean ~12 ms and a tail past 40 ms.

## 10. Reproduce

```bash
cd ~/dev/breadstuffs
cargo test -p dregg-circuit --release --test ir2_phase_profile --no-run
B=./target/release/deps/ir2_phase_profile-*
RAYON_NUM_THREADS=1 DREGG_PROFILE_REPS=21 $B phase_profile_blowup_sweep      --nocapture --test-threads=1  # §A
RAYON_NUM_THREADS=1 DREGG_PROFILE_REPS=21 $B phase_profile_parity_ladder     --nocapture --test-threads=1  # §B
RAYON_NUM_THREADS=1                       $B phase_profile_raw_spans         --nocapture --test-threads=1  # §C geometry
RAYON_NUM_THREADS=1                       $B poseidon2_permutation_counts    --nocapture --test-threads=1  # §D
RAYON_NUM_THREADS=1                       $B poseidon2_rate                  --nocapture --test-threads=1  # §E
RAYON_NUM_THREADS=1 DREGG_PROFILE_REPS=9  $B phase_profile_trace_height      --nocapture --test-threads=1  # §F
```
Release only. Report the load average with any number taken from it.
