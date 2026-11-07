# Dark learning gen 6: the train lane (dataset, plaintext training, the pinned d = 4096 program, release policy)

Lane: train (ad36593ec00657538). The code is in native/darktrain/ (the trainer) and native/darkstep/src/step.rs and tape.rs
(the program). Research references:
- research/dark_learning_2026_11_06/step_spec.py (Program, GEN6, Init)
- train_owner.py (the data owner)
- train_eval.py (the custodians' evaluation and release rule)
- train_check.py
- train_genesis_gen6.json (the genesis)
- train_results/ (every sweep, configs and curves)

## 1. Dataset and encoder

**MNIST**, the official IDX files [EXECUTED].
- Source: `curl https://ossci-datasets.s3.amazonaws.com/mnist/*.gz` (torchvision's mirror; yann.lecun.com returns 404).
- The gzip md5s equal torchvision's published ones (f68b3c2d…, d53e105e…, 9fb629c4…, ec29112d…).
- train-images also matches the Google cvdf mirror.
- The sha256 of the 4 decompressed files is pinned in `darktrain::data::MNIST` and `train_owner.MNIST`. Loading refuses any mismatch, and also checks the IDX magic, dimensions and label range.
- The files are in research/.../data/mnist/, which is gitignored. Parsing is our own; nothing from the download is executed.

**Encoder (the data owner, `train_owner.encode` = `darktrain::encode`)**, with d = 4096:
- **Input x.**
  - The 784 pixels sit at coordinates 0..783, mean-centred: x_k = clamp(round(7 (p_k - mu_k) / 255), -7, 7).
  - mu_k is the training split's integer pixel mean (round half up).
  - Coordinates 784..4095 are 0.
- **Target y.**
  - Rows 0..9: y_c = 128 if c is the label, else 0.
  - The owner then subtracts 2^(S2-1) = 64 from those rows. This makes e >> S2 round instead of floor, at no cost to the program.
  - All other rows are 0.
- **Prediction rule (custodians):** o = z2 >> S1 on rows 0..9. The prediction counts as correct iff o_label > o_k for every other class k, so ties are wrong.
- **Init (public, genesis):**
  - r = random.Random(1);
  - W1[j][k] = r.randint(-512, 512) for j < 4096, k < 784, row-major;
  - W2 = 0.
  - Zero W1 columns stay zero, because their x is 0.
  - Zero W2 rows with target 0 stay zero. A zero W1 row together with a zero W2 column is a dead unit forever. This was checked: d = 1024 and d = 4096 with hid = 1024 give identical curves.
- **Order:** step t trains on example order[t mod 60000], where order = random.Random(seed_order).shuffle(range(60000)).
  - seed_order is the owner's private seed. The study used 2..6.
- Rust and Python agree bit for bit [EXECUTED, `cargo test --release -p darktrain --test vs_python`]:
  - the init, three MNIST steps at d = 1024, and the custodians' evaluation, per example on 20 test examples;
  - Python's side is train_owner.py + step_spec.step.

## 2. Plaintext training of the same integer model

`darktrain` is the exact integer trainer.
- It is sparse in x, d2 and d1 (zero terms contribute exactly zero), with rows in parallel. It runs at 13 ms/step at d = 4096 on the Mac.
- Every step, and every test forward, it counts the MPC's preconditions: |z1|, |z2| < 2^K1, u1 in the table's domain, |e| < 2^K2, |b g1 + R3| < 2^K3. A run that breaks one is not executable by the custodians.
- Equality [EXECUTED, `cargo test --release -p darktrain --test vs_step`]:
  - the fast step equals the scalar step on random d = 16 and 64 cases (with and without rounding), and on MNIST at d = 1024;
  - the fast step equals darkstep's `Plain::step_prog(GEN6)` (step_spec under GEN6) on MNIST at d = 4096;
  - negative controls: a changed shift, and r3 = 0, both differ.

### Findings (sweeps g1-g5, ~330 runs; bb2, niced, memory-capped)

1. **The floor in d1 = (b g1) >> S3 must become a rounding (R3 = 2^(S3-1)).** A program change: one public cadd before the last truncation.
   - With floor, every unit with a small negative b gets W1 += x on every step.
   - At S3 >= 10 this collapses learning to chance: 11.7% against 75-78% with rounding (g1, hid 1024).
   - At S3 = 8 it learns, then drifts down: 83.8% at 2000 steps falls to 78.5% by 4000 (g5, `gen6_floor_d1`).
   - e's floor is fixed by the owner's target offset (above). The u1 and o floors are harmless bias shifts.
2. **§12's wide shifts do not train.** S1 = 11, S2 = 4, S3 = 14 with floor and no rounding (g5, `wide_sec12_shifts`):
   - the layer-2 gain ||h||^2 / 2^(S1+S2) is ~4 at hid = 4096, so it diverges;
   - accuracy is 10%, with 3x10^7 bound violations.
3. **The z2 bound decides the learning rate.** |z2| < 2^19 gives o 8 bits, and the layer-2 step per unit of d2 is ||h||^2 / 2^S1. At hid = 4096, S2 = 7 is what keeps that gain below 1.
   - S2 = 4..6 trains, but noisily.
   - S2 = 8 with ypos = 128 never updates, because the dead zone equals the target.
4. Mean-centred x beats pixels in [0, 7] by 2-3 points. W1 init 512 beats 256 and 1024. Other choices matter little within noise:
   - output replication (10 x 409 rows, ensemble readouts): no gain;
   - a constant bias input;
   - yneg = 0 or -32;
   - S3 = 8 or 9.
5. **Width:** hid = 4096 against hid = 1024 (same d), full test, orders 2 and 3:
   - 86.4 / 87.3% against 84.7 / 85.1% at 2000 steps;
   - 87.1 / 87.6% against 86.7 / 86.9% at 3000.
   - Width beyond the input helps a little and costs nothing in the program.
   - Sanity check, d = 1024 at the same program: 84.7 / 85.1% at 2000.

### The curve at d = 4096 under GEN6 (test accuracy on all 10,000 official test images, 5 data orders) [EXECUTED, sweep g5]

| steps | 25 | 50 | 100 | 200 | 300 | 400 | 500 | 750 | 1000 | 1500 | 2000 | 3000 | 4000 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| mean % | 38.5 | 49.1 | 60.9 | 68.2 | 71.7 | 76.8 | 79.2 | 81.9 | 83.6 | 84.9 | 86.6 | 86.7 | 87.3 |
| min-max | 36-41 | 47-52 | 59-63 | 66-73 | 70-74 | 75-80 | 77-81 | 80-83 | 82-84 | 84-86 | 85-87 | 86-88 | 86-88 |

- Zero precondition violations, training or eval, in all five runs.
- Maximum observed values over 4000 steps and every test forward, against the bounds:

  | value | max observed | bound | margin |
  |---|---:|---:|---:|
  | |z1| | 1.05x10^5 | 2^18 (table domain) | x2.5 |
  | |z2| | 3.22x10^5 | 2^19 | x1.6 |
  | |e| | 166 | 2^8 | x1.5 |
  | |b g1 + R3| | 395 | 2^19 | large |

  |W1| <= 633 and |W2| <= 196.
- Ties are 1.3% of test examples (they count as wrong).

**The float twin** (same architecture, init, order and squared-error targets in f64; continuous hard-tanh; rates = the integer program's matched rates x lrmul, swept 1/8..2, best 1). Full test, orders 2 and 3:
- 83.3 / 81.0% at 1000 steps, 83.9 / 83.9% at 2000, 84.3 / 84.4% at 3000.
- **The integer program is 2-3 points better than its float twin, not worse.** The owner's rounding offset gives d2 a dead zone of |e| < 64, which acts as a margin loss; the float twin's plain squared error has none.
- Softmax cross-entropy in the float twin was no better (hid 1024).
- For scale: a float softmax regression on raw pixels, single pass, gets 81% after 2000 samples (first 2000 test examples, Python).
- What the integer model gives up, against float nets of this shape, is nothing measurable at these step counts. The data seen (2000 examples) is the limit.

**Run length (ember's call):** 500 steps gives ~79%, 1000 ~84%, 2000 ~86.6%; past 2000 it is flat (+0.7 by 4000). 2000 steps is the knee.

## 3. The pinned program (genesis)

`step_spec.GEN6` = `darkstep::step::Program::GEN6`:

| | S | K | |
|---|---:|---:|---|
| z1, z2 | 11 | 19 | K1 = 19 is the 61-bit field's maximum at KAPPA = 40 |
| e | 7 | 8 | |
| b g1 + R3 | 8 | 19 | R3 = 2^7 |

- The table domain is [-128, 128).
- |x| <= 7, weights unbounded, and every truncation bound is asserted.

Plumbing:
- `step_spec.Program` and `step::Program` parameterize the step.
- The defaults are the old program, byte-identical [EXECUTED]:
  - `python3 -I train_check.py harness <old step_spec>`: 80/80 random cases identical, 41 of them raising its assertions, and the control differs;
  - `cargo test --release -p darkstep --test vs_reference`: 6/6 against the committed digests.
- darkstep:
  - `run_step_prog`;
  - `run_step_shares` (carried weights; the deploy lane's request);
  - `tape::deal_one_step` and `deal_steps_prog` (a K-step ideal dealer on one stream);
  - `inputs_for(d, program)`.
- MPC under GEN6 [EXECUTED, `cargo test --release -p darkstep --test program`]: three custodians at d = 64 ACCEPT and refine step_spec(GEN6); the floor variant gives different shares.
- Genesis: `train_genesis_gen6.json`. `train_check.py genesis` shows it is GEN6, and darktrain's test shows the same.
- Sent to the proof lane (a02632eb) and the deploy lane (ae142f25), and the truncation shapes to the prep lane (aa66b1f8).
- Note for the coordinator: mpc_fork.run_step and fhe_fork still hard-code 5/13, 4/8, 8/13. They need the program too before the Python harness can run GEN6 (not my files).

## 4. Release policy and evaluation (`train_eval.py`; sent to the proof lane)

- **What leaves custody:** one integer C, the number of the first M = 64 official test images (t10k indices 0..63, public, with their labels) that the custodied model classifies strictly correctly.
- Never released: the weights, the scores, or per-example predictions.
- The evaluation, per public example:
  - z1 = W1 x is local on shares, since x is public;
  - u1 = trunc(z1, 11, 19), h = SIG[u1];
  - z2_c = W2[c] . h for the 10 class rows (HE matvec);
  - o_c = trunc(z2_c, 11, 19);
  - q_k = trunc(o_l - o_k - 1, 10, 10) for k != l, which is -1 iff o_l <= o_k;
  - ok = prod (1 + q_k), 8 products.
- C = sum ok, then a single opening.
- The comparison is the existing truncation gate with s = K, so the proof needs no new gate type.
- The proof lane prices it at ~150 s of proof per example, so M = 64 is ~2.7 h per custodian, batched into one proof.
- **Check:** the run is bit-exact, so the released C must EQUAL the plaintext twin's.
  - `darktrain shadow '<genesis + seed_order>' STEPS 64` prints it, with the weight digest the revealed weights must match (tests only).
  - Order 2: C = 50 / 55 / 57 of 64 after 500 / 1000 / 2000 steps.
- **Input feed (deploy lane):** `darktrain feed '<genesis + seed_order>' START COUNT` prints one JSON line {t, k, x, y} per step.
  - The genesis weights go in once (darktrain::init).
  - Later steps input only x, y.

## 5. Open, for ember

- [OPEN] The run length: 2000 steps, the knee above, or fewer.
- [OPEN] Releasing per-example predictions on the 64 (b) instead of the count (c) would let a verifier recompute accuracy itself, at 64 x log2(10) bits of leakage against ~6.
- [OPEN] The bound margins (x1.5 on e, x1.6 on z2) are empirical for this data stream. A violation in deployment would silently break the truncation's correctness and masking. An in-MPC range check would make them enforced; it is not built.

## Review

Cross-model review (`codex exec -m gpt-6-astra --sandbox read-only`) covered commits f26c8289, 5d02dad3, 0b26d20c and 364a02d9.
- It found no correctness bugs in four areas:
  - HARNESS is byte-identical and Plain::step_prog equals step_spec(prog), with R3 before the last truncation;
  - the dealer order matches consumption, and carried steps deal 2d inputs;
  - the fast step, encoder, init and order equal Python;
  - the strict comparison under |v| < 2^10 is correct.
- It reran the trainer tests and the harness identity. The MPC tests could not run in its sandbox (sockets), so it reviewed them statically.

## 6. The harness runs GEN6; explicit truncation intervals (follow-on)

- `mpc_fork.run_step(..., prog)` and `tables(p, prog)` take the program, including R3 as a public cadd before the d1 truncation.
  - The default is unchanged [EXECUTED]: native_ref at d = 8 gives a transcript, shares, sigma and wire identical to the committed file.
- `native_ref.py --program GEN6` uses `inputs_for(d, prog)`, which mirrors darkstep.
  - [EXECUTED] At N = 4096, L = 3, F = 118, d = 64 the result is ACCEPT and refines step_spec(GEN6). It is committed as native_ref_results/native_ref_N4096_L3_F118_d64_GEN6.json.
  - [EXECUTED, `cargo test --release -p darkstep --test program`] darkstep under GEN6 equals that reference on the transcript, every party's shares and sigma, and the SPDZ wire counts. Control: the HARNESS reference differs.
- Truncation intervals are now explicit, as [a, a + 2^B) (`Program.intervals()` and `step::Program::intervals`, also listed in the genesis JSON):

  | value | GEN6 interval |
  |---|---|
  | z1 | [-2^18, 2^18) (B 19, the table domain) |
  | z2 | [-2^19, 2^19) (B 20) |
  | e | [-2^8, 2^8) (B 9) |
  | b g1 + R3 | [-2^19, 2^19) (B 20) |
  | release comparisons | [-2^10, 2^10) (B 11) |

  - The non-harness check changed from |v| < 2^K to -2^K <= v < 2^K, which is the MPC's exact precondition. The proof proves these intervals and the ledger refuses a step outside them.
