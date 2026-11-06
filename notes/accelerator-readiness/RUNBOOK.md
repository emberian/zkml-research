# Paid-box runbook (initiative 17): what to rent, in what order, and what each result decides

2026-11-06. Budget: **$30 of vast.ai credit** (ember). Nothing here is rented by a lane; ember hands over a box.
Every script below passed its shrunk dry run on a Kaggle T4 first (KAGGLE-LEDGER.md). Prices are vast.ai
on-demand offers read from the public offers API at 2026-11-06 22:25 UTC, single GPU, so they move.

**STATUS: box order provisional.** The hardware lane (initiative 14) is remapping the workloads onto each
chip's fastest exact datapath (including GF(2) as the parity of exact FP8 0/1 sums on B300) and will hand
over a revised probe list. §3 is rewritten when it arrives; §1, §2 and §4 stand.

## 1. vast.ai prices read (on-demand, 1 GPU, $/h)

| GPU | offers | min | median | notes |
|---|---:|---:|---:|---|
| H100 SXM | 8 | 2.33 | 2.83 | 28 vCPU typical; CUDA driver up to 13.4 |
| H100 PCIe | 3 | 2.67 | 3.57 | |
| H200 | 7 | 2.99 | 4.34 | |
| B200 | 1 | 12.51 | 12.51 | US, reliability 0.996, 24 vCPU |
| GB200 | 1 | 8.14 | 8.14 | Indonesia; **Grace aarch64 host**: scripts were dry-run on x86 only |
| B300 | 0 | | | none listed |

## 2. The three scripts

| workload | script (on the box) | bundle (made on the Mac from committed content) | T4 dry run | full-run wall | box |
|---|---|---|---|---|---|
| 1 BFV RNS NTT + HE returns | `bash bfv/notes/accelerator-readiness/runbook/bfv.sh --sku H100` | `runbook/bfv-bundle.sh ~/dev/zkml-research` | `accel-bfv-dry-t4-04` pass, 198 s | 20-35 min (watchdog 3000 s) | H100 SXM, no toolkit needed (cupy ctk wheels) |
| 2 Tower256 FRI prover | `bash tower256/tower256.sh --sku H100` | `runbook/tower256-bundle.sh <minidregg lane/accel-tower256-gpu checkout>` | `accel-tower-dryrun-04` pass, 118 s | ~10 min | any box with >= 16 host cores |
| 3 tensor-core probe | `bash mma/mma.sh --sku B300` (or B200, H100) | `runbook/mma-bundle.sh ~/dev/degg-research` | `accel-mma-t4-runbook-01` pass, 44/44 | <= 60 min incl. CUTLASS build bounded at 25 min | B300/B200 hour + optional H100 SXM hour |

Each script: pinned venv/toolchain, `nvidia-smi` SKU gate (`--any-gpu` overrides), wall + no-output
watchdog with a PID file (`runbook/common.sh`), results in `~/accel-results/<workload>-<utc>/`
(`results.json`, `log.txt`, `box.json`). Copy that directory back to
`notes/accelerator-readiness/runs/paid-<sku>-<workload>/` and commit it.

## 3. Order and cost (PROVISIONAL, pending initiative 14's revised probe list)

| # | box | runs | wall | cost |
|---|---|---|---|---|
| 1 | one H100 SXM (~$2.33-2.83/h) | mma.sh `--sku H100` (BGMMA vs IGMMA b1 rate, QGMMA FP8 width), bfv.sh, tower256.sh | ~1.75 h | **~$4-5** |
| 2 | one B200 ($12.51/h; B300 if one appears) | mma.sh `--sku B200` (tcgen05 e4m3/e2m1 accumulator widths, FP4 promotion interval) | 1 h | **~$12.5** |
| | | total | | **~$17-18**, leaving ~$12 for a rerun or the remapped probes |

Why this order: box 1 is cheap and settles two workloads plus the Hopper half of the probe in one rental;
box 2 is the expensive single question (the unpublished Blackwell accumulator widths). If the credit must
shrink, drop tower256 first (it does not need paid hardware, §4), then BFV's H100 run (the T4 numbers
already answer the fork verdict).

## 4. What each result decides

- **BFV (workload 1).** T4 measured, every check exact: NTT N = 8192 in 1.8-2.2 us; one d = 4096 training
  step's HE work 2.8-4.0 s on one T4. The H100 run turns the model's 0.25-0.4 s per step into a
  measurement. It decides nothing the T4 has not already decided qualitatively (the HE outer product is not
  a training bottleneck); it fixes the number the fork verdict quotes. B200 is not worth it (integer-multiply
  bound, model 1.1-1.3x an H100). TPU: MXU int8 four-step path exact on CPU, not yet run on v5e (queue).
- **Tower256 (workload 2).** Fixed CPU prover: 55 ms per proof at ell 14 on one core (the existing kernel
  is ~2000x slower at ell 10), so **no GPU per proof**. A GPU pays only for batches; the H100 run decides
  whether it beats the same box's CPU cores by >= 3x (prediction: not until a bit-sliced Tower256 multiply
  exists). Optional, < $1 riding on box 1.
- **Tensor-core probe (workload 3).** H100: the `wgmma .b1` rate against INT8 (decides Tower256 on Hopper:
  HBM-bound vs unpack-bound) and the native FP8 accumulator width m (the `HoldsBelow m` premise; m < 12
  refutes PTX's wording). B200/B300: the tcgen05 f8f6f4 accumulator width and FP4 promotion interval
  (F3's B300 column), INT8 vs FP8 rate. Blackwell has no hardware 1-bit MMA (measured by emulation cost).

Per-workload detail: BFV.md, TOWER256.md, MMA.md.
