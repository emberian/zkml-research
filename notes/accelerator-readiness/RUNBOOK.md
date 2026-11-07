# Paid-box runbook (initiative 17): what to rent, in what order, and what each result decides

2026-11-06. Budget: **$30 of vast.ai credit** (ember). Nothing here is rented by a lane; ember hands over a box.
Every script below passed its shrunk dry run on a Kaggle T4 first (KAGGLE-LEDGER.md). Prices are vast.ai
on-demand offers read from the public offers API at 2026-11-06 22:25 UTC, single GPU, so they move.

**STATUS: final (2026-11-06 23:10 UTC).** Initiative 14's revised probe list (`notes/tensor-core-holography/
ROTATION.md` §5, dev a82e4738) is folded into `runbook/mma.sh` (T4 dry run `accel-mma-t4-runbook-03`, 81/81).
Its free T4 items ran first: the bit-sliced Tower256 multiply (`accel-tower-bitslice-01`: ~52,700 int32-op
equivalents, the tables ~12,000-17,400; F3's 718 is below the ideal ~860 LOP3 count) and the FP16 0/1 parity
bias read (`accel-mma-fp16parity-01`, 37/37: exact below 2^(m-1), coin-flip past it, as predicted).
Rentals go through `harness/vast_box.py` (smoke-tested end to end, VAST-LEDGER.md).

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

## 3. Order and cost (final)

No B300 is listed on vast.ai (checked 23:05 UTC); the B200 runs the B300 items. Re-read at 23:05: B200 $7.50/h
(Oregon, reliability 0.99, two offers), H100 SXM $2.335/h (Japan, 0.99).

| # | box (vast.ai, 1 GPU, image nvidia/cuda:12.9.1-devel-ubuntu24.04) | runs | expected wall incl. boot | expected cost | cap / watchdog |
|---|---|---|---|---|---|
| 1 | B200 ($7.50/h) | `mma.sh --sku B200`: mxf4 and FP8 0/1 count/parity sweeps K = 2^10..2^20 (fast accum on/off), bias read, FP16 byte-limb BabyBear^8 IP, peak INT8/FP8/FP4/FP16 rates and copy, Tower256 fixed-r 0/1 GEMM, CUTLASS tcgen05 examples | 20-25 min (14-18 run + boot) | **~$3** | $6.50 / 50 min |
| 2 | H100 SXM ($2.34/h) | `mma.sh --sku H100 --no-cutlass` (wgmma IGMMA/QGMMA/HGMMA/BGMMA and.popc rates; QGMMA m, expected 12; bias read in-accumulator; FP8 0/1 parity; TensorZKP-shape INT8 IP vs copy), then `bfv.sh --sku H100`, then `tower256.sh --sku H100` | 50-65 min | **~$2.5** | $4.00 / 95 min |
| | | total | | **~$5.5**, caps sum $10.50 (< the $25 stop) | |

B300 items that do not transfer to the B200 (w3, MMA.md §9): the INT8 rate and hence which prime-field path
wins (INT8 on B200, FP16 bytes on B300), the FP4 and peak rates, and (probably) the tcgen05 accumulator width,
which is evidence for B300 rather than a measurement of it. On Blackwell the bias read is checked at the cuBLAS
level only (C enters in the fp32 epilogue); an in-accumulator read needs a CUTLASS-72a-derived kernel (not written).
mxf4 through cuBLASLt (VEC32_UE8M0) has not run anywhere before the box; nvfp4 runs beside it.
The tower256.sh used on the box gained argument pass-through after its dry run 04 (w2's bit-slice jobs ran it).

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

## 5. What actually ran (2026-11-06/07, VAST-LEDGER.md)

| rental | box | outcome | cost |
|---|---|---|---|
| accel-smoke-01/02 | RTX 3060 Ti / 3060 | 01: host could not pull the image; 02: full path ok | $0.00 |
| accel-b200-mma-01/02 | B200, offer 50255943 (blacklisted) | key refused on proxy and direct port | $2.70 |
| accel-h100-all-01 | H100 SXM | launcher bug (backgrounded untar held ssh open); destroyed | $0.34 |
| accel-h100-all-02 | H100 SXM | **bfv measured, bit-exact** (0.23-0.34 s per step); mma: no ensurepip; tower256: lock refused | $0.75 |
| accel-h100-mma-03 | H100 SXM | **mma measured** (QGMMA m = 14, BGMMA 8.0x IGMMA, FP8 fast-accum inexact from K = 65,536) | $0.38 |
| accel-b200-mma-03 | B200, offer 59157383 | key refused again; Blackwell stopped | $1.25 |
| | | **total** | **$5.72** |

Every instance destroyed and verified absent. Not measured: Blackwell (all items), tower256 on a paid box
(not needed). Script fixes after the H100 run are proven by `accel-failclosed-t4-02` (7/7).
