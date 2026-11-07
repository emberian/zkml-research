# Kaggle run ledger (account emberian64), accelerator readiness (initiative 17) and shared users

Rules: /Users/ember/swarm/kaggle.md. Every push goes through `harness/kaggle_job.py` (`stage`, `submit`,
`harvest`), which appends a row here: one row at submit and one at harvest. One id per experiment; an id
is reused only after its harvest row exists. **TPU is serialized**: `submit` takes `TPU-LOCK` (this
directory) with O_EXCL and `harvest` of a terminal job releases it. Any other lane using the TPU on this
account (initiative 8's MXFP4 recompute) takes the same lock: use the harness, or create `TPU-LOCK` with
O_EXCL yourself and remove it when your TPU job is terminal. Check `kaggle kernels list --mine` before a TPU push.

Columns: UTC time, kernel id, version (or `harvest`), accelerator, source sha256 (first 16 hex of the
bundled files), entry, command, holder, status, elapsed/rc/hardware check, harvested files.

Quota (UI is the authority; not read by this lane): historical 30 GPU h/week, 20 TPU h/week, 9 h per TPU
session, one TPU session per account.

| utc | id | ver | acc | src sha | entry | command | holder | status | elapsed / rc | files |
|---|---|---|---|---|---|---|---|---|---|---|
| 2026-11-06 20:56Z | `accel-env-probe-t4-01` | 1 | t4 | 846d5fe80c924702 | `env_probe_gpu.py ` | `kaggle kernels push -p STAGE/accel-env-probe-t4-01 --accelerator NvidiaTeslaT4 --timeout 900` | accel-ready | submitted |  |  |
| 2026-11-06 20:56Z | `accel-env-probe-tpu-01` | 1 | tpu | a59af7fbb44fcc15 | `env_probe_tpu.py ` | `kaggle kernels push -p STAGE/accel-env-probe-tpu-01 --accelerator TpuV5E8 --timeout 900` | accel-ready | submitted |  |  |
| 2026-11-06 20:58Z | `accel-env-probe-t4-01` | harvest | t4 | 846d5fe80c924702 |  |  | accel-ready |  "KernelWorkerStatus.COMPLETE" | elapsed 10.1 s, rc 0, hw_ok True | accel-env-probe-t4-01.log 3491, log.txt 1964, manifest.json 640, results.json 1963 |
| 2026-11-06 21:11Z | `accel-bfv-ntt-t4-01` | 1 | t4 | 7f98f27135fb6593 | `accel_bench_cuda.py --N 8192 --L 3 --rows 384 --quick` | `kaggle kernels push -p STAGE/accel-bfv-ntt-t4-01 --accelerator NvidiaTeslaT4 --timeout 1200` | w1-bfv | submitted |  |  |
| 2026-11-06 21:13Z | `accel-bfv-ntt-t4-01` | harvest | t4 | 7f98f27135fb6593 |  |  | w1-bfv |  "KernelWorkerStatus.ERROR" | elapsed 8.1 s, rc 1, hw_ok True | accel-bfv-ntt-t4-01.log 5083, log.txt 2573, manifest.json 680 |
| 2026-11-06 21:14Z | `accel-bfv-dry-t4-02` | 1 | t4 | 3390720b8cee4a90 | `accel_bfv_run.py --shrink ` | `kaggle kernels push -p STAGE/accel-bfv-dry-t4-02 --accelerator NvidiaTeslaT4 --timeout 1500` | w1-bfv | submitted |  |  |
| 2026-11-06 21:19Z | `accel-bfv-dry-t4-02` | harvest | t4 | 3390720b8cee4a90 |  |  | w1-bfv |  "KernelWorkerStatus.ERROR" | elapsed 126.1 s, rc 1, hw_ok True | accel-bfv-dry-t4-02.log 33059, log.txt 24719, manifest.json 656, results.json 32227 |
| 2026-11-06 21:22Z | `accel-mma-t4-dry-01` | 1 | t4 | 6bfce9e793c8858d | `t4_entry.py ` | `kaggle kernels push -p STAGE/accel-mma-t4-dry-01 --accelerator NvidiaTeslaT4 --timeout 1500` | w3-mma | submitted |  |  |
| 2026-11-06 21:22Z | `accel-bfv-dry-t4-03` | 1 | t4 | 4c0cd0897111b818 | `accel_bfv_run.py --shrink ` | `kaggle kernels push -p STAGE/accel-bfv-dry-t4-03 --accelerator NvidiaTeslaT4 --timeout 1500` | w1-bfv | submitted |  |  |
| 2026-11-06 21:24Z | `accel-mma-t4-dry-01` | harvest | t4 | 6bfce9e793c8858d |  |  | w3-mma |  "KernelWorkerStatus.COMPLETE" | elapsed 76.2 s, rc 0, hw_ok True | accel-mma-t4-dry-01.log 16818, log.txt 10037, manifest.json 634, results.json 42644 |
| 2026-11-06 21:26Z | `accel-mma-t4-dry-02` | 1 | t4 | dfefb277b0c9f933 | `t4_entry.py ` | `kaggle kernels push -p STAGE/accel-mma-t4-dry-02 --accelerator NvidiaTeslaT4 --timeout 1500` | w3-mma | submitted |  |  |
| 2026-11-06 21:26Z | `accel-bfv-dry-t4-03` | harvest | t4 | 4c0cd0897111b818 |  |  | w1-bfv |  "KernelWorkerStatus.COMPLETE" | elapsed 140.2 s, rc 0, hw_ok True | accel-bfv-dry-t4-03.log 39550, log.txt 29722, manifest.json 656, results.json 39103 |
| 2026-11-06 21:29Z | `accel-mma-t4-dry-02` | harvest | t4 | dfefb277b0c9f933 |  |  | w3-mma |  "KernelWorkerStatus.COMPLETE" | elapsed 72.1 s, rc 0, hw_ok True | accel-mma-t4-dry-02.log 17157, log.txt 10199, manifest.json 634, results.json 56407 |
| 2026-11-06 21:29Z | `accel-bfv-dry-t4-04` | 1 | t4 | 26ef12a3642e0030 | `notes/accelerator-readiness/runbook/bfv_kaggle_entry.py ` | `kaggle kernels push -p STAGE/accel-bfv-dry-t4-04 --accelerator NvidiaTeslaT4 --timeout 1500` | w1-bfv | submitted |  |  |
| 2026-11-06 21:33Z | `accel-tower-dryrun-01` | 1 | t4 | b250c3468386a1d0 | `kaggle_entry.py ` | `kaggle kernels push -p STAGE/accel-tower-dryrun-01 --accelerator NvidiaTeslaT4 --timeout 1500` | w2-tower | submitted |  |  |
| 2026-11-06 21:34Z | `accel-bfv-dry-t4-04` | harvest | t4 | 26ef12a3642e0030 |  |  | w1-bfv |  "KernelWorkerStatus.COMPLETE" | elapsed 198.1 s, rc 0, hw_ok True | accel-bfv-dry-t4-04.log 42059, log.txt 31054, manifest.json 679, results.json 39069 |
| 2026-11-06 21:35Z | `accel-tower-dryrun-01` | harvest | t4 | b250c3468386a1d0 |  |  | w2-tower |  "KernelWorkerStatus.COMPLETE" | elapsed 98.1 s, rc 0, hw_ok True | accel-tower-dryrun-01.log 19448, log.txt 12246, manifest.json 640, results.json 14287 |
| 2026-11-06 21:37Z | `accel-mma-t4-runbook-01` | 1 | t4 | b419d66ade47e134 | `mma_kaggle_entry.py ` | `kaggle kernels push -p STAGE/accel-mma-t4-runbook-01 --accelerator NvidiaTeslaT4 --timeout 3600` | w3-mma | submitted |  |  |
| 2026-11-06 21:39Z | `accel-tower-tune-02` | 1 | t4 | 1499560b8ebb2eb8 | `kaggle_entry.py ` | `kaggle kernels push -p STAGE/accel-tower-tune-02 --accelerator NvidiaTeslaT4 --timeout 1500` | w2-tower | submitted |  |  |
| 2026-11-06 21:41Z | `accel-mma-t4-runbook-01` | harvest | t4 | b419d66ade47e134 |  |  | w3-mma |  "KernelWorkerStatus.COMPLETE" | elapsed 162.2 s, rc 0, hw_ok True | accel-mma-t4-runbook-01.log 40005, log.txt 23557, manifest.json 647, results.json 60355 |
| 2026-11-06 21:41Z | `accel-tower-tune-02` | harvest | t4 | 1499560b8ebb2eb8 |  |  | w2-tower |  "KernelWorkerStatus.ERROR" | elapsed 104.1 s, rc 1, hw_ok True | accel-tower-tune-02.log 18504, log.txt 10682, manifest.json 639, results.json 860 |
| 2026-11-06 21:42Z | `accel-tower-tune-03` | 1 | t4 | 5df91ededeade00c | `kaggle_entry.py ` | `kaggle kernels push -p STAGE/accel-tower-tune-03 --accelerator NvidiaTeslaT4 --timeout 1500` | w2-tower | submitted |  |  |
| 2026-11-06 21:45Z | `accel-tower-tune-03` | harvest | t4 | 5df91ededeade00c |  |  | w2-tower |  "KernelWorkerStatus.COMPLETE" | elapsed 108.1 s, rc 0, hw_ok True | accel-tower-tune-03.log 19953, log.txt 12444, manifest.json 639, results.json 16403 |
| 2026-11-06 21:46Z | `accel-tower-dryrun-04` | 1 | t4 | 6bf686755dfbd5bc | `kaggle_entry.py ` | `kaggle kernels push -p STAGE/accel-tower-dryrun-04 --accelerator NvidiaTeslaT4 --timeout 1500` | w2-tower | submitted |  |  |
| 2026-11-06 21:48Z | `accel-tower-dryrun-04` | harvest | t4 | 6bf686755dfbd5bc |  |  | w2-tower |  "KernelWorkerStatus.COMPLETE" | elapsed 118.2 s, rc 0, hw_ok True | accel-tower-dryrun-04.log 19865, log.txt 12361, manifest.json 641, results.json 16234 |
| 2026-11-06 21:51Z | `accel-env-probe-tpu-01` | delete | tpu | a59af7fbb44fcc15 |  |  | accel-ready | deleted while QUEUED (never ran, ~2.6 h in queue); TPU-LOCK released for the waiting TPU lane | 0 TPU time |  |
| 2026-11-06 22:00Z | `tpuperf-calib-01` | 1 | tpu | 1f495434b7ac49a1 | `run_profile.py ` | `kaggle kernels push -p STAGE/tpuperf-calib-01 --accelerator TpuV5E8 --timeout 3000` | tpu-perf | submitted |  |  |
| 2026-11-06 22:01Z | `accel-mma-t4-runbook-02` | 1 | t4 | e313f7e52173ef77 | `mma_kaggle_entry.py ` | `kaggle kernels push -p STAGE/accel-mma-t4-runbook-02 --accelerator NvidiaTeslaT4 --timeout 3600` | w3-mma | submitted |  |  |
| 2026-11-06 22:29Z | `accel-mma-t4-runbook-02` | harvest | t4 | e313f7e52173ef77 |  |  | w3-mma |  "KernelWorkerStatus.COMPLETE" | elapsed 1648.3 s, rc 0, hw_ok True | accel-mma-t4-runbook-02.log 42135, log.txt 24197, manifest.json 648, results.json 63972 |
| 2026-11-06 22:32Z | `er-g2-layer0-t4-01` | 1 | t4 | 2738dee4c7e7fd8b | `g2_entry.py ` | `kaggle kernels push -p STAGE/er-g2-layer0-t4-01 --accelerator NvidiaTeslaT4 --timeout 1800` | init8-exact | submitted |  |  |
| 2026-11-06 22:38Z | `er-g2-layer0-t4-01` | harvest | t4 | 2738dee4c7e7fd8b |  |  | init8-exact |  "KernelWorkerStatus.COMPLETE" | elapsed 284.1 s, rc 0, hw_ok True | er-g2-layer0-t4-01.log 13190, log.txt 3950, manifest.json 634, results.json 2439 |
| 2026-11-06 22:46Z | `tpuperf-calib-01` | delete | tpu | 1f495434b7ac49a1 |  |  | tpu-perf | deleted while QUEUED (never ran, 45 min in queue from 22:00:46Z); TPU-LOCK released | 0 TPU time |  |
| 2026-11-06 22:47Z | `er-g2-layer0-tpu-01` | 1 | tpu | 07c111edfaba231a | `g2_entry.py tpu` | `kaggle kernels push -p STAGE/er-g2-layer0-tpu-01 --accelerator TpuV5E8 --timeout 2400` | init8-exact | submitted |  |  |
| 2026-11-06 22:59Z | `accel-tower-bitslice-01` | 1 | t4 | a0c332853a9e8ca3 | `bitslice_entry.py ` | `kaggle kernels push -p STAGE/accel-tower-bitslice-01 --accelerator NvidiaTeslaT4 --timeout 1500` | w2-tower | submitted |  |  |
| 2026-11-06 23:01Z | `accel-mma-fp16parity-01` | 1 | t4 | bc1b603c0ad67969 | `t4_entry.py rotation` | `kaggle kernels push -p STAGE/accel-mma-fp16parity-01 --accelerator NvidiaTeslaT4 --timeout 1500` | w3-mma | submitted |  |  |
| 2026-11-06 23:02Z | `accel-tower-bitslice-01` | harvest | t4 | a0c332853a9e8ca3 |  |  | w2-tower |  "KernelWorkerStatus.COMPLETE" | elapsed 132.1 s, rc 0, hw_ok True | accel-tower-bitslice-01.log 20465, log.txt 12908, manifest.json 645, results.json 14996 |
| 2026-11-06 23:03Z | `accel-mma-fp16parity-01` | harvest | t4 | bc1b603c0ad67969 |  |  | w3-mma |  "KernelWorkerStatus.COMPLETE" | elapsed 32.2 s, rc 0, hw_ok True | accel-mma-fp16parity-01.log 11253, log.txt 6670, manifest.json 653, results.json 22439 |
| 2026-11-06 23:03Z | `accel-tower-bitslice-01` | 2 | t4 | 5160cf30b8780970 | `bitslice_entry.py ` | `kaggle kernels push -p STAGE/accel-tower-bitslice-01 --accelerator NvidiaTeslaT4 --timeout 1500` | w2-tower | submitted |  |  |
| 2026-11-06 23:04Z | `accel-mma-t4-runbook-03` | 1 | t4 | b1bdb9ce2b064e92 | `mma_kaggle_entry.py nocutlass` | `kaggle kernels push -p STAGE/accel-mma-t4-runbook-03 --accelerator NvidiaTeslaT4 --timeout 1800` | w3-mma | submitted |  |  |
| 2026-11-06 23:06Z | `accel-tower-bitslice-01` | harvest | t4 | 5160cf30b8780970 |  |  | w2-tower |  "KernelWorkerStatus.COMPLETE" | elapsed 120.1 s, rc 0, hw_ok True | accel-tower-bitslice-01.log 20463, log.txt 12911, manifest.json 645, results.json 14980 |
| 2026-11-06 23:07Z | `accel-mma-t4-runbook-03` | harvest | t4 | b1bdb9ce2b064e92 |  |  | w3-mma |  "KernelWorkerStatus.COMPLETE" | elapsed 158.2 s, rc 0, hw_ok True | accel-mma-t4-runbook-03.log 31083, log.txt 18586, manifest.json 663, results.json 82360 |
| 2026-11-06 23:13Z | `er-g2-layer0-tpu-01` | delete | tpu | 07c111edfaba231a |  |  | init8-exact | deleted while QUEUED (~25 min in queue, never ran); TPU-LOCK released; layer-0 TPU run moves to the TPU-perf lane's GCP spot v5e | 0 TPU time |  |
| 2026-11-06 23:27Z | `redesign-encode-t4-01` | 1 | t4 | 894db6794a63ded7 | `kaggle_entry.py ` | `kaggle kernels push -p STAGE/redesign-encode-t4-01 --accelerator NvidiaTeslaT4 --timeout 1800` | redesign | submitted |  |  |
| 2026-11-06 23:30Z | `redesign-encode-t4-01` | harvest | t4 | 894db6794a63ded7 |  |  | accel-ready |  "KernelWorkerStatus.COMPLETE" | elapsed 144.1 s, rc 0, hw_ok True | log.txt 4570, manifest.json 641, redesign-encode-t4-01.log 9729, results.json 4467 |
| 2026-11-06 23:31Z | `redesign-encode-t4-02` | 1 | t4 | f23b154f778511ff | `kaggle_entry.py ` | `kaggle kernels push -p STAGE/redesign-encode-t4-02 --accelerator NvidiaTeslaT4 --timeout 1800` | redesign | submitted |  |  |
| 2026-11-06 23:35Z | `redesign-encode-t4-02` | harvest | t4 | f23b154f778511ff |  |  | accel-ready |  "KernelWorkerStatus.COMPLETE" | elapsed 148.1 s, rc 0, hw_ok True | log.txt 5911, manifest.json 641, redesign-encode-t4-02.log 12060, results.json 6009 |
| 2026-11-06 23:47Z | `redesign-piop-t4-03` | 1 | t4 | c73bad7d544da097 | `kaggle_entry.py ` | `kaggle kernels push -p STAGE/redesign-piop-t4-03 --accelerator NvidiaTeslaT4 --timeout 1800` | redesign | submitted |  |  |
| 2026-11-06 23:50Z | `redesign-openings-t4-01` | 1 | t4 | 306ef8c3362c6776 | `openings_entry.py ` | `kaggle kernels push -p STAGE/redesign-openings-t4-01 --accelerator NvidiaTeslaT4 --timeout 1800` | redesign | submitted |  |  |
| 2026-11-06 23:50Z | `redesign-piop-t4-03` | harvest | t4 | c73bad7d544da097 |  |  | accel-ready |  "KernelWorkerStatus.COMPLETE" | elapsed 150.2 s, rc 0, hw_ok True | log.txt 10387, manifest.json 639, redesign-piop-t4-03.log 20350, results.json 11077 |
| 2026-11-06 23:52Z | `redesign-openings-t4-01` | harvest | t4 | 306ef8c3362c6776 |  |  | accel-ready |  "KernelWorkerStatus.ERROR" | elapsed 10.1 s, rc 1, hw_ok True | log.txt 4724, manifest.json 644, redesign-openings-t4-01.log 10227, results.json 287 |
| 2026-11-06 23:52Z | `redesign-openings-t4-02` | 1 | t4 | 7bb050ca9ae17713 | `openings_entry.py ` | `kaggle kernels push -p STAGE/redesign-openings-t4-02 --accelerator NvidiaTeslaT4 --timeout 1800` | redesign | submitted |  |  |
| 2026-11-06 23:54Z | `redesign-openings-t4-02` | harvest | t4 | 7bb050ca9ae17713 |  |  | accel-ready |  "KernelWorkerStatus.COMPLETE" | elapsed 80.1 s, rc 0, hw_ok True | log.txt 6530, manifest.json 644, redesign-openings-t4-02.log 10283, results.json 11208 |
| 2026-11-06 23:54Z | `redesign-openings-t4-03` | 1 | t4 | d314bca0b077aad9 | `openings_entry.py ` | `kaggle kernels push -p STAGE/redesign-openings-t4-03 --accelerator NvidiaTeslaT4 --timeout 1800` | redesign | submitted |  |  |
| 2026-11-06 23:56Z | `redesign-openings-t4-03` | harvest | t4 | d314bca0b077aad9 |  |  | accel-ready |  "KernelWorkerStatus.COMPLETE" | elapsed 76.1 s, rc 0, hw_ok True | log.txt 4439, manifest.json 644, redesign-openings-t4-03.log 7390, results.json 7490 |
| 2026-11-06 23:59Z | `accel-failclosed-t4-01` | 1 | t4 | 079189ffd2888ed0 | `failclosed_entry.py ` | `kaggle kernels push -p STAGE/accel-failclosed-t4-01 --accelerator NvidiaTeslaT4 --timeout 2700` | accel-ready | submitted |  |  |
| 2026-11-07 00:02Z | `accel-failclosed-t4-01` | harvest | t4 | 079189ffd2888ed0 |  |  | accel-ready |  "KernelWorkerStatus.ERROR" | elapsed 106.1 s, rc 1, hw_ok True | accel-failclosed-t4-01.log 1464, log.txt 202, manifest.json 646, results.json 4677 |
