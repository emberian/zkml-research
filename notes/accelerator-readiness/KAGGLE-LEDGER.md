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
