# GCP Cloud TPU ledger (initiative 18, tpu-perf lane)

Project `gen-lang-client-0657209111`, account ember@lunar.town. Ember's rules (2026-11-06): hard cap **$20**
for the whole campaign, stop and report at **$17**; one TPU VM at a time; every VM is created by
`gcp_run.py`. That script sets a wall-clock watchdog plus a detached reaper, deletes the VM in a finally
block, and confirms with `gcloud compute tpus tpu-vm list` that it is gone. No IAM, billing or quota
changes. Stop and report after two spot preemptions in a row.

Pricing, read 2026-11-06 (cloud.google.com/tpu/pricing, cloud.google.com/spot-vms/pricing):
TPU v5e on demand $1.20 per chip-hour (us-central1, us-east5, us-west1, us-west4); **spot $0.359329 per
chip-hour** (headline spot table; regional spot rates vary, e.g. asia-south1 $0.11232). v6e (Trillium)
spot $0.671112. Cost estimate per VM = chips x hours (create to confirmed delete) x rate; spot prices are
dynamic, so the estimate uses the rate above.

Network: the project had no VPC, so the first create failed. I created the minimum the TPU VM needs for ssh:
network `tpuperf-net` (custom mode), subnet `tpuperf-usw4` (us-west4, 10.90.0.0/24), and firewall
`tpuperf-ssh` (ingress tcp:22 only, source = this Mac's public IP at the time, 73.66.3.250/32). All three are
deleted at the end of the campaign. Nothing else is opened.

| name | zone | type | spot | start (UTC) | end (UTC) | hours | est. $ | outcome | cumulative $ |
|---|---|---|---|---|---|---|---|---|---|
| tpuperf-calib-02 | us-west4-a | v5litepod-1 | spot | 23:09:15 | 23:09:29 | 0.004 | 0.000 | create failed: ERROR: (gcloud.compute.tpus.tpu-vm.create) INVALID_ARGUMENT: Cloud TPU received a bad request. The value "default" provi | 0.000 |
