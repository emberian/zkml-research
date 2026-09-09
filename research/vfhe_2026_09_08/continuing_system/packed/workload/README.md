# Whole packed-class lifecycle

[EXECUTED: preparation] `corpus.json` was frozen before the local E5 helper encoded all 27 public texts once (two forward batches, no cached texts or clipped coordinates). `prepared/` retains the vectors, exact reference, encoder statistics and actual command logs. The preparation command was:

```sh
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -u -B research/vfhe_2026_09_08/continuing_system/packed/workload/workload.py --prepare
```

Root launches a fresh complete instance from repository root:

```sh
python3 -u -B research/vfhe_2026_09_08/continuing_system/packed/workload/workload.py --run research/vfhe_2026_09_08/continuing_system/runtime/packed-lifecycle/resident
```

Use the same command with `--resume` instead of `--run` after an interruption. `--resume` may also adopt an externally initialized revision-zero packed instance with the exact ordered classes in `corpus.json`; adoption opens the instance without key generation. The frozen preparation is the default; `--prepared DIR` selects a byte-identical copy. The workload invokes `packed/core.py` directly in a new OS process for each operation.

[DERIVED] The fixed flow commits 18 teachings: one example for each of the first eight classes, then one network-transport example and nine further proof-integrity examples. The first query at revision 8 has one active bank. The later query at revision 18 has two active banks and proof-integrity retains precisely `pi03` through `pi10`; `pi01` and `pi02` have expired. The explicit restart reopens the same durable head, and a fresh query with its own request ID must recover identical class sums and ranking from identical vector bytes in a distinct process. These are 22 operations including three queries and the restart.

[DERIVED] Each query compares every signed class-sum lane of every occupied bank, including empty padding lanes, to sums of exact integer feature dots. It also compares class counts, count-dependent signed bounds, exact rational means and ranking, and checks the reader's repeat8/zero-empty assertions. The controller requires complete all-bank public acceptance and one private read per occupied bank. It delegates encryption, proofs and acceptance ordering to the packed application; it never invokes the reader directly.

[DERIVED] `ROOT.workload/RESULT.json` reports the actual native proof counts, bytes, phase times, bank reads, and completed query comparisons. Stable requests are counted once across resumes. Per-attempt logs and process IDs remain under `ROOT.workload/steps/`; completed operations are reused, failed phases retain their IDs, and a still-running worker prevents a competing resume. `evaluation.md` updates from those results. The frozen `prepared/reference.json` also records the nine held-out predictions at the one-bank, before-expiry, after-expiry and restart checkpoints.

[OPEN at preparation] Root owns all cryptographic launch. The observed plaintext result is 8/9 with eight taught classes, then 9/9 after the ninth class is introduced, including after FIFO expiry. This small authored set is a utility observation with changing class membership; it is not a general accuracy-gain claim. The full BFV reader remains present.
