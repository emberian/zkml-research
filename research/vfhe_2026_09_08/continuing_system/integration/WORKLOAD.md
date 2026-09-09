# Engine-aware lifecycle workload continuation

[DERIVED] `WORKLOAD-APPLY-LATER.patch` changes only the active `workload.py`. The proposed file lives at `proposed/workload.py`; it is intended to run after application to the continuing-system directory. It uses the core engine integration documented in `README.md`. The baseline squared/compact defaults, frozen corpus and prepared files are preserved.

Apply from repository root:

```sh
git apply research/vfhe_2026_09_08/continuing_system/integration/WORKLOAD-APPLY-LATER.patch
```

Adopt the already HTTP-initialized linear/matched resident, without another key generation:

```sh
python3 -u -B research/vfhe_2026_09_08/continuing_system/workload.py --resume research/vfhe_2026_09_08/continuing_system/runtime/matched-lifecycle/resident --score linear --proof-backend matched
```

For a fresh instance use `--run ROOT` with the same engine flags. Resume any later failed phase with the original root and engine flags. Selecting linear/compact instead requires its own root and `--proof-backend compact`. Existing squared/compact command lines retain their previous behavior.

[DERIVED] The linear reference uses the already frozen E5 vectors and FIFO queues, computes all signed integer dot lanes directly, and ranks exact rational means. The prepared corpus is never re-encoded for an alternate engine. All 12 teachings, four queries, and the explicit restart remain in the fixed workload; the two FIFO-expired teaching examples remain the same. Every decrypted lane, signed sum, count, exact ranking and reader repeat8 assertion is compared against that reference. The restart requires the same revision, model root, class lanes and ranking from a distinct process.

[EXECUTED: reference preparation and patch construction] The proposal parses as Python; its default reference is the unchanged frozen object; the complete signed reference was derived from the frozen preparation; and `git apply --check` succeeded. Signed reference SHA256: `87dd7c6c5e60cdd04333b25626bc884395fb286f9fa11e52afd25ffa27a6350a`. No encoder, encryption or proof process ran during this preparation. The integrated core metadata and answer contract were read directly.

[DERIVED] `ROOT.workload/RESULT.json` names the requested engine and the full resident engine metadata. Proof counts and bytes are accumulated from actual unique-request metrics, including the native matched backend chunk counts, rather than substituted estimates. Completed requests reused during resume are identified separately from newly completed operations. The canonical signed reference is stored as `ROOT.workload/engine_reference.json`. Linear reports use `evaluation-linear-compact.md` or `evaluation-linear-matched.md`, leaving baseline `evaluation.md` to the baseline run.

[OPEN at preparation] Actual alternate-engine lifecycle execution is launched by the root agent. Source and patch hashes are in `WORKLOAD-MANIFEST.json`; baseline artifacts are not evidence of execution under a different engine.
