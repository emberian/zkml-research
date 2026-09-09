# Commands and retained outputs

[EXECUTED] All commands use this repository root unless stated otherwise.

`cargo-check-01.log` (failed while the field module was still being authored):

```sh
CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 /Users/ember/.cargo/bin/cargo check \
  --offline --manifest-path research/vfhe_2026_09_08/matched_field/native/Cargo.toml
```

`cargo-test-lib-01.log` (11 passed, 0 failed, 1 intentionally ignored; working
directory `research/vfhe_2026_09_08/matched_field/native`):

```sh
CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 /Users/ember/.cargo/bin/cargo test \
  --lib --offline --locked -- --nocapture
```

`cargo-build-release-01.log`:

```sh
CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 /Users/ember/.cargo/bin/cargo build \
  --release --offline --locked --manifest-path \
  research/vfhe_2026_09_08/matched_field/native/Cargo.toml
```

[EXECUTED] The ignored standalone proof test was not run. First proof execution
was the parent's authorized full update plus full linear case below.

`caller-contract-check.log`:

```sh
python3 -B -O research/vfhe_2026_09_08/matched_field/experiments/caller-contract-check.py
```

`profile-pin.log`, `profile-check.json`, `native-profile.json`:

```sh
python3 research/vfhe_2026_09_08/matched_field/caller.py pin-config \
  research/vfhe_2026_09_08/full_bfv_infer_composition/artifacts/linear_plan.json \
  research/vfhe_2026_09_08/matched_field/native/target/release/vfhe-matched-field \
  research/vfhe_2026_09_08/matched_field/PIPELINE.json
python3 research/vfhe_2026_09_08/matched_field/caller.py config
research/vfhe_2026_09_08/matched_field/native/target/release/vfhe-matched-field profile
```

`work/fifo-expiry-run001/{update,linear}-{produce,verify}.{stdout,stderr}` retain
the four full-operation process outputs and macOS `/usr/bin/time -l` costs.
The following variables name the exact supplied inputs and output locations:

```sh
task_lane="$PWD/research/vfhe_2026_09_08/matched_field"
task_resident="$PWD/research/vfhe_2026_09_08/continuing_system/runtime/lifecycle/resident"
task_case="$task_resident/teaching/teach_pi10/phases/learn-attempt000/case"
task_run="$task_lane/work/fifo-expiry-run001"
/usr/bin/time -l python3 "$task_lane/caller.py" produce-update \
  "$task_case/acc.ct" "$task_case/fresh.ct" "$task_case/old.ct" \
  "$task_run/update-produced"
/usr/bin/time -l python3 "$task_lane/caller.py" verify-update \
  "$task_run/update-expected.json" "$task_run/update-produced" \
  "$task_run/update-verified"
/usr/bin/time -l python3 "$task_lane/caller.py" produce-linear \
  "$task_run/update-produced/case/out.ct" \
  "$task_resident/queries/query_expiry/query.json" \
  "$task_resident/issuer/evaluation.key" "$task_run/linear-produced"
/usr/bin/time -l python3 "$task_lane/caller.py" verify-linear \
  "$task_run/linear-expected.json" "$task_run/linear-produced" \
  "$task_run/linear-verified"
```

[EXECUTED] `INPUTS.json` retains the exact selected paths and byte hashes;
expectations pin the existing update and dot captures. The two post-run negative
consumer commands, outcomes and stderr are retained under
`work/fifo-expiry-run001/negative-consumers/`; their result is copied into the
publishable `fifo-expiry-run001.json` summary. Runtime files remain ignored.
