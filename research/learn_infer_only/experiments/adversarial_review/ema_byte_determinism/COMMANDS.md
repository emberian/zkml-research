# Retained audit commands

[EXECUTED] Each retained run used the following command shape, with suffixes
001 through 004 identifying the corresponding stdout/stderr files:

```sh
python3 research/learn_infer_only/experiments/adversarial_review/ema_byte_determinism/audit.py > research/learn_infer_only/experiments/adversarial_review/ema_byte_determinism/audit_004.stdout 2> research/learn_infer_only/experiments/adversarial_review/ema_byte_determinism/audit_004.stderr
```

[EXECUTED] Run001 failed only because an excerpt upper line bound was beyond
the end of TFHE's bootstrapping source (625 requested, 604 existing). The
stderr is preserved. Run002 passed after that instrument correction; run003
extended source ranges for encryption/FMADD; run004 added plan-debug source
and checked the owner's final public seal. This is a read-only Python parser
and source hasher, not execution of the encrypted learner or FFT planner.

[SOURCE / instrument] Adaptive source location searches used `rg -n` for
`Fft::new`, `Method::Measure`, `Plan`, `random`, `seeder`, `rayon`, `par_`,
`serialize`, and the called gate/rounding method names within the local pinned
TFHE/FFT/bincode source graph. The resulting selected files, hashes and exact
line ranges are retained in `source_manifest.json`; their contents are in
`SOURCE_EXCERPTS.txt`. Only these corpora support the report's narrow absence
statements. No external search was required.
