# Prove a new learner update with one command

[DERIVED implementation] This public-only pipeline takes four canonical BFV
ciphertexts and joins the existing exact stored-NTT reader, Lean compiler/witness
producer, native prover and fresh-process verifier. It authors no arithmetic
constraints or witness values. The application pins the approved expiry template.

```sh
python3 run.py CASE_DIR NEW_JOB_DIR
```

`CASE_DIR` must contain `acc.ct`, `fresh.ct`, `old.ct`, `out.ct` in the existing
useful learner's RSBFV001 format and fixed parameter set. The runner copies those
public files into the new job, exports their exact coefficient rows, invokes the
Lean producer, creates a new proof and verifies it in a separate process. It
refuses to overwrite an existing job. A producer/prover/verifier failure ends the
pipeline and is retained in `result.json` and per-command logs.

[SOURCE prerequisites] Build `../proved_operation` as described there. The
default Lean executable and dependency search path come from the recorded local
`../arithmetic_coverage/results/checked_modules.json`. They reuse that package's
compiled overlay and the read-only companion dependencies. On another checkout,
apply/build the patches described in `../arithmetic_coverage/README.md` and pass
`--lean PATH --lean-path SEARCH_PATH`. This is a research-workspace command, not
a packaged compiler distribution. `--runtime` selects the native executable;
`--threads` defaults to four; each subprocess has a 600-second default timeout.

[DERIVED scope] The proof constrains `out = acc + fresh − old` for the exact
selected ciphertext coefficients. It does not decide whether those ciphertexts
are an authorized learner event, whether the old example should expire, or who
should receive an answer. The adjacent `proved_journal` service supplies a
separate application binding. A full learner reader key still exists. No private
files are required by this pipeline.

[EXECUTED] The command generated and independently verified a new proof for actual
saved event 66 (`cash_withdrawal_charge`). The initial checked exporter took
218.802 seconds end to end, including 215.887 seconds interpreting every source
constraint before proving. The production exporter took 41.372 seconds, including
38.504 seconds generating the witness, 2.636 seconds in the proof command and
0.177 seconds in the fresh verification command: a 5.29× whole-pipeline difference
in this one same-event pair. The generated template and complete 33,325,056-byte
witness are byte-identical. See `results/COMPARISON.json` and the retained commands,
proofs and verifier outputs in `results/checked/` and `results/production/`.

[DERIVED implementation] `EmitBfvExpiryFast.lean` retains the original
Signature-fold relation and `variableArray` witness construction. It skips only
the extra per-row source interpreter check; the actual prover and verifier check
the unchanged relation. The exporter report explicitly says those interpreter
checks were not run. Use `--checked-export` to select the original exporter.
The approved-template pin still rejects a changed relation. The two emitters are
research entry points over the same proved source modules, not independent AIRs.

[EXECUTED reproduction] The retained input is `cases/event66/`. From this directory:

```sh
python3 run.py cases/event66 runs/local_production
python3 run.py cases/event66 runs/local_checked --checked-export
```

An optional `source_event.json` is carried into the staged case for the journal
service. It is declared metadata, not authenticated by this arithmetic pipeline.
