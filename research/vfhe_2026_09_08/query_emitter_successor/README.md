# Cached query witness emission

[EXECUTED] Total emission time fell from **102.784 to 88.168 seconds** on the same complete real query: **1.166×**, saving **14.616 seconds per class (14.2%)**. Every byte of the 82,214,912-byte witness and553,870-byte template matches both the fresh baseline and the previously proved frozen artifacts. RESULTS.json and the retained command/stdout/stderr files record the complete observation. No cryptographic run was repeated. This package changes witness scheduling only. The entire compiler-derived query relation, both moduli, public reader, backend, source theorems and security parameters remain the frozen query_arithmetic/query_runtime versions.

[DERIVED] `Compiler/BfvQueryWitnessFast.lean` is a reusable producer over the same public-row interface and exact 2509-column layout. It decomposes each word into seven radix-64 digits once per row, reuses those digits in canonical ranges and carries, accumulates each complete convolution in one 7×7 pass, and decomposes bits by repeated integer division. The previous producer rescanned all pairs for each of fourteen columns and repeatedly computed digit powers/quotients. Products, integer quotients, signed carries and output copying are unchanged.

[EXECUTED] Four existing constructed rows (zero, nonzero, maximal residue and modular negative result) compare complete fast and frozen witness arrays for equality, then check the unchanged source relation. Changed output and a radix64 digit still reject. The initial small equality control caught a cast that selected field remainder instead of natural-number remainder in bit decomposition; the selected implementation explicitly types the remainder as Nat before casting. Development failure logs are retained; final build and controls pass.

[DERIVED] This is an executable witness implementation, not a new theorem or new AIR. No claim of universal implementation equivalence is made. All future proofs still check the same source constraints; a producer bug cannot authorize an incorrect accepted output through changed constraints. The measured equality check compares every byte of the actual complete case, not just outputs, random samples or hashes of metadata.

[EXECUTED] `compare_emission.py` performs one sequential, baseline-first pair on the frozen real `card_arrival` class fixture in `query_runtime/results/case001/public_rows.json`. It includes Lean startup, source controls, public JSON parsing, template serialization, witness synthesis and full trace writing. `/usr/bin/time -l` retains CPU/RSS information. It requires byte equality of the full template, trace and sample witness between baseline, successor and the already-proved frozen artifacts. No new encryption, proving or verification run is performed.

[SOURCE, coordination] The live journal demonstration uses its already-pinned baseline cohort. This successor is opt-in and must not relabel that run. The same parser/NTT encoding, service binding, decryption and classifier limitations documented by query_arithmetic remain.


[INFERRED] This is a useful but modest reduction; it leaves 88 seconds of interpreted emission. The result does not establish stable deployment throughput: it is one baseline-first pair on a shared host. Further native compilation or serialization work should be a separately measured successor, not a reason to expand this run into a benchmark grid.

## Opt-in use

[EXECUTED] The source is frozen in SOURCE_PINS.json. `fast-query-emitter.patch` adds only the helper module and a separate root emitter; the old query modules are untouched. `emit.py` checks both source cohorts and refuses to overwrite an existing output directory. The build cache is prepared here. Runtime/journal owners received this interface after byte equality passed:

```sh
python3 /Users/ember/dev/zkml-research/research/vfhe_2026_09_08/query_emitter_successor/emit.py NEW_OUT_DIR PUBLIC_ROWS_JSON
```

[EXECUTED] To rebuild the one new module, run from `/Users/ember/dev/minidregg` using the retained cache (its existing Compiler dependencies are read-only symlinks):

```sh
lake env bash -c 'LEAN_PATH=/Users/ember/dev/zkml-research/research/vfhe_2026_09_08/query_emitter_successor/build:$LEAN_PATH lean --root=/Users/ember/dev/zkml-research/research/vfhe_2026_09_08/query_emitter_successor -o /Users/ember/dev/zkml-research/research/vfhe_2026_09_08/query_emitter_successor/build/Compiler/BfvQueryWitnessFast.olean /Users/ember/dev/zkml-research/research/vfhe_2026_09_08/query_emitter_successor/Compiler/BfvQueryWitnessFast.lean'
```

[EXECUTED] `results/build03.log` is empty with exit0; `results/samples03.log` contains the successful boundary controls. `compare_emission.py` preserves the exact matched command pair and byte comparisons; it refuses to overwrite its output directories. There are no new theorem/lemma declarations or axioms: the existing22-pin query relation remains selected unchanged.
