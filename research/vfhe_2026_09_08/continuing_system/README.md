# Continuing learner

[SOURCE] A local research application combining the corrected whole-row proof
pipeline with continuing text teaching, encrypted inference, a durable journal,
eight-example class memory, and a background-job interface. This is executable
research in this working tree, not a shipped system.

From this directory:

```sh
python3 run.py check
python3 run.py serve --state runtime/local --port 8765
```

Open <http://127.0.0.1:8765>. Declare your class labels, teach examples, and query
the continuing model. The server accepts jobs immediately and runs expensive
proof work serially. Closing the browser does not stop a job. After restarting
the service, resume an interrupted job from its last complete phase; completed
requests return their retained result.

[SOURCE] A teaching is committed only after its update proof has been verified
against the current model. A query produces and independently verifies the
complete kernel computation for every active class before the local reader
returns the class scores. The ninth teaching to a class removes its oldest
example. Setup selects the score and proof engine once; the journal binds that
choice for the lifetime of the instance. New browser setups default to packed
classes, the mode exercised by the complete nine-class lifecycle and fresh-text
browser run in `RESULTS.md`.

| Learner mode | Score | Complete proofs per update / query |
|---|---|---:|
| Squared / compact | Mean squared dot product | 8 / 116 per class |
| Linear / compact | Mean signed dot product | 8 / 88 per class |
| Linear / matched | Mean signed dot product | 32 / 352 per class |
| Packed classes / matched | Mean signed dot product | 32 / 352 per bank of up to eight classes |

[SOURCE] The matched engine proves directly in the four BFV arithmetic fields.
It removes the smaller proof field's carry and range machinery. Its chunk count
is larger; chunk count alone does not measure time, memory or proof bytes. The
linear engines return signed slot values and compare exact rational means.

[SOURCE] Packed mode keeps an encrypted sum of each class's live examples in a
fixed slot. Up to eight classes share a ciphertext bank and query proof batch.
Each class still has its own eight-example FIFO; the bounded reader checks each
class sum against its actual example count. This mode has its own genesis and
does not migrate an existing example-layout instance.

[SOURCE] This app uses the existing E5 encoder environment and retained native
builds. `check` reports required dependencies and source/profile identities;
`build` provides or executes the supported missing-native rebuild steps. The
retained research profiles include absolute paths: this is not yet a portable
installation package.

```sh
python3 run.py check --engine all
python3 run.py build --engine linear-matched
python3 run.py evaluate runtime/my-evaluation/resident --score linear --proof-backend matched
```

[SOURCE] An evaluation uses the fixed public corpus and prepared vectors. Resume
with `run.py resume` and the same root and engine arguments. The local interface
can display that run by serving its parent directory; manual submissions reopen
when the workload finishes (`run.py serve --state runtime/my-evaluation`).
`snapshot.py` exports completed public execution
records for publication without the local key and proof files.

For the packed learner's separate fixed nine-class workload:

```sh
python3 run.py packed-evaluate runtime/my-packed-evaluation/resident
python3 run.py serve --state runtime/my-packed-evaluation
```

[OPEN] The full BFV reader key survives in the local instance. The encoder,
encryption setup, controller, native parser/NTT maps and proof backend retain
their stated trust assumptions. Proof-gated operation is not the absence of
master-read authority. There is no claim here of complete cryptographic
soundness, reader restriction, post-quantum security of the assembled system,
or privacy against the operator of this entire machine.

[SOURCE] `workload.json` fixes the public teaching and held-out corpus before
evaluation. `workload.py` prepares the feature/reference data and runs one
complete lifecycle through later learning, FIFO expiry and process restart.
Its retained results distinguish utility, arithmetic agreement, proof costs,
and what remains outside the implementation.
