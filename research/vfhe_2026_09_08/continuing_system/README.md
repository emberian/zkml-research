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
example. Query ranking compares exact mean squared-dot scores.

[SOURCE] This app uses the existing E5 encoder environment and retained native
builds. `check` reports required dependencies and source/profile identities;
`build` provides or executes the supported missing-native rebuild steps. The
retained research profiles include absolute paths: this is not yet a portable
installation package.

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
