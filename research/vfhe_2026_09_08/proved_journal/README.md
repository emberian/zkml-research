# Proof-gated continuing ciphertext journal

[EXECUTED] The service accepted the real encrypted learner's event 65 using the
508,777-byte proof of the Lean-generated expiry relation. It committed one
durable revision only after native proof acceptance and an in-transaction parent
check. A changed output with matching reconstructed rows was refused by the
actual proof verifier. A stale parent was refused. A new service process recovered
the same head; an exact retry returned the same receipt without a new proof
execution or journal row. See [the report](REPORT.md) and
[the recorded result](results/demo001/RESULT.json).

[SOURCE implementation] `service.py` is a standard-library Python CLI and local
Unix-socket service. It runs the frozen native `vfhe-proved-operation` verifier
over exact ciphertext bytes. It does not implement a new proof system or load a
BFV secret key. [Scope and trust assumptions](SCOPE.md) are part of this artifact.

## Run the retained demonstration

From the repository root:

```sh
python3 -B research/vfhe_2026_09_08/proved_journal/run_demo.py --run demo002
```

[SOURCE interface] The run name must be new. It uses the existing public event-65
ciphertexts, template and proof; it does not rerun the learner, Lean compiler or
prover. Large native binaries, CAS objects, candidate files and SQLite state go
under ignored `runtime/`. Public commands, RPC responses and results go under
`results/<run>/`. The demonstrated `demo001` packet is retained unchanged.

## Reuse for another update

[SOURCE interface] Initialize a fresh journal with a caller-approved initial
accumulator checkpoint, native executable and exact template hash:

```sh
python3 -B service.py init --root /absolute/new-state \
  --binary /absolute/vfhe-proved-operation --template /absolute/template.json \
  --expected-binary-sha256 BINARY_SHA256 --expected-template-sha256 TEMPLATE_SHA256 \
  --initial /absolute/acc.ct --recipient READER_ID \
  --learner-class CLASS --learner-event INITIAL_EVENT
```

[SOURCE interface] The selected case must contain `acc.ct`, `fresh.ct`, `old.ct`,
`out.ct`, native-exported `public_ntt_rows.json` and `source_event.json`. The latter
uses schema `useful-prototype-expiry-proof-join-v1`, with `class`, integer `event`
and `prior_state_event`, and `files.{acc,fresh,old,out}.sha256`. The service binds
those values and the exact source-event bytes; their real-world authorization
and learner semantics remain the trusted caller's responsibility.

```sh
python3 -B service.py request --root /absolute/new-state \
  --case /absolute/case --proof /absolute/proof.bin \
  --request-id UNIQUE_REQUEST_ID --out /absolute/request.json
python3 -B service.py submit --root /absolute/new-state --bundle /absolute/request.json
python3 -B service.py head --root /absolute/new-state
python3 -B service.py history --root /absolute/new-state
```

[SOURCE interface] To run the same gate as a local service:

```sh
python3 -B service.py serve --root /absolute/new-state --socket /tmp/vfhe-journal.sock
python3 -B service.py rpc --socket /tmp/vfhe-journal.sock --request /absolute/rpc.json
```

The RPC JSON is `{"op":"head"}`, `{"op":"history"}`, or
`{"op":"submit","bundle":"/absolute/request.json"}`. SIGTERM/SIGINT stops
accepting requests and waits for active request threads. The socket is mode
0600; callers are trusted processes of the local account. Use a short socket path
because Unix-domain socket names have an OS length limit.

[SOURCE interface] An exact request-ID/request-body retry returns the retained
receipt before applying current-parent checks. A changed body under that ID
refuses. A new update must identify the current head and its exact accumulator;
its learner event must advance. The commit's output remains in `cas/<out-sha256>`
for the surviving external BFV reader. Neither the API nor proof removes that
reader's preexisting key authority.

[SOURCE compatibility] Genesis pins the service source as well as the verifier,
template and policy. Preserve those source bytes to reopen the same journal;
source upgrades require an explicit migration or a newly approved genesis. A
future proof-producing pipeline can supply new cases and proofs through this
interface when it emits the exact approved template and ciphertext format.

