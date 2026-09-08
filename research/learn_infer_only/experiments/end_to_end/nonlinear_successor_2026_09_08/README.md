# Continuing nonlinear text classifier

[EXECUTED] This learner stores the last eight examples of each label and ranks a query by the mean squared dot product with those examples. The BFV backend learns by adding and expiring encrypted examples, and computes the square with actual ciphertext multiplication. The current local model has nine classes at revision 130, including a newly taught `travel_insurance` class. [REPORT.md](REPORT.md) records the completed experiments and limits.

Run from this directory with the existing local encoder environment:

```sh
TASK_PY=../../adaptation_utility/.venv/bin/python
$TASK_PY -B model.py init models/my_kernel --backend bfv
$TASK_PY -B session.py models/my_kernel
```

The session accepts one JSON object per line:

```json
{"op":"teach","label":"travel_insurance","text":"I need travel insurance including hospital treatment abroad."}
{"op":"query","text":"Can I get cover for medical treatment on holiday?"}
{"op":"status"}
```

Use `--backend plain` for a plaintext model with the same feature transform and classifier. Keep one writer per model directory. A session keeps the encoder and public BFV evaluation key loaded. The one-command interface is also available as `model.py teach DIRECTORY --label LABEL --text TEXT` and `model.py query DIRECTORY --text TEXT`; `session.py` uses the faster cached public host.

[EXECUTED] The existing completed BFV model is `models/bfv`, and the corresponding live plaintext model is `models/live_plain`. These are retained evidence; create a new directory for further teaching. [SOURCE] The local E5 encoder is loaded from the unchanged predecessor configuration, with its plaintext feature cache in this new package. No model download is needed in the current workspace.

To build the owned Rust adapter against the existing read-only local backend:

```sh
cargo build --release --offline --manifest-path crypto/Cargo.toml --bin kernel-crypto --bin kernel-crypto-cached
```

[SOURCE] Encoding and query features are plaintext. Class names, active counts and memory lanes are public. The recipient has the full BFV secret key and obtains the eight individual kernel values before averaging/ranking. This is a research implementation, without a restricted-output key or a proof of the whole interface.
