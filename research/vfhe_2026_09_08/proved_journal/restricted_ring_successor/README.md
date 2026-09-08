# Restricted-ring journal commands

[EXECUTED] The [completed run](REPORT.md) creates a fresh setup and six updates
across two classes, accepts both real expiries, reopens the durable head, refuses
a changed candidate and a stale parent, then serves sixteen fixed recipients.
Each candidate is verified by full deterministic recomputation in this ring.

[SOURCE] Run the same bounded workload in a new instance from the repository root:

```sh
research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation/.venv/bin/python -B research/vfhe_2026_09_08/proved_journal/restricted_ring_successor/run_demo.py --run another001
```

[SOURCE] `ring_service.py` also exposes `init`, `head`, `audit`, `prepare`, `submit`,
`publish`, and `receive` subcommands, each with `--root ABSOLUTE_NEW_INSTANCE`.
Use the same Python environment as above. `init` fixes the existing two-class,
sixteen-query registry and creates new setup/key material. `prepare` takes
`--class`, `--input`, `--input-id`, and `--request-id`; its input is a JSON array
of 577 canonical residues modulo the genesis plaintext modulus. It returns a
bundle path and **does not commit**. `submit --bundle PATH` independently recomputes
the full candidate and atomically accepts it only against the current parent.
Use a fresh request ID for each proposal; an exact accepted request may be retried.
`audit` checks retained hashes and reconstructs the head, without rerunning ring
arithmetic. `publish` writes a model file for the current populated class heads.

[SOURCE] `receive --coordinate I --models ACCEPTED_MODEL --out RECEIPT` checks
the accepted model and that recipient's registered key before reading. To retain
the executed OS isolation, invoke it through `/usr/bin/sandbox-exec -f
INSTANCE/profiles/recipient_XX.sb` for the matching two-digit coordinate. Public
commands use `INSTANCE/profiles/public.sb`. The normal driver supplies these
profiles automatically. A bare `receive` command does not install a sandbox.
The current receipt namespace supports one retained delivery per coordinate;
use an additive successor for repeated query deliveries, preserving this run.

[SOURCE] This is a local prototype with an honest issuer and a trusted local
journal/OS, not an authenticated network deployment. [SCOPE.md](SCOPE.md) explains
the fixed-key span, the public fixture and the absence of cryptographic
history-bound release. Sources and the completed `normal001` instance are frozen.

