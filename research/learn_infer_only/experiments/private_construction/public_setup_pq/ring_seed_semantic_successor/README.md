# 384-bit seeded semantic ring transport

[DERIVED/EXECUTED] A new `RINGSSM2`/v3 backend keeps the completed fixed 16-query semantic basis, exact sampler and ring decoder, but stores only explicit registered products plus two public 48-byte seeds. SOURCE_PINS.json freezes executable inputs for the single shared journal service run. THEOREM_APPLICATION.md states the message-basis reduction and conditional QROM boundary.

Use the existing Python environment:

```sh
research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation/.venv/bin/python -B \
  research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_seed_semantic_successor/transport.py \
  --registry /path/to/registry.json --receipt /path/to/receipt.json COMMAND ...
```

[DERIVED API] Commands retain the semantic backend's flags: `init --profile candidate_full --out a.ring`; recipient-local `register --public-a a.ring --coordinate i --key-out key.ring --registration-out registration_i.ring`; `finalize --public-a a.ring --registration ... --out public.ring`; `encode --public public.ring --input input.json --out fresh.ring`; and `combine`, `window`, `query`, `decode`. The single public.ring includes its exact registered-product payload. Every process supplies the same fixed semantic registry. Recipient key files stay mode0600 under their own private directories.

[SOURCE execution owner] The reusable accepted-state service and sole fresh run are under `research/vfhe_2026_09_08/proved_journal/seeded_ring_successor/`. This package does not launch an additional setup. The journal sets process restrictions and preserves public transcripts; backend CLI alone is not a sandbox or authenticated delivery service.

[OPEN] This is a conditional SHAKE/QROM research prototype, not a certified PQ system. Ordinary keys can read their query projection from retained inputs independently of journal acceptance. The query fixture is known public benchmark data, not a new held-out utility estimate.
