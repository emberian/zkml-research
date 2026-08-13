# The weight-commitment registry

Publishable commitments to released open-weight checkpoints, computed by HTTP
range-streaming — no full download, no GPU, **no prover**.

This is the first Hollow-LLM-closure artifact and the one piece of Pillar III
that has zero proof-system dependencies. A zkML proof binds a relation over
*committed* weights, not computational effort; without a public answer to
"committed to *what*?", the proof is about an unnamed object. This directory
produces the name.

**Nothing here is published.** Publication timing is ember's.

## Files

| path | what |
|---|---|
| `registry_tool.py` | the tool. stdlib only. `commit` / `verify` / `canon` / `tamper` |
| `MANIFEST-FORMAT.md` | **normative** format spec: canonicalization, test vector, what it binds and what it does not |
| `COMMITMENTS.md` | the commitments table + measured cost per model |
| `gates.sh` | the gates, including the deliberate-corruption teeth |
| `run_registry.sh` | reproduces every commitment in the table |
| `manifests/` | the manifests themselves (the two giants are `.json.gz`; the tool reads either transparently, and compression never touches the commitment) |
| `runs/` | run logs, cost measurements, rerun manifests |
| `test-vector.json` | synthetic manifest whose exact digest is quoted in the format doc |

## Use

```sh
# commit to a model (streams every weight byte, hashing as it goes)
python3 registry_tool.py commit openai/gpt-oss-20b

# structure only: headers, shapes, dtypes, offsets, config, tokenizer.
# does NOT bind weight bytes, and says so inside the committed core.
python3 registry_tool.py commit moonshotai/Kimi-K3 --mode structure

# cheap spot audit: re-fetch a random sample of tensor ranges and check
python3 registry_tool.py verify manifests/openai__gpt-oss-20b.<rev>.full.json --sample 8

# the exact commitment preimage, for byte-for-byte comparison between runs
python3 registry_tool.py canon <manifest> | sha256sum

# the falsifier: corrupt a manifest on purpose, then watch verify refuse it
python3 registry_tool.py tamper <manifest> --out /tmp/bad.json --mode offsets
python3 registry_tool.py verify /tmp/bad.json   # exit 1
```

Gates:

```sh
./gates.sh manifests/<a-full-manifest>.json <a-small-tensor-name> [<rerun-manifest>]
```

## How it works

Safetensors puts a JSON header at the front of every shard: `u64` header
length, then the header, then the payload, with each tensor's byte range given
relative to the end of the header. So two small range requests reveal the
entire structure of a 65 GB shard, and the payload can be streamed in order
while a hasher per tensor is fed the sub-ranges it owns. The technique is the
one `phase0/e8m0_spread.py` used to pull gpt-oss scale tensors without
downloading the model — including its integrity discipline, which is carried
over here: every ranged response is length-checked against the range asked
for, and one interior slice per shard is re-fetched and compared against what
the stream produced.

The manifest is canonicalized (sorted, whitespace-free, integer-only, ASCII-
escaped) and hashed under a domain tag; that digest is the commitment. The
rules are stated exhaustively in `MANIFEST-FORMAT.md` because the point of a
registry is that a **second implementer reproduces the same digest**.

One more check comes free: for LFS-backed files the Hub API reports the
SHA-256 its *storage* layer computed on upload, so every full shard hash has
an independent comparison that costs one API call and no payload transfer.
The tool aborts a run on disagreement and `verify` re-checks it. It is
recorded in `annotations`, never in the committed core — it is HF metadata
rather than a property of the bytes, and it is not a second trust domain
(HF serving bad bytes and HF reporting a matching oid is one adversary). What
it independently catches is transport corruption and our own bugs.

## What it is honest about

A commitment binds the bytes of a named snapshot of a named repo. It does not
say those bytes are "the real model", it does not bind serving-time behavior,
and it does not pin numerics. Structure-only manifests do not bind weights at
all and are labelled as such **inside the committed core**, so the label
cannot be stripped. The full threat list is §7 of the format doc; read it
before citing a commitment anywhere.
