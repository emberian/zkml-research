# The commitments

Produced 2026-08-13 by `registry_tool.py` v0.1.0, SHA-256 throughout, on a
domestic link measured at 5–13 MB/s. Reproduce with `./run_registry.sh`.
Format and threat notes: `MANIFEST-FORMAT.md` (normative). Run logs: `runs/`.

**Not published anywhere.** These are files on disk. Publication timing is
ember's.

## Table

`coverage` is a field inside the committed core, so it cannot be relabelled
without changing the commitment.

| model | revision | coverage | commitment (SHA-256) | tensors | shards | weight bytes |
|---|---|---|---|---|---|---|
| `openai/gpt-oss-20b` | `6cee5e81ee83` | **full** | `3218eb92942a115dcc79ef1acd8778702991be0a034acc5ab55eb26be47db61f` | 459 | 3 | 13.76 GB |
| `Qwen/Qwen3-8B` | `b968826d9c46` | **full** | `13adc299c5f4d3f8e1c9bdfac84d890c3e3ea6ede6b2bae5fdaa7df8651910fa` | 399 | 5 | 16.38 GB |
| `Qwen/Qwen3-0.6B` | `c1899de289a0` | **full** | `bed2361d5898823569760ebf4bc7998a9bdbc90426afe78c30692aa2c465ba5d` | 311 | 1 | 1.50 GB |
| `openai/gpt-oss-120b` | `b5c939de8f75` | structure-only | `b8699decd118b360206bf47f7783c5ab50706d80fcbc33d75a91577c38de8a76` | 687 | 15 | 65.25 GB |
| `google/gemma-3-27b-it` ⚠ | `005ad3404e59` | structure-only | `7752d385091eea4476db4b51694894f9c402acd38a08d2ddd07b07b08e29eb5e` | 1,247 | 12 | 54.86 GB |
| `meta-llama/Llama-3.1-8B-Instruct` ⚠ | `0e9e39f249a1` | structure-only | `15e0a6c49eb594cbf20e6db9c6c047fe4b1c3b1bc6107f7b204f3f7e67083261` | 291 | 4 | 16.06 GB |
| `deepseek-ai/DeepSeek-V3.1` | `c0781d039fb7` | structure-only | `5db967ae32cc5e96ad951bab72b5ab2fb7c6cb94400e23f209fc7aa589d5e9ba` | 91,991 | 163 | 688.59 GB |
| `moonshotai/Kimi-K3` | `9f62e4e9fffb` | structure-only | `9bf53e646d4b9b9609d6140d0b710140e92a65fcd9ad68b6f7c5d1c3b07d5a2b` | 497,220 | 96 | 1,560.94 GB |

⚠ **Not publicly reproducible.** These two repos refuse anonymous readers
(HTTP 401) and were read with the operator's Hub token, which has their
licences accepted. A stranger cannot re-derive these commitments without their
own accepted licence. `annotations.auth_used` records it. Every other row was
fetched from a repo that serves anonymous readers, and the gpt-oss-20b row was
**audited end to end with no credentials at all** (below).

Every digest above is printed in full and is generated from the manifests, not
transcribed by hand; `gates.sh` re-checks the table against `manifests/*.json`
on every run (gate G10) so a digest in this document cannot drift from the file
it names.

## Measured cost

| model | coverage | fetched | requests | wall | rate |
|---|---|---|---|---|---|
| `openai/gpt-oss-20b` | full | 13,789 MB | 24 | 27.3 min | 8.4 MB/s |
| `Qwen/Qwen3-8B` | full | 16,398 MB | 34 | 34.0 min | 8.0 MB/s |
| `Qwen/Qwen3-0.6B` | full | 1,519 MB | 12 | 2.2 min | 11.5 MB/s |
| `openai/gpt-oss-120b` | structure | 28.2 MB | 69 | 26.7 s | — |
| `google/gemma-3-27b-it` | structure | 35.1 MB | 58 | 30.9 s | — |
| `meta-llama/Llama-3.1-8B-Instruct` | structure | 9.3 MB | 24 | 9.3 s | — |
| `deepseek-ai/DeepSeek-V3.1` | structure | 49.5 MB | 659 | 7.5 min | — |
| `moonshotai/Kimi-K3` | structure | 271.1 MB | 391 | 4.5 min | — |

**Full mode costs one pass over the weight bytes and nothing else.** 31.65 GB
streamed across three models in 63.5 minutes of wall clock; the overhead above
the weight bytes themselves is the aux files and two small header reads per
shard — 0.2% for gpt-oss-20b. Memory is a few MB regardless of model size:
the tool holds hasher state and one 4 KiB slice per shard, never the payload.

**Structure mode costs almost nothing and scales with shard count, not size.**
Kimi-K3 is a 1.56 TB checkpoint recorded in 4.5 minutes for 271 MB — 96 shard
headers (Kimi's are ~820 KB each, fetched twice for the stability re-check)
plus a 12 MB file index. DeepSeek-V3.1 took longer than Kimi despite being
half the size because it has 163 shards against 96: the cost is request
latency, not bandwidth.

### The price of the full pass we did not run

At the measured 8.3 MB/s average for full mode, streaming every weight byte
would cost:

| model | weight bytes | projected full-pass wall |
|---|---|---|
| `meta-llama/Llama-3.1-8B-Instruct` | 16.06 GB | ~32 min |
| `google/gemma-3-27b-it` | 54.86 GB | ~1.8 h |
| `openai/gpt-oss-120b` | 65.25 GB | ~2.2 h |
| `deepseek-ai/DeepSeek-V3.1` | 688.59 GB | ~23 h |
| `moonshotai/Kimi-K3` | 1,560.94 GB | ~52 h |

These are link-bound, not compute-bound: SHA-256 over a stream is far faster
than 8 MB/s, and parallel range requests did **not** raise the aggregate
(measured 4/8/16 concurrent workers: 10.0 / 9.6 / 10.2 MB/s). On a datacentre
link the same runs are hours, not days, and the tool needs no changes to do
them — `--mode full` is the only difference. **Nothing about the design blocks
full coverage of any of these; only this link does.**

## Verification evidence

* `runs/gates-gpt-oss-20b.log` — all 11 gates, including **G7: two independent
  from-scratch runs 27 minutes apart produced a byte-identical canonical
  preimage and the same commitment.**
* `runs/gates-qwen3-0.6b.log` — all 11 gates, G7 passing on a second model.
* `runs/gates-qwen3-8b.log` — 10 gates (no rerun for this model).
* **Five of the eight models were committed twice, from scratch, and produced
  byte-identical canonical preimages and identical commitments**:
  `openai/gpt-oss-20b`, `Qwen/Qwen3-0.6B`, `openai/gpt-oss-120b`,
  `moonshotai/Kimi-K3`, `deepseek-ai/DeepSeek-V3.1`. The rerun manifests are
  in `runs/*.rerun.json` and can be diffed against `manifests/` with
  `registry_tool.py canon`. The three not rerun (`Qwen/Qwen3-8B` and the two
  licence-gated entries) were skipped for link time, not for any other reason.
* `runs/verify-gpt-oss-20b-anonymous.log` — **a stranger's audit.** With
  `--no-auth`, no token in the path: the commitment recomputes, all 7 aux
  files match, all 3 shard headers match *and* the manifest's structural
  claims re-derive from those header bytes, the Hub's own stored file hashes
  agree on all 3 whole shards, and 3 randomly sampled tensors — including a
  265 MB MoE block tensor — hash to their recorded values. 310 MB fetched,
  23 checks, exit 0.
* `runs/gated-probes.log` — what an anonymous reader sees for each repo.

## Refusals, recorded

The registry records what it could not get, not only what it got.

| repo | anonymous | with operator credentials |
|---|---|---|
| `deepseek-ai/DeepSeek-V4` | HTTP 401 | **HTTP 404 — no such repo** |
| `meta-llama/Llama-3.1-8B-Instruct` | HTTP 401 | readable (licence accepted) |
| `google/gemma-3-27b-it` | HTTP 401 | readable (licence accepted) |
| `openai/gpt-oss-20b` | readable | readable |

**`deepseek-ai/DeepSeek-V4` does not exist.** It was named in this lane's
brief as a Tier-1 giant to commit to. The Hub answers 401 to anonymous callers
for gated, private *and* nonexistent repos alike, so the anonymous probe alone
could not tell which; with credentials the revision endpoint answers **404**,
which it would not do for a repo that merely required a licence. The
DeepSeek entry in this table is therefore `DeepSeek-V3.1`, the largest
DeepSeek checkpoint that exists on the Hub today.

The tool distinguishes these outcomes at the exit code: `0` committed,
`2` unreadable, `1` (verify only) audit failure. It never writes a manifest
for a repo it could not read.

## Coverage, stated plainly

Three models are **weight-binding**: every byte of every shard was streamed
and hashed, and the per-tensor hashes name exactly which bytes are which
tensor. Five are **structure-only**: the file index, every shard header, and
the configuration and tokenizer files are bound byte-exactly — so the
architecture, the full tensor inventory with shapes and dtypes, and the
settings a model is loaded under are all fixed — but **the weight payload was
never read and is not bound**. For those five the Hub's own stored file hashes
are recorded in `annotations` as an unverified publisher attestation, clearly
labelled, so a later full pass can be checked against what the Hub said today.

That is the whole of it. A structure-only entry is not a weight commitment and
this document does not let it read as one.

## Not done

Named so the next pass starts from the list rather than from a re-discovery.

1. **No second implementation.** Reproducibility here is the same tool run
   twice on one machine — it proves the process is deterministic, not that
   `MANIFEST-FORMAT.md` is unambiguous. The spec was written for a second
   implementer and carries a worked test vector with exact bytes; nobody has
   written that implementation. Until someone does, "a stranger can reproduce
   this" rests on the spec being as clear as it looks.
2. **No consumer.** Nothing cites these commitments. The registry is the half
   of the Hollow-LLM closure that needs no prover; the half that binds a proof
   to a registry entry is not built, and this lane did not touch it.
3. **No Merkle structure.** The commitment is a hash of a flat manifest, so
   proving "tensor T is under commitment C" means shipping the whole manifest
   (60 KB to 100 MB depending on model — Kimi-K3's has 497,220 tensors). A
   Merkle tree over the sorted tensor list gives O(log n) inclusion proofs and
   is the obvious v2. Deliberately deferred until there is a consumer, because
   the tree shape should follow the consumer's query pattern rather than be
   guessed at now.
4. **Five models are structure-only** — not a design limit, a link limit; the
   projected wall times are above and `--mode full` is the only change needed.
5. **Two entries are not publicly reproducible** (the ⚠ rows). Committing to a
   gated model is possible but the result is only checkable by others with the
   same licence accepted. Whether such entries belong in a public registry at
   all is a judgement call, not a technical one, and it is ember's.
6. **No signature, no anchor.** A manifest is an unsigned claim by whoever ran
   the tool. Signing it, or posting the commitment somewhere append-only, is
   what would make it a *register* rather than a file. Deliberately not done:
   it is the first outward-facing, hard-to-reverse step.
7. **No LoRA/delta support.** Adapters as deltas against a committed base is
   named in the agenda as the composition that makes the registry cheap for
   fine-tunes. Not implemented.
8. **No MoE router binding.** gpt-oss-20b and Kimi-K3 are MoE; the registry
   binds their expert weights but says nothing about routing. That is a
   separate agenda item.
9. **BLAKE3 unused.** The tool supports it; the module was not importable in
   this environment (PEP 668 blocks a bare install), so every commitment here
   is SHA-256. Recorded inside each core, so nothing is ambiguous.
10. **Byte-weighted sampling not implemented.** `verify` samples tensors
    uniformly, which over-samples the many tiny norm tensors relative to byte
    mass. Fine for the audit-game claim actually made; wrong for any claim
    phrased as "fraction of weight bytes verified", which is why no such claim
    is made.
11. **The aux allowlist is fixed.** A repo with a behaviour-relevant file not
    on the list has it unbound, silently. Custom modelling code shipped for
    `trust_remote_code` is the sharp case, and it is unbound today.
