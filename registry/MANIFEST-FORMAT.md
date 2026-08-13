# The weight-commitment manifest format, v1

**Status.** Normative specification of the `zkml-weight-registry` manifest,
format_version 1. `registry_tool.py` in this directory is one implementation
of it. The purpose of this document is that a **second implementer, in any
language, reproduces byte-identical commitments from this text alone** — so
every rule that could differ between implementations is stated here, not left
to Python's defaults.

Nothing here is published. Publication timing is ember's.

---

## 1. What the object is

A manifest is a JSON file with four top-level keys:

```json
{
  "format":      "zkml-weight-registry",
  "commitment":  "<lowercase hex digest>",
  "core":        { ... },
  "annotations": { ... }
}
```

**Only `core` is committed to.** `commitment` is the digest of `core`'s
canonical serialization under the domain tag (§3). `annotations` records how
the run went — wall time, bytes fetched, notes — and is **not binding**: it
may be edited, stripped or regenerated without invalidating the commitment,
and a verifier must never trust it. `format` outside the core is a
convenience label; the authoritative copy is `core.format`, which *is*
committed.

The split exists so that two independent runs of the tool produce **identical
commitments** while their timing and byte-count annotations naturally differ.

## 2. The `core` object

All integers; no floating-point values appear anywhere in `core` (§3).

| field | type | meaning |
|---|---|---|
| `format` | string | always `"zkml-weight-registry"` |
| `format_version` | int | `1` |
| `hash_algorithm` | string | `"sha256"`, `"sha512"` or `"blake3"` — the algorithm used for **every** digest in the manifest **and** for the commitment itself |
| `coverage` | string | `"full"` or `"structure-only"` (§5) |
| `source` | object | `host`, `repo_id`, `revision`, `index_present` |
| `aux_files` | array | small non-weight files, fetched whole; sorted by `path` |
| `shards` | array | one entry per safetensors shard; sorted by `path` |
| `tensors` | array | one entry per tensor; sorted by `name` |

`source.revision` is a **40-character lowercase hex git commit sha**, never a
branch name. The tool resolves `main` to a sha through the Hub API and
performs every subsequent fetch against `/resolve/<sha>/`, so a manifest names
one immutable snapshot of the repo. A manifest against `main` would be
meaningless: `main` moves.

`source.index_present` is `true` iff the repo has a top-level
`model.safetensors.index.json`.

**`aux_files[i]`**: `path` (top-level filename), `byte_len`, `hash` (digest of
the file's entire bytes).

**`shards[i]`**:

| field | meaning |
|---|---|
| `path` | top-level filename of the shard |
| `byte_len` | total file length in bytes |
| `header_len` | `N`, the safetensors header length from the file's first 8 bytes |
| `data_start` | `8 + N` |
| `header_hash` | digest of the `N` header bytes at offsets `[8, 8+N)` — **not** including the 8-byte length prefix |
| `file_hash` | digest of **all** `byte_len` bytes of the file. Present iff `coverage == "full"` |
| `n_tensors` | number of entries in the header other than `__metadata__` |
| `tensor_bytes` | sum of tensor byte lengths in this shard |
| `unclaimed_data_bytes` | `byte_len - data_start - tensor_bytes` |

**`tensors[i]`**: `name`, `shard`, `dtype` (the safetensors dtype string,
e.g. `BF16`, `U8`, `F32`), `shape` (array of ints), `offset_begin`,
`offset_end`, `byte_len` (`= offset_end - offset_begin`), and `hash` (digest
of the tensor's payload bytes), present iff `coverage == "full"`.

⚠ **`offset_begin`/`offset_end` are relative to `data_start`, not to the file.**
The tensor's absolute byte range in the shard is

```
[ shard.data_start + offset_begin , shard.data_start + offset_end )
```

This is the safetensors convention, restated because getting it wrong
produces a manifest that hashes the wrong bytes and still verifies against
itself.

Absent fields are **absent**, never `null`. A structure-only manifest has no
`hash` key on tensors at all; this changes the canonical bytes, so a
structure-only manifest can never be confused with a full one that happens to
have null hashes.

## 3. Canonicalization — normative

The commitment preimage is

```
b"zkml-weight-registry/v1\n"  ||  canonical_json(core)
```

where `||` is byte concatenation and the tag is those exact 24 ASCII bytes,
including the trailing newline (`0x7a 6b 6d 6c ... 76 31 0a`).

`canonical_json` is a **restricted profile** of JSON, chosen so that agreement
between implementations does not depend on subtle spec-reading. It is
essentially RFC 8785 (JCS) with the ambiguous parts forbidden rather than
resolved:

1. **No whitespace anywhere.** Separator between a key and its value is `:`;
   between members of an object or array, `,`. No spaces, no newlines.
2. **Object keys are sorted ascending by Unicode code point.** All keys in
   this format are ASCII (rule 6), so this coincides with byte order, with
   UTF-16 code-unit order, and with `sort_keys=True` in Python. An
   implementation that sorts by UTF-16 code units (JCS) gets the same answer.
3. **Arrays keep their order.** The producer establishes the order:
   `aux_files` and `shards` ascending by `path`, `tensors` ascending by
   `name`, both by Unicode code point. `shape` keeps the order the
   safetensors header gave.
4. **Numbers are integers only**, serialized with no sign for non-negative
   values, no leading zeros, no exponent, no fraction. **Floating-point
   values are forbidden in `core`** — the whole class of "does this
   implementation print `1.0` or `1`" is removed rather than adjudicated. A
   producer that cannot express something as an integer must not put it in
   the core. (This is why timings live in `annotations`.)
5. **Strings are escaped ASCII.** Emit `\"` for `U+0022`, `\\` for `U+005C`,
   `\b \f \n \r \t` for `U+0008 U+000C U+000A U+000D U+0009`, `\uXXXX` with
   **lowercase** hex digits for every other code point below `U+0020`, and
   `\uXXXX` (lowercase hex, surrogate pairs for astral code points) for every
   code point above `U+007E`. `/` is **not** escaped. This is exactly
   Python's `json.dumps(..., ensure_ascii=True)` and makes the output pure
   ASCII, so the encoding question does not arise.
6. **Object keys must be ASCII.** A producer must refuse to emit a core
   containing a non-ASCII key. (Tensor *names* are values, not keys, and may
   contain anything; rule 5 escapes them.)
7. `true`, `false`, `null` are lowercase bare literals. `null` should not
   appear (see §2, absent means absent) but is defined for completeness.
8. The result is a byte string; hash it directly. No trailing newline is
   added.

The digest is written as **lowercase hex**, no algorithm prefix. Which
algorithm produced it is `core.hash_algorithm`, which is itself inside the
committed bytes — so a manifest cannot be reinterpreted under a different
algorithm without changing its commitment.

### Reference implementation of the rule set

```python
json.dumps(core, sort_keys=True, separators=(",", ":"),
           ensure_ascii=True, allow_nan=False).encode("ascii")
```

plus a walker that rejects floats and non-ASCII keys before serializing.

## 4. Test vector

`test-vector.json` in this directory is a synthetic manifest (the repo
`example/tiny` does not exist; the hashes are of the literal byte strings
noted below). A second implementation must reproduce these exactly.

Component digests, all SHA-256:

| input | digest |
|---|---|
| `b"{}"` | `44136fa355b3678a1146ad16f7e8649e94fb4fc21fe77e8310c060f61caaff8a` |
| `b"H" * 64` | `10fbc0ab0346603d52577d1e51bc8dbe5e19c95e6ab2d90ec50fb880de83098d` |
| `b"F" * 80` | `178027ff2691cf2f29fb1e676178318f53f325659cb22e58e4f91a41b0fe2daf` |
| `b"\x00" * 8` | `af5570f5a1810b7af78caf4bc70a660f0df51e42baf91d4de5b2328de0e83dfc` |

The canonical core is **856 bytes**:

```
{"aux_files":[{"byte_len":2,"hash":"44136fa355b3678a1146ad16f7e8649e94fb4fc21fe77e8310c060f61caaff8a","path":"config.json"}],"coverage":"full","format":"zkml-weight-registry","format_version":1,"hash_algorithm":"sha256","shards":[{"byte_len":80,"data_start":72,"file_hash":"178027ff2691cf2f29fb1e676178318f53f325659cb22e58e4f91a41b0fe2daf","header_hash":"10fbc0ab0346603d52577d1e51bc8dbe5e19c95e6ab2d90ec50fb880de83098d","header_len":64,"n_tensors":1,"path":"model.safetensors","tensor_bytes":8,"unclaimed_data_bytes":0}],"source":{"host":"huggingface.co","index_present":false,"repo_id":"example/tiny","revision":"0000000000000000000000000000000000000000"},"tensors":[{"byte_len":8,"dtype":"F32","hash":"af5570f5a1810b7af78caf4bc70a660f0df51e42baf91d4de5b2328de0e83dfc","name":"w","offset_begin":0,"offset_end":8,"shape":[2],"shard":"model.safetensors"}]}
```

The preimage is 24 + 856 = **880 bytes**, and

```
commitment = sha256(preimage) =
  1b34613e012a472aa38b25f760f4ca17ed016058b49d4e95aab141a4a9b2a0e0
```

`./gates.sh` re-derives this from the code on every run, so the document and
the implementation cannot drift apart silently.

## 5. Coverage: `full` versus `structure-only`

`coverage` is **inside the core**, so the coverage claim is itself bound: a
structure-only manifest cannot be relabelled as full without breaking its
commitment.

**`full`** — every byte of every shard was streamed and hashed. Present:
`shards[i].file_hash` and `tensors[i].hash`. Cost: one full pass over the
repo's weight bytes (see COMMITMENTS.md for measured figures).

**`structure-only`** — the shard *headers* were fetched and hashed; the weight
payload was never read. Present: `shards[i].header_hash` (so every shape,
dtype, offset and any `__metadata__` is bound, byte-exactly), aux files in
full (so `config.json` and the tokenizer *are* bound), and `byte_len` per
shard. Absent: `file_hash`, `tensors[i].hash`.

**A structure-only manifest does not bind the weights.** It binds the
architecture, the tensor inventory and the configuration. It is emitted for
repos where a full pass is not currently affordable (a 1.5 TB checkpoint at
the measured ~12 MB/s is ~36 hours of streaming). It is labelled, not
disguised: the mode is in the committed core, in the filename, and in the
commitments table.

## 6. What a `full` commitment binds

Given a manifest with `coverage: "full"` and its commitment value:

- **The exact bytes of every listed shard**, via `file_hash` — including the
  8-byte length prefix, the JSON header, all tensor payloads, and any padding
  or unclaimed gap bytes. Nothing in the file escapes it.
- **The exact bytes of each tensor payload**, via `tensors[i].hash`, at the
  named offsets. This is the part a proof system can cite: "the weights I
  proved over are the ones under commitment C, tensor `model.layers.3.…`".
- **The exact bytes of each listed aux file** — `config.json`,
  `generation_config.json`, `tokenizer.json`, `tokenizer_config.json`,
  `special_tokens_map.json`, `vocab.json`, `merges.txt`,
  `chat_template.jinja`, `preprocessor_config.json`, `processor_config.json`,
  `model.safetensors.index.json`, whichever of those exist at the repo root.
- **The claimed structure** — every shape, dtype and offset, both directly and
  through `header_hash`.
- **The identity of the snapshot** — host, repo id, and the 40-hex commit sha.

Note that `file_hash` and the per-tensor hashes are *independent* claims that
overlap: the shard hash covers the header and any gaps, the tensor hashes
cover only payload. **`file_hash` is not derivable from the tensor hashes**
and the tool does not pretend otherwise — safetensors pads the JSON header to
align `data_start`, and a shard may in principle carry unclaimed bytes between
or after tensors. `unclaimed_data_bytes` reports exactly how many such bytes
exist (`0` for every model measured so far); they are inside `file_hash` and
outside every tensor hash.

### The Hub LFS cross-check (annotation, not a commitment)

For LFS-backed files the Hub API reports `lfs.sha256`, which is the SHA-256 of
the file contents as its **storage layer** computed it — on upload, by a
different code path than the CDN that served us the bytes. When the manifest's
algorithm is SHA-256, the tool compares it against the `file_hash` it computed
from the stream and **aborts the run on disagreement**. Every full manifest
here has it matching for every shard; the result is recorded in
`annotations.hub_lfs_crosscheck`.

It is deliberately **not** in `core`:

- it is HF metadata, not a property of the bytes, and a storage migration that
  stopped reporting it (or reported an xet hash instead) would make old
  manifests unreproducible;
- it is not an independent *trust* domain — HF serving bad bytes and HF
  reporting a matching oid is one adversary, not two. What it independently
  catches is **transport corruption and our own bugs**, which is what it is
  claimed to catch and no more.

For structure-only manifests the oid is recorded with `"match": null` and a
note reading `PUBLISHER ATTESTATION, NOT VERIFIED BY US`. It is kept so that a
later full run can be checked against what the Hub said today. It is **not**
coverage, it is not in the core, and a structure-only manifest carrying one is
still exactly as weight-binding as one without: not at all.

### Aux-file scope decision

Configuration and tokenizer files **are in scope** and are bound in both
coverage modes. They are kilobytes to tens of megabytes, and they are
behavior-relevant in the strong sense: a different `config.json` can change
the architecture the weights are read into (rope scaling, sliding window,
`num_key_value_heads`, quantization config), and a different tokenizer changes
what the model is asked. A weight commitment that left them out would bind a
pile of numbers rather than a model.

## 7. What it does NOT bind — threat notes

This section is the honest half and should be read before the commitment is
cited anywhere.

1. **It does not bind "this is the real model."** It binds the bytes of a
   named snapshot of a named repo. If the publisher uploaded ghost weights,
   the commitment faithfully commits to ghost weights. It converts *"which
   weights?"* from an unanswerable question into a fixed 32-byte answer; it
   does not make the answer good. This is exactly the Hollow-LLM gap
   (arXiv 2607.28884): a proof binds a relation over committed weights, not
   effort, so a registry is a **necessary** and clearly **not sufficient**
   part of closing it.
2. **It does not bind serving-time behavior.** Nothing here says a served
   endpoint runs these weights. Bridging that needs the proof side; the
   registry is what the proof side would *cite*.
3. **It does not pin numerics.** Two backends can execute these exact bytes
   and disagree — reduction order, fused multiply-add contraction,
   MXFP4/OCP-underspecified operations. A statement of the form "output y on
   input x under commitment C" is only well-posed once a backend is pinned.
   (Our own note on this: a deterministic compiled server is a pinned backend
   by construction; nothing in *this* format achieves it.)
4. **It does not bind anything outside the aux allowlist.** Custom modelling
   code (`modeling_*.py`, `trust_remote_code` payloads), README claims,
   licence text, `original/` and `metal/` variant directories, GGUF exports,
   and any non-safetensors weight file are **unbound**. A repo can carry a
   second copy of the weights (gpt-oss-20b does: `original/model.safetensors`)
   which this manifest ignores entirely. If those matter for a use, they must
   be added to the format and the affected commitments re-emitted.
5. **It does not bind the tool that produced it.** `annotations.tool_version`
   is outside the commitment on purpose — the manifest is a claim about a
   repo, not about a program. A reader who wants to know the claim is true
   should re-derive it, not trust the annotation.
6. **The transport is trusted only for availability, not integrity.** Every
   digest is computed over bytes the tool received; a server that serves
   different bytes to different clients would produce a manifest that is
   correct about *what this client saw*. Three things narrow this — the
   interior re-fetch, the pinned `revision`, and the Hub LFS cross-check
   (§6) — but none of them leaves HF's trust domain, so a full defence still
   needs an independent second producer on a different network. The registry
   design *wants* independent re-derivation for exactly this reason.
7. **Hash agility is not migration.** `hash_algorithm` is committed, so a
   registry with mixed algorithms is coherent — but a SHA-256 commitment
   inherits SHA-256's collision resistance and nothing better. The default is
   SHA-256 because it is in every standard library; BLAKE3 is supported and
   faster, and was **not** used for the runs recorded here because the module
   was not importable in this environment. What is in the manifest is what
   was used.

## 8. Verification — the spot audit

`registry_tool.py verify <manifest>` performs, in order:

1. **Recompute the commitment from `core` and compare** to the file's
   `commitment`. Everything after this is meaningless without it: this is
   what makes the sampled checks tests of a *fixed* claim rather than of a
   file the adversary can edit as we go.
2. **Re-fetch every aux file in full** and compare hashes. They are small; a
   sample is not worth it.
3. **Re-fetch a random sample of shard headers** (`--shard-sample`, default 4;
   `--all-shards` for all of them), compare `header_hash` and the shard
   length, then **re-derive the structural claims from those header bytes**
   and compare them field by field against the manifest: tensor membership,
   `offset_begin`/`offset_end`, `byte_len`, `dtype`, `shape`, `data_start`,
   `n_tensors`, `tensor_bytes`, `unclaimed_data_bytes`. `header_hash` proves
   the header is authentic; it does *not* prove the manifest describes it, and
   without this step a producer could commit to hashes of byte ranges the
   header never named.
4. **Re-fetch a random sample of tensor byte ranges** (`--sample`, default 8),
   streaming and hashing each, and compare `tensors[i].hash`. Skipped, with a
   printed note, on structure-only manifests — they never claimed it.

Sampling is uniform without replacement over the tensor list, seeded by
`--seed` for reproducible audits. This is the **audit game** in its plainest
form: an adversary who has altered a fraction *f* of tensors evades a
*k*-tensor audit with probability about (1−*f*)^*k*; the tool prints this
figure for the sample size actually used. Two properties worth stating
plainly:

- The sample is over **tensors, not bytes**. A single flipped byte in one
  tensor is caught only if that tensor is drawn. Detection probability is
  therefore about the *number of tensors touched*, and an adversary who
  corrupts one small tensor is cheap to hide from a small audit. Full
  assurance is the full stream — which is affordable here (~20 minutes for
  gpt-oss-20b) and is what `commit` does.
- Uniform sampling is *not* size-weighted, so it over-samples the many tiny
  norm/bias tensors relative to the byte mass. A byte-weighted variant would
  be the right choice for a "fraction of weight bytes verified" claim; it is
  not implemented and no such claim is made.

Exit code is `0` on pass, `1` on any failure.

### The falsifier

`registry_tool.py tamper` deliberately corrupts a manifest — `tensor-hash`,
`aux-hash`, `header-hash`, `commitment`, `byte-len`, `offsets` — and
**asserts that the output differs from the input**, so the mutation cannot
quietly become a no-op and leave the gate green. `gates.sh` runs verify
against each corruption and requires exit code 1 from the *tool*, read
without a pipe in between (a `| tail` would answer with its own status and
report a passing gate for a crashed tool). Measured: all six refuse.

Two of the six are the interesting ones:

- **`byte-len`** edits a field in `core` and leaves `commitment` alone, so it
  fails at step 1 — the commitment binds the structural claims, not just the
  hashes.
- **`offsets`** shifts a tensor's byte range by 8 *and recomputes the
  commitment*, so the manifest is internally consistent and its `header_hash`
  is still correct. Only the step-3 re-derivation from the live header sees
  it. This is the tooth for a *dishonest producer* rather than a corrupted
  file.

## 9. Producing a manifest — the algorithm

For a second implementer, in full:

1. Resolve the reference to a commit sha: `GET
   https://huggingface.co/api/models/<repo>/revision/<ref>` → `.sha`. Use
   `/resolve/<sha>/<path>` for every subsequent fetch.
2. From `.siblings`, take the intersection with the aux allowlist (§6),
   restricted to top-level paths (no `/`). Fetch each whole; record path,
   length, digest; sort by path.
3. Determine the shard set: if `model.safetensors.index.json` exists, the
   shards are the sorted distinct values of its `weight_map`; otherwise the
   single top-level `model.safetensors`. Refuse a `weight_map` that names a
   non-top-level path.
4. For each shard: `Range: bytes=0-7` → little-endian u64 `N`;
   `Range: bytes=8-(8+N-1)` → the header JSON; `data_start = 8 + N`. Take the
   total file length from the `Content-Range` of a 1-byte ranged GET
   (`bytes 0-0/TOTAL`). Every tensor entry except `__metadata__` yields
   name/dtype/shape/`data_offsets`. Reject offsets that run past EOF.
5. Check the index's `weight_map` against the headers actually observed;
   record disagreements as notes. Reject duplicate tensor names across shards.
6. `structure-only` stops here (after re-fetching each header once more and
   confirming the digest is stable).
7. `full`: stream each shard from byte 0 to EOF. Feed **every** byte to the
   shard hasher; feed the sub-ranges to the per-tensor hashers. Assert at the
   end that the stream delivered exactly `byte_len` bytes and that each tensor
   hasher consumed exactly its `byte_len`. A resumed stream must resume at
   the exact byte offset it stopped at.
8. Integrity discipline, adopted from `phase0/e8m0_spread.py`: **every ranged
   response is length-checked** against the range requested (a server that
   ignores `Range` returns the whole file and would otherwise be hashed as if
   it were the slice), and after each shard is streamed, **one interior 4 KiB
   slice is re-fetched by range and compared** against the bytes the stream
   produced. A mismatch aborts the run rather than being recorded.
9. Assemble `core`, canonicalize (§3), hash under the domain tag, write.

## 10. Known limitations

- Single-producer. Independent re-derivation by a second implementation is
  the missing assurance, and the format exists to make it possible.
- No Merkle structure. The commitment is a hash of a flat manifest, so
  proving "tensor T is under commitment C" requires the whole manifest (a few
  MB). A Merkle tree over the sorted tensor list would give O(log n)
  inclusion proofs and is the obvious v2; it was not needed for v1 and
  guessing at the tree shape before there is a consumer would be the wrong
  order.
- No LoRA/delta support. Adapters as registry deltas against a committed base
  is a named next step, not implemented.
- No signature. A manifest is a claim by whoever ran the tool; anchoring it
  (signing, or posting the commitment somewhere append-only) is out of scope
  for v1 and is a deliberate choice, not an oversight.
- The producer cross-checks `prod(shape) * sizeof(dtype) == byte_len` and
  refuses a header that fails it. The *verifier* re-derives structure from the
  header bytes (§8 step 3) but does not re-run the dtype arithmetic, since a
  header that satisfies the re-derivation already agreed with the producer's
  view. Unknown dtypes skip the cross-check with a recorded note rather than
  a guessed element size.
- The structural re-derivation only covers **sampled** shards. A manifest that
  lies about the offsets in an unsampled shard survives until that shard is
  drawn; `--all-shards` is cheap (headers are tens of KB) and is what
  `gates.sh` uses.
