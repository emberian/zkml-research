# Public BFV arithmetic and an explicit full-key reader

[EXECUTED] The crypto role tranche passes 1,638 CLI invocations plus its secret
file regression test. This directory implements the
crypto roles for `../CONTRACT.md`. The journal lane owns routing, capacity,
sequence, parent/genesis binding, admission, finalization and delivery.

Build from this directory with `cargo build --offline --locked --release`.
The executable is `target/release/resident-crypto`; every command writes one
JSON result to stdout, or a JSON error to stderr and exits 2. Files are written
without replacing different existing bytes. The underlying library is the
read-only `/Users/ember/dev/breadstuffs/vendor/fhe-dregg`.

| Command | Arguments | Role and result |
| --- | --- | --- |
| `params` | none | Fixed parameter/program identities and compiled source hash. |
| `keygen` | `--pk PK --sk SK --zero ZERO` | Initializer; creates real serialized keys and canonical public full group-zero. |
| `issuer-private-vector` | `--out PRIVATE.json` | Issuer; creates 577 fresh OS-random synthetic signed coefficients, mode 0600; stdout omits values. |
| `issuer-encrypt` | `--pk PK --vector PRIVATE.json --out FRESH.ct` | Issuer; real public-key encryption, no secret key. |
| `encode-query` | `--vector PUBLIC.json --out QUERY.json` | Public encoder; fixed canonical query format. |
| `inspect` | `--ct CT` | Public strict validation, canonical whole-envelope SHA256 and byte counts. |
| `normalize` | `--ct CT --out NORMAL.ct` | Explicit precommit seeded/full normalization; never normalize after committing a hash. |
| `host-learn` | `--acc ACC --fresh FRESH [--old OLD] --out NEXT` | Public deterministic `ACC + FRESH - OLD`. Authority chooses the exact original expiry from its queue. |
| `host-infer` | `--acc ACC --query QUERY --out OUTPUT` | Public two ciphertext/plaintext products and subtraction. |
| `reader-decrypt` | `--sk SK --ct OUTPUT` | Benchmark R trusted reader; returns coefficient 576, centered score and sign. Finalized-envelope gate is external. |
| `oracle-issuer-encrypt` | issuer arguments plus `--seed BYTE` | Public deterministic ChaCha20 reproduction only. |
| `oracle-decrypt-polynomial` | `--sk SK --ct CT` | Explicit test-only full polynomial output. |

[DERIVED scope] The host commands accept no secret-key or private-vector
argument. This is process/data-flow separation on one research machine, not
isolation from that machine's operator. Ordinary keygen/encryption use
`rand::rng()`, an OS-seeded `ThreadRng`; this does not mean an OS syscall per
ciphertext. They reject deterministic seed arguments. Oracle commands have
separate names. The library's `SecretKey::encrypt_poly` also draws its uniform
polynomial seed from an internal `rand::rng()` (`keys/secret_key.rs:111`), so
passing a deterministic caller RNG to key generation would not make the key
pair byte-reproducible. There is deliberately no `oracle-keygen` command.
**The same public caller seed still regenerates the full secret key.** The
separate `rng-audit` executable checked identical raw 4099-byte secret payloads,
different public-key bytes, and successful cross-decryption with the regenerated
secret. `rng_audit.json` exposes no key bytes. This preserves the historical
public-seed privacy warning while correcting byte-reproducibility claims.
`oracle-issuer-encrypt` is deterministic only given an existing pinned public
key, its explicit seed and known input; it must not be used for private ingress.
A single retained full reader key is benchmark R, not the
handoff's distributed tier C or its no-master-read target.

Input vectors are JSON arrays of exactly 577 integers in [-127,127]. Booleans,
floats, overflow, extra entries and out-of-range values are rejected. Query
files are compact canonical JSON with exactly `schema`, `params_id`, and
`coefficients` fields; use `encode-query` before hashing/admission. Its schema
is `resident-public-query-v1`. These ranges alone do not make arbitrary public
queries privacy-safe, and ciphertext inspection does not prove hidden input
range, model provenance, noise validity, randomness or correct key ownership.

The binary object envelope is `RSBFV001` (8 bytes), kind (1 byte: ciphertext=1,
public key=2, secret key=3), parameter identity (32 bytes), declared key identity
(32 bytes), payload length (8 bytes, little endian), then the library payload.
Kinds, fixed parameter identity, exact length and a 200,000-byte read cap are
checked before library decode. Every accepted ciphertext has two NTT components,
degree 4096 and level 0; each serialized polynomial roundtrips exactly, which
also rejects the library decoder's short-degree padding behavior. Canonical
ciphertexts use full components, no seed metadata and public variable-time
flags. Unknown/trailing/noncanonical encodings fail strict inspection.

The key identity is SHA256 of the canonical public-key payload. It is declared
metadata inside ciphertext envelopes, not a proof of ciphertext/key relation.
Authority and reader configuration must compare it with their expected identity.
The public zero is computed as a fresh encryption minus that same ciphertext;
it is a nonempty full group-zero, not the library's unserializable empty sentinel.
No initial noise survives that exact subtraction. All commitments hash the whole
envelope, including kind, parameters and key identity.

The fixed arithmetic is W32 per route, two routes, 577 signed coordinates,
N4096, t4294828033, Q=2199023190017*4398046486529, variance10. Query coefficients
are reversed and split by sign. Coefficient576 is the exact dot product; the
declared absolute score bound is 297805856 < floor(t/2). Reader bounds checks
are diagnostics under that domain, not a proof of honest hidden input/noise.

`process_work_ns` includes parameter setup, parsing/loading, arithmetic,
serialization and file sync within the command. Separately returned arithmetic
nanoseconds are not end-to-end journal timings. The 81-byte envelope increases
the prior 85022-byte ciphertext payload to 85103 bytes; neither number includes
the authority's retained journal, signatures, queue metadata or allocator/RSS.

## Executed evidence

[EXECUTED] `test_cli.py` reuses the unchanged fixture SHA256
`41978a10b974a3e8b7f30d5f9c66f7d396fdf7df83b723b3f14dc00359cdb4c0`.
Histories 63000/63001 retain W32, 577 coordinates and all original scores:
384 Learn encryptions, 256 exact-original expiries, and 96 signed-score checks
(80 encrypted-state readouts and 16 known-empty-state readouts). Every Learn
and Infer is recomputed in another keyless process and its complete output
blob matches byte-for-byte. Empty states now use a full public group-zero;
those 16 known answers remain explicitly distinct from private-state evidence.
No model was executed or downloaded.

[EXECUTED] A separate synthetic unknown-ingress smoke creates 40 fresh bounded
OS-random contributions in ignored issuer files, executes 8 expiries and compares
two selected scores privately. The host's recorded successful command arguments
and file inputs contain only public ciphertext/query paths. Private vectors,
state and scalar comparison results are omitted from committed logs. The report
publishes only success/count information for those comparisons. This adds no
utility estimate or isolation from the shared machine's operator.

[EXECUTED] OS-random encryption of the same input produces different ciphertexts.
The oracle issuer reproduces identical bytes with an existing public key, fixed
seed and **public known** input; private ingress never uses published coins.
The CLI rejects secret arguments on host commands, seed arguments on ordinary
issuer commands, malformed numerical vectors, publicly readable existing secret
outputs and secret-path symlinks. The direct Rust `save()` unit test additionally
checks successful exact retry on a private regular file. The independent critic's
broader malformed-codec review is tracked separately in the adversarial lane.

[EXECUTED] `test_results.json` retains all 1,638 commands, exits, results, process
latencies and role-path checks. The final `test_03.log` is green. Earlier
`test_01.log` preserves a test-harness mistake that applied the successful-host
argument rule to an intentional refusal; `test_02.log` preserves the failed
oracle-keygen byte-repetition premise that exposed the internal RNG distinction.
These did not change the declared histories, queries or numeric acceptance rule.

[EXECUTED] On the shared Apple M2 Max, this single CLI run had median/p95 wall
times including process launch and all command work:

| Role command | Successful samples | Median ms | p95 ms |
| --- | ---: | ---: | ---: |
| keygen | 3 | 47.419458 | 140.978833 |
| issuer-encrypt | 425 | 30.938375 | 50.648167 |
| host-learn | 848 | 33.600479 | 55.353250 |
| host-infer | 194 | 33.154146 | 65.318542 |
| reader-decrypt | 98 | 25.643938 | 45.990334 |

The host samples include independent recomputation calls. These are local
measurements under concurrent research load, not end-to-end journal timings or
confidence intervals. Wrapped credentials in this run were 42,628 bytes for
each public key and 4,180 bytes for each full secret key. The stable logical
two-route ciphertext set is at most 66 blobs = 5,616,798 bytes, before the public
key, parameters, transport, history, verification and delivery records. The test
harness intentionally retains earlier outputs and recomputation copies in its
ignored run directory, so this logical-set figure is not its total disk usage.

To reproduce the complete crypto checks from this directory:

```sh
cargo build --offline --locked --release
cargo test --offline --locked --release
python3 test_cli.py
cargo run --offline --locked --release --bin rng-audit
```

The production source is SHA256
`22f0cbe304772263094c228f6598eb4cbfa00432902ba9e5de0993f6735e1b7c`.
`params.json` pins its compiled identity, full fixed parameter description and
program-description digest. The latter is a semantic-version identifier, not
an attestation of an untrusted executable; authority configuration must use its
reviewed implementation. `artifact_hashes.json` and `validation.json` record
source/dependency hashes and measured counts. Files under `runs/` are ignored;
they include real retained test keys and unknown private inputs.

[OPEN] The cryptographic CLI does not authenticate an issuer, enforce routing or
capacity, authorize a query, bind a parent/genesis, sign a receipt, enforce
finality, deduplicate delivery or prevent authority rollback. Those are the
separate journal integration's obligations under the same contract. This
tranche asserts no post-quantum security bit level, no restricted cryptographic
release and no absence of a surviving full-read credential.
