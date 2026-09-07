# Complete utility workload through the verifying reader

[EXECUTED, 2026-09-07] `utility_001/report.json` passes both complete previously
selected public histories through actual BFV, the repaired public journal and
the independent verifying reader: all 384 Learn, 96 Infer and 256 exact-original
expiries. All 96 released integers equal the frozen reference, including 16
known-empty outputs and 80 outputs using nonempty encrypted state. A separate
validator directly sums the retained plaintext contributions at every query;
all 96 independent integer reconstructions also equal both actual outputs and
the recorded oracle. There were exactly 96 verifier decryptions and zero
baseline-reader decryptions. No example was selected anew, and no model was
run, trained or downloaded.

[EXECUTED utility] The exact original denominator and failures are retained:

| Subset | Correct | Total |
|---|---:|---:|
| All checkpoints | 52 | 96 |
| Nonempty encrypted state | 44 | 80 |
| Final checkpoint | 18 | 32 |

These are descriptive results for this fixed subset, not a new utility estimate
or confidence interval. The learner classifies synthetic categories from fixed
model features using a routed window; it does not finetune the language model.
`utility/README.md` retains the complete task and original study denominators.

[SOURCE] Before this run, the repaired baseline
`journal/results/utility_002/report.json` recorded all 480 commands and 96 exact
integer comparisons. The separate `journal/results/live_text_002/report.json`
recorded one new text's issuer encoding and one Learn/two Infer operations.
This driver does not rerun that text or use it to enlarge the held-out sample.
Their exact report hashes, materialized fixture hashes and source/binary hashes
are pinned in this run's `fixture_pins.json` and `source_pins.json`.

[DERIVED protocol] Setup uses fresh OS randomness and the existing real-BFV CLI.
The initial baseline receiver started by the shared Run helper is stopped before
any workload command. A distinct verifying-reader database and CAS take over
the authority's delivery socket. The command authorizer registers each query
ticket there. Learn finalizes and is independently replayed. Infer's first
publication remains pending until its envelope is independently replayed; an
exact authority retry then releases through the verifying reader. No baseline
decryption is used. Fresh inputs, public queries and the initial zero are the
only blobs uploaded to the verifier, which computes each result itself.

[EXECUTED] Each history ended at verified revision 240 with exactly the same
ordered signed journal and encrypted state as the authority. Each route held 32
inputs; admissions were 128 on the reversed route and 64 on the retained route.
All 48 normal Infer publications per history initially waited for verification,
then the exact stored receipt was acknowledged after sync. No extra admitted
transition or second decryption was introduced by that retry.

[EXECUTED costs] The complete run took 682.666087417 seconds (11.38 minutes) on
the shared machine. Per-history median complete Learn times were 1.469 and
1.497 seconds; median complete Infer times were 1.375 and 1.464 seconds. These
include role processes, inspection, authorization, ciphertext computation,
journal installation, verification and delivery. They exclude fresh model
encoding because this run uses the existing frozen feature fixture. The
unoptimized host subprocesses repeatedly inspect the current state; this
overhead is included. The reports separately price every crypto subprocess and
retain all actual command timings.

[EXECUTED storage] Each final learner references 66 ciphertexts, totaling
5,616,798 bytes, and a 7,601-byte public state manifest. The verifier retains
423 CAS files totaling 34,663,205 bytes per history, including public queries and
historical objects. Live window storage is bounded by capacity; retained history
grows with operation count. The validator additionally records authority and
reader database/WAL/SHM sizes after services stop. Instrumented driver
`put`/`sync`/`verified_status` calls per history sent 22,658,676 bytes and received
69,776 bytes; these are not the total traffic of the separate ticket-registration
and authority-publication RPC paths.

[DERIVED data boundary] Only the issuer and test oracle receive the copied
plaintext fixture. Public host/authority processes receive ciphertexts, public
queries and signed command metadata. The trusted verifier retains the full BFV
secret; this is benchmark R, with no master-key-absence or OS-isolation claim.
The fixture was already public, so this is known-state utility integration,
not fresh-private-ingress confidentiality evidence. Issuer provenance, command
policy and reader persistence remain trusted. Ed25519 authentication is
classical; the composition has no end-to-end post-quantum claim.

From the repository root, with the already-built crypto CLI and materialized
frozen inputs, one command executes the complete normal workload:

```sh
python3 research/learn_infer_only/experiments/end_to_end/verified_reader/utility_driver.py
```

Choose unused `--runtime` and `--reports` paths for another execution. Runtime
must remain under the ignored `verified_reader/runtime/` directory to preserve
the intended artifact discipline. Ciphertext bytes and timing vary with fresh
randomness and machine load. No adversarial-control code is imported or run.

The independent integer replay and final artifact audit are reproducible with:

```sh
python3 research/learn_infer_only/experiments/end_to_end/verified_reader/reports/validate_utility.py --run utility_001
```

[EXECUTED provenance] Both commands exited zero on their first complete run.
The driver freezes six normal journal modules, the service and its own source
under the runtime import tree, along with a pinned crypto binary copy. All 384
issuer vectors, 16 public queries and the oracle/index were checked against the
existing materialization manifest before use. The validator checked all source,
binary and fixture pins, all 96 direct integer references, all reader-output
omissions and eight full secret files in raw/hex/base64 encodings against the
expanded public artifacts, including both BFV inner secret payloads. Ignored
runtime was confirmed. This is an artifact audit, not an information-flow proof.

- Driver SHA256: `f623dbf5d903c6a6ced87cfb5735dd1bda47f861665f8d88670184f6dc463847`
- Service SHA256: `f0e79c2a33baa32e2867d467735dafd29b26c480deb1f688289e7468bd2de01b`
- Final report SHA256: `81b240027a7a698e39a48d29fb5813a61838552111e652ff8a1c156afae4c0da`
- Independent validation SHA256: `7f71b51f065f8a4188d7ef1db9daf1476086ab49acf60c3bd2ef0fa41d6d9a19`

`utility_001/manifest.json` pins every retained run artifact. No service, journal
helper, shared ledger, companion tree or previously frozen test artifact was
edited in this integration task.
