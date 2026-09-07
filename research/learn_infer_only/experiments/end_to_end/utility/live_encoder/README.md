# Live trusted-issuer text encoding matches the four frozen examples

[EXECUTED] The original `../issuer_encode_prepared.py` now runs on the four
authorized records0,64,256,320. **All2,308 signed integer coordinates match the
original cache exactly.** Both teacher examples and both held-out query examples
pass; no precision/batch mismatch required a replacement or altered numerical
setting. The original384-Learn/96-query E2E fixture remains unchanged.

[EXECUTED] `run_fixed.py` launches four actual model processes through
`/usr/bin/time -l`. `results/run_001/report.json`, individual stdout/stderr and
`run_fixed.log` retain commands, exits, timing, peak RSS and source/vector hashes.
`audit.py` independently reconstructs normalization and all four quantized vectors
from the original cached features; it does not reuse the exported encoder policy
to compute its reference. Its2,308 agreements and mode0600 checks pass.

## Exact numerical and role boundary

[SOURCE + EXECUTED] This uses the cached SmolLM2-135M revision
`93efa2f097d58c2a74874c7e644dbc9b0cee75a2`. Every execution checks all original
model/tokenizer/config file hashes, uses local-files-only loading with remote code
disabled, and performs an actual forward pass. There are no downloads, dependency
installs or backbone updates.

[SOURCE + EXECUTED] Settings are CPU float32/eager attention, eval/inference mode,
two torch threads, one interop thread, seed7901 and one prompt per process. All30
blocks execute; the representation pools the direct block9 output over real tokens.
The existing teacher-only per-route center/scale and bias1 are applied in float64,
then nearest-even rounding of127 times the feature is clipped to[-127,127].
Multiplier+1 yields the teacher's signed contribution or the public query vector.
Runtime versions are pinned in `runtime.json`: Python3.14.7, torch2.10.0,
transformers4.57.3 and NumPy2.4.2 on macOS arm64.

[DERIVED scope] Equality here means exact **quantized vectors for four specified
texts**, not identical hidden floating-point activations or equivalence for every
text/batch. The earlier filename and docstring said “prepared”; its source is
preserved to retain the original hash. This later execution evidence applies to
those exact bytes and the four fixed cases.

[EXECUTED] Raw plaintext inputs and vectors are confined to ignored
`../issuer_oracle/live_encoder/run_001/`, mode0600 within a mode0700 directory.
Their command paths identify issuer data, but the host and authority never receive
those files. Logs here contain aggregate encoder/timing data and source record IDs,
not source text, token IDs, labels or vectors. This is data-flow segregation on a
shared research machine, not OS isolation. The examples were already public
synthetic research data; this is not a new confidentiality experiment.

## Cost measured at the actual command boundary

| Record / role | Whole command wall | User+system CPU | Model/tokenizer load | Feature forward | Peak RSS bytes |
|---|---:|---:|---:|---:|---:|
| 0 / teacher, route0 | 11.500s | 5.05s | 0.563s | 0.206s | 1,420,083,200 |
| 64 / teacher, route1 | 8.721s | 4.89s | 0.652s | 0.192s | 1,419,952,128 |
| 256 / query, route0 | 8.241s | 5.00s | 0.563s | 0.177s | 1,420,492,800 |
| 320 / query, route1 | 9.274s | 4.98s | 0.519s | 0.198s | 1,420,214,272 |

[EXECUTED + DERIVED] Whole-command wall time includes process/interpreter and
framework startup, source checks, loading, feature computation and exit; it is
the measured8.24–11.50s, not just the0.18–0.21s forward. `time -l` gives whole-child
CPU/RSS; the load/forward subdivisions come from the encoder. These are four
individual local observations on a shared machine, not a latency distribution or
benchmark confidence interval. No warmed persistent-issuer speedup is claimed.
RSS includes Python/framework/model/temporary allocations and is not resident
window memory. This cost belongs to the already-entitled issuer or public-query
encoder, in addition to the cryptographic/journal costs elsewhere.

## A live issuer command for a new text

[EXECUTED component; integration retry pending] `issue_text.py` composes the tested
live encoder with the existing `journal/roles.py issue` command. It accepts
issuer-only `{text,route,label}`, writes a private vector, then uses the configured
public key for OS-random encryption and the issuer signing credential for the
ordinary Learn authorization. The first journal invocation (`live_text_001`)
completed encoding, then failed because its issuer subprocess used the model
environment, which lacks `cryptography`. The repaired wrapper keeps that environment
for the encoder and uses its caller’s `sys.executable` for the journal issuer.
Launch the wrapper with system `python3`, whose `cryptography` import was checked.
The integration owner is rerunning the full path. No dependency was installed;
`interpreter_repair.json` pins the failure evidence and source change. The wrapper
does not submit or finalize the host proposal by itself.

From the repository root, with an independently created journal demonstration
and its current head JSON (preserve the frozen384/96 fixture):

```sh
python3 -B \
  research/learn_infer_only/experiments/end_to_end/utility/live_encoder/issue_text.py \
  --input PRIVATE_TEXT_JSON \
  --issuer-config JOURNAL_DEMO/.private/issuer/config.json \
  --head CURRENT_HEAD_JSON \
  --private-workdir NEW_PRIVATE_ISSUER_WORKDIR \
  --out NEW_ISSUED_CIPHERTEXT_DIRECTORY \
  --request-id live-text-001 --nonce live-text-nonce-001 \
  --record-id opaque-live-observation-001
```

[DERIVED API] `PRIVATE_TEXT_JSON` has exactly string`text`, integer`route`0/1 and
integer`label`−1/+1. A staged new synthetic example is ignored at
`../issuer_oracle/live_encoder/future_new_text.json`; it has not been encoded or
used as utility evidence. Omit `--expect-record-id` for new text. The wrapper
derives the public route from the private input, verifies tested encoder/policy
hashes and keeps raw encoder/issuer logs in the private work directory. It emits
only aggregate status and the existing ciphertext/authorization result to stdout.

[DERIVED integration] The journal coordinator imports `fresh.ct` into its public
CAS, uploads it, invokes `roles.py propose` with only host config/current head/
authorization/CAS, uploads the resulting ciphertext and submits the proposal.
The authority then performs its unchanged verification, durable installation and
finalization. `FRONTEND_INTEGRATION.md` shows the simpler equivalent composition
with the existing `Run.prepare`/`Run.accepted` interface. A subsequent authorized
query follows the ordinary finalized reader path; oracle comparison remains in
the test-oracle role. Source text/vector is never a host proposal input.

[DERIVED trust] The journal's existing feature policy is a trusted issuer's
signed577-coordinate/range assertion. Neither this wrapper nor its signature
proves hidden features originated from this model. The trusted issuer can still
issue other valid vectors, and the reader still retains a full BFV key. This
frontend adds live source encoding, not master-read absence or an authenticated
proof of encrypted model execution.

## Reproduction

[EXECUTED] Run from the repository root:

```sh
python3 -B research/learn_infer_only/experiments/end_to_end/utility/live_encoder/run_fixed.py
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -B research/learn_infer_only/experiments/end_to_end/utility/live_encoder/audit.py
```

[EXECUTED] The run and independent audit exit0. Each repetition creates a new
result/private-input directory; the frozen audit currently selects run001.
`manifest.json` pins the sources, exact results and original model inventory.
Model runs4; backbone updates0; downloads0; new dependencies0; searches0.
