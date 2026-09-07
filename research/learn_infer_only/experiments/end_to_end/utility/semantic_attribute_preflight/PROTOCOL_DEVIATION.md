# The first run sampled despite the requested greedy configuration

[EXECUTED] `run.stderr` reports that Transformers replaced the requested
GenerationConfig values with model defaults: do_sample=True, temperature0.6,
top_p0.95. The intended settings recorded in `results.json`/`generation_config.json`
therefore do not describe the effective decoding mode. Preserve these original
files as evidence of the error; **do not cite the run as a greedy preflight**.

[SOURCE: installed implementation] `GenerationMixin._prepare_generation_config`
in the pinned Transformers4.57.3 `generation/utils.py`, lines1704–1801, gives
per-call kwargs precedence over non-global-default config values, then model
defaults. With use_model_defaults unspecified and the saved model version>=4.50,
it replaces config fields equal to global defaults, including an explicitly
constructed do_sample=False. The model's saved defaults enable sampling.
The subsequent generate dispatch at lines2378–2381 uses that merged mode.

[EXECUTED] `config_diagnostic.py` reproduces the merge without loading a model
or running inference: the original call yields `sample`; explicit
use_model_defaults=False yields `greedy_search`. Direct do_sample=False kwargs
also have the required precedence. Installed source SHA:
`a20024b1e82ed5361a524d238d2197be5407abc91297dd9888c57e8284d63fef`.
Exact diagnostic command/output and source are retained.

[EXECUTED] The deviating run did establish that the local cached3B model loads
and generates on MPSfloat16: all eight source inputs completed, none reaching
the32-token cap, with57.5335s full process wall and8,215,461,888B peak process
RSS. Seven responses contained prohibited markdown fences; only one passed
the frozen strict parser. Nulls and an incorrect factual bit also appear in
the complete raw outputs. No fence stripping, output repair or semantic prompt
change was applied. These outputs remain a failed/protocol-deviating preflight,
not evidence of held-out semantic utility.

[DERIVED: correction scope] A conforming implementation must disable model
default merging, pass do_sample=False explicitly, and capture/assert the
effective generation configuration returned during the actual generate call.
This corrects execution of the original contract; it does not justify trying
multiple semantic prompts, relaxing the parser, switching precision/backend,
or selecting teacher examples. Any corrected run must preserve all first-run
artifacts, use the same frozen rendered strings/token IDs and keep both physical
run counts visible. No held-out inputs or utility history are authorized here.

[DERIVED: role note] The integrity verifier hashes all frozen source files,
including oracle bytes, before inference. Oracle JSON is decoded only after all
model responses for scoring. No oracle fields enter rendered prompts or model
inputs. This is a local code/data-flow distinction, not OS isolation between
an issuer and an oracle.
