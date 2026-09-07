# Source and provenance scope

[SOURCE: selected implementation] `../semantic_axis_selection/manifest.json`
pins the full teacher-selection run. `prepare.py` asserts that the new scorer
is the selected scorer's exact source with only four output-metadata edits:
teacher/new-test naming, one framing, 128 held-out texts, and oracle-parsed
wording. The model-forward, padding, positions, precision, likelihood and
tie-handling code are unchanged. The selected framing and semantic definitions
are loaded from the original `prompts.json`, not rewritten in this directory.
New rendered prompt strings and token IDs are frozen before scoring.

[SOURCE: official model and runtime documentation, previously inspected]
[SmolLM3-3B official card](https://huggingface.co/HuggingFaceTB/SmolLM3-3B)
documents the instruction model and no-thinking interface. Its exact scope
and the [PyTorch 2.10 MPS documentation](https://docs.pytorch.org/docs/2.10/notes/mps.html)
were recorded in `../semantic_attribute_preflight/SOURCES.md`. The local model
snapshot and installed implementation hashes are verified here. No official
benchmark result is borrowed as a result on our task, and no model was downloaded.

[SOURCE: frozen original baseline] `../encoder_policy.json` fixes the SmolLM2
mean10 representation, public teacher centers/scales, bias and integer rounding.
`../encoder_feasibility.json` pins the locally cached model files. The new
baseline extractor executes the same CPU float32/eager, batch16, masked mean
of the direct block9 output used in the earlier surface tests. Original
teacher/selection hidden features are reused; only fresh test texts are encoded.
The public teacher coordinates are checked against the frozen original-feature
arrays retained by the E5 study. No earlier test outcomes tune this baseline.

[SOURCE: existing feature/control algorithms] The original
`../../../adaptation_utility/text_transfer_data.py` defines balanced rules,
history permutations and gold category labels, and its `features` function
sets attribute coordinate `4*skill+2*a+b`. The executed E5 utility control
`../e5_successor/run.py` uses exactly value 127 at that coordinate, padded577.
This experiment substitutes inferred bits in that existing map; it introduces
no new feature selection. Update and query algorithms use integer W32
add/expire and sign(score), as in that earlier routed window control.

[EXECUTED: source/search accounting] The only discovery operation in this
tranche is the local numeric history-seed search recorded in
`seed_inventory.json`. No web, Scry or Kagi query, new dependency, model download,
training run or cryptographic benchmark is performed. All stimuli are public
synthetic text, not private user logs.

[DERIVED: provenance wording correction] Hash verification reads file bytes,
including oracle/record files. Therefore the frozen teacher-selection field
`oracle_opened_by_scoring_process=false` and its report phrase saying the
oracle file was first opened by the evaluator were too literal. The accurate
claim is that oracle values are not parsed by the scoring process or supplied
to the model; their file hashes are checked. The new field is
`oracle_parsed_by_scoring_process=false`. Both old preflight outputs and the
teacher-selection bytes remain preserved; no score or decision is changed.
