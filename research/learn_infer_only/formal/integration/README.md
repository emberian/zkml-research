# Combined proposal patch

[DERIVED: artifact scope] `minidregg-combined-resident.patch` combines the finished
proposed modules selected by the most recent integration manifest and their four
umbrella additions. `../../experiments/integration/modules.json` selects the
twelve-module, 217-pin baseline; `modules_with_ema.json` selects sixteen modules
and 265 pins. The baseline is preserved separately in
`minidregg-combined-resident-217.patch`; the passed EMA extension is preserved as
`minidregg-combined-resident-265.patch`. Both runs passed; their summary is
`../../experiments/integration/REPORT.md`.

[EXECUTED] The current combined proposal is the passed 371-pin, 27-module batch,
also preserved as `minidregg-combined-resident-371.patch`. It adds the generic
contextual EMA proof, distributional budget, simplifier and exact BFV source
certificate modules. The intermediate 307-pin pass is preserved separately.
All passed sets, hashes, exact commands, and the two corrected census-only
failures are summarized in the same report.
It is generated against the **current companion file bytes**, including any
pre-existing dirty changes, rather than assuming that HEAD describes those bytes.
It leaves the independently reviewed lane patches unchanged.

[EXECUTED] Applicability, actual application in a separate source copy, exact
patched-content comparison, import-boundary checks, and sequential Lean overlay
builds are recorded by
`../../experiments/integration/results/latest.json`. That pointer identifies the
precise numbered report; every run retains its own copy of the combined patch and
hash. Read the report's status before treating the generated patch as checked.

[OPEN] Maintainer application to the companion and a clean dependency rebuild are
outside this research run. The tool writes only inside the research integration
directories. The proof statements retain their original assumptions and scope;
integration does not upgrade receipt binding into confidentiality or an engine
model into a runtime implementation theorem.
