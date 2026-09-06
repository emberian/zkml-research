# Source phase core and interrupted successor

[EXECUTED] Theory/BfvPhaseAlgebra.lean (27 pins) and Assurance/ResidentBfvSourcePhase.lean (18 pins) are packaged in minidregg-bfv-source-phase.patch and pass the final 651-pin combined check. They derive the source encoding/phase equations and selected packed coefficient in a mathematical negacyclic ring, with nonzero witnesses and falsifiers. This is not Rust/compiler/NTT refinement or a secrecy theorem.

[OPEN] Theory/BfvNoiseSource.lean has a matching successful elaboration but no pinned inventory or proposed patch. Assurance/ResidentBfvSourceWindow.lean fails its last recorded check. These two interrupted successors are intentionally excluded from the 45-pin patch and final combined proposal. Exact failed/source-matching records are in experiments/he_closure_costs/source_phase/. Do not fold this entire directory as though every module passed.
