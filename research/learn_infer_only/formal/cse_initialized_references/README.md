# Initialized references through CSE

[DERIVED] `Compiler/CseInitializedReferences.lean` proves that the existing CSE pass
preserves the existing `EmittedScheduleExecution.ForwardValid` predicate for every
F2 descriptor satisfying it. It then proves `ForwardValid` for every emitted F2 source
term list, including the exact frozen Learn and Infer descriptors. The corresponding
`validCheck ... = true` results are now kernel theorems. No concrete CSE expression is
normalized, no compiled verdict is imported as proof, and no predecessor file changes.

[SOURCE / DERIVED] `Compiler/AirFlatten.lean:449` already provides `flatten_covers`:
every allocated auxiliary index has a producer. This package reuses that theorem,
lifts it through `flattenSystem` and the existing emitted wire layout, and combines
producer coverage with the existing SSA/order and allocation theorems. It does not
re-prove coverage by recursing over source terms. `shape_refs_valid` requires an
explicit `AllRefs` premise in addition to SSA and allocation bounds; it never assumes
the false implication from SSA plus bounds to initialization.

[DERIVED] The CSE induction carries four facts: future output keys are not yet
substituted; every previously available wire maps to a retained wire or original
input; signature-table hits name kept gates; and kept gate operands have initialized
support. A hit maps the current output to an existing kept output. A miss keeps the
rewritten gate and preserves the availability of the old operands. The already proved
`CseStructure` theorem supplies final ordering and bounds. Final roots transfer through
the same substitution; ordering then places each operand's producer before its reader.

[DERIVED] `learn_valid_kernel` and `infer_valid_kernel` apply this structural proof to
the frozen `learnSchedule` and `inferSchedule`, closing the initialized-reference
residual of the preceding package. These are statements about the Lean descriptors
used by the existing emitter; their connection to the saved JSON bytes remains the
predecessor's executed emission/byte-reproduction evidence.

[DERIVED storage model] `inputStore` maps the input prefix to `Some` input values and
all other indices to `None`. `prefixStore` folds `Function.update` over the existing
gate records, writing `Some` arbitrary payload at each `gate.out`. `readOption` returns
`Some` for constants or reads a wire's option. No XOR, AND, gate evaluator, circuit or learner
arithmetic is implemented. This is a model of which locations contain values, independent
of what gate values mean.

[DERIVED quantified lookup guarantee] `LookupSuccess` quantifies over every value type,
input assignment, gate-payload assignment and constant assignment. For every decomposition
of the descriptor's gate list at a gate, both operand reads after the preceding writes
return `Some`; every final output read also returns `Some`. `valid_lookup_success`
derives this from `ForwardValid`, rather than assuming lookup success. The actual Learn
and Infer lookup theorems have no initialization premise. Allocation bounds remain the
separate inherited `WellFormed` result; the functional store itself is not a Rust vector.

[DERIVED nonvacuity and falsifier] `raw_forward_valid` inhabits the premise for every
source list, and the actual learner descriptors instantiate the final conclusions.
The hole descriptor has no inputs, allocates two slots, and writes output wire one
after reading wire zero. It has SSA and allocation bounds but lacks a producer for
wire zero. The file proves that it fails `ForwardValid`, returns `None` at that operand
under the storage model, and does not satisfy `LookupSuccess`. This is a direct
counterexample to dropping initialized-reference coverage.

[OPEN runtime TCB] No Rust-language refinement is claimed. Mapping the typed Lean
descriptor to JSON and back through serde, schema tags, operation dimensions, resource
caps, `usize` representation, `Vec<Option<_>>` allocation/indexing/borrowing/cloning,
compiled Lean/Rust, backend completion and TFHE values remain outside this proof.
The arbitrary-payload model assumes each modeled write occurs; it proves no backend
termination, value correctness, noise bound, ciphertext serialization property, replay
determinism, learning utility or privacy property. Existing value semantics remain in
the previous theorem package. No crypto or finite fixture replay is run here.

[EXECUTED isolation] The four frozen proposal dependencies are freshly compiled into
an owned olean overlay against cached companion/Mathlib dependencies. Exact commands,
source hashes and outputs are in `results/environment.json`; failed single-file
iterations are retained. `results/verification.json` records the final pin census,
source/patch equality, isolated patch application, import-boundary checks and unchanged
predecessor hashes. Root owns independent review and the full umbrella build.

[EXECUTED final check] All 29 theorem declarations have exact axiom pins and pass in
`results/lean_006.json` with empty stdout/stderr. Dependencies are drawn only from
`propext`, `Classical.choice` and `Quot.sound`. Patch application and import checks pass;
all 96 frozen predecessor files and companion HEAD/status are unchanged. Source SHA-256:
`1e8037c2c4ce35727a804912560b13a89a673682a8ca7405f2d1d4504d884386`.
Patch SHA-256: `39afffcab611adc4a3a292bd3935ea551ae5f22e264660c9d2c0523256c74c6c`.

[DERIVED integration] Apply after `PrivateAddressEma`, `PrivateAddressEmaSchedule`,
`EmittedScheduleExecution` and `CseStructure`. `integration_entry.json` names the module
and pin count. The new proof supplies the initialized-reference premise previously
supported only by compiled checks, while preserving all frozen long-run artifacts.
