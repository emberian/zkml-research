# EMA from an emitted Boolean schedule

[EXECUTED checked proposal] The source is
[`Compiler/PrivateAddressEmaSchedule.lean`](Compiler/PrivateAddressEmaSchedule.lean),
with 46 theorems and 46 exact axiom pins. The checked patch is
[`minidregg-private-address-ema-schedule.patch`](minidregg-private-address-ema-schedule.patch).
It instantiates the existing
`Compiler.Signature.Term` with `AirSig (ZMod 2)`; XOR is addition, AND is
multiplication. NOT and MUX are source combinators with proved Boolean meanings.
`AirFlatten.flatten`, `emit`, and `EmitShare.cse` author the gate list. No
hand-authored gate schedule or new flattening/CSE algorithm is introduced.

[EXECUTED emitted artifacts] `EmitPrivateAddressEma.lean` writes the exact
[`artifacts/learn.json`](artifacts/learn.json) and
[`artifacts/infer.json`](artifacts/infer.json) using the existing compiler.
The first emission, retained in `results/emission_001.json`, has 538 Learn
XOR/AND gates, 42 inputs, 32 outputs, and an allocated wire bound of 11,562;
Infer has nine gates, 34 inputs, one output and wire bound 46. The sharing pass
keeps the original numbering and removes repeated gates, so holes are expected.
These are top-level circuit operation counts, not measured TFHE bootstrap counts.
The [schema](SCHEMA.md) is frozen and shared with the independent runtime lane.

[EXECUTED frozen bytes] Learn SHA256:
`94e8369ffc8fcdf57b8351b278d5af90dc49a26d83600d40f0bd6a0da359dde8`;
Infer SHA256:
`b742ed7710d2680119eceeff0c553d675e1ce187a503981fc500a6a4a683b80c`.
The independent runtime lane has begun using these bytes. Later reproduction
must emit in another directory and compare; these files are not overwritten.

[DERIVED proof spine] `shared_output_correctness` is universal over every
source-expression list and every input assignment. Any valuation satisfying
the shared gates and pinning the input wires has exactly the source-expression
outputs. `shared_premises_inhabited` constructs an accepting gate valuation for
every such source and input, through the existing `fillAux` evaluator and CSE
forward theorem. This is not an assumption that arbitrary expressions are zero:
the existing descriptor's `zeros` list supplies expression-root references,
which this schedule interface deliberately interprets as freely valued outputs.
The theorem proves those root values and never imposes the zero checks.

[SOURCE inspected theorem spine] All paths below are in the read-only
`/Users/ember/dev/minidregg` tree, whose source hashes are retained in
`results/verification.json`: `Compiler/Signature.lean:165` (`fold_unique`);
`Compiler/AirFlatten.lean:145` (`flatten`, explicitly a fold) and `:197`
(`flatten_forces`); `Compiler/Emit.lean:187` (`emit`);
`Compiler/EmitShare.lean:136` (`cse`), `:421` (`cse_holds`), `:447`
(`holds_of_cse_holds`) and `:552` (`emit_ssa`);
`Compiler/DescriptorEval.lean:191` (`fillAux_gates_hold`) and `:212`
(`fillAux_getD_of_lt`). These are imported proof bodies, not abstract-only
claims or a citation to an uninspected interface.

[DERIVED application spine] The source ripple terms instantiate the frozen
`RippleTrace`; `ripple_bitvec` gives word addition. The sign-extension,
complement, concatenation and extraction source terms prove exactly the
`candidate` word equation. `learnE_value` and `inferE_eval` compose address
selection and sign inference. The concrete wire-layout theorems use all 42
Learn or 34 Infer input positions and end at the original four-byte `learn`
and `infer` definitions. The mathematical floor and untouched-register
conclusions are the first package's universal theorems, not fixture comparisons.

[EXECUTED final validation] `python3 .../emitted_schedule/check.py` produced
[`results/lean_009.json`](results/lean_009.json): exit zero, unchanged source
hash before/after, no stdout or stderr, all 46 exact guards accepted.
`python3 .../emitted_schedule/package.py` produced
[`results/verification.json`](results/verification.json): theorem/pin census,
fresh source-only patch application/content comparison and both import-boundary
checks pass. It re-executed the Lean emission runner in a separate temporary
directory and compared both full JSON byte strings with the original frozen
artifacts; both match. The companion HEAD and dirty status match the pre-run
snapshot. No full umbrella build is claimed here.

[EXECUTED final hashes] Source SHA256:
`2c89af0fa69ceca9d9a7f0ed3a7a8746255dded42b63d2dc021315ba429d0d1b`.
Patch SHA256:
`c96679078731512508994cd3804c111e096e9e8cb14409592154d1d8bf9cbb30`.
[`integration_entry.json`](integration_entry.json) supplies the root's lane entry.
The IO runner is a separate executed tool, not a rooted theorem module; exclude
`formal/private_address_ema/emitted_schedule/EmitPrivateAddressEma.lean` from
the library-theorem census.

[OPEN runtime TCB] The generic Rust interpreter, its parser, bounds checks,
array loop, TFHE XOR/AND implementations, cryptographic correctness/noise,
encryption, serialization and exact ciphertext-byte determinism are not Lean
theorems. A gate-satisfying F2 valuation is the formal boundary. The independent
`experiments/end_to_end/private_ema/emitted_runtime/` lane owns concrete plain
Boolean comparisons and encrypted execution. Those records must keep their
scope distinct from this formal claim. Credentials, physical isolation,
journal finality, arbitrary encrypted utility and PQ security are unchanged
external obligations.

[OPEN next action] Root owns combined-umbrella compilation and collection.
Single-file iteration and checked patches use a read-only dependency overlay;
the companion tree and first 28-pin word patch remain unchanged.

[EXECUTED search accounting] This work uses local compiler and Lean library
sources only: no web, Scry, Kagi or PDF queries.
