# Private-address EMA word seam

[EXECUTED checked proposal] The 28-theorem, 28-exact-pin proposal is
[`Theory/PrivateAddressEma.lean`](Theory/PrivateAddressEma.lean), with
[`minidregg-private-address-ema.patch`](minidregg-private-address-ema.patch).
It uses standard `BitVec` operations to state the
eleven-bit arithmetic and four-register address obligation; it adds no Boolean
executor. The actual encrypted Rust path is
`experiments/end_to_end/private_ema/src/lib.rs:82` (`candidate`), `:100` (`learn`)
and `:123` (`infer`). No companion source is edited.

[SOURCE inspected proof] The prior combined 708-pin patch contains
`Compiler.ResidentEmaCertificate.descriptor_semantic`, which forces floor EMA
through the existing public biased-byte field descriptor, and
`ema_fullbyte_closed`; `Assurance.ResidentEmaCell.biased_representation_exact`
relates its biased byte to two's complement. The source-window successor proves
BFV source/noise equations. These results do not prove this eleven-bit word
extraction and encrypted-address selection seam.

[DERIVED / checked scope] The new proof quantifies over all four signed byte registers,
both address bits and every signed byte label; no cryptographic key or ciphertext
appears. A second invariant covers states in [-120,120] and labels ±120.
The keystone is declared before proof work, with a changed-state subject,
inhabited invariant premises, negative-floor tooth, ten-bit-width tooth and
unselected-register tooth.

[DERIVED / checked ripple seam] `RippleTrace` is a relation containing the
actual local XOR/AND full-adder equations, not a duplicate executable loop.
For every width, `ripple_correctness` proves exact weighted-bit conservation,
including final carry; `ripple_bitvec` proves the corresponding modular sum.
The all-zero trace inhabits its premises at every width, and a one-bit carry
example proves that dropping the carry cannot mean unbounded integer addition.

[EXECUTED verification] `python3 .../private_address_ema/check.py` produced
[`results/lean_010.json`](results/lean_010.json): exit zero, no stdout/stderr,
all exact axiom guards accepted. `python3 .../private_address_ema/package.py`
produced [`results/verification.json`](results/verification.json): lexical
theorem/pin census, fresh source-only patch application and byte comparison,
and both staged and companion import-boundary checks pass. Cached dependency
oleans were reused; the root owns whole-umbrella integration. The companion
HEAD and dirty status match the pre-run snapshot. Earlier failed attempts are
retained and are not used as successful verification evidence.

[EXECUTED frozen hashes] Lean source SHA256:
`0b148bff8a53447bc9f30950948771a4b0f53edeb1110cc78f44e85a960d562d`.
Patch SHA256:
`9fabd5d64ab3280dde1bbb1affab9ced9d5835f248f984dd4bb9d0488622ebae`.
[`integration_entry.json`](integration_entry.json) supplies the root's lane entry.

[OPEN runtime TCB] Boolean gate correctness under TFHE noise, realization of
the relational ripple trace by the Rust array loop, Rust/LLVM/serialization,
same read-time inputs, OS role separation,
restricted reader credentials and journal composition are outside the theorem.

[OPEN successor, separately owned here] `emitted_schedule/` is the next bounded
work package. Its source will reuse `AirSig (ZMod 2)` and the existing
`AirFlatten` / `emit` / `cse` compiler, lowering NOT and MUX to XOR/AND source
terms. A generic Rust interpreter can then consume the Lean-emitted schedule
and replace the successor's authored `add/candidate/learn/infer` code. The
frozen runtime and this first patch remain unchanged. Until that join is
checked, no claim of a Lean-emitted TFHE learner is made.

[EXECUTED search accounting] No web, Scry, Kagi or PDF calls were used.
