# catgrad as a proving target — lane findings, and where they meet bf16

2026-08-11. Lane report against `~/src/catgrad` @ `faf053f` (2026-05-14),
cross-checked vs upstream master (2026-06-10). Op counts below are measured by
an instrumented probe, not estimated.

## The synthesis: catgrad's "blocking" problem is the bf16 finding's answer

The lane ranked **float-only `Dtype`** as its #1 blocking issue:

```rust
// catgrad/src/category/core.rs:23-29
pub enum Dtype { F32, F16, BF16, F8, U32 }
```

No integer, no fixed-point. Its three options were (a) prove IEEE-754 f32
faithfully — expensive; (b) reinterpret F32 as fixed-point in the backend —
cheap but **proves a different function than the one the reference computes**;
(c) fork catgrad to add a fixed-point `Dtype`.

**There is a fourth option the lane did not consider, and it is the one we
want: prove the bf16 path natively.** `BF16` is already a first-class dtype
here. Per `docs/bf16-exact-arithmetization.md`:

- every unary function on bf16 is an **exact 2^16 lookup table** — no
  approximation error term at all;
- **bf16 × bf16 → fp32 never rounds** (verified, 200k pairs).

So the semantic gap in option (b) does not have to be paid. We prove the same
function catgrad computes, because bf16 is what catgrad computes in.

**And `F8` is stronger still.** fp8 e4m3 has 256 values, so a *binary* op table
is 256 × 256 = 65_536 entries — the same size as a bf16 unary table. **Every fp8
operation, including multiply and add, is a single full-precision lookup.** For
any part of a network that tolerates fp8, arithmetization is essentially free.

This also dissolves the lane's issue #2. In the local clone `exp` is synthesized
as `pow(e, x)` with a tensor-valued real exponent — the worst possible
primitive. Upstream fixed it with graph-level Taylor/Cody–Waite approximations
(`approx.rs`, 646 lines). **With bf16 tables we need neither**: `exp` is one
lookup, exactly, at whatever rounding the table encodes.

Remaining real numeric question is unchanged and unmeasured: **accumulator
width** for exact fp32 accumulation of bf16 products.

## What the lane established about the seam

**It is a clean `Backend` replacement.** One trait, 39 methods
(`interpreter/backend/mod.rs:24-124`); upstream is 41 after adding `exp`/`round`.
`backend/shape_only.rs` (732 lines) is *already* an abstract backend that
computes nothing but shapes — a proving backend is that plus a wire id and a
trace append.

**Tensor data can never become a shape — verified exhaustively.** `Value::Nat`
is constructed in exactly three places, all in `abstract_interpreter/eval.rs`,
and none reads tensor data. The only crossing goes the safe way
(`NatToU32 : Nat → Tensor`). **Fix the input shapes and the entire trace
geometry is determined.** This is the property that makes arithmetization
tractable and catgrad has it by construction.

**Exactly one data-dependent escape in the eval loop**: `to_bool`, for
`Operation::If`. Zero of the pure transformers use it (llama, gpt2, qwen3, phi3,
gemma3, granite, deepseek, mistral3, gpt_oss). The four hybrid SSM families that
do have a **shape-derived** predicate — verified at `nemotron.rs:649-651`, where
the condition comes from `unpack(shape(in_k))` — so it is statically resolvable
and bindable as a public input.

**Sampling is greedy argmax inside the graph** (`llama.rs:225`). No temperature,
no top-p, no sampler anywhere. **Autoregressive generation is fully
deterministic and in-circuit.** Worth noting against the seed-grinding concern
in `audit-sampling-prior-art.md`: for catgrad-style inference there is no seed to
grind, because there is no sampler. That concern applies to stacks that sample,
not to this one.

**KV cache is explicit graph I/O** — `(x, in_k, in_v, max_positions) → (token,
out_k, out_v)`, cache updated by `concat` and threaded by the host. Ideal for
per-token IVC: cache state is an explicit input/output pair you can commit to.

**Weights are a `BTreeMap<Path, Value>`** — deterministic path-ordered
iteration, which is exactly the canonical object to Merkle-commit.

## Measured op counts

| term | ops | `Copy` | MatMul | Pow |
|---|---|---|---|---|
| `nn::Softmax` | 35 | 18 | 0 | 1 |
| `nn::Gelu` | 99 | 50 | 0 | 2 |
| toy GPT-2 (1 layer, d=32, vocab 128) | 864 | 456 | 7 | 7 |
| GPT-2 small (12 layers, d=768, vocab 50257) | 7288 | 3844 | 73 | 62 |

**53% of ops are `Copy`** — pure wiring, zero constraints. Another ~1300 are
shape/nat ops that stage away entirely. Circuit cost is dominated by tensor
*extents*, not node count.

## The seam must not author constraints in Rust

The lane read our house law and got this right. A `impl Backend for
ProvingBackend` that starts emitting `builder.assert_zero(...)` is exactly the
drift the Lean-authored-AIR law exists to catch — and it would compile at every
step, so nothing would look wrong.

Correct three-stage shape:

```
catgrad core::Term
  → Interpreter<ProvingBackend>   [Rust STAGER: resolves shapes and branches,
                                   records a trace. Authors NO constraints.]
  → resolved op trace (op, dtype, concrete shapes, wire ids, branch decisions)
  → Lean: per-op constraint semantics + DescriptorIR2 emission
  → circuit/src/descriptor_ir2.rs   [existing multi-table batch STARK + LogUp]
  → Plonky3 over BabyBear
```

The Rust side is a *tracer*, carries no soundness weight, and is genuinely small.

## Project status — matters for how we engage

MIT licensed, no obstacle. But: **dormant ~9 weeks.** Commits Feb→Aug 2026:
98 / 154 / 107 / 35 / 6 / 0 / 0. Last commit 2026-06-10. crates.io 0.2.1 is
~10 months behind the repo — depend on git, not the release.

The team appears to have moved to **`hellas-ai/catena-lang`** — *"a categorical
verifiable array language"* — created 2026-02-13, **pushed today**, 253 commits,
spiking to 152 in June exactly as catgrad fell to 6. Same top two contributors.
*This is inference from timing and shared contributors, not a public statement,
and there is no deprecation notice or archive flag.*

**Nobody is building ZK for either.** GitHub code search for `zk` across catgrad
returns one hit — a README bullet. Zero in Rust source. catena-lang's README
frames verification as determinism → replay/fraud proofs, with no mention of
zero-knowledge or proving systems. The June determinism work is determinism, not
ZK.

So the space is genuinely open. It also means we would be the only party
maintaining the seam — and that a direct question to the maintainers about
catgrad vs catena-lang should come **before** engineering, not after.

## Smallest end-to-end demo

`SimpleMNISTModel` in `catgrad/examples/hidden.rs:100-159` — 2-layer MLP,
784→100→10, sigmoid. Already the canonical demo with a registered test.
**Swapping in `ProvingBackend` at `hidden.rs:73-95` is a ~10-line diff.**

Then: `tests/test_models.rs` fixtures as differential harness → `tests/test_if.rs`
for branch binding → toy GPT-2 (1 layer, d=32, vocab 128, **needs no weights on
disk**, zero `If` nodes, 864 ops).

Minimum viable op set for that: ~20 of the 32 primitives.

## Open questions the lane flagged

- Is catgrad deliberately deprecated? Not archived, 13 open issues, no notice.
  **Ask before committing engineering** — the answer decides upstream vs fork vs
  target catena-lang.
- Is catena-lang the better target? Not read. Same `open-hypergraphs`
  foundation, actively developed, verifiability-oriented.
- Prover cost in rows, not ops. Deliberately not estimated before the numeric
  decision — a number derived first would be meaningless.
- Do candle and ndarray backends agree numerically? f32 addition is
  non-associative and the two use different reduction kernels, so "the model
  output" may be backend-relative. This is another argument for the
  accumulate-exactly-round-once approach.
