# zkML build log — the pillar's first implementation

Started 2026-08-13. BUILD lane against the design memo
`zkml-integration-architecture.md` (cards Z1–Z4). Everything here is written as
it happens; `[measured]` means a command ran, `[read]` means read at source.

**Substrate, said out loud: this is Lean-authored arithmetization.** The op
vocabulary, its denotation, the per-op constraint relation and the emit path are
all Lean. The catgrad fork is a *stager* — it records ops, shapes, wire ids and
branch decisions and authors no constraint. Nothing in this lane writes an
`assert_zero` in Rust.

---

## 0. Ground truth read before writing a line

`[read]` `minidregg/Theory/IndexedProgram.lean` (273 lines) — `IxSignature`
(`Op : Ix → Type`, `Resp`, `next`), `Program`, `Algebra`, `fold`, `AlgebraHom` +
`fold_fusion` (:93–119), `AlgebraRel` + `fold_rel` (:123–146), `Handler` /
`execAlgebra` / `interpret` (:153–179), and the mismatch tooth
`wrong_algebra_mismatch` (:267–269, `by decide`).

`[read]` `minidregg/Compiler/Signature.lean` — `Signature`/`Term`/`Alg`/`fold`,
`fold_unique`, `agree_by_initiality`, and the `[N3-converse]` law: **opaque
(function-valued) constructor payloads forbid any faithful compositional second
reading into a countable target** (`opaqueConflation_proved`, Cantor). This is a
hard design constraint on the op vocabulary — see §1.

`[read]` `minidregg/Compiler/Air.lean` — the arithmetization DSL: `AirOp`
(`const`/`var`/`add`/`mul`), `eval` (fold) vs `evalExec` (hand recursion),
`eval_agrees_exec` free by initiality, `accepts`/`semHolds`,
`accepts_iff_semHolds`.

`[read]` `minidregg/Compiler/AirRange.lean:62-80` — `ConstraintSystem F Idx =
List (Term (AirSig F Idx))`, `systemAccepts`, `systemSemHolds`,
`systemAccepts_iff_systemSemHolds`.

`[read]` `minidregg/Compiler/Emit.lean` — `ConstraintDescriptor`,
`descriptorHolds`, `emit`, `emit_faithful` (unconditional, both directions),
`emit_accepts_iff` / `emit_accepts_iff_fin` / `emit_semHolds_iff`,
`emit_wellFormed`.

`[read]` `minidregg/Compiler/EmitSerialize.lean` — the descriptor JSON wire
format, `babyBearP = 2013265921` with `Fact (Nat.Prime babyBearP)` proved, and
the `#eval writeDescriptorJson` build-time emission pattern.

`[measured]` `phase0/mnist-trace.json` — 26 ops. Full op census by kind:
`const×7, broadcast×4, cast×4, add×2, div×2, matmul×2, neg×2, pow×2, reshape×1`.

`[measured]` shared-tree state of `~/dev/minidregg` at start: `Compiler.lean`
and `prover/src/lib.rs` modified by codex, four `docs/` deletions staged, three
untracked `Uwueave*` files. `Theory.lean` **clean**. `lakefile.toml` clean.

---

## 1. Card Z1 — `minidregg/Theory/ZkmlTensorOps.lean` (LANDED, `fdc272f` + `3f90089`)

`[measured]` builds green; `scripts/check-import-boundary.sh` green; axiom
footprints `#guard_msgs`-guarded and clean (`propext, Classical.choice,
Quot.sound` — no `sorryAx`, no `Lean.ofReduceBool`, so nothing is
`native_decide`d).

Thirteen constructors, twenty-three operations once the `Un1`/`Bin2`/`Cmp2` kinds
are counted: elementwise `un`/`bin`/`cmp`, `select`, `fma`, a syntactically
identified pure `map`, `cast`, matmul as an **ordered fold**, an ordered `reduce`,
`gather`, and `reshape`/`broadcast`/`transpose`.

### Three decisions that were forced, and by what

**No op carries tensor data.** `Compiler/Signature.lean`'s `[N3-converse]`
(`opaqueConflation_proved`, a Cantor argument) proves that a signature with
semantic payloads admits *no* faithful compositional second reading into any
countable target. catgrad's v0 trace carries weights as a `const` op with a
digest — a payload. So every constant here is an entry of the initial context,
referenced by a `Var`. This was not a stylistic choice; it is also the right
deployment shape, since weights are a **commitment** surface (committed once,
referenced by index) and not a per-inference **constraint** surface.

**The denotation is a fold.** `run = fold denAlg`. One program, N readings; the
spec/executable twin is structurally impossible rather than merely avoided.

**`select` denotes `s·a + (1−s)·b`, not an `if`.** Denoting it as an `if` would
have hidden the booleanity obligation *inside the reference semantics*, where no
constraint-side theorem would ever have to discharge it.

### The content: two collapses and one derived bill

* **`run_transport`** — `fold_rel` applied once. Two `ScalarHom`-related scalar
  readings give corresponding results on **every** trace. Zero induction at the
  use site; `diag_hom` inhabits the hypothesis at a genuinely different carrier.
* **`arith_transport`** — the honest zkML statement. Along a `RingHom`, on the
  fragment `TOp.arithmetic`. **The complement of that fragment is the
  arithmetization bill, and it is derived rather than asserted**: `div`, `pow`,
  `cmp`, `map`, `gather` and a *dtype-changing* `cast` are exactly what a ring
  homomorphism fails to carry. Instantiated at `Int.castRingHom (ZMod 7)` on a
  real 2×3·3×2 matmul.
* **`census_macs_eq_macAlg`** — the same collapse by `fold_fusion`, for the cost
  reading.
* **`gadgetCount_eq_zero_iff`** — turns the computable gadget count into a
  *certificate* for `arith_transport`'s hypothesis, rather than a statistic.

### Teeth (all kernel-decided)

1. `wrong_macs_mismatch` — a cost algebra charging a matmul `m·n` instead of
   `m·k·n` (the mistake that would price MNIST **784× cheap**) computes 4 against
   12 and is caught.
2. `wrong_scalar_mismatch` — a reading that mis-denotes `sub` as `add` computes 2
   where the correct one computes 0. Sharing constructor names supplies no
   agreement.
3. `div_reading_disagrees` / `arith_reading_agrees` — two readings that agree on
   the *whole* arithmetic fragment disagree on a one-op division trace. So
   `run_transport`'s hypothesis is load-bearing, not decoration, and the fragment
   boundary is exhibited on one concrete pair rather than argued.

### Not closed, named not stubbed

Numeric adequacy is untouched: this fixes the **shape** of the reference reading
and the **order** of every accumulation, not which scalar semantics is adequate.
bf16 exactness, accumulator width and backend agreement remain exactly as open as
the memo left them. `slice`, `concat` and general non-scalar broadcast are
**absent**; MNIST needs none of them, a KV cache needs `concat`.

---

## 2. Card Z2 seam — the trace format and a checked reader (LANDED, `3f90089`)

`minidregg/Compiler/ZkmlTraceCheck.lean` + `zkml-research/phase0/v0_to_v1.py`.

### The reader's result type IS the theorem

`checkTrace : RawTrace → Except String CheckedTrace` returns the **intrinsically
typed** `Trace tOut Γ`. A trace with a wire out of scope, a dtype mismatch, a
disagreeing matmul contraction, or an element-count-changing `reshape` is *not a
term of that type*. "The reader returned `.ok`" is therefore not a claim to be
audited — it is the construction of an object whose existence is the
well-typedness. There is no separate validator to fall out of sync.

### What v0 leaves under-determined — the answer to the brief's question

Greenfield doctrine applies and was applied: v1 is **not** v0 plus fields, and
`catgrad-trace/v0` now refuses to load (`mnistForgedVersion_refused`). Each item
below is a fact v0 does not carry; `v0_to_v1.py` prints all of them at conversion
time, including where it had to guess.

| # | v0 gap | Why it matters | v1 |
|---|---|---|---|
| 1 | **One `const` op** for model weights, the inference input *and* program literals | Different commitment obligations entirely. And a constant is identified only by an FNV digest, so the trace **cannot say which weight entered a wire** — no weight commitment can be checked against it at all | initial-context entries with mandatory `role` (`input`/`param`/`literal`) and `path`. The converter assigns roles by tensor **rank**, which is a guess, and says so — the tracer must supply them |
| 2 | **No output declaration** | "the last op" is a convention, and nothing checks its type | `out` + `out_ty` required; the checker refuses a mismatch |
| 3 | **Per-op `dtype`**, with no statement of whether it is operand or result | for `cast` they differ *by definition*; the field is ambiguous on exactly the op that needs it | field removed. Operand dtypes come from the operand wires, result dtype is derived — they cannot disagree |
| 4 | **matmul rank unstated** — a `contract` attribute and nothing about rank>2 | batched? which axes? two readings compute different functions | rank-2 only; the checker **refuses** rather than picking a reading |
| 5 | **No memory order** on `reshape` | row-major and column-major readings of the same record compute different functions | row-major pinned **once**, at `idxEquiv` |
| 6 | **No public/witness split** | the emit layout has nothing to consume | `role` is the split |
| 7 | 4 of 26 ops are identity `f32→f32` casts; two constant pairs share a digest | canonicalization is available for free | kept (canonicalization is a separate checkable transform), but `TOp.arithmetic` makes an identity cast **visibly free** |

Still open and not pretended otherwise: **FNV is still FNV.** `path` makes a
constant's *identity* expressible; binding it needs a collision-resistant
commitment (memo item v1-2).

### `[measured]` from the real MNIST trace, kernel-computed from the typed term

```
7 context entries (2 param, 1 input, 4 literal)   19 ops   output f32[2,10]
census      = ⟨ops 19, macs 158800, outElems 3548⟩
gadgetCount = 4
```

* **158 800 MACs** — independently reproducing the tracer's own measured figure by
  a completely different route (Lean fold over an intrinsically typed term vs. a
  Rust counter over a `Backend` trace).
* **3 548** elementwise output elements. The memo's 3 552 counts the four scalar
  constants; here they are context entries, not ops. Stated so nobody rediscovers
  the 4.
* **4 gadget ops, and by `gadgetCount_eq_zero_iff` that is a certificate.** MNIST
  is **not** in the arithmetic fragment, and the four responsible ops are exactly
  the sigmoid's two `pow` and two `div`. Both matmuls, both negations, the four
  identity casts, the four broadcasts, the reshape and both adds are carried by
  the ring structure and cost no gadget at all. *The entire non-ring content of a
  two-layer MLP is the sigmoid.*

Four refusal teeth, each mutation built **constructively** (`List.set`) and proved
to be a real change before its refusal is read — a mutation that silently became a
no-op would fail loudly instead of leaving a green test asserting nothing.

Lean authors the v1 JSON (writer + reader, round trip checked at build time on the
real trace). `[measured]` the Python converter's output and the Lean-authored file
parse to the **same object**.

---

## 3. Card Z3 first rung — one op, end to end (LANDED, `3f90089`)

`minidregg/Compiler/ZkmlEltwiseAir.lean`.

```
  TOp.bin .add                    Theory: the op, candidate-independent
    ⇣ denotation                  run S (eltAddTrace t)
  eltAddSystem                    the constraint relation, DERIVED at any shape/layout
    ⇣ eltAddSystem_denotes        systemAccepts ⟺ the denotation holds
  emit                            Compiler/Emit, emit_faithful (unconditional, both ways)
    ⇣ emit_accepts_iff_fin
  addDemoDescriptor               ⟹ addDemoDescriptor_means_denotation
```

**`addDemoDescriptor_means_denotation`**: a total wire vector satisfying the
emitted BabyBear descriptor exists **iff** `Theory/ZkmlTensorOps`'s denotation of
the trace equals the claimed output. No step in that chain is an audit.

The generic half is proved at an **arbitrary** shape, wire layout, field and
ring-shaped scalar reading — it does not depend on what the field reading chose for
`div`, `pow`, `cmp`, the map tables or `toIdx`, which is the correct scope for an
`add`. `mem_idxList` is what makes "one assertion per element of the enumeration"
mean "every element constrained": an emitter that dropped an index would constrain
a proper subset and nothing downstream would notice.

`[measured]` demo `f32[4]`, inference-shaped split (claimed output public at wires
0–3, operands committed witness at 4–11): **12 gates, 24 wires, 4 zero-checks**,
871 bytes of JSON. Satisfiable decided; a **one-element** forged output refused at
*both* the descriptor and the denotation.

`[EMIT-sound]` unchanged: this says what the descriptor **means**, never what the
prover proves. `[EMIT-backend]` unchanged: no Rust reader consumes either new
testdata file, so the label on the JSON is exactly **vector agreement**.

---

## 4. What matmul needs that the scalar ops do not

It is 98.7% of the trace, so this is the question that decides the pillar. Eight
findings, in descending order of how much they change the design. **One of them
corrects the design memo.**

### 4.1 The naive path lands exactly on the size wall — derived, not guessed

Calibration `[measured]`: the emitted `add` descriptor has **12 gates for 12 DSL
nodes** — `AirFlatten`'s `flatten` emits exactly one gate per `add`/`mul` node.
The matmul denotation is a left fold of `k` steps of `acc + a·b`, i.e. `2k` nodes
per output element, plus 2 for the `out − (…)` assertion. So a tree-flattened
matmul costs `m·n·(2k+2)` gates:

```
MNIST matmul 1  [2,784]·[784,100]   →  314 000 gates
MNIST matmul 2  [2,100]·[100,10]    →    4 040 gates
                                    →  318 040 gates total
elementwise (3 328 elements, 1–4 gates each)  ≲ 13 000
```

At the measured ~52 bytes/gate of the emitted JSON that is a **≈17 MB
descriptor** — inside the range where the memo records a 24 MB descriptor being
deliberately withheld from routing. The naive path is not merely slow; it hits a
limit the repo has already hit once.

### 4.2 ⚠ CSE does **not** rescue matmul — a correction to the memo

The memo names expression sharing as "matmul's make-or-break" and cites
`EmitShare.lean`'s 2 696 666 → 220 gate result. That measurement is on the
**note-spend**, whose shape is a Poseidon2/Merkle tree that genuinely re-reads the
same subterms. Matmul does not: the `m·k·n` products `a[i,p]·b[p,j]` are pairwise
**distinct**, and `flatten` already emits a variable read as a leaf rather than a
gate. **There is no structural sharing in a contraction to exploit**, so
`EmitShare` leaves 318 040 gates at 318 040 gates.

That does not weaken the memo's *conclusion* (minidregg over breadstuffs) — CSE is
still decisive for the hash/Merkle shapes, and the other two deciding facts stand
untouched. But the reason to reach for a vector relation is **not** that sharing
is unavailable in breadstuffs; it is that **no gate-level emit of any kind gets
below `m·k·n`**. The vector relation is the only lever.

### 4.3 The `foldl → Finset.sum` bridge does not exist, and everything waits on it

`TOp.denote` for matmul is a `List.foldl` over `List.finRange k`, because the
accumulation **order is part of the semantics** (§4.4). Every MLE and sumcheck
statement in `Selvage/` and `Assurance/` is written over `Finset.sum`. So the
first concrete piece of matmul work is a bridge lemma

```
run S matmulTrace ρ (i,j,⋆) = ∑ p : Fin k, a i p * b p j        (over a CommRing)
```

which is ~10 lines given commutativity and associativity — and which is **exactly
where the ordered semantics is deliberately discarded**, so it must be stated with
the commutativity hypothesis visible. `foldl_hom` (already in the file) is the
transport lemma it will use. Nothing else in the matmul path can be stated before
this exists.

### 4.4 The order is a semantic commitment the constraint system does not honour

`run` folds left; a field-level constraint system may reassociate freely, and
`arith_transport` is undisturbed because ℤ is associative too. The gap is entirely
in **numeric adequacy**: f32 addition is *not* associative, so "the field/integer
computation models what the f32 reference computed" is a claim the ordered fold
makes precise and neither `run_transport` nor `arith_transport` establishes. The
scalar `add` case cannot see this at all. It is the same open question the memo
lists (accumulator width, candle-vs-ndarray agreement), now located at a specific
definition.

### 4.5 Power-of-two padding becomes a vocabulary question

The MLE face needs `Â` over `{0,1}^{log m} × {0,1}^{log k}`. The vocabulary's
shapes are arbitrary `ℕ`: MNIST is `784 → 1024` (30% waste), `100 → 128` (28%),
`10 → 16`, `2 → 2`. Either

* a `pad` op enters `Theory/` **with a denotation** and a theorem that
  zero-extension does not change the contraction, or
* the MLE machinery handles non-dyadic domains.

This is the single most concrete new requirement, and it is a `Theory/` change —
the only one matmul needs. Everything else is `Compiler/` and `Selvage/`.

### 4.6 The R1CS face is not the matmul identity

`Assurance/AirSumcheckQuadratic.lean` carries `Σ_b (Â·B̂ − Ĉ)(b) = 0` — a
**Hadamard**-shaped check, not a contraction. Matmul needs

```
Ĉ(r_i, r_j) = Σ_{p ∈ {0,1}^{log k}} Â(r_i, p) · B̂(p, r_j)
```

i.e. a sumcheck over `log k` variables at *bound* outer points. The degree-2 face
is the right machinery and the right bound shape, but it is an **adaptation**, not
an instantiation. The memo's "an instance of machinery that exists" is optimistic
by one lemma.

### 4.7 Matmul needs a commitment scheme; `add` needs none

The verifier of the above must evaluate `Â(r_i, ·)` and `B̂(·, r_j)` at the end —
**two polynomial-commitment openings**. The scalar path needs no PCS, no
challenges, no transcript: its descriptor is a static gate system. Matmul needs a
PCS *and* Fiat–Shamir, and `[PROVER-fs]` is open. `Compiler/FiatShamirAir.lean`
exists but is the *recursive verifier's* FS binding, not the prover's.

### 4.8 The headline theorem changes shape, and the ε propagates

`eltAddSystem_denotes` and `emit_faithful` are **unconditional iff**s: acceptance
*is* the denotation. A sumcheck-based matmul relation is sound only up to
`≈ deg·μ/|F|`. So the matmul rung's headline is `accepts ⟹ denotes except with
probability ε`, and **everything above it inherits an ε the scalar path does
not**. A design mixing the two must add them, and the audit hookup's `ε_chk` is
where they land. Worth saying in advance, because the two rungs will otherwise be
quoted with the same words.

### 4.9 What the vocabulary already got right

Matmul is **one op with its own denotation**, not a program of 158 800 `fma`s. So
there is no way to "reduce matmul to the scalar path" inside the vocabulary — and
that is the point: `run` already says exactly what a sumcheck must prove, and
`arith_transport` already says the integer and field readings of it agree. **Only
the `Compiler/`+`Selvage/` side changes.** That is the payoff of putting the op in
`Theory/` with a fold denotation rather than in an emitter.

---

## 5. Honest ledger — what this lane did NOT do

* **No inference is proved.** No prover ran. The engine remains where the memo
  left it (`prover/src/sumcheck.rs` was degree-1 at the start of this lane; codex
  landed a degree-3 rung concurrently — unaudited by me).
* **The matmul constraint semantics does not exist.** Only its denotation does.
  §4 is the specification of that work, not the work.
* **FNV is still FNV.** The v1 `path` field makes a constant's identity
  expressible; nothing binds it.
* **No Rust reader consumes either testdata file** (`[EMIT-backend]`), so the only
  label the JSON carries is *vector agreement*.
* ⚠ **`minidregg/Compiler.lean`'s two import lines are in the worktree and NOT
  committed.** That file carries another lane's uncommitted work and
  `git commit --only` is path-granular, so committing it would have swept an
  import of a file that is not in HEAD. **Until those two lines land, both new
  Compiler modules are outside the default `Minidregg` build target** — the
  gating-defaults-to-silence class, named here rather than discovered later. Both
  build clean as explicit targets and the whole `Compiler` root builds green with
  the lines in place.

## 6. Build evidence

```
lake env lean Theory/ZkmlTensorOps.lean              → no output (green)
lake build Theory                                    → 3010 jobs, success
bash scripts/check-import-boundary.sh                → OK: Theory, OK: Selvage
lake build Compiler.ZkmlEltwiseAir Compiler.ZkmlTraceCheck → 2956 jobs, success
lake build Compiler   (with the two import lines)    → 3213 jobs, success
#print axioms (guarded): propext, Classical.choice, Quot.sound — no sorryAx,
                          no Lean.ofReduceBool (nothing is native_decide'd)
```

Commits: `fdc272f` (Theory vocabulary), `3f90089` (trace format + one-op path).
