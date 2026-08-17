# Batching the reduced opening — the obstruction the decision doc did not name, and the lever that survives it

2026-08-16. BUILD lane. Target: the `×2.13`-on-the-wrap lever named in
`breadstuffs/docs/deos/WRAP-NATIVE-HASH-DECISION.md` lever 3(b) and
`notes/leaf-vs-recursion.md` §3d — *"GKR-batch the reduced openings (one sumcheck replaces
~14,300 per-column ExtMuls)"*.

Landed: `emberian/plonky3-recursion@b471aca` (branch `lane/batched-reduced-opening`). Every count
in §2 is `[MEASURED]` — an exact op/cell census off a deterministic circuit build, before and after,
in the same environment. Nothing here is a wall clock. `[READ]` means at source.

⚠ An earlier, one-section draft of this file was swept into `d64dd19` by a sibling lane's commit
before it was finished. This is the finished note; the header it carried is unchanged.

---

## 0. Where the idea is named, and what each place says about why it was not taken

| place | what it says | obstruction named? |
|---|---|---|
| `docs/deos/WRAP-NATIVE-HASH-DECISION.md:134` | lever 3(b) of a three-lever plan; *"one sumcheck replaces ~14,300 per-column ExtMuls → the ~3.2M residual toward ~0.3M"* | **no** — it is listed as pure upside |
| `docs/deos/APEX-VERIFIER-AIR-REDUCTION.md:157` (Lever D) | *"**COORDINATION-REQUIRED** … changing them to a sumcheck is a **recursion-backend rewrite in the `plonky3-recursion` fork**, not an `apex_shrink.rs` change"* | **yes, but only an ownership one** — "it is in someone else's crate" |
| `HORIZONLOG.md:18343-18345` (2026-07-13, gnark) | after the `S_z − S_x` algebraic hoist landed in `chain/gnark/stark_open_input.go`: *"**GKR-batching the alpha-combination itself is now MARGINAL** (S_x arithmetic ≈ 0.32M total) — the algebraic hoist obsoleted most of that ask."* | **yes, and it retires the lever — on the gnark side only** |
| `notes/leaf-vs-recursion.md` §3d | `×2.13` on the wrap, `×2.05` per turn, *"already named in this repo, undated and untaken"* | no |

So the record holds **three different verdicts on the same phrase**, and nobody had noticed that
the third one (gnark, "marginal") is about a **different circuit** from the first, second and
fourth (the BabyBear in-circuit recursion verifier). The gnark hoist did not touch
`plonky3-recursion`; `HornerAcc = 390,716` is still there.

### 0a. ⚑ The obstruction none of them names, and it is a real one

A sumcheck that batches `Σ_k α^k v_k` over the `q · Σw ≈ 390,716` opened values terminates in a
single claim about the **multilinear extension of those values at a random point**, `Ṽ(r)`. The
verifier must discharge that claim. It has exactly two ways:

1. **Recompute `Ṽ(r)` from the values** — Θ(N) again. No saving. The sumcheck was free only if
   someone else answers the final claim.
2. **Open it from a commitment to `V`** — but the only commitment the opened values have is the
   **Merkle leaf** of the child's MMCS, and a Merkle root supports **no evaluation opening**.

⚑ And the verifier *already holds every one of those values in the clear*: it must, because it
hashes them into the per-query leaf sponge (`64.9%` of in-circuit permutations, §2c of
`leaf-vs-recursion.md`). So the values are not hidden behind a commitment that could be opened —
they are plaintext circuit witnesses that are separately hashed.

> ### ⚑⚑ Batching the reduced opening with a sumcheck requires an **evaluation-binding commitment on the opened values**. Two-adic FRI gives **univariate** openings only. So lever 3(b), *as stated*, is not a prover-side rearrangement — it is a **PCS replacement**, and its cost is a new commitment scheme, not a backend rewrite.
>
> That is exactly why SP1 6.4 went Jagged → Stacked → **BaseFold** and OpenVM 2.0 went Stacked →
> **WHIR** (`leaf-vs-recursion.md` §5): both are multilinear PCSs whose openings *are* MLE
> evaluations, so the sumcheck's terminal claim is answerable. Our stack cannot answer it.

The `×2.13` in `leaf-vs-recursion.md` §3d is therefore **derived against an assumption that the
sumcheck's terminal claim is free**, and it is not free. The lever is not wrong; it is
mispriced and mis-scoped — it is a PCS migration wearing a backend-rewrite's clothes.

---

## 1. The lever that *does* survive, and it is pure algebra

### 1a. What the verifier opens separately, and why (established before touching anything)

`p3-batch-stark` presents the PCS with **four rounds**, and they do **not** agree on how many points
a matrix is opened at (`recursion/src/verifier/batch_stark.rs`, cross-checked against
`chain/gnark/stark_open_input.go:109-133` and `bridge/mina-zkapp/src/DeepQuotient.ts:722-745`):

| round | matrices | points per matrix | source |
|---|---|---|---|
| trace | one per instance | **2** — `zeta`, `zeta·g`, when `air.uses_main_next_row()` | `batch_stark.rs:896-923` |
| preprocessed | one per instance with prep | **2** when a `next` row exists | `:1030-1055` |
| permutation (LogUp) | one per instance | **2**, always | `:1076-1100` |
| quotient chunks | `quotient_degree` per instance | **1** — `zeta` only | `:960-972` |
| random (ZK) | one per instance | 1 | `:880-892` |

The quotient chunks are separate matrices **because the verifier opens them separately** — the
in-tree statement of this is `circuit/tests/ir2_field_op_counts.rs:1765-1769`, guarding
`batched_chunk_ldes_are_bit_identical`: *"a batching that changed what those matrices ARE would be
a wire change."* Nothing here changes what any matrix is.

The in-circuit verifier already exploits one consequence of this table:
`open_input`'s `unified_z` fast path (`recursion/src/pcs/fri/verifier.rs:1215-1279`) runs **one**
Horner chain across every matrix of a height group *when all of them expose exactly one shared
point* — i.e. it already covers the **quotient round**. Everything with `P = 2` — trace,
preprocessed, permutation — falls to the per-matrix-per-point fallback and pays `P·n` Horner steps
per query.

### 1b. The identity

For a matrix of width `n` opened at `z_1 .. z_P`, entering the height's α-ladder at power `A`, the
verifier must produce

```text
  Σ_j  A·α^{(j-1)n} · (z_j - x)^{-1} · Σ_i α^i (p_{z_j}[i] - p_x[i])
```

and the inner sum splits as `Q_j - R`:

```text
  Q_j = Σ_i α^i p_{z_j}[i]     (α and the OOD values are the SAME at every query)
  R   = Σ_i α^i p_x[i]         (the only query-dependent half — and independent of j)
```

Two consequences, and the second is the one nobody took:

1. **`Q_j` is query-independent** — this is the `S_z` hoist `chain/gnark/stark_open_input.go`
   landed on 2026-07-13. In the Rust in-circuit verifier it is *free*, because `p3-circuit`'s
   `horner_acc_pool` is a real CSE pool: written as a pure function of `(alpha, ps_at_z)`, each
   `Q_j` chain is emitted **once for the whole circuit**, not once per query.
2. ⚑ **`R` does not depend on `j`** — so **one** chain serves all `P` points. The gnark hoist does
   *not* do this; it still recomputes `S_x` per `(matrix, point)`. This is the part that was never
   taken anywhere.

Per-query Horner cost per matrix falls `P·n → n`, against a one-off `P·n`. Over `q` queries:

```text
  q·P·n   →   q·n + P·n
```

At the deployed `q = 19, P = 2`: `38n → 21n`, a **1.81×** cut on every `P = 2` matrix. A `P = 1`
matrix would go `19n → 20n`, so the split is applied **only when `P ≥ 2`** and the fused
`HornerAcc` (`acc·α + p_z − p_x` in one op) is kept everywhere else.

⚑ **This is a re-association of the same field expression.** `ro` is bit-identical, so the FRI
fold sees the same input word, and **the child proof is untouched** — no wire change, no change
to what the verifier accepts. What moves is the wrap's own op list, hence its own VK (§4).

### 1c. ⚑ What it cost to land: a latent contract nothing was checking

The first implementation was arithmetically correct and produced
`OodEvaluationMismatch { index: Some(2) }` — the **ALU table** — with nothing naming a cause.

`Op::horner_acc`'s accumulator is not a constrained operand. `circuit/src/ops/op.rs:145`:
*"In the AIR, the accumulator comes implicitly from the previous row's `out` column."* And
`AluAir::compute_schedule` (`circuit-prover/src/air/alu_air.rs:345-362`) recovers chains as
**maximal runs of adjacent `HornerAcc` ops in the op list**, seeding each run from a zero
`Separator` row and packing `k` steps per row whose intra-row constraints chain `out_t → acc_{t+1}`
(`AluPackedHornerStepPrepCols` carries only `a_idx`/`c_idx` per extra step — there is no accumulator
index at all).

So an emitter owes two things, and **nothing checked either**:

1. every chain starts from a **zero** accumulator (the separator supplies zero; any other seed is
   unrepresentable) — my first draft seeded at the top coefficient to save one op per chain;
2. two independent chains are **never adjacent** in the op list — my first draft put the `R` chain
   immediately before the `Q_1` chain, with the intervening `α^n` lookup a cache hit that emitted
   no op.

> ### ⚑ The contract held only because the **one** emitter that produces `HornerAcc` happened to satisfy it. It was an emitter convention, documented in prose on the op constructor and enforced by nothing — and its violation is invisible: an unproved chain link produces the *same shape* of trace, and fails only as an OOD mismatch against a table, naming neither the op nor the reason.

Landed with the fix: `CircuitError::HornerChainContractViolated`, checked in
`Circuit::generate_preprocessed_columns` (`circuit/src/circuit.rs`), which walks the op list once
and refuses on either violation with the offending op index. It is a *completeness* guard, not a
soundness one — the preprocessed columns are part of the VK, so a violation cannot be induced by a
prover — but it converts a silent, undiagnosable break into a named refusal at build time. It also
turns "I reasoned that the chains are separated" into "the build refuses if they are not."

⚠ **And the guard had only ever been seen to ACCEPT** — it landed in the same commit as the
emitter fix that stopped violating it, which is the shape of a gate that cannot go red. Four tests
(`0ed1182`) make it satisfiable *and* refutable in both directions: a non-zero seed and two
adjacent independent chains each refuse with the offending op index, and a well-formed chain and
two chains separated by a single non-`HornerAcc` op each pass. The second refusal reproduces the
exact op sequence the first draft emitted.

---

## 2. ⚑ MEASURED — the deployed leaf wrap, before and after

Instrument: `breadstuffs/circuit-prove/tests/leaf_vs_recursion_sweep.rs` (§A/§B) and
`recursion_tower_profile.rs::l1_leaf_wrap_over_the_deployed_ir2_leaf`, unchanged — the same
harness that produced `leaf-vs-recursion.md`. Child: the deployed rotated transfer leaf,
`trace_width 1804 / pi_count 61`, three main traces at log₂ rows `[6, 8, 4]`, `Σwidth 3738`.

**This is a WORK claim, not a latency claim.** Every number below is an exact op or cell count off
a deterministic circuit build; none is a wall clock, and no figure here depends on load, thread
count, or `target-cpu`. No latency column is offered because none was measured.

### 2a. Op counts at the deployed point `(lb 6, arity 2, q 19, m 14)`

| | before | after | |
|---|---:|---:|---|
| `poseidon2_perm` | 38,168 | **38,168** | **control — hashing untouched** |
| `recompose` | 160,263 | **160,263** | **control** |
| `Hint` | 66,777 | **66,777** | **control** |
| **`HornerAcc`** | 390,716 | **216,330** | **×1.806** |
| **`Alu` (all)** | 441,684 | **267,526** | **×1.651** |
| witness count | 1,123,022 | 948,750 | ×1.184 |

Three counts that my change cannot touch are identical **to the digit**, which is what makes the
two builds comparable at all (they differ in one more thing: the `after` build ran with
`DREGG_REQUIRE_LEAN=0` because a sibling lane had the Lean tree red — the controls are the evidence
that this is irrelevant to a circuit-shape census).

### 2b. ⚑ The falsifier fired exactly where predicted

`leaf-vs-recursion.md` §2b's headline law was **`HornerAcc = 20,564·q`, exactly linear with
exactly ZERO intercept**, `max|resid| 0.00` across five query counts and three blowups. The whole
point of this change is to move work *out* of the query loop, so it must break that law in one
specific way: a nonzero intercept equal to the hoisted `Q_j` chains.

| fit | before | after |
|---|---|---|
| `HornerAcc` per-query | 20,564.00 | **10,306.00** |
| `HornerAcc` q-independent | **0.00** | **20,516.00** |
| max\|resid\| | 0.00 | **0.00** |
| `perms` per-query / intercept | 1,423.13 / 11,128.39 | **1,423.13 / 11,128.39** |
| `recompose` per-query / intercept | 2,581.04 / 111,222.10 | **2,581.04 / 111,222.10** |

Still exact to the op across `q ∈ {12, 19, 28, 38, 57}` and `lb ∈ {2, 3, 6}`, and the `perms` and
`recompose` fits are unmoved. And the two new coefficients are not free parameters — the model
predicts `intercept = W₂` and `slope = 20,564 − W₂/2`, so

```text
  2 · (20,564 − 10,306) = 20,516      ✓ exactly
```

> ### ⚑ `W₂ = 20,516` of the `20,564` opened values per query — **99.77%** — are in two-point matrices. Only 48 values per query were ever single-point. The reduced opening was, to within a quarter of a percent, *entirely* the `P = 2` case that nothing was sharing.

Because the hoisted half is paid once, the win **grows with `q`**: at `q = 57` (the `lb 2` engine)
`HornerAcc` goes 1,172,148 → 607,958 = **×1.928**, approaching the `×2` ceiling of the two-point
collapse.

### 2c. The committed geometry — one power-of-two rung

`l1_leaf_wrap_over_the_deployed_ir2_leaf`, real table geometry via `get_airs_and_degrees_with_prep`
(the call the prover makes), deployed packing `p1/a4`:

| table | rows before | rows after | cells(m+p) before | cells(m+p) after |
|---|---:|---:|---:|---:|
| Const | 4,096 | 4,096 | 40,960 | 40,960 |
| Public | 2,048 | 2,048 | 12,288 | 12,288 |
| **Alu** (w 76+59) | **2¹⁸ = 262,144** | **2¹⁷ = 131,072** | **35,389,440** | **17,694,720** |
| poseidon2 w16 | 65,536 | 65,536 | 21,233,664 | 21,233,664 |
| recompose | 262,144 | 262,144 | 1,572,864 | 1,572,864 |
| **TOTAL** | | | **58,249,216** | **40,554,496** |

`degree_bits [12, 11, 18, 16, 18] → [12, 11, 17, 16, 18]`.

> ### ⚑ **×1.436 on the wrap's committed cells**, and the Poseidon2 share moves **36.45% → 52.36%** — so a *free hash* is worth **×1.57 → ×2.10**.
>
> ⚑ **The global max height does NOT move** (2¹⁸, now set by `recompose`, not `Alu`). So the wrap's
> own FRI shape — query count, fold-round count, `log_global_max_height` — is unchanged, and
> anything that verifies *this* wrap sees the identical FRI structure. Same argument as
> `APEX-VERIFIER-AIR-REDUCTION.md`'s Lever A, and it holds for the same reason.

⚠ **This is ×1.436, not the ×2.13 `leaf-vs-recursion.md` §3d claimed.** That figure was derived on
`Alu` collapsing from 441,684 ops to ~51,053 — *three* rungs, `2^18 → 2^15` — which is the
**sumcheck** endpoint, and §0a says why that endpoint is not reachable over two-adic FRI. The
algebraic collapse gets **one** rung. The §3d number should be read as the (unreachable) sumcheck
figure, and **×1.436 as the one that is now on disk**.

⚑ And a lever this exposes: `recompose` is now the tallest table (2¹⁸ rows for 160,263 ops at
`npo_lanes = 1`, 4+2 columns wide). It sets the wrap's whole FRI envelope while occupying 3.9% of
its cells. Nobody has priced its lane count.

### 2d. Reproduce

```bash
cd ~/dev/breadstuffs
P=/Users/ember/dev/p3rec-batched-ro
G='patch."https://github.com/emberian/plonky3-recursion"'
DREGG_REQUIRE_LEAN=0 cargo test -p dregg-circuit-prove --release \
  --test leaf_vs_recursion_sweep --test recursion_tower_profile --no-run \
  --config "$G.p3-recursion.path=\"$P/recursion\"" \
  --config "$G.p3-circuit.path=\"$P/circuit\"" \
  --config "$G.p3-circuit-prover.path=\"$P/circuit-prover\"" \
  --config "$G.p3-poseidon2-circuit-air.path=\"$P/poseidon2-circuit-air\""
RAYON_NUM_THREADS=4 ./target/release/deps/leaf_vs_recursion_sweep-* \
  b_blowup_sweep_at_fixed_queries --ignored --nocapture --test-threads=1
RAYON_NUM_THREADS=4 ./target/release/deps/recursion_tower_profile-* \
  l1_leaf_wrap_over_the_deployed_ir2_leaf --ignored --nocapture --test-threads=1
```

Point `$P` at `/Users/ember/dev/p3rec-pristine` (a worktree at the pinned `fc3c6df`) for the
`before` column — that is how both columns above were taken, in the same environment. The
`--config` patch avoids touching the shared `Cargo.toml`; it is swarm-safe.

---

## 3. ⚑ The correctness verdict: byte-identical child, VK-rotating wrap

The brief asked for a byte-identical-or-flag-day verdict against the LDE-layout precedent (proof
bytes byte-identical at `b = 2..8`, no wire change, no VK rotation). **This one is not that.** It
sits one notch below, and the two halves must not be merged:

| object | verdict |
|---|---|
| **the child proof the wrap consumes** | **unchanged, bit for bit.** No field moves, no matrix changes, no opening point is added or removed, no commitment is restructured. `ro` is the same field element by associativity. |
| **what the verifier accepts** | **unchanged.** Same predicate, same soundness, same FRI input word. Completeness and soundness are both preserved by construction — this is one expression re-associated. |
| **the wrap's own circuit** | **changed.** Different op list ⇒ different `AluAir` `num_ops` and `degree_bits` ⇒ different preprocessed commitment ⇒ **different `RecursionVk` fingerprint.** |

> ### ⚑ **It is a VK-rotation flag day, not a wire-format flag day.** No serialized shape moves. Every `RecursionVk` fingerprint does — leaf wrap, fold, apex and shrink alike, because all four go through `open_input`.

### 3a. What re-emits, named

1. **Every `RecursionVk` / vk-spine value** derived from a HEAD circuit build
   (`leaf_vk_spine_host()`, `ivc_turn_chain.rs`'s spine, the fold VK pins).
2. **`chain/gnark/fixtures/apex_vk_identity.json`** — re-mint via
   `circuit-prove/tests/apex_shrink_gnark_fixture.rs::derive_deployed_apex_vk_identity_and_check_fixture`.
3. **`chain/gnark/settlement_circuit.go:170`**, the governance-pinned
   `DreggApexRecursionVk = "588720d922f1990378fae6cb8c06d08882a723f70422487e48b38098b72be92e"`
   — the anchor the derived fixture is fail-closed against.
4. **The Groth16 artifacts** — setup, `chain/contracts/DreggGroth16Verifier25.sol`,
   `settlement_groth16.json`, then the `bridge/src/ethereum.rs` calldata keccak pin.
   (The shrink's ALU table also drops a rung, so the R1CS and the setup get *cheaper*.)
5. **A devnet re-genesis** if any anchored fingerprint is on-chain.

### 3b. ⚠ Why the pin bump is NOT in this lane, stated as a decision and not a cost

`breadstuffs/Cargo.toml:370-373` still points at `fc3c6df`. The change is on
`emberian/plonky3-recursion@b471aca`, branch `lane/batched-reduced-opening`, pushed.

The reason is **not** that the re-mint is expensive — by house doctrine that would be no reason at
all. It is that item (4) ends at a **deployed on-chain verifier and its bridge pin**, which is the
short pause list's item 3 (*outward-facing and irreversible acts — anything a third party sees*),
and item (5) is a devnet re-genesis. Bumping the pin without carrying (2)–(4) through in the same
pass would leave every VK tooth red with no re-mint, which is the "red as steady state" failure the
repo has a note about. The lane's own work — the implementation, the guard, the measurement — is
done and landed, not deferred; what is handed over is a mechanical re-mint chain whose last two
steps are a deployment.

⚠ Two facts that bear on sequencing, both measured today: `metatheory` was **red** while this ran
(a sibling lane's `wip/Measure19d.lean`), so `dregg-lean-ffi`'s release gate refuses — every
measurement here used `DREGG_REQUIRE_LEAN=0`, which is sound for a circuit-shape census (the three
controls prove it) but blocks the node build the re-mint needs. And `fc3c6df` has two targets that
do not compile in the fork itself (`recursive_keccak`, `normalize_to_shape_spike`), fixed on the
fork's own `52e1fab` tip; a pin bump should probably go to a rev that carries both.

---

## 4. What this does and does not settle

1. **Lever 3(b) as written — "one sumcheck replaces the per-column ExtMuls" — is a PCS
   replacement, not a backend rewrite.** §0a. The sumcheck's terminal claim is an MLE evaluation
   of the opened values, and a Merkle leaf cannot answer it. That is the obstruction, it is real,
   and no document named it. `APEX-VERIFIER-AIR-REDUCTION.md`'s Lever D should be re-tagged from
   COORDINATION-REQUIRED (fork work) to **PCS-REQUIRED**.
2. **`leaf-vs-recursion.md` §3d's ×2.13 is the sumcheck endpoint and is not reachable over
   two-adic FRI.** The algebraic collapse that *is* reachable lands **×1.436 on wrap cells,
   ×1.651 on `Alu`, ×1.806 on `HornerAcc`** — measured, one power-of-two rung.
3. **The hashing-argument precondition moves but does not close.** A free hash goes ×1.57 → **×2.10**,
   not ×4.5. The remaining gap to ×4.5 is exactly the part that needs the PCS.
4. **The gnark verdict does not transfer, in either direction.** `HORIZONLOG.md:18344` retired the
   α-batching ask as MARGINAL after the `S_z − S_x` hoist — true, *of the gnark circuit*. The Rust
   in-circuit verifier never got that hoist, and the point-sharing half of it was never taken
   anywhere. ⚠ **And the gnark side may still have the point-sharing half open**:
   `deriveOpenInputReducedNative` recomputes `S_x` per `(matrix, point)`, so the same 1.81× applies
   to its ~0.32M `S_x` term. Small, but it is the same identity and it is right there.
5. ⚑ **A latent contract in `p3-circuit` was found and closed** (§1c) — the `HornerAcc`
   implicit-accumulator chain was an unchecked emitter convention whose violation is invisible.
   That is arguably worth more than the 1.44×: it is what any *future* reduced-opening emitter
   would have hit, silently.

### The next lever, priced by what this measurement exposed

`recompose` now sets the wrap's global max height — **2¹⁸ rows for 160,263 ops at
`npo_lanes = 1`, 6 columns wide, 3.9% of the wrap's cells**. It pins `log_global_max_height`, and
therefore the FRI envelope of everything that verifies the wrap, while carrying almost none of the
work. Its lane count has never been priced. That is the cheapest thing on the board now, and it
did not exist as a question before the `Alu` table dropped below it.

### ⚠ Substrate, said out loud

The in-circuit FRI verifier in `emberian/plonky3-recursion` is **pre-existing Rust-authored circuit
logic**, and by the house law (`project-lean-authored-air-law`) that is debt, not a foundation.
This change did **not** author a constraint: `AluAir` is untouched, no gadget was written, and the
constrained predicate is identical — it re-associates the expression an existing emitter builds.
The one *new* thing, `validate_horner_chain_contract`, is a refusal on a build-time structural
invariant, not an AIR. **Nothing here is Lean-authored, and nothing here should be quoted as
verified.**
