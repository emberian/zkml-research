# The K≠2 proof and the Weft branch number — two obligations banked

2026-08-17. MEASUREMENT + TEETH lane. Two standing obligations, both discharged this session:
**(1)** `galois-levers.md` §6 follow-up tooth #1 — prove a wrap at the measured packing optimum
`a4/K16/rec4` (until now the ×2.011 was geometry from the prover's own extraction call, with no
proof ever minted at any K ≠ 2); **(2)** `aligned-hash-space.md` §3d [WEFT-subspace] — the branch
number of the Weft mixing layer, the one computation the note said settles whether the sketch's
structured linear layer is safe.

Everything below is `[MEASURED]` (a test/script that ran, artifact named), `[READ]` (file:line),
or `[DERIVED]` (labeled). Substrate said out loud: nothing here authors a constraint anywhere —
part 1 exercises the existing (fork-side, pre-existing Rust) prover at a new `TablePacking` value;
part 2 is a computation over the proved Lean objects' twins.

---

## 1. PART 1 — the wrap PROVES at `a4/K16/rec4`, and a forged committed cell REFUSES

**Artifact**: `breadstuffs/circuit-prove/tests/recursion_tower_profile.rs::
k16_wrap_proves_and_a_corrupted_trace_refuses` (landed `a8e8842a5`, falsifier repaired in
`44d0dea45`; hbox run log `/tank/dregg-build/hbox-rig/k16-run.log`). One leaf prove + one wrap circuit build (the deployed pipeline exactly:
`recursion_layer_over(ir2_leaf_wrap_config())` — in-circuit verify of the lb6/19q/pow16 child,
mint at lb3/38q/pow14, the same object `prove_descriptor_leaf_rotated_with_config` hands
`build_and_prove_next_layer`), then four arms in order.

### 1a. The four arms, and what each measured

| arm | claim | result |
|---|---|---|
| control | packing-invariant op census reproduces the grid's control TO THE DIGIT before anything else is read | ✅ Alu 267,526 / HornerAcc 216,330 / in-circuit perms 38,168 / recompose 160,263 |
| geometry | shape extraction reproduces the measured cells | ✅ deployed `a4/K2` 40,554,496 (max 2¹⁸) → `a4/K16/rec4` **28,971,008** (max **2¹⁶**), ×1.400; Alu = 2¹⁴ × (216+157) |
| prove+verify | `prove_next_layer` at the K16/rec4 params; verified by the PRODUCTION entry `verify_recursive_batch_proof_with_config` (which reads packing off the proof — `batch_stark_prover.rs` `rebuild_airs_pvs_common` uses `proof.table_packing`) | ✅ proved and production-verified; the proof's own embedded packing asserts K16/a4/rec4 (falsifier guard against a params-ignoring prover) |
| VK rotation | the deployment class is measured, not asserted: a deployed-packing prove of the SAME circuit must verify AND fingerprint differently | ✅ deployed vk `73f8dc7d…` ≠ K16 vk `6fdd7b64…` — the retune IS a VK rotation |
| refusal | a forged COMMITTED chain cell at the new geometry must refuse | ✅ REFUSED at VERIFY: `OodEvaluationMismatch { index: Some(2) }` — instance 2 = the **Alu table**: the packed-row constraint quotient, exactly the rail the K16 repack had to keep (see 1b — the first mutation was a no-op and the tooth caught it) |

**Run twice, two machines, identical counts and identical VK fingerprints** `[MEASURED]`:

| box | conditions | K16 prove | K2 prove | verdicts |
|---|---|---:|---:|---|
| laptop (M2 Max) | load ~68, RAYON=4 | 2.6 s | 5.0 s | all four arms green |
| hbox (i9-12900) | `/tank/dregg-build/hbox-rig` detached clone @`44d0dea45`, `swarm-build` (P-cores, 48G cgroup), `-C target-cpu=native`, RAYON=4, load 2→24 (a CI job arrived mid-run) | 2.7 s | 10.3 s | all four arms green, whole test 25.2 s |

Census (Alu 267,526 / HornerAcc 216,330 / perms 38,168), cells 28,971,008, and both VK
fingerprints reproduce byte-identically across the two architectures — the counts-primary
discipline demonstrated by the instrument again. Wall clocks are labeled upper bounds; the
consistent direction (K16 wrap prove ~2–4× faster than deployed K2) is the cells win plus the
2¹⁸→2¹⁶ height drop arriving in the wrap's own LDE, not a defensible magnitude.

### 1b. ⚑ THE INSTRUMENT LESSON — a mid-chain Horner `out` is NOT a committed cell

The first refusal arm forged a MID-chain `HornerAcc` `out` (Alu trace + witness bus, consistently)
and its "the corrupted trace VERIFIED — unsound!" assert fired. **The prover was not unsound; the
falsifier was dead.** `[READ]` `p3rec-batched-ro/circuit-prover/src/air/alu_air.rs:471`
`trace_to_matrix`: a `PackedHorner(first, k)` group commits the FIRST op's `a,b,c`, the per-step
`(a_t, c_t)` pairs, the **recomputed** intermediate accumulators (recomputed from operands — NOT
copied from `trace.values[i][3]`), and the LAST op's `out`. A mid-chain `out` in the `AluTrace`
struct feeds nothing committed; mutating it produces a byte-identical proof that verifies
legitimately.

Two consequences, both banked in the revised test:

* the mutation site is now a chain-TAIL `out` (last op of its chain ⇒ last op of its packed
  group ⇒ the committed `out_last`, bus-carried via `mult_out`);
* the arm now carries an **artifact-level falsifier**: a clean baseline is proved through the
  same inline path, and the forged proof's postcard bytes must DIFFER from it — a mutation that
  never reaches the committed transcript refuses to conclude instead of reading a verdict.
  (This is `minted-a-falsifier-that-stopped-falsifying` arriving in a new costume: "mutation
  asserted first" must mean asserted AT THE COMMITTED ARTIFACT, not at the convenient struct.)

With the corrected site: the forged proof's bytes differ from clean, and
`verify_recursive_batch_proof_with_config` **refuses**. ✅

### 1c. Verdict and the flag-day list if `a4/K16/rec4` is to land

**The ×2.011 cumulative is now BANKED**: proven at the new geometry, refusing when forged, VK
rotation measured. To make it the deployed default (`ProveNextLayerParams::default()` /
`prove_recursion_layer_auto_*`'s params — `gpu_backend.rs` call sites), the re-mint chain is
`sumcheck-batched-opening.md` §3a's, plus one item that lane did not have:

1. every `RecursionVk`/vk-spine value derived from a HEAD circuit build (leaf spine, fold pins);
2. `chain/gnark/fixtures/apex_vk_identity.json` (re-mint via `apex_shrink_gnark_fixture.rs`);
3. the governance pin `chain/gnark/settlement_circuit.go` `DreggApexRecursionVk`;
4. the Groth16 artifacts + `bridge/src/ethereum.rs` calldata keccak pin;
5. devnet re-genesis for any on-chain anchored fingerprint;
6. ⚑ **new vs the §3a list**: `rec4` moves the wrap's own global max height 2¹⁸ → 2¹⁶, so the
   wrap's OWN FRI envelope loses two fold rounds — the parent's in-circuit verifier changes
   SHAPE, not just fingerprint (`galois-levers.md` §3c bullet 3). The apex VK re-mints anyway
   (item 1), but the parent-layer circuit shape change is why this is a coordinated flip, not a
   per-layer knob.

Child proofs are byte-identical throughout (measured: the packing grid's op-census control, and
arm 3's proofs were both minted over the same inner proof).

---

## 2. PART 2 — [WEFT-subspace] SETTLED: branch(Weft mixing, t=24) = 6, EXACT

**Artifact**: `~/src/ring-ro-hash/weft_branch.py` (versioned; run log
`weft-branch-run.log`, ~7 s). Adapted from `design_branch_frontier.py`'s
branch-by-rank-deficient-submatrix method, with two exact passes per side and a duality trick
that makes the certification total.

### 2a. The concrete object, pinned

* Field: GF(2³²) as the Fan–Paar tower, packed 32-bit ints — a computational twin of
  `minidregg/Theory/BinaryTowerFanPaar.lean` (`fpGen_base`/`fpGen_step`/`towerMulStep`), with
  the relations `x₀² = x₀+1`, `x_{k+1}² = x_k·x_{k+1}+1` asserted plus field self-checks
  (assoc/comm/distr, inverses, Fermat; 200 samples).
* Mixing layer: the LCH novel-basis EVALUATION map of `Selvage/AdditiveBaseFold.lean`'s
  `novelPack`: state = coefficients on `X̂_c = ∏ Ŵᵢ^{cᵢ}`; the un-normalized `Ŵᵢ` from the
  `q_β(X) = X²+βX` recursion **is** the monic subspace vanishing polynomial `sᵢ` of
  `Vᵢ = span(β₀..β_{i−1})` (composition of monic linearized q's; normalization is a diagonal
  scaling and cannot move a branch number).
* Stage-0 Weft width t = 24 (rate 16 + capacity 8): `M[j][i] = X̂ᵢ(xⱼ)`, points = the first 24
  of the dim-5 domain enumeration. Domain basis `βⱼ = 2^j` (the packed Fan–Paar basis; points
  are the integers 0..23) — [ASSUMED-BY-THIS-LANE as the natural binius-style instantiation,
  stated]; a sensitivity arm re-ran everything at 3 random independent bases: **identical
  result**, because the structure driving it is basis-free (below).

### 2b. Method — exact, not certified-to-w

`branch(M) = branch(M⁻¹)` (codeword `(v, Mv) ↔ (Mv, v)`), and any codeword with
`wt_in + wt_out = B` has `min(wt_in, wt_out) ≤ ⌊B/2⌋`. Four passes compute EXACTLY the minimum
over all codewords with min-side ≤ 2: wt=1 (column zero counts) and wt=2 (projective-ratio
grouping — the exact max simultaneous zeros for every column pair) on M and on M⁻¹. The
four-pass minimum came out **6**, and ⌊(6−1)/2⌋ = 2, so any strictly better codeword would have
min-side ≤ 2 and would have been found: **branch = 6 is exact and certified, not a bound.**

### 2c. The numbers

| layer | branch | status |
|---|---:|---|
| **Weft mixing (novel-eval, t=24, GF(2³²))** | **6** | EXACT, certified; witness = span{X̂₁₆, X̂₂₀} (= `s₄·(s₂−c)`), 20 zeros; basis-independent (3 random bases identical) |
| same, 32-point full-coset variant | ≤ 8 | witness `s₄(s₃−c₃)(s₂−c₂)`, support {16,20,24,28}, 28 zeros; min-side ≤ 2 exhausted at ≥ 10; min-side-3 shapes not exhausted |
| Poseidon2 M_E t=16 (the deployed hash's own layer, BabyBear) | **8** | EXACT (witness = dense 4-block u with M4u=e₀ → (4,4); min-side ≤ 3 exhausted ≥ its value) |
| Poseidon2 M_E t=24 (same width as Weft) | ≤ 10 (= 10 by block analysis) | witness (4,6); min-side ≤ 3 exhausted at ≥ 10; only (4,4)/(4,5)/(5,4) shapes below 10 uncertified |
| MDS bound at t=24 | 25 | Cauchy-programmed dense layer attains it by theorem at every q (`design_branch_frontier.py` Part A) |
| random 24×24 control, same instrument | passes report 25 | the instrument distinguishes structure from genericity |

### 2d. ⚑ Why 6 — and the finding that is WORSE than the number

The branch-6 witness is not an accident of the instance; it is the subspace-polynomial structure
itself, which is the exact thing the alignment thesis wanted to reuse:

* `X̂₁₆ = s₄` vanishes on ALL of V₄ = the first 16 evaluation points (wt-1 input, wt-8 output:
  B = 9); `s₄·(s₂ − s₂(x₁₆))` has novel support {16, 20} and vanishes on 20 of the 24 points
  (B = 6). Every ingredient is basis-free: the domain enumeration always contains V₄ and a
  V₂-coset of its complement.
* ⚑⚑ **The matrix is block-triangular along the subspace flag** (asserted in-script): for
  b = 1..4, every `X̂ᵢ` with i ≥ 2^b vanishes on V_b, so the lane subspace
  `{coeff support ⊆ [2^b, 24)}` maps INTO `{point support outside V_b}` — which is the SAME
  lane set {2^b..23} on the output side. And Weft's S-box is lane-wise `x⁻¹` with 0 ↦ 0, which
  **preserves every zero-pattern lane subspace**. So the round map (S-box ∘ mixing) carries a
  **4-deep nested chain of invariant lane subspaces** — lanes ≥ 2, ≥ 4, ≥ 8, ≥ 16 — broken only
  by round-constant addition. That is the 2026/306 subspace-trail wound and the Grassl
  invariant-subspace shape, present BY CONSTRUCTION before any cryptanalysis is attempted: the
  alignment thesis ("make the hash's mixing the code's transform") imports the code's
  triangularity, and triangularity is the opposite of diffusion.

### 2e. The Chaghri axis, answered honestly

The task's caveat ("if the branch number is good but the Frobenius-sparsity matches Chaghri's,
say so") inverts here — the branch number is bad — but the axis is worth recording: the
novel-eval mixing as specified is **K-linear** (evaluation is linear over the coefficient field;
the butterflies are twiddle-multiplies and XORs), i.e. it spends **zero** Frobenius terms.
Chaghri's coefficient-grouping recurrence runs on layers that are linearized polynomials
(sums of Frobenius powers) per word; it does not start in-kind against a multiplication-only
matrix. So Weft's death is not Chaghri's death: it is the Starkad/HADES/Mε death (structured-
for-cost linear layer), delivered at branch 6/25 with an invariant flag attached.
[WEFT-coeffgroup] is therefore MOOT for this mixing layer as specified (nothing to group), and
would only revive on a variant that reintroduces linearized terms.

### 2f. VERDICT — [WEFT-subspace] resolved: the sketch AS WRITTEN is killed; the fallback is priced as the design

> ⚑⚑ **CORRECTED SAME DAY — `notes/weft2.md` (`~/src/ring-ro-hash/weft2_structure.py`).
> The kill STANDS. The reason below does NOT.** (1) **Branch 6 is not disqualifying**:
> one active `x⁻¹` at GF(2³²) is worth 30 bits on *both* sides (δ=4 and |W| = 2^(n/2+1),
> both measured exhaustively at n=8), so branch 6 = 180 bits per 2 rounds vs a 128-bit
> bar — and **Poseidon2's own internal layer is branch 2 and ships**
> (`ring-hash-design.md:326`). The Poseidon2 rows in §2c are also
> **cross-characteristic** — `M_E`'s {1,2,3} entries collapse in char 2, and the char-2
> reduction reads ≤ 8. (2) ⚑ **The flag is 5 deep, not 4**: `weft_branch.py:300` loops
> `range(1, 5)`, and the skipped `b = 0` level is `row 0 of M = e₀` — **output lane 0
> equals input lane 0**, an autonomous 32-bit quotient `x₀ ↦ x₀⁻¹ + c₀`. **Round
> constants break invariant subspaces but NOT invariant quotients.** That is the actual
> kill; `B_l = 2` (the linear branch, never computed here) is its shadow. (3) A third,
> unrecorded defect: with `βⱼ = 2ʲ` every entry of M lies in **GF(2⁸)** (max 253), so
> `(GF(2⁸))²⁴` = 2¹⁹² is round-invariant unless the *constants* leave GF(2⁸).
> ⭐ (4) The fallback below is **not** the only live form: evaluating on an affine
> **coset** (same butterflies, shifted twiddles, zero ops) gives `B_d = 8` EXACT with
> zero invariant subspaces either side — **one transform, prize intact**.

**Branch 6 against an MDS bound of 25, below even Poseidon2's non-MDS external layer at both
widths (8 at t=16, ≤10 at t=24), with a 4-deep round-invariant lane-subspace flag aligned with
the 0-fixing S-box.** The aligned-hash note's own fallback clause ("Weft composes the transform
with a cheap dense layer and loses some of the sharing — that fallback must be priced, not
assumed away") is now the only live form: the mixing layer cannot be the bare encoder transform.
What survives of the alignment thesis:

* the S-box half (inverse S-box, degree-3 witnessed relation, F2-degree n−1) is untouched by
  this measurement;
* the shared-circuitry prize survives only in the composed form
  `dense-mixing ∘ novel-eval` — where the novel-eval factor buys shared butterflies but the
  dense factor (Cauchy-programmed = MDS by theorem, branch 25) is what carries diffusion, i.e.
  the "ONE proved linear object in the TCB" consequence is lost: there are two again;
* a kill is a fine outcome; this one is sharp enough that no further Weft work should precede a
  redesign of §3b's mixing line, and [WEFT-integral]/[WEFT-groebner] should not be run against
  the dead layer.
* ⚑ *(2026-08-17, successor lane)* — the composed fallback named above was then measured and
  **also killed** (branch(D·E) ≤ 11, branch(E·D) ≤ 21 vs 25, `ring-ro-hash@04d0d95`); the
  surviving form of the alignment is the **systematic-RS matrix** `V₂·V₁⁻¹` (the same
  butterflies, evaluated on a DISJOINT point set — MDS by theorem, Mark-32's own §3.3
  construction), and the char-2 hash slot itself is dissolved for now by the
  recursion-scenario check. Do not act on this section's fallback clause;
  see `notes/post-weft-hash.md`.

---

## 3. Obligation-table updates written into the source notes

* `aligned-hash-space.md` §3d [WEFT-subspace]: **RESOLVED — killed as specified** (branch 6/25,
  invariant flag; this note §2).
* `galois-levers.md` §6 follow-up tooth 1: **DONE** (this note §1) — remaining: the Lean lemmas
  (tooth 2) and the dedicated chain table (tooth 3), unchanged.

## 4. Reproduce

```bash
# Part 1 (laptop; hbox run via /tank/dregg-build/hbox-rig at the same SHA):
cd ~/dev/breadstuffs
P=/Users/ember/dev/p3rec-batched-ro
G='patch."https://github.com/emberian/plonky3-recursion"'
DREGG_REQUIRE_LEAN=0 cargo test -p dregg-circuit-prove --release \
  --test recursion_tower_profile --no-run \
  --config "$G.p3-recursion.path=\"$P/recursion\"" \
  --config "$G.p3-circuit.path=\"$P/circuit\"" \
  --config "$G.p3-circuit-prover.path=\"$P/circuit-prover\"" \
  --config "$G.p3-poseidon2-circuit-air.path=\"$P/poseidon2-circuit-air\""
RAYON_NUM_THREADS=4 ./target/release/deps/recursion_tower_profile-* \
  k16_wrap_proves_and_a_corrupted_trace_refuses --ignored --nocapture --test-threads=1 --exact

# Part 2:
cd ~/src/ring-ro-hash && python3 weft_branch.py
```
