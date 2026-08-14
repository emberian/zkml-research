# Cross-limb binding — the vFHE #1 hole, EXHIBITED, priced, and narrowed

**Status 2026-08-14.** The hole is stated in Lean and exhibited (`breadstuffs`
`5b653ba5d`, `metatheory/Bfv/CrossLimb.lean`, `lake build Bfv` green,
`#assert_namespace_axioms Bfv` 90 → **113 theorems kernel-clean**). The closure is
priced in committed felts and permutations. The ct×pt narrowing is a verdict, not
a hope. Everything below that is a count was measured or read; everything that is
a design claim is labelled.

**House law, said out loud:** the constraint semantics here are **authored in
Lean**. No AIR constraint was written in Rust in this lane. The Rust touched was
read-only (measurement and the deployed bridge).

---

## 0. The headline, before the detail

1. ⚑ **The name was carrying two different holes with two different fixes.** The
   repo's prose ("nothing binds the limbs together" / "the extended-basis tensor +
   t/Q rounding is not expressible in any single limb") describes **provenance**
   and **expressibility**. They are independent. Closing either leaves the other
   open.
2. ⚑ **The reason nobody had exhibited it: every Lean BFV carrier in the tree
   makes the attack unrepresentable.** `Market/DarkBazaarSameOpeningPoly.lean:45`
   says so in its own residual list — *"a forged single residue row is not
   representable in this model"*. That is a true sentence about the model, and it
   is exactly why the model cannot see the wound. The first job was a carrier in
   which the forgery is an inhabitant like any other.
3. ⚑ **The first-named candidate fix is a tautology.** "A CRT-consistency relation
   over the limbs" (brief; `VERDICTS.md` §7.5) can never refuse: the CRT map is a
   **bijection**, so every limb tuple is the image of some ring element. The
   exhibited forgery is itself perfectly CRT-consistent.
4. ⚑ **The hole is a LAYOUT decision, and the correct fix is free in counts.** If
   the `L` limbs of one coefficient share a row, the row *is* the shared opening
   and provenance is closed by construction: **+0 committed felts, +0
   permutations.** The price is not the binding — it is the 2-felt BabyBear bridge
   that sharing a row forces, and that bridge is already deployed.
5. **ct×pt is genuinely narrower than recorded, on one axis and not the other.**
   Expressibility is **absent** there. Provenance **survives**, at a square root of
   the attack surface. And it closes outright when the pool is a singleton — so the
   hole is a function of *how many ciphertexts the transcript exposes*, not of the
   operation.
6. **Scope, plainly: there is at present NO ct×ct arithmetization anywhere in the
   tree to fix.** Verified by search across `circuit/`, `circuit-prove/`,
   `constraint-lowering/`, `metatheory/Market/`, `metatheory/Dregg2/Circuit/`. The
   hole is in the **design**. `Bfv/CrossLimb.lean` is what a future emitter must
   refute.

---

## 1. What the per-limb system actually pins

Setup. `Q = ∏_{i<L} q_i`; a ciphertext element lives in `R_Q = ℤ_Q[X]/(X^N+1)` and
is **stored** as `L` residue vectors — `fhegg-core/src/bfv_lean.rs:164`
`RnsPoly { rows : Vec<Vec<u64>> }`, `rows[i][j]` = coefficient `j` mod `moduli[i]`.
Deployed: `L = 3`, `FOLD_MODULI = [0xffffee001, 0xffffc4001, 0x1ffffe0001]`
(36, 36, 37 bits; `log Q = 109`), `N = 4096`.

A verifier that checks the multiply limb-by-limb checks, for each `i`:

```
out^(i) ≡ a^(i) · b^(i)   (mod q_i)
```

**It does NOT pin less arithmetic than the ring relation.** `perLimb_pins_modProd`
(Lean): with the operands held fixed, the conjunction of the `L` congruences is
*exactly* the congruence mod `∏ q_i` — the CRT isomorphism, no loss. This matters
because it says where the hole is **not**: strengthening the equations cannot
close it.

What it fails to pin is a **quantifier order**:

| | statement |
|---|---|
| honest (`BoundMul`) | `∃ source. ∀ i.  limb i checks against THAT source` |
| checked (`PerLimbMul`) | `∀ i. ∃ source. limb i checks against SOME source` |

`bound_imp_perLimb` proves the checked system is *necessary*. It is not wrong; it
is incomplete — which is why no honest-prover differential and no completeness test
can ever see it.

### Hole A — provenance. **Exhibited.**

`perLimb_not_imp_bound`, by kernel computation (`decide`). Two limbs (`q₀=3`,
`q₁=5`), one coefficient, a pool of two ciphertexts `ct₀ = (1,0)`, `ct₁ = (0,1)`.
The forgery takes limb 0 from `ct₀·ct₀` and limb 1 from `ct₁·ct₁`:

- `exhibit_perLimb` — **every per-limb equation is satisfied.** Limb 0 checks
  against `ct₀`; limb 1 checks against `ct₁`. Neither limb is anomalous.
- `exhibit_not_bound` — **no single pair from the pool works.** All four candidate
  pairs fail at some limb.
- `exhibit_bound_satisfiable` — the refuted predicate is **not vacuous** (house law:
  satisfiable *and* refutable). The honest product of `ct₀` with itself satisfies it.

And the forgery is a **wrong answer, not merely an unbound proof**
(`exhibit_accepted_value_is_dishonest`): in the reconstructed ring `ℤ/15` the
accepted output is `1`, while the only values an honest evaluation of this pool can
produce are `10`, `6` and `0`. The prover commits to a ciphertext **outside the
image of the evaluation**.

### Hole B — expressibility. **Exhibited, and it is a different hole.**

`rescale_not_limb_local`: the ct×ct rescale `⌊t·x/Q⌉` (`Bfv.rescale`, the same
integer form as `Bfv.mulPhase`) reads the **CRT reconstruction**. Two integers with
the same residue mod `q₀` have rescales that differ mod `q₀`. So limb `i`'s output
is not a function of limb `i`'s input, and **there is no per-limb equation to bind
in the first place** — however perfectly the operands are bound.

This is what `notes/archive/vfhe-shortest-path.md:47` means. It is **not** fixed by
a commitment, an RLC, or a shared opening index. Its fix is different in kind: the
rescale must be arithmetized over a representation that carries the reconstruction
(a redundant/extended basis with in-circuit reconstruction, or a single prime).

---

## 2. The candidate that is a tautology — and the one that is a layout

### CRT-consistency: not a weak fix, **not a fix**

`crt_consistency_vacuous` (Lean, general `L`, via `ZMod.prodEquivPi`): for
pairwise-coprime moduli the CRT map `ZMod (∏ qᵢ) ≃+* Π ZMod qᵢ` is a **bijection**,
so *every* limb tuple whatsoever is the image of a ring element. A "check the limbs
are CRT-consistent" gate can never refuse, on any input. The forgery of §1
reconstructs to `1 ∈ ℤ/15` and is perfectly consistent.

`deployed_moduli_pairwise_coprime` pins that this applies to the real tower, not
just the exhibit.

⚠ **A redundant-basis check is a different object and is not refuted here** — but it
does not close Hole A either, for the same reason: the auxiliary residue is also
prover-supplied, and checking it *is* the reconstruction. It is relevant to Hole B,
not Hole A.

### The real fork: **one table per limb, or limbs interleaved into one row**

This is where the whole cost lives, and it was not previously named.

- **Layout A — one table per limb.** The natural choice: each limb is its own
  ~36-bit prime field, the FHE NTT is per-limb, and `owner_batch_equations`
  (`fhegg-fhe/src/private_book_bfv_exact.rs:170`) already loops
  `for (qi, &modulus) in FOLD_MODULI.iter().enumerate()` emitting one equation
  family per modulus. **Hole A is live**: nothing in a per-limb table forces limb
  `i`'s opening index to equal limb `j`'s.
- **Layout B — limbs interleaved, one row per (poly, coefficient) position holding
  all `L` residues.** **Hole A is closed by construction.** The row *is* the object;
  `boundMul_iff_sharedSelector` (Lean) is satisfied because there is one opening
  index — the row index — feeding every limb's equation.

**Layout B forces a common field**, because a row's cells are all in one field. The
limbs are 36/36/37-bit; BabyBear is 31. The bridge already exists and is deployed:
`fhegg-fhe/src/mle_gpu.rs:479` `bridge_lanes_to_babybear` — **an injective 2-limb
base-2^30 encoding, 2 BabyBear felts per RNS residue.**

⚑ **So the price of closing Hole A is the abandonment of per-limb-native proving.**
That idea was already refuted by the field-choice lane on two-adicity grounds (the
limbs' 13/14/17 is fully consumed by the FHE NTT). This adds a *soundness* reason
to the same verdict. The two arguments converge.

---

## 3. The price, in counts

**Instrument.** Committed felts and Poseidon2 permutations, never milliseconds.
Calibrated model (`notes/low-rank-updates.md:295`, delta = 2 against measurement at
all five rungs):

```
perms ≈ (2^lb / 8) · N · (1 + 8/w),      N = w·h committed felts
```

Aspect penalty `(1+8/w)`: **1.50** at `w=16`, **1.12** at `w=64`. Deployed IR-v2
runs at `lb=6`; the live candidate is `lb=2`. Counters to reuse:
`circuit/tests/ir2_phase_profile.rs:886` (`CountingPerm`), `:235` `reset_totals`,
`:923` `counting_config` — ⚠ process-global, hold `serialize_measurement()`.

**A reference for scale** (measured, `notes/blowup-drop.md:267`, prover perms,
self-verify excluded): the whole deployed IR-v2 **transfer** proof is **217,150**
permutations at `(6,19)` and **14,295** at `(2,57)`. ⚠ That is a different circuit —
it is a magnitude reference, not an apples-to-apples comparison.

**The object.** One BFV ciphertext = 2 polynomials × 3 limbs × 4096 coefficients =
**24,576 residues**.

| | committed felts / ct | perms @ lb=6 (w=16 / w=64) | perms @ lb=2 (w=16 / w=64) |
|---|---:|---:|---:|
| Layout A, limbs in native fields | 24,576 | 294,912 / 220,201 | 18,432 / 13,763 |
| **Layout B, bridged + interleaved** | **49,152** | **589,824 / 440,402** | **36,864 / 27,525** |
| **Closure 1** (shared opening index, on Layout B) | **+0** | **+0** | **+0** |
| Closure 2 (RLC across limbs, Ext4 accumulator) | +32,768 | +393,216 / +293,601 | +24,576 / +18,350 |
| Closure 3 (cross-table logup binding, on Layout A) | ≥ +98,304 | ≥ +1,179,648 / +880,804 | ≥ +73,728 / +55,050 |

Read the table:

- **Closure 1 costs nothing.** The residues are already committed; what changes is
  that every limb's equation opens at the same index. It is a shape change to the
  checked predicate, not an extra constraint. `boundMul_iff_sharedSelector` is
  stated as an `Iff` precisely so it is visible that this **is** the honest
  predicate, not an approximation of it.
- **The bill is the bridge, not the binding.** Going from Layout A to Layout B
  doubles the ciphertext's committed felts (1 → 2 felts per residue) — a delta of
  **+220,201 to +294,912 permutations per ciphertext at lb=6** (1.01×–1.36× the
  transfer-proof reference) and **+13,763 to +18,432 at lb=2** (0.96×–1.29×). That
  is the real number, and it is the size of a whole proof.
- **Closure 2 is strictly worse than Closure 1 and buys less.** It needs the
  residues combined in one field; `L` residues of 37 bits do not fit BabyBear, so
  the accumulator must be Ext4 (4 base felts × 8192 positions = 32,768 felts/ct).
  It also delivers only a *probabilistic* binding where Closure 1 delivers a
  structural one. It is priced here because the brief named it; it is not the
  recommendation.
- **Closure 3 is the price of keeping Layout A.** Binding `L` separate tables needs
  a logup/permutation argument (≥1 Ext4 column per table over 24,576 rows). It is
  ~4× Closure 2 and ~2× the bridge it was trying to avoid. **Keeping per-limb-native
  tables costs more than abandoning them.**

**Recommendation: Layout B + Closure 1.** Cheapest, structural rather than
probabilistic, and it re-uses a bridge that is already deployed and already tested.

**Soundness error, for the closure that has one.** `rlc_binds` (Lean): if the
prover's limb vector differs from the committed one at any limb, at most `L−1`
challenges out of `|F|` accept — `2/|F|` at the deployed three-limb tower,
negligible at Ext4 (2^123.6). `rlc_binds_hypothesis_necessary` pins the failing
side, so the bound is not satisfied by a check that always passes. ⚠ The lemma sums
in **one** field; the embedding that puts 37-bit residues into that field is where
the cost lives, and the docstring says so rather than hiding it. Closure 1 has **no**
soundness error — it is an identity of predicates.

---

## 4. Does the coefficient-matmul route change the answer? **Yes, and the hole is narrower than recorded.**

`fhegg-fhe/src/bfv_coeff_matmul.rs` is ct×pt with a **public** matrix. Two verdicts,
opposite directions:

### Hole B is ABSENT. ✅

`scalarStep_limb_local` (Lean): a public integer multiplier commutes with reduction
mod every `q_i`, so limb `i` of the output is a function of limb `i` of the input.
This is the **same property `Bfv.stepR_noise_le` runs on** — the reason the
coefficient-encoded route has a *provable* noise budget (no `δ_R` factor, the
row-sum bound surviving verbatim) is also the reason it has no expressibility hole.
One property, two payoffs.

Corroborated independently in the Rust and in a prior lane: the module performs **no
RNS basis extension at all** (grep for `moduli|rns|limb` in
`bfv_coeff_matmul.rs` returns only the scalar `plaintext_modulus`), and
`notes/koalabear-limb.md:352` had already measured that *"the deployed workload
(pt-ct coefficient matmul) has no RNS basis extension at all"* and that the
CRT-reconstructing rows are **49,152 of 1,032,192 = 4.8%** of the NTT family.

### Hole A SURVIVES, at a square root. ❌

`perLimbPt_not_imp_boundPt` (Lean): with a public multiplier and the same
two-ciphertext pool, the frankenstein still passes every per-limb equation and still
matches no single ciphertext. Making one operand public removes it from the
selector space; it does not remove the other one.

| | selector space | honest | forgeries at `L=3, K=2` |
|---|---|---:|---:|
| ct×ct | `(K²)^L` | `K²` | **60** of 64 |
| ct×pt | `K^L` | `K` | **6** of 8 |

(`forgery_surface_ctct` / `forgery_surface_ctpt` / `deployed_forgery_counts`.)
A square root of the surface — narrower, still exponential in the limb count.

### And it closes when the pool is a singleton

`perLimbPt_singleton_pool_bound` / `perLimb_singleton_pool_bound`: with one
ciphertext available, the per-limb system implies the bound one outright. **The hole
is a function of how many ciphertexts the transcript exposes, not of the
operation.** At depth 1 against a single committed input there is nothing to mix.

⚠ **Deployed depth is 2** (measured, 40/40) and the blocked packing gives 132
results per multiply — so the deployed transcript is exactly the many-ciphertext
regime, and the second multiply consumes an intermediate. **The hole is live for the
deployed workload, and the singleton escape does not apply to it.**

### The narrowing, stated as a correction to the record

`VERDICTS.md` §7.5 and `SELVAGE.md` §7 carry one item. It should be two, and the
ct×pt column is not the same as the ct×ct one:

| | ct×ct | ct×pt (coeff-matmul) |
|---|---|---|
| Hole A — provenance | live, `(K²)^L` | live, `K^L` |
| Hole B — expressibility | live | **absent** |
| singleton-pool escape | yes | yes |
| deployed workload in that regime? | yes (depth 2) | yes (132 results/multiply) |

---

## 5. What the deployed per-limb system actually does today

The only live per-limb equation family in the tree is
`fhegg-fhe/src/private_book_bfv_exact.rs` — **fresh-encryption**, not multiply:
`OWNER_BATCH_EQUATION_COUNT = FOLD_MODULI.len() * COMPRESSION_ROUNDS` = **384**
equations (3 moduli × 128 Rademacher rounds), each carrying its own `modulus` field,
with `derive_signs` hashing `qi` so each limb gets independent signs.

⚑ **It is cross-limb bound — but the binding is a LAYOUT PROPERTY, not a checked
gate.** The witness coordinates `u`, `e1`, `e2` are shared column indices
(`u_base`, `e1_base`, `e2_base`) across all three limbs, and the ciphertext limbs
enter only the **public constant**. So the honest structure is Layout B already, by
accident of how the witness was laid out. Nothing *checks* that a distributed
worker used the same witness columns for all three moduli — and
`private_book_bfv_exact.rs:1-7` says a distributed backend must not substitute
caller-supplied coefficients, which is the same concern one layer up.

The Lean counterpart, `Market/PrivateBookBfvBindingAir.lean`, binds the limbs in
the **type**: `witness.u : OrderIx → CoeffIx → Int` is one signed integer vector
that `liftSigned` pushes into every RNS row. That is a faithful model of the
intended layout and an unfaithful model of the adversary — which is the whole
reason this hole survived in prose for months. Its docstring is honest about scope
(*"does not claim that a Rust emitter implements these gates"*); the gap was that
nobody had built a carrier that could disagree with it.

**This is the `documented ≠ detected` class, in our own tree**: the binding is
real, the binding is unchecked, and every instrument we had was constructed so that
it could not go red.

---

## 6. The honest remainder

Named precisely, with what each would take.

1. **`A,B` correctness — not this lane.** Untouched.
2. **The nonlinearity boundary.** `t = 2²⁰` binds any BFV polynomial nonlinearity to
   degree ≤ 2 regardless of levels; nonlinearities go through the MPC/PBS boundary.
   Nothing in this lane speaks to whether that boundary composes with the audit
   game (`FRONTIER-QUEUE.md` G6). Open, unchanged.
3. **Accumulated exactness over many steps.** `Bfv.iterR_noise_le` gives `G^T·M` on
   the ring for the public-linear path, and `Bfv.Mul` covers **one** multiply with
   its ring lift still a named gap. The depth-budget recursion with the *output*
   noise as the next *input* noise is deliberately not stated. Open, unchanged.

   ⚑ **A PREFLIGHT correction, verified at source, not relayed.**
   `swarm/PREFLIGHT.md` warns that *"`Bfv/Mul.lean` and `Bfv/Smudging.lean` are in
   NO default build target … 43 keystones are unpinned by CI"*. **That is stale.**
   Both are rooted through `Market`, which IS a defaultTarget:
   `Bfv.Mul` ← `Market/OraclePitQuadratic.lean:3` ← `Market.lean:48`, and
   `Bfv.Smudging` ← `Market/DarkBazaarCollectiveOpening.lean:59` ← `Market.lean:45`.
   Both files also carry their own `#assert_all_clean` blocks (`Mul.lean:402`,
   `Smudging.lean:539`) — a per-keystone pin, which is *stronger* than the
   namespace walk. **The only true residue** is that `#assert_namespace_axioms Bfv`
   in `Bfv.lean` does not reach them (`Bfv.lean` does not import them), so the
   namespace-wide sweep is incomplete while the per-file pins are not. I repeated
   the stale claim in an earlier draft of this note before checking; the check took
   two greps.
4. **`ε_chk` instantiation.** The audit theorem's checker is abstract; tier 2/3
   soundness are parameters until it is instantiated. Nothing here instantiates it.
   ⚠ Note the interaction this lane *does* add: a checker for "the FHE engine
   performed these ciphertext operations faithfully" must decide Hole A, and Hole A
   is invisible to any per-limb check by construction. **`ε_chk` cannot be
   instantiated limb-locally.** That is new information for that item.
5. **Hole B has no closure in this lane.** Only an exhibit. Its fix (in-circuit CRT
   reconstruction over a redundant basis, or the single prime) is unpriced.
   `FRONTIER-QUEUE.md` G1's single-prime route dissolves **both** holes and remains
   the highest-leverage answer — gated on H1's 2.4-bit margin, unchanged by this
   lane.
6. **Nothing here says the deployed Rust enforces any of it.** As everywhere in
   `Bfv/`, these are the statements an emitter would have to discharge, and the
   emitter does not exist.

---

## 7. Artifacts

- `breadstuffs` `5b653ba5d` — `metatheory/Bfv/CrossLimb.lean` (new, 23 keystones
  across three `#assert_all_clean` blocks) + one import in `metatheory/Bfv.lean` so
  it is rooted in the `Bfv` defaultTarget. `lake build Bfv` green, 1601 jobs;
  `#assert_namespace_axioms Bfv`: **113 theorems pinned kernel-clean** (was 90).
- Theorem index: `perLimb_not_imp_bound` · `exhibit_accepted_value_is_dishonest` ·
  `exhibit_bound_satisfiable` · `rescale_not_limb_local` · `perLimb_pins_modProd` ·
  `crt_consistency_vacuous` · `deployed_moduli_pairwise_coprime` ·
  `scalarStep_limb_local` · `perLimbPt_not_imp_boundPt` ·
  `perLimbPt_singleton_pool_bound` · `boundMul_iff_sharedSelector` · `rlc_binds` ·
  `rlc_binds_hypothesis_necessary` · `forgery_surface_ctct` / `_ctpt` /
  `deployed_forgery_counts`.
