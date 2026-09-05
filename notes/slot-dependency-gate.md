# The slot-dependency gate — the ideal-quotient gate was insufficient, and both candidates pass the real one

2026-09-05. Written by the coordinator (Opus) from the lane's script output: the
Fable lane that built `notes/ring-hash-scripts/slot_dependency_gate.py` reached the
usage wall before writing its note, so the script and its run are the evidence here
and the Lean half (`Selvage/CrtSlotSeparability.lean`) was never started.

## 0. Why a second gate

`ideal_quotient_gate.py` asks, per CRT ideal `I_k`, whether `∃ x ≡ y (mod I_k)` with
`F(x) ≢ F(y) (mod I_k)`, and calls a map an *escape* when that holds at all eight
`k`. An external reviewer's correction, verified here at the algebra level:

- For `R_q ≅ (F_{q²})^8` a **ring-polynomial map acts slot-by-slot**, and `σ_e` is
  ring-polynomial **iff `e ∈ ⟨q⟩ = {1, 31}` mod 32** — so `σ₃₁` is the Frobenius
  (what last night's gate found) and `σ₅`, `σ₂₅`, `σ₁₇` are not.
- **But "not ring-polynomial" is not "mixes slots".** A bare `σ₅` merely *permutes*
  the eight slots and **passes the old gate at all eight ideals** while its
  dependency matrix is a permutation matrix. The old gate cannot see the difference
  between diffusion and a relabelling.
- The reviewer's composition theorem: rounds built only from (1) slotwise nonlinear
  maps, (2) `R_q`-linear mixing among state words, and (3) **one global `σ_e`
  applied to every word** compose to a **slot-separable** map `F(x)_i = f_i(x_{π(i)})`
  — a one-slot input difference stays one-slot forever, a two-query distinguisher
  against an ideal permutation.

The replacement instrument is the dependency matrix
`Dep_ij(F) ⟺ ∃ x, y : (∀ k ≠ j, x_k = y_k) ∧ F_i(x) ≠ F_i(y)`.

## 1. What ran

`notes/ring-hash-scripts/slot_dependency_gate.py`, at the real modulus
`q = 2⁶⁴ − 257`, over the eight CRT slots, per state word and whole state, by
sampling (a `0` entry is **not observed**, not proved absent). σ-Poseidon is
`sigma_poseidon.frog_like` (t = 9, R_F = 8, R_P = 22, α = 7, σ every round); the
gadget-Feistel is `design_gadget_feistel.Feistel` (w = 4 per branch, B = 2¹⁶,
K = 4, P = 2, NR = 16).

## 2. Results

**The reviewer's counterexample, reproduced.** Bare automorphisms are permutation
matrices — `σ₅`, `σ₂₅`, `σ₁₇` derangements (nnz 8, one in-slot per out-slot);
`σ₃₁` the identity permutation (componentwise, as the Frobenius must be). Each
passes the old gate.

**Our σ-layer is not of the reviewer's type (3).** `x + c·σ₅(x)` has nnz 16, two
in-slots per out-slot — the composition theorem does not apply to it, which is why
the whole round function had to be measured rather than argued.

**σ-Poseidon reaches FULL whole-state dependency at 7 rounds of 30.** Cumulative
`nnz`: 1 round 16, 3 rounds 24, 4 rounds 40, 5 rounds 56, **7 rounds 64 = FULL**,
and full thereafter through round 30. Per-word 72×72 saturates at 5,184/5,184 on
the same round. **So the deployed schedule is not slot-separable, and it carries
23 rounds of margin past the point where every output slot depends on every input
slot.** The reviewer's concern is real about the *gate*, and does not bite our
*design*.

**The gadget-Feistel is full immediately.** `G⁻¹` alone is already FULL at the slot
level (the digit map is not a ring map); one round FULL, per-word 64×64 saturating
by 3 rounds.

## 3. The actionable finding: the exponent schedule, not the layer, sets the speed

| schedule | first FULL |
|---|---|
| `σ₅` every round (deployed) | **7 rounds** |
| exponents `(5, 25, 17)` cycling | **3 rounds** |
| reviewer's `L = (I+2σ⁴)(I+2σ²)(I+2σ)` | 1 layer (3 rows), per-word 576/5,184 |
| `(I + c₁σ₅ + c₂σ₂₉)`, 3 rows | 1 layer |
| same, 2 rows (control) | nnz 48 — not full |

Cycling the automorphism exponent instead of repeating `σ₅` **more than halves the
rounds to full dependency at identical cost per round** — the σ-layer's shape is
unchanged, only which exponent each round uses. That is a free structural
improvement if the margin analysis wants it, and it is the shape Definition 9's
two automorphism channels already permit (`ring-hash-design.md` §2.0).

## 4. What is NOT established

- Full dependency is a **necessary structural check, not a security proof**; formal
  derivatives alone are insufficient (Frobenius maps can have vanishing derivatives
  and still depend on their input).
- Sampling gives no absence proof; a `0` is "not observed".
- The Lean half was never written. **Standing work**: `Selvage/CrtSlotSeparability.lean`
  — (a) a map over `∏ K_i` is ring-polynomial iff componentwise, and an algebra
  automorphism is componentwise iff it fixes every primitive idempotent (instance:
  `σ_e` polynomial ⟺ `e ∈ ⟨q⟩`); (b) slot-separability is closed under composition
  and contains types (1)–(3), with `x + c·σ₅(x)` exhibited as *not* separable;
  (c) `oldGate_passed_by_slotPermutation` — the reviewer's counterexample as a
  theorem.
- The cost comparison between our σ-rows and the reviewer's `L` at equal
  full-dependency depth is measured only in dependency terms here, not in rows or
  constraint cells.

## 5. The standing gate, for BRIEF 3

> Re-run `slot_dependency_gate.py` on any change to a σ-layer exponent, the gadget,
> the round schedule, or the modulus. The ideal-quotient gate is necessary and
> **not sufficient**: a pure slot permutation passes it. The bar is full
> whole-state dependency well inside the round count, and the deployed σ-Poseidon
> meets it at 7 of 30.
