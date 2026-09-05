# Exceptional sets in local rings, and the fixed-weight sets of GR(4, φ(3^a)) — in Lean

2026-09-04. Lean 4 lane for the `ShortExceptionalCyclotomicTower` ingredient of the inert-cyclotomic-tower
work (`notes/inert-cyclotomic-tower.md`, harness `scratchpad/joint_algebra_checks.py`). Two new files in
`~/dev/minidregg/Theory/`, sorry-free, every headline theorem pinned to `[propext, Classical.choice,
Quot.sound]` by `#guard_msgs`, import boundary green:

- `Theory/ExceptionalSetLocalRing.lean` (296 lines, 19 pins) — the general lemma and its ZMod 4 teeth.
- `Theory/CyclotomicExceptionalSet.lean` (632 lines, 28 pins) — the Galois-ring tower, the fixed-weight
  sets, the count, conductors 9 and 6561, the negacyclic falsifier, the operator-norm bound.

Neither is yet imported from `Theory.lean` (the lane was told to touch only new files); two `import`
lines there make them part of the umbrella build.

## 1. The general lemma (any local ring)

Definition: `IsExceptional (A : Set R) : Prop := ∀ a ∈ A, ∀ b ∈ A, a ≠ b → IsUnit (a - b)`.

Statements, copied:

```lean
theorem injOn_of_isExceptional [Ring S] [Nontrivial S] (f : R →+* S) {A : Set R}
    (hA : IsExceptional A) : Set.InjOn f A
theorem isExceptional_of_injOn [Field S] (f : R →+* S) [IsLocalHom f] {A : Set R}
    (hA : Set.InjOn f A) : IsExceptional A
theorem isExceptional_iff_injOn [Field S] (f : R →+* S) [IsLocalHom f] {A : Set R} :
    IsExceptional A ↔ Set.InjOn f A
-- at the residue map of a local ring R:
theorem isUnit_sub_of_injOn_residue {A : Set R} (hA : Set.InjOn (residue R) A) :
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → IsUnit (a - b)
theorem isExceptional_iff_injOn_residue {A : Set R} : IsExceptional A ↔ Set.InjOn (residue R) A
theorem card_le_card_residueField [Fintype (ResidueField R)] {A : Finset R}
    (hA : Set.InjOn (residue R) A) : A.card ≤ Fintype.card (ResidueField R)
theorem card_le_card_residueField_of_isExceptional [Fintype (ResidueField R)] {A : Finset R}
    (hA : IsExceptional (A : Set R)) : A.card ≤ Fintype.card (ResidueField R)
theorem card_le_two_of_card_residueField_eq_two [Fintype (ResidueField R)]
    (h2 : Fintype.card (ResidueField R) = 2) {A : Finset R} (hA : IsExceptional (A : Set R)) : A.card ≤ 2
```

The lemma is stronger than asked: it is an *iff*, and the `⇐` direction needs only a local
homomorphism into a field (not the residue map specifically), which is what the cyclotomic instance
uses. The `F_2` corollary is the negacyclic obstruction of `galois-ring-stack.md` §2 stated in general.

Witness / falsifier / inhabitation, all on Mathlib's real `ZMod 4`:

- Inhabitation: **Mathlib has no `IsLocalRing (ZMod 4)` instance** (none for `ZMod (p^k)` at rev
  1c2b90b); `instIsLocalRingZMod4` supplies it by `decide` over the 16 pairs of
  `IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add` after rewriting `IsUnit` to `∃ c, a * c = 1`. Also
  `finite_residueField : [Finite R] → Finite (ResidueField R)` (Mathlib does not find it because
  `ResidueField` is a `def`).
- Witness: `isExceptional_zero_one : IsExceptional {0, 1}`, `injOn_residue_zero_one`.
- Falsifier (the injectivity hypothesis is load-bearing): `residue_two_eq_residue_zero`,
  `not_injOn_residue_zero_two`, `not_isUnit_two_zmod4`, `not_isExceptional_zero_two`.
- Sharpness: `card_residueField_zmod4 : Nat.card (ResidueField (ZMod 4)) = 2`, hence
  `card_le_two_of_isExceptional_zmod4` from the general theorem, AND
  `card_le_two_of_isExceptional_zmod4_by_decision` by exhaustive decision over all 16 subsets — two
  independent derivations of the same statement, sibling-file style.

## 2. The cyclotomic instance — route: Mathlib quotient, NOT an explicit finite model

Mathlib's `Polynomial` is noncomputable, so `decide` cannot run inside `AdjoinRoot`. But every step
needed is a uniform degree/coefficient argument, so doing it once over `AdjoinRoot` gave the *general*
theorems (any prime `p`, any `n` with `p ∣ n ∣ p^e`, any monic `f` with `f mod p` irreducible, any
weight `h`), where a `Fin 6 → ZMod 4` model would have given one 4096-element table. `decide` is used
where it is the right tool: `ord₉(2) = 6`, `φ(9) = 6`, `2 ∣ 4 ∣ 2²`, subset membership for the witness,
and `powMod` at 6561.

The tower `(ZMod n)[X]/(f) → F_p[X]/(f mod p)`:

```lean
abbrev red (hpn : p ∣ n) : ZMod n →+* ZMod p := ZMod.castHom hpn (ZMod p)
noncomputable def toResidue (hpn) (f : (ZMod n)[X]) : AdjoinRoot f →+* AdjoinRoot (f.map (red hpn))
theorem toResidue_surjective : Function.Surjective (toResidue hpn f)
theorem pow_eq_zero_of_toResidue_eq_zero (hnp : n ∣ p ^ e) {x} (hx : toResidue hpn f x = 0) : x ^ e = 0
theorem isLocalHom_toResidue (hnp : n ∣ p ^ e) : IsLocalHom (toResidue hpn f)
theorem isLocalRing_adjoinRoot (hnp : n ∣ p ^ e) [Fact (Irreducible (f.map (red hpn)))] :
    IsLocalRing (AdjoinRoot f)
```

Mechanism: `ker (ZMod n → ZMod p) = (p)` (`eq_mul_of_red_eq_zero`), `Polynomial.ker_mapRingHom`
lifts it to `(C p)`, so the kernel of `toResidue` is nil (`p^e = 0`); a surjection with nil kernel is a
local hom (`IsNilpotent.isUnit_one_add`); `RingHom.domain_isLocalRing` finishes.

Fixed-weight sets:

```lean
noncomputable def indicatorPoly (S : Finset ℕ) : R[X] := ∑ i ∈ S, X ^ i
noncomputable def weightSet (f : R[X]) (h : ℕ) : Finset (AdjoinRoot f) :=
  (Finset.powersetCard h (Finset.range f.natDegree)).image (fun S => AdjoinRoot.mk f (indicatorPoly S))
theorem isExceptional_weightSet (hnp : n ∣ p ^ e) [Fact (Irreducible (f.map (red hpn)))]
    (hf : f.Monic) (h : ℕ) : IsExceptional (weightSet f h : Set (AdjoinRoot f))
theorem card_weightSet_le_card_residueField ... : (weightSet f h).card ≤ Fintype.card (ResidueField (AdjoinRoot f))
```

Instance at conductor 9 (`GR4Cyc9 := AdjoinRoot (cyclotomic 9 (ZMod 4))`, residue field F₆₄):
`orderOf_two_mod9`, `irreducible_cyclotomic_9_zmod2` (via the sibling's inertia bridge
`irreducible_cyclotomic_of_orderOf_eq_totient`), `GR4Cyc9_isLocalRing`,
`isExceptional_weight_one_GR4Cyc9` (`{X^j : j < 6}`), `isExceptional_weight_two_GR4Cyc9`
(`{X^i + X^j : i < j < 6}`), and the concrete witness
`isUnit_witness_GR4Cyc9 : IsUnit (mk Φ₉ (1 + X) - mk Φ₉ (1 + X^2))`.

Falsifier (irreducible-mod-p is load-bearing): over the negacyclic `(ZMod 4)[X]/(X² + 1)`,
`not_isUnit_root_sub_one : ¬ IsUnit (root - 1)` — the weight-1 set `{1, X}` is not exceptional.
Proof by the same tower: the image in `F₂[X]/(X²+1) = F₂[X]/((X+1)²)` is `X + 1`, nonzero
(`mk_ne_zero_of_natDegree_lt`) and square-zero (`X_sub_one_sq_zmod2`), so not a unit; units map to units.
This is `¬IsUnit` in Mathlib's real quotient, not in a hand-rolled model.

## 3. Counting — general theorem, not instance-only

```lean
theorem indicatorPoly_injective [Nontrivial R] : Function.Injective (indicatorPoly (R := R))
theorem mk_eq_mk_of_natDegree_lt [Nontrivial R] {f : R[X]} (hf : f.Monic) {p q : R[X]}
    (hp : p.natDegree < f.natDegree) (hq : q.natDegree < f.natDegree)
    (h : AdjoinRoot.mk f p = AdjoinRoot.mk f q) : p = q
theorem mk_indicatorPoly_injOn [Nontrivial R] {f : R[X]} (hf : f.Monic) (h : ℕ) :
    Set.InjOn (fun S => AdjoinRoot.mk f (indicatorPoly S)) (Finset.powersetCard h (Finset.range f.natDegree))
theorem card_weightSet [Nontrivial R] {f : R[X]} (hf : f.Monic) (h : ℕ) :
    (weightSet f h).card = Nat.choose f.natDegree h
```

Counting needs neither `p` nor irreducibility: the monomials `X^0..X^{d-1}` are independent mod any
monic `f` of degree `d` over any nontrivial commutative ring (`Monic.not_dvd_of_natDegree_lt`; the
`modByMonic` route, no domain hypothesis — this matters because `(ZMod 4)[X]` is not a domain).
Instances: `card_weightSet_GR4Cyc9 : |A_h| = C(6, h)`, values 6 and 15.

## 4. The deployment conductor 6561 — proved, not just counted

`orderOf_two_mod6561 : orderOf ((2 : ℕ) : ZMod 6561) = 4374` is beyond `decide` on `ZMod 6561` (the
elaborator refuses `2^4374`, `maxRecDepth`), so the three modular powers `2^4374 ≡ 1`, `2^2187 ≡ 6560`,
`2^1458 ≡ 2188` go through the sibling's kernel-evaluated `powMod` and its bridge
`natCast_pow_eq_one_iff_powMod` (`decide`, no `native_decide`). Hence
`irreducible_cyclotomic_6561_zmod2`, `GR4Cyc6561_isLocalRing` (`GR(4, 4374)`),
`isExceptional_weight_sixteen_GR4Cyc6561` — **the ≈2^149 challenge set has pairwise-unit differences,
as a theorem** — and `card_weightSet_GR4Cyc6561 : |A_16| = Nat.choose 4374 16`.

## 5. The coefficient operator norm over ℤ (item 4, a different carrier)

`phi3Shift r m v` is the harness's `phi3_shift` (`rotCoeff` = rotate by `m` in the cyclic ring
`X^{3r} = 1`, then fold `X^{2r+j} = -X^{r+j} - X^j`), defined over `Fin (2r) → ℤ`.

```lean
theorem abs_phi3Shift_le (r m : ℕ) (v : Fin (2 * r) → ℤ) {B : ℤ} (hv : ∀ j, |v j| ≤ B)
    (i : Fin (2 * r)) : |phi3Shift r m v i| ≤ 2 * B
theorem abs_phi3Shift_le_conductor9 (m : ℕ) (v : Fin 6 → ℤ) ... : |phi3Shift 3 m v i| ≤ 2 * B
```

General in `r`, `m`, `v`; decide-free (each output coordinate is a difference of two rotated
coordinates). This is the `‖X^m·v‖_∞ ≤ 2‖v‖_∞` bound that the harness enumerates at `r = 3`.

## 6. What generalizes, what is instance-only, what remains named

- General (any `p`, `n` with `p ∣ n ∣ p^e`, monic `f`, weight `h`): the local-ring lemma and ceiling
  (§1), the tower and `isLocalRing_adjoinRoot`, `isExceptional_weightSet`, `card_weightSet` (§2–3),
  the norm bound (§5). Note `Z_{2^64}` is `n = 2^64, e = 64`: nothing here is specific to `ZMod 4`
  beyond the two instantiated conductors.
- Instance-only: `IsLocalRing (ZMod 4)` (by decision; a general `IsLocalRing (ZMod (p^k))` is easy
  from the same tower with `f = X` but was not needed), the ZMod 4 teeth, conductors 9 and 6561
  (each needs its own `ord(2)` computation — the sibling's family law does the `3^k` tower for
  KoalaBear, not for `p = 2`; `ord_{3^k}(2) = φ(3^k)` for all `k` by lifting-the-exponent from
  `v₃(2² − 1) = 1` would be the general statement, not attempted).
- Named obligations (not proved): **`phi3Shift_spec`** — that `phi3Shift` agrees with multiplication
  by `X^m` in `AdjoinRoot (X^{2r} + X^r + 1)` over ℤ (the bound is about the explicit function, as the
  brief allowed); and the residue-field cardinality `|ResidueField GR4Cyc9| = 64` (the ceiling is
  stated against `Fintype.card (ResidueField _)` abstractly; the count 64 was not needed for any tooth).
