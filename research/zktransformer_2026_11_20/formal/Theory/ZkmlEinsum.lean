/-
# `Theory/ZkmlEinsum.lean` — general two-operand Einsum contraction, ordered fold, and padding

**Substrate, said out loud: this is Lean-authored denotational content.** No field, no
polynomial, no sumcheck, and no commitment appears here; the file stays strictly inside the
`Theory/` import tier (`scripts/check-import-boundary.sh`: `Mathlib` and `Theory/` only).

## What this file builds

`Theory/ZkmlTensorOps.lean` and `Theory/ZkmlMatmulSum.lean` gave 2D `matmul` (`ij,jk->ik`) an
ordered left-fold denotation over `ScalarOps α`, bridged that fold to `Finset.sum` across two
explicit algebraic steps (`AddMonoid` associativity, then `AddCommMonoid` commutativity), and
proved that dyadic zero-padding is a property of **tables** rather than an op constructor.

Every trace-free two-operand Einsum contraction (`zkTransformer`, CCS 2026, §3 & App. F)
partitions its indices into six disjoint blocks:

* **Free indices** (present in the output):
  - `mL` — **left-only** free indices (`F_L ⊆ F_1`, in `A` and output `Z`, absent from `B`),
  - `mR` — **right-only** free indices (`F_R ⊆ F_1`, in `B` and output `Z`, absent from `A`),
  - `mS` — **shared** free indices (`F_S = F_{≥2}`, in `A`, `B`, and output `Z`);
* **Summation (contracted) indices** (absent from the output):
  - `sL` — **left-only** summation indices (`S_L`, marginalized out of `A`, ignored by `B`),
  - `sM` — **shared** summation indices (`S_M`, contracted across `A` and `B`),
  - `sR` — **right-only** summation indices (`S_R`, ignored by `A`, marginalized out of `B`).

Keeping all six blocks explicit (and proving equivalence with the 4-block unified-summation
view where each operand ignores unused coordinates) lets every transformer linear contraction
sit inside one definition without dummy broadcast axes:

1. **2D `matmul` (`ij,jk->ik`)** — `mS = 1, sL = 1, sM = k, sR = 1`, recovering
   `ZkmlMatmulSum.contract` and `run S (matmulTrace …)` verbatim;
2. **Hadamard product (`i,i->i`)** — `mL = 1, mR = 1, mS = m, sL = sM = sR = 1`, recovering
   `(TOp.bin .mul …).denote`;
3. **Batched matmul (`bij,bjk->bik`)** — `mS = B` non-singleton, the case where naive
   `eq`-free substitution (`zkGPT` Eq. 8) loses completeness;
4. **Grouped-Query Attention (`igrc,jgc->grij` and `grij,jgc->igrc`)** — KV-group `g` in `mS`,
   query-within-group `r` and query-position `i` packed in `mL`, key-position `j` in `mR`, and
   head dimension `c` in `sM`, so neither `K` nor `V` is ever `G`-repeated;
5. **Asymmetric contraction (`bsdhv,btdh->bsth`, `zkTransformer` App. F Eq. 9)** — `sL = V > 1`.
-/
import Theory.ZkmlMatmulSum

namespace Minidregg.Theory.ZkmlEinsum

open Minidregg.Theory.ZkmlTensorOps

/-! ## §1. Ordered left-fold denotation and the two-step `Finset.sum` bridge -/

section Contraction

/-- General canonical two-operand Einsum as an **ordered nested left fold** over
`List.finRange` in an arbitrary law-free `ScalarOps α`, matching `TOp.denote`'s
left-to-right accumulation semantics. -/
def einsumFold {α : Type} (S : ScalarOps α) {mL mR mS sL sM sR : ℕ}
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α) :
    Fin mL → Fin mR → Fin mS → α :=
  fun iL iR h =>
    (List.finRange sL).foldl (fun accL pL =>
      (List.finRange sM).foldl (fun accM pM =>
        (List.finRange sR).foldl (fun acc pR =>
          S.bin .add acc (S.bin .mul (A iL h pL pM) (B iR h pM pR)))
        accM)
      accL)
    S.zero

/-- General canonical two-operand Einsum as an unordered `Finset.sum` contraction over a
semiring. -/
def einsumContract {α : Type} [Semiring α] {mL mR mS sL sM sR : ℕ}
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α) :
    Fin mL → Fin mR → Fin mS → α :=
  fun iL iR h =>
    ∑ pL : Fin sL, ∑ pM : Fin sM, ∑ pR : Fin sR, A iL h pL pM * B iR h pM pR

/-- **Step 1 + Step 2 from `ZkmlMatmulSum` with an arbitrary initial accumulator.**
Reuses `foldl_add_eq_listSum` (associativity) and `listSum_finRange_eq_sum` (commutativity)
without re-deriving either. -/
theorem foldl_finRange_add_eq_sum {α : Type} [AddCommMonoid α] {k : ℕ}
    (f : Fin k → α) (z : α) :
    (List.finRange k).foldl (fun acc p => acc + f p) z = z + ∑ p : Fin k, f p := by
  rw [foldl_add_eq_listSum f, listSum_finRange_eq_sum]

/-- **Step 1 alone — associativity (`AddMonoid`) suffices to turn the nested left fold into
ordered `List.sum`s**, before any commutativity is invoked. -/
theorem einsumFold_addMonoid_eq_listSum {α : Type} [AddMonoid α] (mulOp : α → α → α)
    {mL mR mS sL sM sR : ℕ}
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α)
    (iL : Fin mL) (iR : Fin mR) (h : Fin mS) :
    (List.finRange sL).foldl (fun accL pL =>
      (List.finRange sM).foldl (fun accM pM =>
        (List.finRange sR).foldl (fun acc pR =>
          acc + mulOp (A iL h pL pM) (B iR h pM pR))
        accM)
      accL) 0
      = ((List.finRange sL).map fun pL =>
          ((List.finRange sM).map fun pM =>
            ((List.finRange sR).map fun pR =>
              mulOp (A iL h pL pM) (B iR h pM pR)).sum).sum).sum := by
  have hR : ∀ (pL : Fin sL) (pM : Fin sM) (accM : α),
      (List.finRange sR).foldl (fun acc pR => acc + mulOp (A iL h pL pM) (B iR h pM pR)) accM
        = accM + ((List.finRange sR).map fun pR => mulOp (A iL h pL pM) (B iR h pM pR)).sum :=
    fun pL pM accM => foldl_add_eq_listSum _ _ accM
  simp only [hR]
  have hM : ∀ (pL : Fin sL) (accL : α),
      (List.finRange sM).foldl (fun accM pM =>
        accM + ((List.finRange sR).map fun pR => mulOp (A iL h pL pM) (B iR h pM pR)).sum) accL
        = accL + ((List.finRange sM).map fun pM =>
            ((List.finRange sR).map fun pR => mulOp (A iL h pL pM) (B iR h pM pR)).sum).sum :=
    fun pL accL => foldl_add_eq_listSum _ _ accL
  simp only [hM]
  rw [foldl_add_eq_listSum, zero_add]

/-- **The ordered-to-unordered Einsum bridge.** Under `IsRingReading S`, the ordered nested
left fold `einsumFold S` equals the `Finset.sum` contraction `einsumContract` at every output
index `(iL, iR, h)`. -/
theorem einsumFold_eq_contract {α : Type} [Ring α] {S : ScalarOps α} (hS : IsRingReading S)
    {mL mR mS sL sM sR : ℕ}
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α)
    (iL : Fin mL) (iR : Fin mR) (h : Fin mS) :
    einsumFold S A B iL iR h = einsumContract A B iL iR h := by
  unfold einsumFold einsumContract
  simp only [hS.add, hS.mul, hS.zero, foldl_finRange_add_eq_sum, zero_add]

/-- **Marginalization identity.** In any semiring, left-only (`sL`) and right-only (`sR`)
summation indices factor through per-operand marginal sums; `EinSumcheck` sums `(sL, sM, sR)`
jointly in one sumcheck so those marginal intermediates never need to be materialized or
committed. -/
theorem einsumContract_factors {α : Type} [Semiring α] {mL mR mS sL sM sR : ℕ}
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α)
    (iL : Fin mL) (iR : Fin mR) (h : Fin mS) :
    einsumContract A B iL iR h =
      ∑ pM : Fin sM, (∑ pL : Fin sL, A iL h pL pM) * (∑ pR : Fin sR, B iR h pM pR) := by
  unfold einsumContract
  calc
    (∑ pL : Fin sL, ∑ pM : Fin sM, ∑ pR : Fin sR, A iL h pL pM * B iR h pM pR)
        = ∑ pM : Fin sM, ∑ pL : Fin sL, ∑ pR : Fin sR, A iL h pL pM * B iR h pM pR :=
          Finset.sum_comm
    _ = ∑ pM : Fin sM, (∑ pL : Fin sL, A iL h pL pM) * (∑ pR : Fin sR, B iR h pM pR) := by
          refine Finset.sum_congr rfl fun pM _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun pL _ => ?_
          rw [Finset.mul_sum]

/-- Four-block Einsum with a single unified summation axis `Fin k`, where operands ignore
any coordinates of `p : Fin k` they do not depend on. -/
def einsum4Contract {α : Type} [Semiring α] {mL mR mS k : ℕ}
    (A : Fin mL → Fin mS → Fin k → α)
    (B : Fin mR → Fin mS → Fin k → α) :
    Fin mL → Fin mR → Fin mS → α :=
  fun iL iR h => ∑ p : Fin k, A iL h p * B iR h p

/-- Equivalence between the explicit 6-block `(sL, sM, sR)` contraction and the unified-axis
4-block contraction on `Fin (sL * (sM * sR))` where `A` ignores `pR` and `B` ignores `pL`. -/
theorem einsumContract_eq_unified {α : Type} [Semiring α] {mL mR mS sL sM sR : ℕ}
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α)
    (iL : Fin mL) (iR : Fin mR) (h : Fin mS) :
    einsumContract A B iL iR h =
      einsum4Contract (k := sL * (sM * sR))
        (fun iL' h' p =>
          let q := finProdFinEquiv.symm p
          let r := finProdFinEquiv.symm q.2
          A iL' h' q.1 r.1)
        (fun iR' h' p =>
          let q := finProdFinEquiv.symm p
          let r := finProdFinEquiv.symm q.2
          B iR' h' r.1 r.2)
        iL iR h := by
  unfold einsumContract einsum4Contract
  let e : (Fin sL × Fin sM × Fin sR) ≃ Fin (sL * (sM * sR)) :=
    (Equiv.prodCongr (Equiv.refl (Fin sL)) finProdFinEquiv).trans finProdFinEquiv
  calc
    (∑ pL : Fin sL, ∑ pM : Fin sM, ∑ pR : Fin sR, A iL h pL pM * B iR h pM pR)
        = ∑ t : Fin sL × Fin sM × Fin sR, A iL h t.1 t.2.1 * B iR h t.2.1 t.2.2 := by
          symm
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun pL _ =>
            Fintype.sum_prod_type (fun mr : Fin sM × Fin sR => A iL h pL mr.1 * B iR h mr.1 mr.2)
    _ = ∑ p : Fin (sL * (sM * sR)),
          let q := finProdFinEquiv.symm p
          let r := finProdFinEquiv.symm q.2
          A iL h q.1 r.1 * B iR h r.1 r.2 := by
          refine Fintype.sum_equiv e _ _ fun t => ?_
          rcases t with ⟨pL, pM, pR⟩
          simp [e]

end Contraction

/-! ## §2. Dyadic zero-padding across all six blocks

Extending `ZkmlMatmulSum`'s table-padding principle (`padded_contraction`,
`padded_matmul_table`) to all six Einsum blocks:
* zero-padding summation blocks `(sL, sM, sR)` leaves every output entry unchanged;
* zero-padding free blocks `(mL, mR, mS)` zero-pads the output table itself. -/

section Padding

variable {α : Type} [Semiring α]

/-- Zero-pad left operand `A` along its summation axes `(sL + tL, sM + tM)`. -/
def padSumA {mL mS sL sM : ℕ} (tL tM : ℕ)
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α) :
    Fin mL → Fin mS → Fin (sL + tL) → Fin (sM + tM) → α :=
  fun iL h =>
    Fin.addCases
      (fun pL => Fin.addCases (fun pM => A iL h pL pM) (fun _ => 0))
      (fun _ _ => 0)

/-- Zero-pad right operand `B` along its summation axes `(sM + tM, sR + tR)`. -/
def padSumB {mR mS sM sR : ℕ} (tM tR : ℕ)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α) :
    Fin mR → Fin mS → Fin (sM + tM) → Fin (sR + tR) → α :=
  fun iR h =>
    Fin.addCases
      (fun pM => Fin.addCases (fun pR => B iR h pM pR) (fun _ => 0))
      (fun _ _ => 0)

@[simp] theorem padSumA_cast_cast {mL mS sL sM tL tM : ℕ}
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (iL : Fin mL) (h : Fin mS) (pL : Fin sL) (pM : Fin sM) :
    padSumA tL tM A iL h (Fin.castAdd tL pL) (Fin.castAdd tM pM) = A iL h pL pM := by
  simp [padSumA]

@[simp] theorem padSumA_cast_nat {mL mS sL sM tL tM : ℕ}
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (iL : Fin mL) (h : Fin mS) (pL : Fin sL) (qM : Fin tM) :
    padSumA tL tM A iL h (Fin.castAdd tL pL) (Fin.natAdd sM qM) = 0 := by
  simp [padSumA]

@[simp] theorem padSumA_nat {mL mS sL sM tL tM : ℕ}
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (iL : Fin mL) (h : Fin mS) (qL : Fin tL) (pM : Fin (sM + tM)) :
    padSumA tL tM A iL h (Fin.natAdd sL qL) pM = 0 := by
  simp [padSumA]

@[simp] theorem padSumB_cast_cast {mR mS sM sR tM tR : ℕ}
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α)
    (iR : Fin mR) (h : Fin mS) (pM : Fin sM) (pR : Fin sR) :
    padSumB tM tR B iR h (Fin.castAdd tM pM) (Fin.castAdd tR pR) = B iR h pM pR := by
  simp [padSumB]

@[simp] theorem padSumB_cast_nat {mR mS sM sR tM tR : ℕ}
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α)
    (iR : Fin mR) (h : Fin mS) (pM : Fin sM) (qR : Fin tR) :
    padSumB tM tR B iR h (Fin.castAdd tM pM) (Fin.natAdd sR qR) = 0 := by
  simp [padSumB]

@[simp] theorem padSumB_nat {mR mS sM sR tM tR : ℕ}
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α)
    (iR : Fin mR) (h : Fin mS) (qM : Fin tM) (pR : Fin (sR + tR)) :
    padSumB tM tR B iR h (Fin.natAdd sM qM) pR = 0 := by
  simp [padSumB]

/-- **Zero-padding all three summation axes `(sL, sM, sR)` leaves the contraction
pointwise unchanged.** Notice that on `qL : Fin tL`, `padSumA` alone supplies the `0` that
annihilates `B` even though `B` carries no `sL` coordinate (and symmetrically on `qR : Fin tR`). -/
theorem padded_einsum_summation {mL mR mS sL sM sR : ℕ} (tL tM tR : ℕ)
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α) :
    einsumContract (padSumA tL tM A) (padSumB tM tR B) = einsumContract A B := by
  funext iL iR h
  simp only [einsumContract, Fin.sum_univ_add,
    padSumA_nat, padSumA_cast_cast,
    padSumB_nat, padSumB_cast_nat, padSumB_cast_cast,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

/-- Zero-pad left operand `A` along its free axes `(mL + dL, mS + dS)`. -/
def padFreeA {mL mS sL sM : ℕ} (dL dS : ℕ)
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α) :
    Fin (mL + dL) → Fin (mS + dS) → Fin sL → Fin sM → α :=
  Fin.addCases
    (fun iL => Fin.addCases (fun h => A iL h) (fun _ _ _ => 0))
    (fun _ _ _ _ => 0)

/-- Zero-pad right operand `B` along its free axes `(mR + dR, mS + dS)`. -/
def padFreeB {mR mS sM sR : ℕ} (dR dS : ℕ)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α) :
    Fin (mR + dR) → Fin (mS + dS) → Fin sM → Fin sR → α :=
  Fin.addCases
    (fun iR => Fin.addCases (fun h => B iR h) (fun _ _ _ => 0))
    (fun _ _ _ _ => 0)

/-- Zero-pad an output table `Z` along all three free axes `(mL + dL, mR + dR, mS + dS)`. -/
def padFreeZ {mL mR mS : ℕ} (dL dR dS : ℕ)
    (Z : Fin mL → Fin mR → Fin mS → α) :
    Fin (mL + dL) → Fin (mR + dR) → Fin (mS + dS) → α :=
  Fin.addCases
    (fun iL => Fin.addCases
      (fun iR => Fin.addCases (fun h => Z iL iR h) (fun _ => 0))
      (fun _ _ => 0))
    (fun _ _ _ => 0)

/-- **Zero-padding all three free axes `(mL, mR, mS)` commutes with `einsumContract`.**
Out-of-range slices on `mL`, `mR`, or `mS` vanish automatically in the contraction, producing
exact zero-padding of the true output tensor. -/
theorem padded_einsum_free {mL mR mS sL sM sR : ℕ} (dL dR dS : ℕ)
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α) :
    einsumContract (padFreeA dL dS A) (padFreeB dR dS B)
      = padFreeZ dL dR dS (einsumContract A B) := by
  funext iL iR h
  refine Fin.addCases (motive := fun iL =>
    einsumContract (padFreeA dL dS A) (padFreeB dR dS B) iL iR h
      = padFreeZ dL dR dS (einsumContract A B) iL iR h) ?_ ?_ iL
  · intro iL₀
    refine Fin.addCases (motive := fun iR =>
      einsumContract (padFreeA dL dS A) (padFreeB dR dS B) (Fin.castAdd dL iL₀) iR h
        = padFreeZ dL dR dS (einsumContract A B) (Fin.castAdd dL iL₀) iR h) ?_ ?_ iR
    · intro iR₀
      refine Fin.addCases (motive := fun h =>
        einsumContract (padFreeA dL dS A) (padFreeB dR dS B)
            (Fin.castAdd dL iL₀) (Fin.castAdd dR iR₀) h
          = padFreeZ dL dR dS (einsumContract A B)
              (Fin.castAdd dL iL₀) (Fin.castAdd dR iR₀) h) ?_ ?_ h
      · intro h₀; simp [einsumContract, padFreeA, padFreeB, padFreeZ]
      · intro h₁; simp [einsumContract, padFreeA, padFreeB, padFreeZ]
    · intro iR₁; simp [einsumContract, padFreeA, padFreeB, padFreeZ]
  · intro iL₁; simp [einsumContract, padFreeA, padFreeB, padFreeZ]

/-- **Full six-axis dyadic zero-padding (`padded_einsum`).** Padding both free axes
`(dL, dR, dS)` and summation axes `(tL, tM, tR)` with zeros on `A` and `B` yields the exact
zero-padded true output tensor `padFreeZ dL dR dS (einsumContract A B)`. -/
theorem padded_einsum {mL mR mS sL sM sR : ℕ} (dL dR dS tL tM tR : ℕ)
    (A : Fin mL → Fin mS → Fin sL → Fin sM → α)
    (B : Fin mR → Fin mS → Fin sM → Fin sR → α) :
    einsumContract (padSumA tL tM (padFreeA dL dS A)) (padSumB tM tR (padFreeB dR dS B))
      = padFreeZ dL dR dS (einsumContract A B) := by
  rw [padded_einsum_summation, padded_einsum_free]

end Padding

/-! ## §3. Concrete specializations: 2D matmul, Hadamard, batched matmul, GQA, asymmetric -/

section Specializations

/-- **(i) 2D `matmul` (`ij,jk->ik`)**: `mS = 1` (no shared free bits), `sL = 1`, `sM = k`,
`sR = 1`. Recovers `ZkmlMatmulSum.contract` identically. -/
theorem einsum_matmul_eq_contract {α : Type} [Semiring α] {m k n : ℕ}
    (A : Fin m → Fin k → α) (B : Fin k → Fin n → α) (i : Fin m) (j : Fin n) :
    einsumContract (mL := m) (mR := n) (mS := 1) (sL := 1) (sM := k) (sR := 1)
      (fun i' _ _ p => A i' p) (fun j' _ p _ => B p j') i j 0
      = contract A B i j := by
  simp [einsumContract, contract]

/-- ...and connects directly to `ZkmlTensorOps.run` on `matmulTrace` under `IsRingReading`. -/
theorem einsum_matmul_eq_run {α : Type} [Ring α] {S : ScalarOps α} (hS : IsRingReading S)
    {Γ : Ctx} {d : Dtype} {m k n : ℕ}
    (a : Var Γ ⟨d, [m, k]⟩) (b : Var Γ ⟨d, [k, n]⟩) (ρ : Env α Γ)
    (i : Fin m) (j : Fin n) :
    einsumFold S (mL := m) (mR := n) (mS := 1) (sL := 1) (sM := k) (sR := 1)
      (fun i' _ _ p => ρ.get a (i', p, PUnit.unit))
      (fun j' _ p _ => ρ.get b (p, j', PUnit.unit)) i j 0
      = run S (matmulTrace d m k n a b) ρ (i, j, PUnit.unit) := by
  rw [einsumFold_eq_contract hS, einsum_matmul_eq_contract, run_matmul_sum hS]
  rfl

/-- **(ii) Hadamard elementwise product (`i,i->i`)**: `mL = 1, mR = 1, mS = m` (every output
axis is shared free) and `sL = sM = sR = 1` (singleton summation). -/
theorem einsum_hadamard_eq_mul {α : Type} [Semiring α] {m : ℕ}
    (A B : Fin m → α) (i : Fin m) :
    einsumContract (mL := 1) (mR := 1) (mS := m) (sL := 1) (sM := 1) (sR := 1)
      (fun _ h _ _ => A h) (fun _ h _ _ => B h) 0 0 i
      = A i * B i := by
  simp [einsumContract]

/-- ...and matches `(TOp.bin .mul …).denote` in `ZkmlTensorOps` under `IsRingReading`. -/
theorem einsum_hadamard_eq_denote {α : Type} [Ring α] {S : ScalarOps α} (hS : IsRingReading S)
    {Γ : Ctx} {d : Dtype} {m : ℕ}
    (a b : Var Γ ⟨d, [m]⟩) (ρ : Env α Γ) (i : Fin m) :
    einsumFold S (mL := 1) (mR := 1) (mS := m) (sL := 1) (sM := 1) (sR := 1)
      (fun _ h _ _ => ρ.get a (h, PUnit.unit))
      (fun _ h _ _ => ρ.get b (h, PUnit.unit)) 0 0 i
      = (TOp.bin .mul ⟨d, [m]⟩ a b).denote S ρ (i, PUnit.unit) := by
  rw [einsumFold_eq_contract hS, einsum_hadamard_eq_mul]
  simp [TOp.denote, hS.mul]

/-- **(iii) Batched matmul (`bij,bjk->bik`)**: shared free batch axis `mS = B`, left-only row
`mL = m`, right-only col `mR = n`, shared contraction `sM = k`. Recovers batchwise `contract`. -/
theorem einsum_batchedMatmul_eq {α : Type} [Semiring α] {B_batch m k n : ℕ}
    (A : Fin B_batch → Fin m → Fin k → α) (B : Fin B_batch → Fin k → Fin n → α)
    (b : Fin B_batch) (i : Fin m) (j : Fin n) :
    einsumContract (mL := m) (mR := n) (mS := B_batch) (sL := 1) (sM := k) (sR := 1)
      (fun i' b' _ p => A b' i' p) (fun j' b' p _ => B b' p j') i j b
      = contract (A b) (B b) i j := by
  simp [einsumContract, contract]

/-- **(iv) Grouped-Query Attention (`igrc,jgc->grij`) — left operand embedding.**
Query tensor `Q[i, g, r, c]` (`Sq` query positions, `KV` key/value head groups, `G` queries per
group so `H = KV * G`, `HD` head dimension) packs `(r, i)` into `mL = G * Sq`, places `g` in
shared free `mS = KV`, and contracts `c` in `sM = HD`. -/
def gqaLeft {α : Type} {Sq KV G HD : ℕ}
    (Q : Fin Sq → Fin KV → Fin G → Fin HD → α) :
    Fin (G * Sq) → Fin KV → Fin 1 → Fin HD → α :=
  fun ri g _ c =>
    let p := finProdFinEquiv.symm ri
    Q p.2 g p.1 c

/-- **Grouped-Query Attention (`igrc,jgc->grij`) — right operand embedding.**
Key tensor `K[j, g, c]` (`Skv` key positions, `KV` groups, `HD` head dim) places `j` in
`mR = Skv`, `g` in `mS = KV`, and `c` in `sM = HD` — **never duplicated by `G`**. -/
def gqaRight {α : Type} {Skv KV HD : ℕ}
    (K : Fin Skv → Fin KV → Fin HD → α) :
    Fin Skv → Fin KV → Fin HD → Fin 1 → α :=
  fun j g c _ => K j g c

/-- GQA attention-score tensor `Scores[g, r, i, j]`, realized as a single `einsumContract`. -/
def gqaScores {α : Type} [Semiring α] {Sq Skv KV G HD : ℕ}
    (Q : Fin Sq → Fin KV → Fin G → Fin HD → α)
    (K : Fin Skv → Fin KV → Fin HD → α)
    (g : Fin KV) (r : Fin G) (i : Fin Sq) (j : Fin Skv) : α :=
  einsumContract (gqaLeft Q) (gqaRight K) (finProdFinEquiv (r, i)) j g

/-- **GQA score specialization (`igrc,jgc->grij`).** `gqaScores` computes the exact per-head
inner product `∑ c : Fin HD, Q i g r c * K j g c` without materializing a `G`-repeated `K`. -/
theorem einsum_gqa_scores_eq {α : Type} [Semiring α] {Sq Skv KV G HD : ℕ}
    (Q : Fin Sq → Fin KV → Fin G → Fin HD → α)
    (K : Fin Skv → Fin KV → Fin HD → α)
    (g : Fin KV) (r : Fin G) (i : Fin Sq) (j : Fin Skv) :
    gqaScores Q K g r i j = ∑ c : Fin HD, Q i g r c * K j g c := by
  simp [gqaScores, einsumContract, gqaLeft, gqaRight]

/-- **GQA value aggregation (`grij,jgc->igrc`)**: the second attention contraction shares the
exact same index partition (`(r, i)` in `mL = G * Sq`, `c` in `mR = HD`, `g` in `mS = KV`,
`j` in `sM = Skv`), so `V` is never `G`-repeated either. -/
def gqaValueOut {α : Type} [Semiring α] {Sq Skv KV G HD : ℕ}
    (Scores : Fin KV → Fin G → Fin Sq → Fin Skv → α)
    (V : Fin Skv → Fin KV → Fin HD → α)
    (i : Fin Sq) (g : Fin KV) (r : Fin G) (c : Fin HD) : α :=
  einsumContract (mL := G * Sq) (mR := HD) (mS := KV) (sL := 1) (sM := Skv) (sR := 1)
    (fun ri g' _ j =>
      let p := finProdFinEquiv.symm ri
      Scores g' p.1 p.2 j)
    (fun c' g' j _ => V j g' c')
    (finProdFinEquiv (r, i)) c g

theorem einsum_gqa_valueOut_eq {α : Type} [Semiring α] {Sq Skv KV G HD : ℕ}
    (Scores : Fin KV → Fin G → Fin Sq → Fin Skv → α)
    (V : Fin Skv → Fin KV → Fin HD → α)
    (i : Fin Sq) (g : Fin KV) (r : Fin G) (c : Fin HD) :
    gqaValueOut Scores V i g r c = ∑ j : Fin Skv, Scores g r i j * V j g c := by
  simp [gqaValueOut, einsumContract]

/-- **(v) Asymmetric contraction (`bsdhv,btdh->bsth`, `zkTransformer` App. F Eq. 9)**:
`sL = V_dim` is summed out of `A` only while `sM = D_dim` is contracted across both `A` and `B`. -/
theorem einsum_asymmetric_eq {α : Type} [Semiring α] {B_dim S_dim T_dim D_dim H_dim V_dim : ℕ}
    (A : Fin B_dim → Fin S_dim → Fin D_dim → Fin H_dim → Fin V_dim → α)
    (B : Fin B_dim → Fin T_dim → Fin D_dim → Fin H_dim → α)
    (b : Fin B_dim) (s : Fin S_dim) (t : Fin T_dim) (h : Fin H_dim) :
    einsumContract (mL := S_dim) (mR := T_dim) (mS := B_dim * H_dim)
      (sL := V_dim) (sM := D_dim) (sR := 1)
      (fun s' bh v d =>
        let p := finProdFinEquiv.symm bh
        A p.1 s' d p.2 v)
      (fun t' bh d _ =>
        let p := finProdFinEquiv.symm bh
        B p.1 t' d p.2)
      s t (finProdFinEquiv (b, h))
      = ∑ v : Fin V_dim, ∑ d : Fin D_dim, A b s d h v * B b t d h := by
  simp [einsumContract]

end Specializations

/-! ## §4. Computed witnesses and teeth (`decide`) -/

namespace EinsumExample

/-- Concrete GQA witness (`Sq = 1, Skv = 2, KV = 2, G = 2, HD = 2`) over `ℤ`: two query heads
`r = 0, 1` in group `g = 0` share one key head `K[·, 0, ·]` and produce distinct attention
scores (`7` vs `11`). -/
def exQ : Fin 1 → Fin 2 → Fin 2 → Fin 2 → ℤ :=
  fun _ g r c =>
    if g.val = 0 then
      if r.val = 0 then (if c.val = 0 then 1 else 2)
      else (if c.val = 0 then 3 else 1)
    else 1

def exK : Fin 2 → Fin 2 → Fin 2 → ℤ :=
  fun j g c =>
    if g.val = 0 then
      if j.val = 0 then (if c.val = 0 then 3 else 2) else 1
    else 2

/-- **Witness — GQA ordered fold and `Finset.sum` contraction agree and separate heads inside
the same KV group**: `r = 0` gives `1·3 + 2·2 = 7` and `r = 1` gives `3·3 + 1·2 = 11`. -/
theorem gqa_witness_computes :
    einsumFold zOps (gqaLeft exQ) (gqaRight exK)
        (finProdFinEquiv (⟨0, by decide⟩, ⟨0, by decide⟩)) ⟨0, by decide⟩ ⟨0, by decide⟩ = 7 ∧
    gqaScores exQ exK ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ = 7 ∧
    gqaScores exQ exK ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ = 11 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Tooth 1 — `einsumFold_eq_contract`'s `IsRingReading` hypothesis is refutable.** Under
`SatExample.satOps` (commutative but non-associative saturating addition at `10`), `einsumFold`
gives `5` (`((0 + 9) + 5) + (-5)` saturates at `10`, then `10 - 5 = 5`) while `einsumContract`
over `ℤ` gives `9`. -/
def satLeft : Fin 1 → Fin 1 → Fin 1 → Fin 3 → ℤ :=
  fun _ _ _ p => (![9, 5, -5] : Fin 3 → ℤ) p

def satRight : Fin 1 → Fin 1 → Fin 3 → Fin 1 → ℤ :=
  fun _ _ _ _ => 1

theorem einsum_sat_bridge_fails :
    einsumFold SatExample.satOps satLeft satRight 0 0 0 ≠
      einsumContract satLeft satRight 0 0 0 := by
  decide

/-- **Tooth 2 — zero-padding in `padded_einsum_summation` is load-bearing.** Extending a
right-only summation axis `sR = 1` to `1 + 1` by repeating `B` (`fun _ _ _ _ => 3`) instead of
zero-padding `B` (`padSumB`) doubles the contraction from `6` to `12`. -/
def padToothA : Fin 1 → Fin 1 → Fin 1 → Fin 1 → ℤ := fun _ _ _ _ => 2
def padToothB : Fin 1 → Fin 1 → Fin 1 → Fin 1 → ℤ := fun _ _ _ _ => 3
def padToothBBad : Fin 1 → Fin 1 → Fin 1 → Fin (1 + 1) → ℤ := fun _ _ _ _ => 3

theorem bad_repeat_pad_summation_breaks :
    einsumContract padToothA padToothBBad 0 0 0 ≠
      einsumContract padToothA padToothB 0 0 0 := by
  decide

end EinsumExample

/-! ## §5. Axiom pins (house law) -/

/-- info: 'Minidregg.Theory.ZkmlEinsum.foldl_finRange_add_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldl_finRange_add_eq_sum
/-- info: 'Minidregg.Theory.ZkmlEinsum.einsumFold_addMonoid_eq_listSum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsumFold_addMonoid_eq_listSum
/-- info: 'Minidregg.Theory.ZkmlEinsum.einsumFold_eq_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsumFold_eq_contract
/-- info: 'Minidregg.Theory.ZkmlEinsum.einsumContract_factors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsumContract_factors
/-- info: 'Minidregg.Theory.ZkmlEinsum.einsumContract_eq_unified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsumContract_eq_unified
/-- info: 'Minidregg.Theory.ZkmlEinsum.padded_einsum_summation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_einsum_summation
/-- info: 'Minidregg.Theory.ZkmlEinsum.padded_einsum_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_einsum_free
/-- info: 'Minidregg.Theory.ZkmlEinsum.padded_einsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_einsum
/-- info: 'Minidregg.Theory.ZkmlEinsum.einsum_matmul_eq_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_matmul_eq_run
/-- info: 'Minidregg.Theory.ZkmlEinsum.einsum_hadamard_eq_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_hadamard_eq_denote
/-- info: 'Minidregg.Theory.ZkmlEinsum.einsum_batchedMatmul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_batchedMatmul_eq
/-- info: 'Minidregg.Theory.ZkmlEinsum.einsum_gqa_scores_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_gqa_scores_eq
/-- info: 'Minidregg.Theory.ZkmlEinsum.einsum_gqa_valueOut_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_gqa_valueOut_eq
/-- info: 'Minidregg.Theory.ZkmlEinsum.einsum_asymmetric_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_asymmetric_eq
/-- info: 'Minidregg.Theory.ZkmlEinsum.EinsumExample.gqa_witness_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms EinsumExample.gqa_witness_computes
/-- info: 'Minidregg.Theory.ZkmlEinsum.EinsumExample.einsum_sat_bridge_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms EinsumExample.einsum_sat_bridge_fails
/-- info: 'Minidregg.Theory.ZkmlEinsum.EinsumExample.bad_repeat_pad_summation_breaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms EinsumExample.bad_repeat_pad_summation_breaks

end Minidregg.Theory.ZkmlEinsum
