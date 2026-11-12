/-
# Selvage.DecomposableTable -- Lasso's decomposable (SOS) tables: the identity, with teeth

Lasso (Setty--Thaler--Wahby, ePrint 2023/1216, Eq. (14); Jolt, ePrint 2023/1217,
Def. 2.6) prices one lookup into a table of size `N = 2^(c*w)` as one lookup into
each of `alpha` sub-tables of size `2^w` plus a single evaluation of a COMBINING
multilinear polynomial `g`:

    T[r] = g(T_1[r_{chunk 1}], ..., T_alpha[r_{chunk alpha}]),

where the address `r` is split into `c` chunks of `w` bits and each sub-table
reads one chunk.  This module states that identity as a structure with `g`
explicit -- as its Boolean-cube value table, so `mle gTable` IS the combining
polynomial and multilinearity is structural rather than hypothesized -- and
supplies the instances and refutations that make the notion earn its name:

* `spark_table_decomposes` -- Spark's own table (entry `j` is the Lagrange basis
  value `chi_j(rho)`, the table whose sparse inner product IS multilinear
  evaluation) decomposes with `g = product`.  This is "sparse evaluation is a
  lookup into a decomposable table" as a theorem rather than a slogan.
* `interleavedEq_decomposes` (k = 1, `g = product`, any chunk count) and
  `LtuExample.ltu_decomposes` (k = 2, Jolt's less-than-unsigned with
  `g = LT_hi + EQ_hi * LT_lo`) -- the two canonical Jolt shapes, one general and
  one concrete.
* **TEETH** `splitEq_not_decomposable` -- the SAME equality function under the
  split chunking (all of `x` in one chunk, all of `y` in the other) admits NO
  decomposition with one sub-table per chunk, over EVERY field: a multilinear
  `g` is affine in each coordinate and an affine map cannot pass through the
  four distinct rows of the identity matrix.  With `splitEq_transpose`
  (the transposed chunking of the same function, which `interleavedEq_decomposes`
  handles), this pins that decomposability is a property of the
  (function, CHUNKING, alpha) triple, not of the function.
* `TableDecomposition.combined_by_chi` -- every sub-table read is literally the
  `binaryTableDot`/`binaryLookupEq` object that `BinaryLookup`/`LogupStar`/
  `LogupIndexLink` already price: the decomposition layer is a SECOND instance
  of the landed lookup machinery, not a new primitive.

Scope, disclaimed in the open: this is the TABLE-side identity only.  What it
does NOT contain, named so the next lane can aim at it:

* `[LASSO-PRIMARY-SUMCHECK]` -- Surge's main reduction (2023/1216 Fig. 5 step 2)
  sumchecks `sum_j eq(r,j) * g(E_1(j), ..., E_alpha(j))`, whose round polynomials
  have degree `alpha + 1`.  The engine (`adaptive_sumcheck_soundness`) is
  degree-generic; the honest-prover REALIZER beyond the landed degree-2/3 rungs
  is not built.
* `[LASSO-COUNTER-LAYER]` -- the read-multiset integrity layer: offline memory
  checking with grand products in the paper (Claims 2--4), a LogUp logarithmic-
  derivative fingerprint in modern instantiations.  `LogupStar.logupPushforward`
  is exactly the multiplicity object (`final_cts`); the paper's counter route
  additionally carries the `m < char F` counter-wraparound floor (Claim 2 +
  Remark 2), which is a VALIDITY precondition, not an error term.
* `[LASSO-CHUNK-LINK]` -- that the committed chunk addresses `dim_i` decode the
  canonical chunking of the looked-up index: the `c`-fold instance of
  `[LOGUP-ADDRESS-LINK]` (`LogupIndexLink`).

`SurgeReadOracle` names the read-integrity obligation at this interface, and
`surgeReadOracle_all_accepting_refuted` shows it is not free.
-/
import Mathlib.Tactic.LinearCombination
import Selvage.BinaryLookup

namespace Minidregg.Selvage

variable {F : Type*} [Field F]

/-! ## The decomposition structure -/

/-- Lasso Eq. (14) data for a table over `c` chunks of `w` bits
(`N = 2^(c*w)`), with `alpha` sub-tables of size `2^w`.  `chunk a` says which
address chunk sub-table `a` reads; Lasso's block layout (`alpha = c*k`,
sub-tables `(j-1)k+1 .. jk` reading chunk `j`) is `lassoBlockChunk`.  The
combining polynomial is carried as its cube table `gTable`; `mle gTable` is the
polynomial itself, multilinear by construction (`mle_multilinear`), which is
exactly Jolt Def. 2.6's requirement on `g`. -/
structure TableDecomposition (F : Type*) [Field F] (c w α : ℕ) where
  /-- The `alpha` sub-tables, each over `w`-bit indices. -/
  subTable : Fin α → (Fin w → Bool) → F
  /-- Which of the `c` address chunks each sub-table reads. -/
  chunk : Fin α → Fin c
  /-- The combining polynomial `g`, as its Boolean-cube value table. -/
  gTable : (Fin α → Bool) → F

/-- Lasso's canonical block chunk map: sub-table `a` reads chunk `a / k`
(Eq. (14) with `alpha = c*k`, `k` sub-tables per chunk). -/
def lassoBlockChunk (c k : ℕ) : Fin (c * k) → Fin c :=
  fun a => ⟨a / k, Nat.div_lt_of_lt_mul (by simp [Nat.mul_comm, a.2])⟩

/-- A decomposition in Lasso's block layout. -/
def TableDecomposition.ofBlocks {c w k : ℕ}
    (sub : Fin (c * k) → (Fin w → Bool) → F)
    (gT : (Fin (c * k) → Bool) → F) : TableDecomposition F c w (c * k) :=
  ⟨sub, lassoBlockChunk c k, gT⟩

namespace TableDecomposition

variable {c w α : ℕ}

/-- The combining polynomial `g`, explicit. -/
def g (D : TableDecomposition F c w α) : (Fin α → F) → F := mle D.gTable

/-- The `alpha` sub-table reads at a chunked Boolean address. -/
def readsAt (D : TableDecomposition F c w α) (r : Fin c → Fin w → Bool) :
    Fin α → F :=
  fun a => D.subTable a (r (D.chunk a))

/-- The right-hand side of Lasso Eq. (14): `g` applied to the sub-table reads. -/
def combined (D : TableDecomposition F c w α) (r : Fin c → Fin w → Bool) : F :=
  mle D.gTable (D.readsAt r)

/-- The low-degree extension `T-hat(rho) = g(T_1-mle(rho_1), ...)` that the
Surge VERIFIER evaluates on its own in `O(alpha * w)` field operations -- the
"MLE-structured" object of Jolt Def. 2.5/2.6.  Its degree in each address
variable is at most the number of sub-tables reading that variable's chunk. -/
def extension (D : TableDecomposition F c w α) (ρ : Fin c → Fin w → F) : F :=
  mle D.gTable (fun a => mle (D.subTable a) (ρ (D.chunk a)))

/-- On the Boolean cube the extension is exactly the combined read. -/
theorem extension_agrees (D : TableDecomposition F c w α)
    (r : Fin c → Fin w → Bool) :
    D.extension (fun i => cubePt (r i)) = D.combined r := by
  unfold extension combined readsAt
  congr 1
  funext a
  exact mle_agrees _ _

end TableDecomposition

/-- **The decomposition identity** `T[r] = g(T_1[r_{chunk 1}], ...)`,
Lasso Eq. (14) / Jolt Def. 2.6, with the combining polynomial explicit. -/
def Decomposes {c w α : ℕ} (T : (Fin c → Fin w → Bool) → F)
    (D : TableDecomposition F c w α) : Prop :=
  ∀ r, T r = D.combined r

/-- `T` admits SOME `(c, w, alpha)`-decomposition ("Spark-only structure"). -/
def Decomposable (c w α : ℕ) (T : (Fin c → Fin w → Bool) → F) : Prop :=
  ∃ D : TableDecomposition F c w α, Decomposes T D

/-! ## The product combining polynomial -/

/-- The cube table of the product polynomial `prod_a v_a`. -/
def prodTable (α : ℕ) : (Fin α → Bool) → F := fun b => ∏ a, ofBool (b a)

/-- The product is affine in every coordinate. -/
theorem prod_multiAffine (α : ℕ) :
    MultiAffine (fun u : Fin α → F => ∏ a, u a) := by
  intro i x t
  simp only [Finset.prod_update_of_mem (Finset.mem_univ i)]
  ring

/-- `mle` of the product cube table IS the product polynomial -- the combining
polynomial of every tensor-shaped decomposition. -/
theorem mle_prodTable (α : ℕ) :
    mle (prodTable (F := F) α) = fun u => ∏ a, u a :=
  (multiAffine_eq_mle (prod_multiAffine (F := F) α)).symm

/-! ## Spark's own table decomposes -- sparse evaluation IS a decomposable lookup

Spark evaluates an `m`-sparse `(c*w)`-variate multilinear polynomial at
`rho` by looking its nonzero cube points up in the table whose entry `j` is the
Lagrange basis value `chi_j(rho)` (2023/1216 Section 3.1).  That table is the
tensor of `c` per-chunk `chi` tables, i.e. it decomposes with one sub-table per
chunk and `g = product`.  This is the observation that turns Spark into Surge,
and it is the sense in which the SPARK gap of `Assurance/SpartanR1CS.lean`
(`SpartanSparseEvalOracle`) is an instance of the lookup machinery. -/

/-- The tensor decomposition of Spark's `chi`-value table at evaluation point
`rho`: sub-table `a` is the chunk-`a` Lagrange table `b ↦ chi_b(rho_a)`. -/
def sparkDecomposition {c w : ℕ} (ρ : Fin c → Fin w → F) :
    TableDecomposition F c w c where
  subTable := fun a b => chiEval b (ρ a)
  chunk := id
  gTable := prodTable c

/-- **Spark's table is decomposable** with `g = product`. -/
theorem spark_table_decomposes {c w : ℕ} (ρ : Fin c → Fin w → F) :
    Decomposes (fun j : Fin c → Fin w → Bool => ∏ i, chiEval (j i) (ρ i))
      (sparkDecomposition ρ) := by
  intro r
  simp only [TableDecomposition.combined, TableDecomposition.readsAt,
    sparkDecomposition, mle_prodTable, id]

/-! ## Each sub-table read is the object `BinaryLookup` already prices -/

namespace TableDecomposition

variable {c w α : ℕ}

/-- Flat (LSB-first) spelling of a sub-table. -/
def flatSub (D : TableDecomposition F c w α) (a : Fin α) : Fin (2 ^ w) → F :=
  fun i => D.subTable a (binaryAddressBits w i)

/-- The combined read is `g` applied to `alpha` chi-vector table dot products --
i.e. to `alpha` instances of the indexed-lookup object the LogUp family
(`LogupStar`, `BinaryLookup`, `LogupIndexLink`) prices.  The decomposition
layer is a SECOND instance of the landed machinery, not a new primitive. -/
theorem combined_by_chi (D : TableDecomposition F c w α)
    (r : Fin c → Fin w → Bool) :
    D.combined r
      = mle D.gTable (fun a =>
          binaryTableDot (D.flatSub a)
            (binaryLookupEq w (cubePt (r (D.chunk a))))) := by
  unfold combined readsAt
  congr 1
  funext a
  rw [binaryTableDot_lookupEq_cubePt]
  simp [flatSub]

end TableDecomposition

/-! ## Jolt's two canonical shapes -/

/-- Per-chunk equality table: is the chunk's `(x_i, y_i)` pair equal? -/
def eqChunkTable : (Fin 2 → Bool) → F := fun b => if b 0 = b 1 then 1 else 0

/-- Equality under the INTERLEAVED chunking: chunk `i` holds `(x_i, y_i)`. -/
def interleavedEqTable (c : ℕ) : (Fin c → Fin 2 → Bool) → F :=
  fun r => if ∀ i, r i 0 = r i 1 then 1 else 0

/-- `EQ = prod_chunks EQ_chunk` (Jolt Section 5, "equality"): one sub-table per
chunk (`k = 1`), `g = product`. -/
def interleavedEqDecomposition (c : ℕ) : TableDecomposition F c 2 c where
  subTable := fun _ => eqChunkTable
  chunk := id
  gTable := prodTable c

/-- The interleaved equality table decomposes, at every chunk count. -/
theorem interleavedEq_decomposes (c : ℕ) :
    Decomposes (interleavedEqTable (F := F) c) (interleavedEqDecomposition c) := by
  intro r
  simp only [TableDecomposition.combined, TableDecomposition.readsAt,
    interleavedEqDecomposition, mle_prodTable, id, interleavedEqTable,
    eqChunkTable]
  by_cases h : ∀ i : Fin c, r i 0 = r i 1
  · rw [if_pos h]
    exact (Finset.prod_eq_one fun a _ => if_pos (h a)).symm
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [if_neg h]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

namespace LtuExample

/-- Per-chunk strict less-than table: `x_i < y_i` on the chunk's pair. -/
def ltChunk : (Fin 2 → Bool) → ZMod 5 := fun b => if !b 0 && b 1 then 1 else 0

/-- 2-bit unsigned less-than, interleaved chunking: chunk `i` holds
`(x_i, y_i)`, chunk 1 the high bit. -/
def ltuTable : (Fin 2 → Fin 2 → Bool) → ZMod 5 := fun r =>
  if 2 * (r 1 0).toNat + (r 0 0).toNat < 2 * (r 1 1).toNat + (r 0 1).toNat
  then 1 else 0

/-- Jolt Eq. (5)'s shape at two chunks: sub-tables `LT_lo, EQ_lo` read chunk 0
and `LT_hi, EQ_hi` read chunk 1 (`k = 2`), combined by
`g = LT_hi + EQ_hi * LT_lo`. -/
def ltuDecomposition : TableDecomposition (ZMod 5) 2 2 4 where
  subTable := ![ltChunk, eqChunkTable, ltChunk, eqChunkTable]
  chunk := ![0, 0, 1, 1]
  gTable := fun b => ofBool (b 2) + ofBool (b 3) * ofBool (b 0)

/-- **`k = 2` is real**: less-than needs two sub-tables per chunk, and the
combining polynomial is genuinely non-tensor (`LT_hi + EQ_hi * LT_lo`). -/
theorem ltu_decomposes : Decomposes ltuTable ltuDecomposition := by
  unfold Decomposes
  decide

end LtuExample

/-! ## TEETH -- the split chunking refused, over every field -/

/-- Equality under the SPLIT chunking: chunk 0 holds all of `x`, chunk 1 all of
`y`.  As a `2^w x 2^w` matrix this is the identity matrix. -/
def splitEqTable (w : ℕ) : (Fin 2 → Fin w → Bool) → F :=
  fun r => if r 0 = r 1 then 1 else 0

/-- The split table is the interleaved table after transposing the chunking --
the FUNCTION is the same; only the chunk assignment differs. -/
theorem splitEq_transpose (r : Fin 2 → Fin 2 → Bool) :
    splitEqTable (F := F) 2 (fun j i => r i j) = interleavedEqTable 2 r := by
  simp [splitEqTable, interleavedEqTable, funext_iff]

private theorem finTwoCases : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide

/-- The engine of the refutation: no multilinear `g` factors the `4 x 4`
identity matrix through one field coordinate per side.  `g` is affine in its
first coordinate; an affine map with two distinct roots is zero everywhere,
and the diagonal demands a `1`. -/
private theorem no_multilinear_eq_factoring
    {u v g : (Fin 2 → Bool) → F}
    (hfact : ∀ x y : Fin 2 → Bool,
      (if x = y then (1 : F) else 0) = mle g ![u x, v y]) : False := by
  -- distinct rows force `u` to be injective
  have hinj : ∀ x x' : Fin 2 → Bool, u x = u x' → x = x' := by
    intro x x' hxx'
    by_contra hne
    have h1 := hfact x x
    have h2 := hfact x' x
    rw [if_pos rfl] at h1
    rw [if_neg (Ne.symm hne)] at h2
    rw [hxx'] at h1
    exact one_ne_zero (h1.trans h2.symm)
  set vb := v ![false, false] with hvb
  -- `mle g` is affine in its first coordinate
  have haff : ∀ s : F, mle g ![s, vb]
      = (1 - s) * mle g ![(0 : F), vb] + s * mle g ![(1 : F), vb] := by
    intro s
    have hupd : ∀ t : F,
        Function.update (![(0 : F), vb]) 0 t = ![t, vb] := by
      intro t
      funext i
      fin_cases i <;> simp [Function.update]
    have h := mle_multilinear g 0 (![(0 : F), vb]) s
    rw [hupd s, hupd 0, hupd 1] at h
    exact h
  have H0 := hfact ![false, false] ![false, false]
  have H1 := hfact ![true, false] ![false, false]
  have H2 := hfact ![false, true] ![false, false]
  rw [if_pos rfl] at H0
  rw [if_neg (by decide)] at H1
  rw [if_neg (by decide)] at H2
  rw [haff] at H0 H1 H2
  have hs : u ![true, false] ≠ u ![false, true] := fun h =>
    (by decide : ¬(![true, false] = ![false, true])) (hinj _ _ h)
  -- two distinct roots of an affine map kill both coefficients
  have h12 : (u ![true, false] - u ![false, true])
      * (mle g ![(1 : F), vb] - mle g ![(0 : F), vb]) = 0 := by
    linear_combination H2 - H1
  have hBA : mle g ![(1 : F), vb] = mle g ![(0 : F), vb] := by
    rcases mul_eq_zero.mp h12 with h | h
    · exact absurd (sub_eq_zero.mp h) hs
    · exact sub_eq_zero.mp h
  have hA0 : mle g ![(0 : F), vb] = 0 := by
    linear_combination -H1 - u ![true, false] * hBA
  rw [hBA, hA0] at H0
  simp at H0

/-- **TEETH: the split-chunking equality table is NOT decomposable** with one
sub-table per chunk, over ANY field.  Same function as
`interleavedEq_decomposes`'s (by `splitEq_transpose`); only the chunking
changed.  Decomposability is a property of the (function, chunking, alpha)
triple. -/
theorem splitEq_not_decomposable :
    ¬ Decomposable (F := F) 2 2 2 (splitEqTable 2) := by
  rintro ⟨D, hD⟩
  rcases finTwoCases (D.chunk 0) with h0 | h0 <;>
    rcases finTwoCases (D.chunk 1) with h1 | h1
  · -- both sub-tables read chunk 0: the table cannot depend on `y`, but it does
    have e1 : (1 : F) = D.combined ![![false, false], ![false, false]] := by
      simpa [splitEqTable] using hD ![![false, false], ![false, false]]
    have e0 : (0 : F) = D.combined ![![false, false], ![true, false]] := by
      simpa [splitEqTable,
        (by decide : ¬((![false, false] : Fin 2 → Bool) = ![true, false]))]
        using hD ![![false, false], ![true, false]]
    have hreads : D.readsAt ![![false, false], ![false, false]]
        = D.readsAt ![![false, false], ![true, false]] := by
      funext a
      rcases finTwoCases a with ha | ha <;> subst ha <;>
        simp [TableDecomposition.readsAt, h0, h1]
    have hcomb : D.combined ![![false, false], ![false, false]]
        = D.combined ![![false, false], ![true, false]] := by
      unfold TableDecomposition.combined
      rw [hreads]
    exact one_ne_zero (e1.trans (hcomb.trans e0.symm))
  · -- chunk map is the identity: the bilinear factoring engine fires
    refine no_multilinear_eq_factoring (u := fun x => D.subTable 0 x)
      (v := fun y => D.subTable 1 y) (g := D.gTable) ?_
    intro x y
    have h := hD ![x, y]
    simp only [splitEqTable, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    refine h.trans ?_
    unfold TableDecomposition.combined TableDecomposition.readsAt
    congr 1
    funext a
    rcases finTwoCases a with ha | ha <;> subst ha <;> simp [h0, h1]
  · -- chunk map is the swap: same engine after flipping the diagonal
    refine no_multilinear_eq_factoring (u := fun x => D.subTable 0 x)
      (v := fun y => D.subTable 1 y) (g := D.gTable) ?_
    intro x y
    have h := hD ![y, x]
    simp only [splitEqTable, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hcomm : (if x = y then (1 : F) else 0) = if y = x then 1 else 0 := by
      by_cases hxy : x = y
      · simp [hxy]
      · simp [hxy, Ne.symm hxy]
    refine (hcomm.trans h).trans ?_
    unfold TableDecomposition.combined TableDecomposition.readsAt
    congr 1
    funext a
    rcases finTwoCases a with ha | ha <;> subst ha <;> simp [h0, h1]
  · -- both sub-tables read chunk 1: the table cannot depend on `x`, but it does
    have e1 : (1 : F) = D.combined ![![false, false], ![false, false]] := by
      simpa [splitEqTable] using hD ![![false, false], ![false, false]]
    have e0 : (0 : F) = D.combined ![![true, false], ![false, false]] := by
      simpa [splitEqTable,
        (by decide : ¬((![true, false] : Fin 2 → Bool) = ![false, false]))]
        using hD ![![true, false], ![false, false]]
    have hreads : D.readsAt ![![false, false], ![false, false]]
        = D.readsAt ![![true, false], ![false, false]] := by
      funext a
      rcases finTwoCases a with ha | ha <;> subst ha <;>
        simp [TableDecomposition.readsAt, h0, h1]
    have hcomb : D.combined ![![false, false], ![false, false]]
        = D.combined ![![true, false], ![false, false]] := by
      unfold TableDecomposition.combined
      rw [hreads]
    exact one_ne_zero (e1.trans (hcomb.trans e0.symm))

/-! ## The read-integrity obligation, named and refutable -/

/-- `[LASSO-READ-ORACLE]`: an accepting read oracle for the sub-tables only
accepts true sub-table MLE evaluations.  This is what the counter layer
(offline memory checking / LogUp fingerprint) plus `[LASSO-CHUNK-LINK]` must
deliver; stating it keeps the obligation from quietly reading as `True`. -/
def SurgeReadOracle {c w α : ℕ} (D : TableDecomposition F c w α)
    (Accepts : Fin α → (Fin w → F) → F → Prop) : Prop :=
  ∀ a x v, Accepts a x v → v = mle (D.subTable a) x

/-- The obligation is not free: the all-accepting oracle falsifies it. -/
theorem surgeReadOracle_all_accepting_refuted {c w α : ℕ}
    (D : TableDecomposition F c w α) (a : Fin α) :
    ¬ SurgeReadOracle D (fun _ _ _ => True) := by
  intro h
  have hbad := h a (fun _ => 0) (mle (D.subTable a) (fun _ => 0) + 1) trivial
  simp at hbad

/-- info: 'Minidregg.Selvage.spark_table_decomposes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spark_table_decomposes
/-- info: 'Minidregg.Selvage.interleavedEq_decomposes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms interleavedEq_decomposes
/-- info: 'Minidregg.Selvage.LtuExample.ltu_decomposes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LtuExample.ltu_decomposes
/-- info: 'Minidregg.Selvage.splitEq_not_decomposable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms splitEq_not_decomposable
/-- info: 'Minidregg.Selvage.TableDecomposition.combined_by_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TableDecomposition.combined_by_chi
/-- info: 'Minidregg.Selvage.surgeReadOracle_all_accepting_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms surgeReadOracle_all_accepting_refuted

end Minidregg.Selvage
