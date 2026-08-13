/-
# Selvage.Proximity — the FRI/WHIR folding low-degree test (the rate<1 linchpin).

The ONE reduction behind `[DEC-proximity]`, `[OB3-c-prox]`, `[ACC-sound-list]`:
turning "is this word δ-close to the Reed–Solomon code" into a checkable
claim, by iterated folding down to a directly-checkable constant.

**Construction** (FRI/BS08; WHIR §2/§4 folding): a word `f` on a domain `L`
closed under negation folds, at challenge `α`, to the word on `L²`

  `Fold(f, α)(x²) = (f(x) + f(−x))/2 + α · (f(x) − f(−x))/(2x)`

— the even/odd decomposition `p(X) = pₑ(X²) + X·pₒ(X²)` evaluated: a
degree-<2d codeword folds to the degree-<d codeword `pₑ + α·pₒ`. A
`FoldingTower` iterates this down to degree < 1, where membership is literally
"the word is constant" (`mem_reedSolomonCode_one_iff`). Towers are NECESSARILY
finite: the section `sec` makes `sq` surjective, so levels halve exactly
(`card_eq_two_mul_card`) — the `j < m` guard is mathematics, not convenience.

**PROVED here, no sorry, standard axioms only** (propext/choice/Quot.sound):

* the even/odd algebra: decomposition identity, degree halving, and the
  recomposition `pₑ(X²) + X·pₒ(X²)` with its degree bound — both directions;
* `fold` well-definedness (the section choice is immaterial: `foldEven_sq`,
  `foldOdd_sq`), the reconstruction identity `E(x²) + x·O(x²) = f(x)`, and
  **`fold_preserves_code`** — one round is complete;
* **`proximity_complete`** — an honest codeword passes the whole descent for
  EVERY challenge stream (`word_mem_code`, induction on the tower);
* **`proximity_far_covering`** — the FRI round-reduction STRUCTURE: a δ-far
  word's acceptance event is covered by per-round, prefix-measurable
  (`word_congr`) bad sets of size ≤ b, given per-level distance preservation.
  The output is EXACTLY the input shape of `AdaptiveUnionBound`
  (Selvage/Sumcheck.lean), so the two compose on sight;
* the adaptive counting union bound (`card_filter_exists_coord_mem_le`,
  fiberwise counting) and the heads **`proximity_sound`** (≤ m·b·|F|^{m−1}
  accepting tuples) and **`proximity_sound_prob`** (probability ≤ m·b/|F|);
* **`fold_notMem_of_notMem`** — the exact-membership folding lemma, `b = 1`,
  UNCONDITIONAL: the fold is affine in α, two good challenges force both
  components into the linear code, recomposition puts `f` in the code;
* **`close_of_correlatedAgreement`** — correlated agreement of the two fold
  components lifts through the `sq`-preimage (`card_sq_preimage`) to δ-close
  the word itself: the arrow that makes proximity gaps imply folding
  soundness.

**The residual `[PROX-fold-distance]`** (`FoldDistancePreserving`, bad-set
form: a δ-far word folds δ-far off ≤ b challenges) is not a monolith — it is
delivered in one regime and REDUCED in the other:

* sub-quantization `0 ≤ δ < 1/|κ|`: **PROVED**, `b = 1`
  (`foldDistancePreserving_of_lt_inv_card`) — so the iterated test is
  end-to-end sound TODAY at exact-membership resolution: the F₅ keystone
  discharges EVERY hypothesis of `proximity_sound` and attains the bound;
* macroscopic `δ ∈ (0, 1−B)`: **REDUCED**
  (`foldDistancePreserving_of_isProximityGenerator`, `b ≥ err(δ)·|F|`) to
  `IsProximityGenerator (affineGenerator F)` for the folded RS code — WHIR
  Theorem 4.8 / BCIKS 2020/654, the SAME standing `hPG` hypothesis that
  Selvage/ReedSolomon.lean's Corollary 4.11 carries. ONE proximity-gap
  hypothesis now gates the entire rate<1 story (mutual CA and the LDT
  alike); its UD-regime instantiation is the ladder's next rung
  (docs/SELVAGE-RECOMPOSITION.md §5) and is NOT claimed here.

**Honest scope limits.** This is the folding/decision skeleton of the LDT at
claim resolution, matching the strict decider contract (`[DEC-proximity]`):
the verifier here reads whole level words. NOT modeled: the oracle/Merkle
query phase (spot-checks, per-round consistency openings, their
`t = λ/−log(1−δ)` repetition — that layer is `[DEC-open]`-adjacent), the
derandomized powers-of-α batching, and the WHIR-style δ-vs-min(δ,·) radius
refinements (absorbed into the bad-set abstraction). The probability
statement is uniform counting over challenge tuples `Fin m → F` — the
`uniformProb` rendering lives in Selvage/Sumcheck.lean's engine, whose import
chain (Selvage.Depth) is lane-blocked; unification of the two union-bound
renderings is flagged integration debt, not hidden.
-/
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Selvage.ReedSolomon

namespace Minidregg.Selvage

open Polynomial

variable {F : Type*} [Field F]
variable {ι : Type*} {κ : Type*}

/-! ## The even/odd polynomial decomposition

`p(X) = pₑ(X²) + X·pₒ(X²)`: the algebra that makes folding degree-halving.
Everything here is proved; no Fintype/domain structure is needed yet. -/

/-- The even part `pₑ`: coefficient `k` is `p`'s coefficient `2k`. -/
noncomputable def evenPart (p : Polynomial F) : Polynomial F :=
  ∑ k ∈ Finset.range (p.natDegree + 1), C (p.coeff (2 * k)) * X ^ k

/-- The odd part `pₒ`: coefficient `k` is `p`'s coefficient `2k+1`. -/
noncomputable def oddPart (p : Polynomial F) : Polynomial F :=
  ∑ k ∈ Finset.range (p.natDegree + 1), C (p.coeff (2 * k + 1)) * X ^ k

theorem evenPart_eval (p : Polynomial F) (y : F) :
    (evenPart p).eval y
      = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff (2 * k) * y ^ k := by
  simp [evenPart, eval_finsetSum]

theorem oddPart_eval (p : Polynomial F) (y : F) :
    (oddPart p).eval y
      = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff (2 * k + 1) * y ^ k := by
  simp [oddPart, eval_finsetSum]

/-- Parity split of a range sum: `∑_{j<2N} f j = ∑_{k<N} f(2k) + ∑_{k<N} f(2k+1)`. -/
private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), f j
      = ∑ k ∈ Finset.range N, f (2 * k) + ∑ k ∈ Finset.range N, f (2 * k + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring]
      simp only [Finset.sum_range_succ]
      rw [ih]
      abel

/-- **The even/odd decomposition, evaluated**: `pₑ(x²) + x·pₒ(x²) = p(x)`. -/
theorem evenPart_add_X_mul_oddPart_eval (p : Polynomial F) (x : F) :
    (evenPart p).eval (x ^ 2) + x * (oddPart p).eval (x ^ 2) = p.eval x := by
  rw [evenPart_eval, oddPart_eval, Finset.mul_sum,
    Polynomial.eval_eq_sum_range' (n := 2 * (p.natDegree + 1)) (by omega),
    sum_range_two_mul (fun j => p.coeff j * x ^ j)]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by rw [pow_mul]
  · exact Finset.sum_congr rfl fun k _ => by
      conv_rhs => rw [pow_succ, pow_mul]
      ring

/-- If `p` has degree `< 2d`, its even part has degree `< d`. -/
theorem degree_evenPart_lt {p : Polynomial F} {d : ℕ}
    (hp : p.degree < ((2 * d : ℕ) : WithBot ℕ)) :
    (evenPart p).degree < (d : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun k _ => ?_)
  by_cases hkd : k < d
  · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le k _) (WithBot.coe_lt_coe.mpr hkd)
  · have hc : p.coeff (2 * k) = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hp (by exact_mod_cast Nat.mul_le_mul_left 2 (not_lt.mp hkd)))
    rw [hc, map_zero, zero_mul, degree_zero]
    exact WithBot.bot_lt_coe d

/-- If `p` has degree `< 2d`, its odd part has degree `< d`. -/
theorem degree_oddPart_lt {p : Polynomial F} {d : ℕ}
    (hp : p.degree < ((2 * d : ℕ) : WithBot ℕ)) :
    (oddPart p).degree < (d : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun k _ => ?_)
  by_cases hkd : k < d
  · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le k _) (WithBot.coe_lt_coe.mpr hkd)
  · have h2k : 2 * d ≤ 2 * k + 1 :=
      le_trans (Nat.mul_le_mul_left 2 (not_lt.mp hkd)) (Nat.le_succ _)
    have hc : p.coeff (2 * k + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hp (by exact_mod_cast h2k))
    rw [hc, map_zero, zero_mul, degree_zero]
    exact WithBot.bot_lt_coe d

/-! ## Folding domains

The structure a domain needs to support one FRI fold: closure under negation
(`neg`, an involution through `dom`), a squaring projection `sq` onto the next
level's index set, and a computable section `sec` of `sq` (each folded point
names a square root — keeps `fold` computable for the concrete keystones).
`sec` forces `sq` surjective, so `|ι| = 2·|κ|` exactly: folding domains halve,
and towers over a finite field are NECESSARILY finite (the `j < m` guard in
`FoldingTower` below is mathematics, not convenience). `dom`/`domSq` are
PARAMETERS, not fields, so consecutive tower levels share their embedding
definitionally — no coherence conditions anywhere. -/

/-- Folding structure on an evaluation domain: negation closure, the squaring
projection to the folded domain, a section of it, and the two nondegeneracy
facts the fold's divisions need (`0 ∉ L`, `char F ≠ 2`). -/
structure FoldingData (F : Type*) [Field F] {ι κ : Type*}
    (dom : ι ↪ F) (domSq : κ ↪ F) where
  /-- Negation on the index set: `dom (neg i) = −dom i`. -/
  neg : ι → ι
  dom_neg : ∀ i, dom (neg i) = - dom i
  /-- The squaring projection: `domSq (sq i) = (dom i)²`. -/
  sq : ι → κ
  domSq_sq : ∀ i, domSq (sq i) = dom i ^ 2
  /-- A section of `sq`: each folded point names one of its two square roots. -/
  sec : κ → ι
  sq_sec : ∀ k, sq (sec k) = k
  dom_ne_zero : ∀ i, dom i ≠ 0
  two_ne : (2 : F) ≠ 0

namespace FoldingData

variable {dom : ι ↪ F} {domSq : κ ↪ F} (D : FoldingData F dom domSq)

/-- `neg` has no fixed point: `x = −x` would force `2x = 0`. -/
theorem neg_ne (i : ι) : D.neg i ≠ i := by
  intro h
  have hd : dom i = - dom i := by rw [← D.dom_neg i, h]
  have h2 : (2 : F) * dom i = 0 := by
    have := congrArg (· + dom i) hd
    simpa [two_mul] using this
  rcases mul_eq_zero.mp h2 with h2' | hdz
  · exact D.two_ne h2'
  · exact D.dom_ne_zero i hdz

/-- `neg` is an involution (through the injective embedding). -/
theorem neg_neg (i : ι) : D.neg (D.neg i) = i :=
  dom.injective (by rw [D.dom_neg, D.dom_neg, _root_.neg_neg])

/-- Negation does not change the square: `sq (neg i) = sq i`. -/
theorem sq_neg (i : ι) : D.sq (D.neg i) = D.sq i :=
  domSq.injective (by rw [D.domSq_sq, D.domSq_sq, D.dom_neg, neg_sq])

/-- The fibre of `sq` over `sq i` is exactly `{i, neg i}`: equal squares in a
field mean equal up to sign. -/
theorem eq_or_eq_neg_of_sq_eq {i j : ι} (h : D.sq j = D.sq i) :
    j = i ∨ j = D.neg i := by
  have hsq : dom j ^ 2 = dom i ^ 2 := by
    rw [← D.domSq_sq, ← D.domSq_sq, h]
  have hms : dom j * dom j = dom i * dom i := by
    rw [← pow_two, ← pow_two]; exact hsq
  rcases mul_self_eq_mul_self_iff.mp hms with h1 | h1
  · exact Or.inl (dom.injective h1)
  · exact Or.inr (dom.injective (by rw [D.dom_neg, h1]))

end FoldingData

/-! ## The fold -/

section Fold

variable {dom : ι ↪ F} {domSq : κ ↪ F}

/-- The even component of the folded word: `(f(x) + f(−x))/2` at `x = sec k`. -/
def foldEven (D : FoldingData F dom domSq) (f : ι → F) (k : κ) : F :=
  (f (D.sec k) + f (D.neg (D.sec k))) / 2

/-- The odd component of the folded word: `(f(x) − f(−x))/(2x)` at `x = sec k`. -/
def foldOdd (D : FoldingData F dom domSq) (f : ι → F) (k : κ) : F :=
  (f (D.sec k) - f (D.neg (D.sec k))) / (2 * dom (D.sec k))

/-- **The FRI fold at challenge `α`**: `Fold(f,α) = foldEven f + α · foldOdd f`
— affine in `α` (the fact the proximity-gap machinery consumes). -/
def fold (D : FoldingData F dom domSq) (f : ι → F) (α : F) : κ → F :=
  fun k => foldEven D f k + α * foldOdd D f k

variable (D : FoldingData F dom domSq)

/-- The even component is well-defined: at `sq i` it reads `(f i + f(−i))/2`
whichever square root the section chose. -/
theorem foldEven_sq (f : ι → F) (i : ι) :
    foldEven D f (D.sq i) = (f i + f (D.neg i)) / 2 := by
  rcases D.eq_or_eq_neg_of_sq_eq (D.sq_sec (D.sq i)) with h | h
  · rw [foldEven, h]
  · rw [foldEven, h, D.neg_neg, add_comm]

/-- The odd component is well-defined: at `sq i` it reads `(f i − f(−i))/(2x)`
whichever square root the section chose (the sign of the root cancels against
the sign of the difference). -/
theorem foldOdd_sq (f : ι → F) (i : ι) :
    foldOdd D f (D.sq i) = (f i - f (D.neg i)) / (2 * dom i) := by
  rcases D.eq_or_eq_neg_of_sq_eq (D.sq_sec (D.sq i)) with h | h
  · rw [foldOdd, h]
  · rw [foldOdd, h, D.neg_neg, D.dom_neg, mul_neg, div_neg, ← neg_div, neg_sub]

/-- **The reconstruction identity**: the two fold components determine the word
— `foldEven f (sq i) + x · foldOdd f (sq i) = f i`. This is what makes the fold
lossless on honest data and powers the proximity-gap reduction below. -/
theorem foldEven_add_mul_foldOdd (f : ι → F) (i : ι) :
    foldEven D f (D.sq i) + dom i * foldOdd D f (D.sq i) = f i := by
  have hx := D.dom_ne_zero i
  have h2 := D.two_ne
  rw [foldEven_sq, foldOdd_sq]
  field_simp
  ring

/-- The fold is well-defined on squares:
`Fold(f,α)(sq i) = (f i + f(−i))/2 + α·(f i − f(−i))/(2x)`. -/
theorem fold_sq (f : ι → F) (α : F) (i : ι) :
    fold D f α (D.sq i)
      = (f i + f (D.neg i)) / 2 + α * ((f i - f (D.neg i)) / (2 * dom i)) := by
  rw [fold, foldEven_sq, foldOdd_sq]

private theorem foldEven_eval_sq (p : Polynomial F) (i : ι) :
    foldEven D (fun j => p.eval (dom j)) (D.sq i)
      = (evenPart p).eval (domSq (D.sq i)) := by
  have h2 := D.two_ne
  rw [foldEven_sq, D.domSq_sq, D.dom_neg]
  rw [← evenPart_add_X_mul_oddPart_eval p (dom i),
    ← evenPart_add_X_mul_oddPart_eval p (-dom i), neg_sq]
  field_simp
  ring

private theorem foldOdd_eval_sq (p : Polynomial F) (i : ι) :
    foldOdd D (fun j => p.eval (dom j)) (D.sq i)
      = (oddPart p).eval (domSq (D.sq i)) := by
  have h2 := D.two_ne
  have hx := D.dom_ne_zero i
  rw [foldOdd_sq, D.domSq_sq, D.dom_neg]
  rw [← evenPart_add_X_mul_oddPart_eval p (dom i),
    ← evenPart_add_X_mul_oddPart_eval p (-dom i), neg_sq]
  field_simp
  ring

/-- On the evaluations of a polynomial, the even fold component is the even
part evaluated on the folded domain. -/
theorem foldEven_eval (p : Polynomial F) (k : κ) :
    foldEven D (fun i => p.eval (dom i)) k = (evenPart p).eval (domSq k) := by
  conv_lhs => rw [← D.sq_sec k]
  rw [foldEven_eval_sq, D.sq_sec]

/-- On the evaluations of a polynomial, the odd fold component is the odd part
evaluated on the folded domain. -/
theorem foldOdd_eval (p : Polynomial F) (k : κ) :
    foldOdd D (fun i => p.eval (dom i)) k = (oddPart p).eval (domSq k) := by
  conv_lhs => rw [← D.sq_sec k]
  rw [foldOdd_eval_sq, D.sq_sec]

/-- **The fold of a codeword's evaluations is the evaluation of `pₑ + α·pₒ`.** -/
theorem fold_eval (p : Polynomial F) (α : F) (k : κ) :
    fold D (fun i => p.eval (dom i)) α k
      = (evenPart p + C α * oddPart p).eval (domSq k) := by
  rw [fold, foldEven_eval, foldOdd_eval, eval_add, eval_mul, eval_C]

/-- **`fold_preserves_code` — one FRI round is complete.** A degree-<2d
codeword on the domain folds, at EVERY challenge, to a degree-<d codeword on
the folded domain: the even/odd parts are genuinely lower degree. -/
theorem fold_preserves_code {d : ℕ} {f : ι → F}
    (hf : f ∈ reedSolomonCode dom (2 * d)) (α : F) :
    fold D f α ∈ reedSolomonCode domSq d := by
  obtain ⟨p, hdeg, hfp⟩ := mem_reedSolomonCode_iff.mp hf
  have hfold : fold D f α = fold D (fun i => p.eval (dom i)) α := by
    funext k
    simp only [fold, foldEven, foldOdd, hfp]
  refine mem_reedSolomonCode_iff.mpr ⟨evenPart p + C α * oddPart p, ?_, fun k => ?_⟩
  · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (degree_evenPart_lt hdeg) ?_)
    calc (C α * oddPart p).degree ≤ (oddPart p).degree := by
          rw [← Polynomial.smul_eq_C_mul]; exact degree_smul_le _ _
      _ < (d : WithBot ℕ) := degree_oddPart_lt hdeg
  · rw [hfold, fold_eval]

end Fold

/-! ## The degree-<1 base: Reed–Solomon at `d = 1` is exactly the constants -/

/-- The base check of the LDT, made directly checkable: membership in
`RS[dom, 1]` is exactly "the word is constant". -/
theorem mem_reedSolomonCode_one_iff {dom : ι ↪ F} {f : ι → F} :
    f ∈ reedSolomonCode dom 1 ↔ ∀ i j, f i = f j := by
  constructor
  · rintro hf i j
    obtain ⟨p, hdeg, hfp⟩ := mem_reedSolomonCode_iff.mp hf
    have hle : p.degree ≤ 0 := Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hdeg)
    obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨p.coeff 0, Polynomial.eq_C_of_degree_le_zero hle⟩
    rw [hfp i, hfp j, eval_C, eval_C]
  · intro hconst
    rcases isEmpty_or_nonempty ι with hι | hι
    · have : f = 0 := funext fun i => absurd ⟨i⟩ (not_nonempty_iff.mpr hι)
      rw [this]; exact Submodule.zero_mem _
    · obtain ⟨i₀⟩ := hι
      refine mem_reedSolomonCode_iff.mpr ⟨C (f i₀), ?_, fun i => ?_⟩
      · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.zero_lt_one)
      · rw [eval_C]; exact hconst i i₀

/-! ## Folding towers and the iterated test

A tower is a chain of folding domains `ι 0 → ι 1 → ⋯ → ι m`. The level
embeddings are a SINGLE field `dom` consumed by every level's `FoldingData` as
a parameter, so consecutive levels agree definitionally — no coherence
conditions. The `j < m` guard on the folding data is forced by mathematics,
not convenience: `sec` makes `sq` surjective, so `|ι j| = 2·|ι (j+1)|` and an
unguarded ℕ-indexed tower over a finite field cannot exist. -/

/-- A height-`m` FRI folding tower: an embedding for every level and folding
structure between consecutive levels below `m`. -/
structure FoldingTower (F : Type*) [Field F] (ι : ℕ → Type*) (m : ℕ) where
  /-- The level-`n` evaluation domain. -/
  dom : ∀ n, ι n ↪ F
  /-- The folding structure from level `j` down to level `j+1`. -/
  data : ∀ j, j < m → FoldingData F (dom j) (dom (j + 1))

section Tower

variable {ι : ℕ → Type*} {m : ℕ}

/-- The descent: the level-`n` word of the iterated fold of `f` under the
challenge stream `αs` (round `j` consumes `αs j`). -/
def FoldingTower.word (T : FoldingTower F ι m) (f : ι 0 → F) (αs : ℕ → F) :
    ∀ n, n ≤ m → (ι n → F)
  | 0, _ => f
  | n + 1, h => fold (T.data n h) (T.word f αs n (Nat.le_of_succ_le h)) (αs n)

variable (T : FoldingTower F ι m)

@[simp] theorem FoldingTower.word_zero (f : ι 0 → F) (αs : ℕ → F) (h : 0 ≤ m) :
    T.word f αs 0 h = f := rfl

theorem FoldingTower.word_succ (f : ι 0 → F) (αs : ℕ → F) {n : ℕ} (h : n + 1 ≤ m) :
    T.word f αs (n + 1) h
      = fold (T.data n h) (T.word f αs n (Nat.le_of_succ_le h)) (αs n) := rfl

/-- The level-`n` word reads only the challenge PREFIX `αs 0, …, αs (n−1)` —
the measurability fact the adaptive union bound consumes. -/
theorem FoldingTower.word_congr (f : ι 0 → F) {αs βs : ℕ → F} :
    ∀ (n : ℕ) (hn : n ≤ m), (∀ j, j < n → αs j = βs j) →
      T.word f αs n hn = T.word f βs n hn := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ k ih =>
      intro hn hpre
      rw [T.word_succ, T.word_succ,
        ih (Nat.le_of_succ_le hn) (fun j hj => hpre j (Nat.lt_succ_of_lt hj)),
        hpre k (Nat.lt_succ_self k)]

/-- **The low-degree test**: run the `m`-round descent on `f` with challenge
stream `αs`, then check the base word is a degree-`< deg m` codeword. With
`deg m = 1` the base check is literally "the final word is constant"
(`mem_reedSolomonCode_one_iff`). -/
def proximityTest (T : FoldingTower F ι m) (deg : ℕ → ℕ) (f : ι 0 → F)
    (αs : ℕ → F) : Prop :=
  T.word f αs m le_rfl ∈ reedSolomonCode (T.dom m) (deg m)

/-- Codewords descend: at every level of the tower the word of an initial
codeword is a codeword for the halved degree bound (`fold_preserves_code`,
iterated). -/
theorem FoldingTower.word_mem_code {deg : ℕ → ℕ}
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1)) {f : ι 0 → F}
    (hf : f ∈ reedSolomonCode (T.dom 0) (deg 0)) (αs : ℕ → F) :
    ∀ (n : ℕ) (hn : n ≤ m),
      T.word f αs n hn ∈ reedSolomonCode (T.dom n) (deg n) := by
  intro n
  induction n with
  | zero => intro _; exact hf
  | succ k ih =>
      intro hn
      rw [T.word_succ]
      have hmem := ih (Nat.le_of_succ_le hn)
      rw [hdeg k hn] at hmem
      exact fold_preserves_code (T.data k hn) hmem (αs k)

/-- **Completeness, PROVED**: an honest codeword passes the test for EVERY
challenge stream. -/
theorem proximity_complete {deg : ℕ → ℕ}
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1)) {f : ι 0 → F}
    (hf : f ∈ reedSolomonCode (T.dom 0) (deg 0)) (αs : ℕ → F) :
    proximityTest T deg f αs :=
  T.word_mem_code hdeg hf αs m le_rfl

/-- Read a `Fin m` challenge tuple as a total stream (junk `0` past the
horizon; never consumed in range). Same device as Selvage/Sumcheck.lean's
`chalOf`, named apart to keep the import graph disjoint this lane. -/
def chalExt {m : ℕ} (r : Fin m → F) (n : ℕ) : F :=
  if h : n < m then r ⟨n, h⟩ else 0

@[simp] theorem chalExt_coe {m : ℕ} (r : Fin m → F) (j : Fin m) :
    chalExt r j.val = r j := by
  rw [chalExt, dif_pos j.isLt]

end Tower

/-! ## Distance preservation: the `[PROX-fold-distance]` interface -/

section FoldDistance

variable [DecidableEq F] [Fintype ι] [Fintype κ]
variable {dom : ι ↪ F} {domSq : κ ↪ F}

/-- Membership is δ-closeness at any δ ≥ 0 — the bridge from "far" to "the
base check rejects". -/
theorem close_of_mem {C : Submodule F (ι → F)} {g : ι → F} (hg : g ∈ C)
    {δ : ℝ} (hδ : 0 ≤ δ) : close δ C g :=
  ⟨g, hg, by rw [relDist, hammingDist_self]; simpa using hδ⟩

/-- **`[PROX-fold-distance]` — one round of folding preserves δ-farness, in
bad-challenge-set form.** If `f` is δ-far from the degree-`dbig` code, then
off a set of at most `b` fold challenges, `Fold(f, α)` stays δ-far from the
degree-`dsmall` code. This is the WHIR/BCIKS folding lemma (over a finite
field, "except with probability `err`" IS a bad set of `≤ err·|F|`
challenges). Realizers in this file: PROVED unconditionally with `b = 1` below
the quantization radius (`foldDistancePreserving_of_lt_inv_card`), and reduced
to Reed–Solomon's one standing `IsProximityGenerator` hypothesis (WHIR Thm
4.8 / BCIKS 2020/654) at macroscopic δ
(`foldDistancePreserving_of_isProximityGenerator`). -/
def FoldDistancePreserving (D : FoldingData F dom domSq) (dbig dsmall : ℕ)
    (δ : ℝ) (b : ℕ) : Prop :=
  ∀ f : ι → F, ¬ close δ (reedSolomonCode dom dbig) f →
    ∃ bad : Finset F, bad.card ≤ b ∧
      ∀ α, α ∉ bad → ¬ close δ (reedSolomonCode domSq dsmall) (fold D f α)

end FoldDistance

/-! ## Soundness: the round-reduction structure, proved

Far at the top + distance preservation each round ⇒ far at the base ⇒ the
base check rejects. Rendered as: the acceptance event is COVERED by
prefix-measurable per-round bad sets of size ≤ b — exactly the input shape of
the adaptive union bound (`AdaptiveUnionBound`, Selvage/Sumcheck.lean), then
counted directly. -/

section Soundness

variable [DecidableEq F] {ι : ℕ → Type*} [∀ n, Fintype (ι n)] {m : ℕ}

/-- **The FRI round-reduction, PROVED modulo `[PROX-fold-distance]`**: a δ-far
word's acceptance event is covered by per-round bad challenge sets — each of
size ≤ `b`, each depending only on the challenge PREFIX (adaptively, through
the level word). The residual is EXACTLY the per-level `hfold` hypothesis;
everything else — far-persistence off the bad sets, the base catch — is
proved. -/
theorem proximity_far_covering (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    {f : ι 0 → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    ∃ bad : (Fin m → F) → Fin m → Finset F,
      (∀ (i : Fin m) (r r' : Fin m → F),
        (∀ j : Fin m, (j : ℕ) < (i : ℕ) → r j = r' j) → bad r i = bad r' i)
      ∧ (∀ r i, (bad r i).card ≤ b)
      ∧ ∀ r : Fin m → F, proximityTest T deg f (chalExt r) → ∃ i, r i ∈ bad r i := by
  classical
  -- the bad set attached to a level-`j` word (∅ for words that are not far)
  have hbadAt : ∀ (j : ℕ) (hj : j < m) (w : ι j → F),
      ∃ bad : Finset F, bad.card ≤ b ∧
        (¬ close δ (reedSolomonCode (T.dom j) (deg j)) w →
          ∀ α, α ∉ bad →
            ¬ close δ (reedSolomonCode (T.dom (j + 1)) (deg (j + 1)))
              (fold (T.data j hj) w α)) := by
    intro j hj w
    by_cases hw : ¬ close δ (reedSolomonCode (T.dom j) (deg j)) w
    · obtain ⟨bad, hc, hb⟩ := hfold j hj w hw
      exact ⟨bad, hc, fun _ => hb⟩
    · exact ⟨∅, Nat.zero_le b, fun hw' => absurd (not_not.mp hw) hw'⟩
  choose badAt hbadCard hbadSpec using hbadAt
  refine ⟨fun r i => badAt i i.isLt (T.word f (chalExt r) i (le_of_lt i.isLt)),
    ?_, ?_, ?_⟩
  · -- prefix-measurability: the level-`i` word reads only challenges `< i`
    intro i r r' hagree
    exact congrArg (badAt i i.isLt)
      (T.word_congr f i (le_of_lt i.isLt) fun j hj => by
        have hjm : j < m := lt_trans hj i.isLt
        rw [chalExt, dif_pos hjm, chalExt, dif_pos hjm]
        exact hagree ⟨j, hjm⟩ hj)
  · exact fun r i => hbadCard i i.isLt _
  · -- far persists off the bad sets, so acceptance must hit one
    intro r hacc
    by_contra hmiss
    have hmiss' : ∀ i : Fin m,
        r i ∉ badAt i i.isLt (T.word f (chalExt r) i (le_of_lt i.isLt)) :=
      fun i hi => hmiss ⟨i, hi⟩
    have hfarAll : ∀ (n : ℕ) (hn : n ≤ m),
        ¬ close δ (reedSolomonCode (T.dom n) (deg n)) (T.word f (chalExt r) n hn) := by
      intro n
      induction n with
      | zero => intro _; exact hfar
      | succ k ih =>
          intro hn
          have hk : k < m := hn
          rw [T.word_succ]
          have hkfar := ih (Nat.le_of_succ_le hn)
          have hα : chalExt r k
              ∉ badAt k hk (T.word f (chalExt r) k (Nat.le_of_succ_le hn)) := by
            have h := hmiss' ⟨k, hk⟩
            rw [chalExt, dif_pos hk]
            exact h
          exact hbadSpec k hk _ hkfar _ hα
    exact hfarAll m le_rfl (close_of_mem hacc hδ)

end Soundness

/-! ## The counting engine

Adaptive union bound at the `Finset.card` level, self-contained on Mathlib.
(`adaptiveUnionBound_holds` in Selvage/Sumcheck.lean is the `uniformProb`
rendering of the same engine; that file's import chain — `Selvage.Depth` — is
off-limits to this lane by swarm hygiene, so the two renderings coexist until
an integration pass unifies them. Flagged as debt, not hidden.) -/

section Counting

variable [Fintype F] [DecidableEq F]

/-- One coordinate of a tuple lands in a bad set that does not depend on that
coordinate: at most `b·|F|^{m−1}` of the `|F|^m` tuples. Fiberwise counting
over the remaining coordinates; each fibre injects into its (frozen) bad set
via the free coordinate. -/
theorem card_filter_coord_mem_le {m b : ℕ} (i : Fin m)
    (bad : (Fin m → F) → Finset F)
    (hmeas : ∀ r r' : Fin m → F, (∀ j : Fin m, j ≠ i → r j = r' j) → bad r = bad r')
    (hcard : ∀ r, (bad r).card ≤ b) :
    (Finset.univ.filter fun r : Fin m → F => r i ∈ bad r).card
      ≤ b * Fintype.card F ^ (m - 1) := by
  classical
  set S := Finset.univ.filter fun r : Fin m → F => r i ∈ bad r with hS
  set proj : (Fin m → F) → ({j : Fin m // j ≠ i} → F) := fun r j => r j.val with hproj
  set ext : ({j : Fin m // j ≠ i} → F) → (Fin m → F) :=
    fun a j => if h : j = i then 0 else a ⟨j, h⟩ with hext
  rw [Finset.card_eq_sum_card_fiberwise
    (f := proj) (t := (Finset.univ : Finset ({j : Fin m // j ≠ i} → F)))
    (fun r _ => Finset.mem_univ _)]
  have hfiber : ∀ a : {j : Fin m // j ≠ i} → F,
      (S.filter fun r => proj r = a).card ≤ b := by
    intro a
    refine le_trans (Finset.card_le_card_of_injOn (fun r => r i) ?_ ?_) (hcard (ext a))
    · intro r hr
      obtain ⟨hrS, hra⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hr)
      have hri : r i ∈ bad r := (Finset.mem_filter.mp hrS).2
      have hbr : bad r = bad (ext a) := by
        refine hmeas r (ext a) fun j hj => ?_
        rw [hext]
        simp only [dif_neg hj]
        exact congrFun hra ⟨j, hj⟩
      exact Finset.mem_coe.mpr (hbr ▸ hri)
    · intro r hr r' hr' hrr'
      obtain ⟨-, hra⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hr)
      obtain ⟨-, hra'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hr')
      funext j
      by_cases hj : j = i
      · rw [hj]; exact hrr'
      · calc r j = a ⟨j, hj⟩ := congrFun hra ⟨j, hj⟩
          _ = r' j := (congrFun hra' ⟨j, hj⟩).symm
  refine le_trans (Finset.sum_le_sum fun a _ => hfiber a) ?_
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcardfun : Fintype.card ({j : Fin m // j ≠ i} → F)
      = Fintype.card F ^ (m - 1) := by
    rw [Fintype.card_fun]
    congr 1
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  rw [hcardfun, mul_comm]

/-- **The adaptive counting union bound**: `m` prefix-measurable bad sets of
size ≤ `b` are hit by at most `m·b·|F|^{m−1}` of the `|F|^m` challenge
tuples — i.e. probability `≤ m·b/|F|`. -/
theorem card_filter_exists_coord_mem_le {m b : ℕ}
    (bad : (Fin m → F) → Fin m → Finset F)
    (hmeas : ∀ (i : Fin m) (r r' : Fin m → F),
      (∀ j : Fin m, (j : ℕ) < (i : ℕ) → r j = r' j) → bad r i = bad r' i)
    (hcard : ∀ r i, (bad r i).card ≤ b) :
    (Finset.univ.filter fun r : Fin m → F => ∃ i, r i ∈ bad r i).card
      ≤ m * (b * Fintype.card F ^ (m - 1)) := by
  classical
  have hsub : (Finset.univ.filter fun r : Fin m → F => ∃ i, r i ∈ bad r i)
      ⊆ Finset.univ.biUnion
          (fun i : Fin m => Finset.univ.filter fun r => r i ∈ bad r i) := by
    intro r hr
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hr).2
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hi⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  refine le_trans (Finset.sum_le_sum fun i _ =>
    card_filter_coord_mem_le i (fun r => bad r i)
      (fun r r' hj => hmeas i r r' fun j hji =>
        hj j fun hje => absurd (congrArg Fin.val hje) (Nat.ne_of_lt hji))
      (fun r => hcard r i)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Counting

/-! ## The soundness heads: `proximity_sound` -/

section SoundnessHead

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] {m : ℕ}
variable [Fintype F]

/-- The acceptance set of the test: the challenge tuples on which a fixed word
passes (classically measurable — base-code membership is a `Prop`). -/
noncomputable def acceptSet (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (f : ι 0 → F) : Finset (Fin m → F) :=
  letI : DecidablePred fun r : Fin m → F => proximityTest T deg f (chalExt r) :=
    fun _ => Classical.propDecidable _
  Finset.univ.filter fun r => proximityTest T deg f (chalExt r)

omit [∀ n, Fintype (ι n)] in
theorem mem_acceptSet {T : FoldingTower F ι m} {deg : ℕ → ℕ} {f : ι 0 → F}
    {r : Fin m → F} :
    r ∈ acceptSet T deg f ↔ proximityTest T deg f (chalExt r) := by
  simp [acceptSet]

variable [DecidableEq F]

/-- **`proximity_sound` (counting form)** — the LDT soundness, proved modulo
the per-level `[PROX-fold-distance]` hypothesis `hfold` and NOTHING else: a
δ-far word passes for at most `m·b·|F|^{m−1}` of the `|F|^m` challenge tuples.
Round-reduction structure (`proximity_far_covering`) + adaptive counting union
bound. -/
theorem proximity_sound (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    {f : ι 0 → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (acceptSet T deg f).card ≤ m * (b * Fintype.card F ^ (m - 1)) := by
  classical
  obtain ⟨bad, hmeas, hcard, hcover⟩ := proximity_far_covering T deg hδ hfold hfar
  refine le_trans (Finset.card_le_card fun r hr => ?_)
    (card_filter_exists_coord_mem_le bad hmeas hcard)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hcover r (mem_acceptSet.mp hr)⟩

/-- **`proximity_sound`, probability rendering**: a δ-far word passes with
probability at most `m·b/|F|` over the uniform challenge tuple — `b/|F|` per
round, `m` rounds, exactly the FRI/WHIR soundness shape with the per-round
distance-preservation error as the residual constant. -/
theorem proximity_sound_prob (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    {f : ι 0 → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    ((acceptSet T deg f).card : ℝ) / (Fintype.card F : ℝ) ^ m
      ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcount := proximity_sound T deg hδ hfold hfar
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : (acceptSet T deg f).card = 0 := Nat.le_zero.mp (by simpa using hcount)
    rw [h0]
    norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
    have hP : (0 : ℝ) < (Fintype.card F : ℝ) ^ k := by positivity
    have hcast : ((acceptSet T deg f).card : ℝ)
        ≤ ((k + 1 : ℕ) : ℝ) * (b : ℝ) * (Fintype.card F : ℝ) ^ k := by
      calc ((acceptSet T deg f).card : ℝ)
          ≤ (((k + 1) * (b * Fintype.card F ^ k) : ℕ) : ℝ) := by
            exact_mod_cast (by simpa using hcount)
        _ = ((k + 1 : ℕ) : ℝ) * (b : ℝ) * (Fintype.card F : ℝ) ^ k := by
            push_cast; ring
    rw [pow_succ]
    have h1 : ((acceptSet T deg f).card : ℝ)
          / ((Fintype.card F : ℝ) ^ k * (Fintype.card F : ℝ))
        ≤ (((k + 1 : ℕ) : ℝ) * (b : ℝ) * (Fintype.card F : ℝ) ^ k)
          / ((Fintype.card F : ℝ) ^ k * (Fintype.card F : ℝ)) := by
      gcongr
    refine le_trans h1 (le_of_eq ?_)
    have hPne : ((Fintype.card F : ℝ) ^ k) ≠ 0 := ne_of_gt hP
    have hFne : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hF
    field_simp

end SoundnessHead

/-! ## Realizers of `[PROX-fold-distance]`

Two regimes are DELIVERED here, so the residual is inhabited and precisely
delimited rather than a monolith:

* **sub-quantization (δ < 1/|κ|): PROVED unconditionally, `b = 1`.** The fold
  is affine in α, so two challenges folding a word into the code force both
  fold components into the code, and the recomposition `pₑ(X²) + X·pₒ(X²)`
  puts the word itself in the code.
* **macroscopic δ ∈ (0, 1−B): REDUCED to the one standing RS proximity-gap
  hypothesis** — `IsProximityGenerator (affineGenerator F)` for the folded
  code, i.e. WHIR Theorem 4.8 / BCIKS 2020/654, the SAME `hPG` that
  Selvage/ReedSolomon.lean carries as its keystone TODO. The reduction
  (fold = PG(2) combination of the components; correlated agreement ⇒
  recomposition ⇒ the word is δ-close) is proved; `b ≥ err(δ)·|F|`. -/

/-- The recomposition `pₑ(X²) + X·pₒ(X²)` — the inverse of the even/odd
split. -/
noncomputable def recompose (pE pO : Polynomial F) : Polynomial F :=
  pE.comp (X ^ 2) + X * pO.comp (X ^ 2)

theorem recompose_eval (pE pO : Polynomial F) (x : F) :
    (recompose pE pO).eval x = pE.eval (x ^ 2) + x * pO.eval (x ^ 2) := by
  simp [recompose, eval_comp]

theorem degree_comp_X_sq_lt {p : Polynomial F} {d : ℕ}
    (hp : p.degree < (d : WithBot ℕ)) :
    (p.comp (X ^ 2)).degree < ((2 * d : ℕ) : WithBot ℕ) := by
  by_cases h0 : p = 0
  · rw [h0, zero_comp, degree_zero]
    exact WithBot.bot_lt_coe _
  · have hnp : p.natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hp
    have hcomp : (p.comp (X ^ 2)).natDegree ≤ p.natDegree * 2 := by
      have h := Polynomial.natDegree_comp_le (p := p) (q := (X ^ 2 : Polynomial F))
      rwa [natDegree_X_pow] at h
    have hlt : (p.comp (X ^ 2)).natDegree < 2 * d := by omega
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hlt)

theorem degree_recompose_lt {pE pO : Polynomial F} {d : ℕ}
    (hE : pE.degree < (d : WithBot ℕ)) (hO : pO.degree < (d : WithBot ℕ)) :
    (recompose pE pO).degree < ((2 * d : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (degree_comp_X_sq_lt hE) ?_)
  by_cases h0 : pO = 0
  · rw [h0, zero_comp, mul_zero, degree_zero]
    exact WithBot.bot_lt_coe _
  · have hnO : pO.natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hO
    have hcomp : (pO.comp (X ^ 2)).natDegree ≤ pO.natDegree * 2 := by
      have h := Polynomial.natDegree_comp_le (p := pO) (q := (X ^ 2 : Polynomial F))
      rwa [natDegree_X_pow] at h
    have hmul : (X * pO.comp (X ^ 2)).natDegree ≤ 1 + pO.natDegree * 2 :=
      le_trans natDegree_mul_le (by rw [natDegree_X]; omega)
    have hlt : (X * pO.comp (X ^ 2)).natDegree < 2 * d := by omega
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hlt)

section Realizers

variable {dom : ι ↪ F} {domSq : κ ↪ F}

/-- Pointwise: if both fold components at `sq i` agree with evaluations of
`pₑ`, `pₒ`, then `f i` is the evaluation of the recomposition — the
reconstruction identity in polynomial form. -/
theorem eq_recompose_of_agree (D : FoldingData F dom domSq)
    {f : ι → F} {pE pO : Polynomial F} (i : ι)
    (hE : foldEven D f (D.sq i) = pE.eval (domSq (D.sq i)))
    (hO : foldOdd D f (D.sq i) = pO.eval (domSq (D.sq i))) :
    f i = (recompose pE pO).eval (dom i) := by
  rw [recompose_eval, ← D.domSq_sq, ← hE, ← hO]
  exact (foldEven_add_mul_foldOdd D f i).symm

/-- **The exact-membership folding lemma — PROVED, no hypotheses.** The fold
of a NON-codeword stays a non-codeword for all but at most ONE challenge: the
fold is affine in α, so two good challenges force both components into the
(linear) code and the recomposition puts `f` itself in the code. This is the
δ → 0 end of `[PROX-fold-distance]`, with bad-set bound `b = 1`. -/
theorem fold_notMem_of_notMem (D : FoldingData F dom domSq)
    {d : ℕ} {f : ι → F} (hf : f ∉ reedSolomonCode dom (2 * d)) :
    ∃ bad : Finset F, bad.card ≤ 1 ∧
      ∀ α, α ∉ bad → fold D f α ∉ reedSolomonCode domSq d := by
  classical
  by_cases hex : ∃ α, fold D f α ∈ reedSolomonCode domSq d
  · obtain ⟨α₀, hα₀⟩ := hex
    refine ⟨{α₀}, by simp, fun α hα hmem => ?_⟩
    have hne : α ≠ α₀ := by simpa using hα
    have hsub : fold D f α - fold D f α₀ = (α - α₀) • foldOdd D f := by
      funext k
      simp only [Pi.sub_apply, Pi.smul_apply, fold, smul_eq_mul]
      ring
    have hOs : (α - α₀) • foldOdd D f ∈ reedSolomonCode domSq d := by
      rw [← hsub]; exact Submodule.sub_mem _ hmem hα₀
    have hαne : α - α₀ ≠ 0 := sub_ne_zero.mpr hne
    have hO : foldOdd D f ∈ reedSolomonCode domSq d := by
      have h := Submodule.smul_mem _ (α - α₀)⁻¹ hOs
      rwa [smul_smul, inv_mul_cancel₀ hαne, one_smul] at h
    have hE : foldEven D f ∈ reedSolomonCode domSq d := by
      have hEeq : foldEven D f = fold D f α₀ - α₀ • foldOdd D f := by
        funext k
        simp only [Pi.sub_apply, Pi.smul_apply, fold, smul_eq_mul]
        ring
      rw [hEeq]
      exact Submodule.sub_mem _ hα₀ (Submodule.smul_mem _ _ hO)
    obtain ⟨pE, hpEdeg, hpE⟩ := mem_reedSolomonCode_iff.mp hE
    obtain ⟨pO, hpOdeg, hpO⟩ := mem_reedSolomonCode_iff.mp hO
    exact hf (mem_reedSolomonCode_iff.mpr
      ⟨recompose pE pO, degree_recompose_lt hpEdeg hpOdeg,
        fun i => eq_recompose_of_agree D i (hpE _) (hpO _)⟩)
  · exact ⟨∅, by simp, fun α _ hmem => hex ⟨α, hmem⟩⟩

/-- **`[PROX-fold-distance]` PROVED in the sub-quantization regime,
unconditionally**: for `0 ≤ δ < 1/|κ|`, δ-close to the folded code means IN
the folded code, so the exact lemma delivers distance preservation with
`b = 1`. The iterated test is therefore end-to-end sound TODAY at
exact-membership resolution (`m/|F|` acceptance for a non-codeword); the
macroscopic-δ regime is what remains. -/
theorem foldDistancePreserving_of_lt_inv_card
    [DecidableEq F] [Fintype ι] [Fintype κ] [Nonempty κ]
    (D : FoldingData F dom domSq) (d : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδκ : δ < 1 / (Fintype.card κ : ℝ)) :
    FoldDistancePreserving D (2 * d) d δ 1 := by
  intro f hfar
  have hf : f ∉ reedSolomonCode dom (2 * d) := fun hmem => hfar (close_of_mem hmem hδ0)
  obtain ⟨bad, hb, hspec⟩ := fold_notMem_of_notMem D hf
  refine ⟨bad, hb, fun α hα hclose => ?_⟩
  obtain ⟨u, huC, hurel⟩ := hclose
  have heq : fold D f α = u := by
    by_contra hne
    have hfloor := one_div_card_le_relDist (F := F) hne
    linarith
  exact hspec α hα (heq ▸ huC)

/-! ### The macroscopic-δ regime: reduction to the RS proximity gap -/

section FibreCount

variable [Fintype ι] [Fintype κ] [DecidableEq κ]
variable {dom : ι ↪ F} {domSq : κ ↪ F}

omit [Fintype κ] in
/-- Each folded point has exactly the two roots `{sec k, neg (sec k)}`: the
`sq`-preimage of any `S ⊆ κ` has size exactly `2·|S|`. -/
theorem card_sq_preimage (D : FoldingData F dom domSq) (S : Finset κ) :
    (Finset.univ.filter fun i : ι => D.sq i ∈ S).card = 2 * S.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun i : ι => D.sq i ∈ S)
    (f := D.sq) (t := S) (fun i hi => (Finset.mem_filter.mp hi).2)]
  have hfib : ∀ k ∈ S,
      ((Finset.univ.filter fun i : ι => D.sq i ∈ S).filter fun i => D.sq i = k).card
        = 2 := by
    intro k hk
    have hset : (Finset.univ.filter fun i : ι => D.sq i ∈ S).filter (fun i => D.sq i = k)
        = {D.sec k, D.neg (D.sec k)} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨-, hik⟩
        exact D.eq_or_eq_neg_of_sq_eq (hik.trans (D.sq_sec k).symm)
      · rintro (rfl | rfl)
        · exact ⟨by rw [D.sq_sec]; exact hk, D.sq_sec k⟩
        · exact ⟨by rw [D.sq_neg, D.sq_sec]; exact hk, by rw [D.sq_neg, D.sq_sec]⟩
    rw [hset, Finset.card_insert_of_notMem
      (by rw [Finset.mem_singleton]; exact fun h => D.neg_ne (D.sec k) h.symm),
      Finset.card_singleton]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The halving law: `|ι| = 2·|κ|` for every folding domain. -/
theorem card_eq_two_mul_card (D : FoldingData F dom domSq) :
    Fintype.card ι = 2 * Fintype.card κ := by
  have h := card_sq_preimage D Finset.univ
  simpa [Finset.filter_true_of_mem, Finset.card_univ] using h

end FibreCount

/-! ### Folding at most DOUBLES the distance, and the decoded chain is a fold chain

Two facts that cost ZERO error — they are deterministic, consume no proximity gap,
and hold unconditionally. Together they are ZCF23's Lemma 8 (BaseFold's
chain-consistency step), and the radius they want, `3δ < d_C`, is
`RateRegimeSelector`'s `oneThirdUD` band arrived at from the other side.

The direction matters. "`f` is δ-close to `u`, therefore `fold f α` is δ-close to
`fold u α`" is FALSE as a distance-preservation claim in the useful direction — the
fold is 2-to-1, so the same disagreement count sits on a domain of half the size and
the FRACTION can double. `relDist_fold_le` states exactly that doubling and no more,
and `relDist_fold_le_tight` below attains it with equality. Soundness still argues
by the contrapositive (`FoldDistancePreserving`); this pair is what turns "each level
decodes to SOMETHING" into "each level decodes to the FOLD of the level above", which
is a different obligation and the one that keeps the terminal constant from being the
extension of nothing in particular. -/

section FoldDoubling

variable [DecidableEq F] [Fintype ι] [Fintype κ]
variable {dom : ι ↪ F} {domSq : κ ↪ F}

omit [DecidableEq F] [Fintype ι] [Fintype κ] in
/-- The fold at `k` reads exactly two coordinates: `sec k` and `neg (sec k)`. -/
theorem fold_congr_of_eq (D : FoldingData F dom domSq) {f u : ι → F} (α : F) (k : κ)
    (h1 : f (D.sec k) = u (D.sec k))
    (h2 : f (D.neg (D.sec k)) = u (D.neg (D.sec k))) :
    fold D f α k = fold D u α k := by
  simp only [fold, foldEven, foldOdd, h1, h2]

/-- **Folding creates no new disagreements.** Every folded coordinate where the two
folds differ is charged to a DISTINCT coordinate where the words differ: the charge
lands in the fibre `{sec k, neg (sec k)}`, and `sq` recovers `k` from it, so the
charging map is injective. The COUNT does not grow — only the domain shrinks. -/
theorem hammingDist_fold_le (D : FoldingData F dom domSq) (f u : ι → F) (α : F) :
    hammingDist (fold D f α) (fold D u α) ≤ hammingDist f u := by
  classical
  have hA : hammingDist (fold D f α) (fold D u α)
      = (Finset.univ.filter fun k => fold D f α k ≠ fold D u α k).card := by
    simp [hammingDist]
  have hB : hammingDist f u = (Finset.univ.filter fun i => f i ≠ u i).card := by
    simp [hammingDist]
  have hsq : ∀ j : κ,
      D.sq (if f (D.sec j) = u (D.sec j) then D.neg (D.sec j) else D.sec j) = j := by
    intro j
    by_cases h : f (D.sec j) = u (D.sec j)
    · rw [if_pos h, D.sq_neg, D.sq_sec]
    · rw [if_neg h, D.sq_sec]
  rw [hA, hB]
  refine Finset.card_le_card_of_injOn
    (fun k => if f (D.sec k) = u (D.sec k) then D.neg (D.sec k) else D.sec k) ?_ ?_
  · intro k hk
    have hne : fold D f α k ≠ fold D u α k := (Finset.mem_filter.mp hk).2
    by_cases h1 : f (D.sec k) = u (D.sec k)
    · have h2 : f (D.neg (D.sec k)) ≠ u (D.neg (D.sec k)) :=
        fun h2 => hne (fold_congr_of_eq D α k h1 h2)
      simpa [if_pos h1] using h2
    · simpa [if_neg h1] using h1
  · intro k _ l _ hkl
    have hkl' : (if f (D.sec k) = u (D.sec k) then D.neg (D.sec k) else D.sec k)
        = (if f (D.sec l) = u (D.sec l) then D.neg (D.sec l) else D.sec l) := hkl
    calc k = D.sq (if f (D.sec k) = u (D.sec k) then D.neg (D.sec k) else D.sec k) :=
          (hsq k).symm
      _ = D.sq (if f (D.sec l) = u (D.sec l) then D.neg (D.sec l) else D.sec l) := by
          rw [hkl']
      _ = l := hsq l

/-- **`relDist_fold_le` — one fold at most DOUBLES the relative distance.** The
disagreement count does not grow (`hammingDist_fold_le`) while the domain halves
(`card_eq_two_mul_card`), so the fraction gains a factor of at most `2`. Attained
with equality — see `relDist_fold_le_tight`. -/
theorem relDist_fold_le (D : FoldingData F dom domSq) (f u : ι → F) (α : F) :
    relDist (fold D f α) (fold D u α) ≤ 2 * relDist f u := by
  classical
  rcases isEmpty_or_nonempty κ with _ | _
  · have h0 : Fintype.card κ = 0 := Fintype.card_eq_zero
    have h0' : Fintype.card ι = 0 := by rw [card_eq_two_mul_card D, h0]
    simp [relDist, h0']
  · have hn : (0 : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
    have hd : (hammingDist (fold D f α) (fold D u α) : ℝ) ≤ (hammingDist f u : ℝ) := by
      exact_mod_cast hammingDist_fold_le D f u α
    rw [relDist, relDist, card_eq_two_mul_card D]
    push_cast
    rw [show (2 : ℝ) * ((hammingDist f u : ℝ) / (2 * (Fintype.card κ : ℝ)))
          = (hammingDist f u : ℝ) / (Fintype.card κ : ℝ) by
        rcases eq_or_ne (Fintype.card κ : ℝ) 0 with h | h
        · rw [h]; simp
        · field_simp]
    exact (div_le_div_iff_of_pos_right hn).mpr hd

/-- **Fold-chain consistency — ZCF23's Lemma 8, and it costs ZERO error.** On an
accepting transcript the verifier learns only that each level's word is δ-close to
SOME codeword. This says that at `3δ < d_C` those decoded codewords are forced to
form a genuine fold chain: the level-below codeword IS the fold of the level-above
one. Deterministic: no challenge is sampled, no proximity gap is consumed, no error
term is paid. `relDist_fold_le` puts `fold D v α` within `2δ` of `π'`, `w` is within
`δ`, both are codewords, and `3δ < d_C` closes the triangle. -/
theorem fold_chain_consistent [Nonempty κ] (D : FoldingData F dom domSq) {d : ℕ}
    {dC δ : ℝ}
    (hdC : ∀ x ∈ reedSolomonCode domSq d, ∀ y ∈ reedSolomonCode domSq d,
      x ≠ y → dC ≤ relDist x y)
    {π : ι → F} {v : ι → F} {w : κ → F} (α : F)
    (hv : v ∈ reedSolomonCode dom (2 * d)) (hw : w ∈ reedSolomonCode domSq d)
    (hπv : relDist π v ≤ δ) (hπ'w : relDist (fold D π α) w ≤ δ)
    (h3δ : 3 * δ < dC) :
    fold D v α = w := by
  by_contra hne
  have hfv : fold D v α ∈ reedSolomonCode domSq d := fold_preserves_code D hv α
  have h1 : dC ≤ relDist (fold D v α) w := hdC _ hfv _ hw hne
  have h2 : relDist (fold D π α) (fold D v α) ≤ 2 * relDist π v := relDist_fold_le D π v α
  have h3 : relDist (fold D v α) w
      ≤ relDist (fold D v α) (fold D π α) + relDist (fold D π α) w :=
    relDist_triangle _ _ _
  have h4 : relDist (fold D v α) (fold D π α) = relDist (fold D π α) (fold D v α) :=
    relDist_comm _ _
  linarith

/-- The Reed–Solomon instantiation, with the radius written out: at
`3δ < 1 − (d−1)/|κ|` the decoded chain is a fold chain, UNCONDITIONALLY — no
proximity-gap hypothesis, no conjecture, no named residual. The band is
`RateRegimeSelector.oneThirdUD`'s `(1−ρ)/3` reached from the other direction, and a
hair wider, because `reedSolomonCode_minDist` carries the exact Singleton distance
`1 − (d−1)/n` rather than the papers' rounded `1 − ρ`. -/
theorem fold_chain_consistent_RS [Nonempty κ] (D : FoldingData F dom domSq) {d : ℕ}
    {δ : ℝ} {π : ι → F} {v : ι → F} {w : κ → F} (α : F)
    (hv : v ∈ reedSolomonCode dom (2 * d)) (hw : w ∈ reedSolomonCode domSq d)
    (hπv : relDist π v ≤ δ) (hπ'w : relDist (fold D π α) w ≤ δ)
    (h3δ : 3 * δ < 1 - ((d : ℝ) - 1) / (Fintype.card κ : ℝ)) :
    fold D v α = w :=
  fold_chain_consistent D (reedSolomonCode_minDist domSq d) α hv hw hπv hπ'w h3δ

end FoldDoubling

section ProximityGap

variable [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype κ]
variable {dom : ι ↪ F} {domSq : κ ↪ F}

/-- **Correlated agreement of the two fold components puts the word δ-close to
the big code — PROVED.** The CA agreement set `S ⊆ κ` lifts to its
`sq`-preimage (size `2|S|`, same relative measure by the halving law), on
which `f` agrees with the recomposition of the two component codewords. This
is the reduction arrow that makes BCIKS/WHIR proximity gaps imply folding
soundness. -/
theorem close_of_correlatedAgreement [Nonempty ι] (D : FoldingData F dom domSq)
    {d : ℕ} {f : ι → F} {δ : ℝ}
    (hCA : CorrelatedAgreement (reedSolomonCode domSq d) δ
      ![foldEven D f, foldOdd D f]) :
    close δ (reedSolomonCode dom (2 * d)) f := by
  classical
  obtain ⟨S, hScard, hSgood⟩ := hCA
  obtain ⟨uE, huEC, huEAg⟩ := hSgood 0
  obtain ⟨uO, huOC, huOAg⟩ := hSgood 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at huEAg huOAg
  obtain ⟨pE, hpEdeg, hpE⟩ := mem_reedSolomonCode_iff.mp huEC
  obtain ⟨pO, hpOdeg, hpO⟩ := mem_reedSolomonCode_iff.mp huOC
  refine ⟨fun i => (recompose pE pO).eval (dom i),
    mem_reedSolomonCode_iff.mpr
      ⟨recompose pE pO, degree_recompose_lt hpEdeg hpOdeg, fun i => rfl⟩,
    relDist_le_of_agreesOn
      (S := Finset.univ.filter fun i : ι => D.sq i ∈ S) ?_ ?_⟩
  · intro i hi
    have hik : D.sq i ∈ S := (Finset.mem_filter.mp hi).2
    exact eq_recompose_of_agree D i
      ((huEAg _ hik).trans (hpE _)) ((huOAg _ hik).trans (hpO _))
  · rw [card_sq_preimage D S, card_eq_two_mul_card D]
    push_cast
    linarith

/-- **`[PROX-fold-distance]` at macroscopic δ, REDUCED to the RS proximity
gap.** If PG(2) (the affine generator `(1, α)`) is a proximity generator for
the FOLDED code with bound `B` and error `err` — WHIR Theorem 4.8 / BCIKS
2020/654, the SAME standing hypothesis `hPG` of Selvage/ReedSolomon.lean — then
one fold round preserves δ-farness for every `δ ∈ (0, 1−B)`, with bad-set
bound any `b ≥ err(δ)·|F|`. Proof: `Fold(f,·)` IS the PG(2) combination of
`(foldEven f, foldOdd f)`; if more than `err(δ)·|F|` challenges fold `f`
δ-close, Def 4.7 yields correlated agreement of the components, and
`close_of_correlatedAgreement` puts `f` itself δ-close — contradiction. -/
theorem foldDistancePreserving_of_isProximityGenerator
    [Fintype F] [Nonempty ι] (D : FoldingData F dom domSq) (d : ℕ)
    {B : ℝ} {err : ℝ → ℝ}
    (hPG : IsProximityGenerator (affineGenerator F) (reedSolomonCode domSq d) B err)
    {δ : ℝ} (hδ0 : 0 < δ) (hδB : δ < 1 - B) {b : ℕ}
    (hb : err δ * (Fintype.card F : ℝ) ≤ (b : ℝ)) :
    FoldDistancePreserving D (2 * d) d δ b := by
  classical
  intro f hfar
  set bad : Finset F :=
    Finset.univ.filter (fun α : F => close δ (reedSolomonCode domSq d) (fold D f α))
    with hbad
  have hfe : ∀ α : F,
      comb ((affineGenerator F).gen α) ![foldEven D f, foldOdd D f] = fold D f α := by
    intro α
    funext x
    simp [comb_affineGenerator, fold]
  have hpr : (affineGenerator F).pr
        (fun r => close δ (reedSolomonCode domSq d)
          (comb r ![foldEven D f, foldOdd D f]))
      ≤ err δ := by
    by_contra hgt
    exact absurd (close_of_correlatedAgreement D
        (hPG ![foldEven D f, foldOdd D f] δ hδ0 hδB (not_le.mp hgt))) hfar
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpr_eq : (affineGenerator F).pr
        (fun r => close δ (reedSolomonCode domSq d)
          (comb r ![foldEven D f, foldOdd D f]))
      = (bad.card : ℝ) / (Fintype.card F : ℝ) := by
    unfold ProximityGenerator.pr
    have hfilter :
        (Finset.univ.filter fun ω : (affineGenerator F).Seed =>
            close δ (reedSolomonCode domSq d)
              (comb ((affineGenerator F).gen ω) ![foldEven D f, foldOdd D f]))
          = bad := by
      rw [hbad]
      refine Finset.filter_congr fun α _ => ?_
      rw [hfe α]
    rw [hfilter]
    calc ∑ ω ∈ bad, (affineGenerator F).weight ω
        = ∑ _ω ∈ bad, ((Fintype.card F : ℝ))⁻¹ :=
          Finset.sum_congr rfl fun ω _ => rfl
      _ = (bad.card : ℝ) * ((Fintype.card F : ℝ))⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (bad.card : ℝ) / (Fintype.card F : ℝ) := (div_eq_mul_inv _ _).symm
  have hcard : (bad.card : ℝ) ≤ (b : ℝ) := by
    have h1 : (bad.card : ℝ) / (Fintype.card F : ℝ) ≤ err δ := by
      rw [← hpr_eq]; exact hpr
    have h2 : (bad.card : ℝ) ≤ err δ * (Fintype.card F : ℝ) :=
      (div_le_iff₀ hF).mp h1
    linarith
  refine ⟨bad, by exact_mod_cast hcard, fun α hα => ?_⟩
  rw [hbad, Finset.mem_filter] at hα
  exact fun hclose => hα ⟨Finset.mem_univ α, hclose⟩

end ProximityGap

end Realizers

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

The one-round tower over F₅: level 0 = `{1,2,3,4}` (all units, closed under
negation), level 1 = `{1,4}` (the squares), degree schedule `2 → 1`.

* **satisfiable**: the line `X`'s evaluations `(1,2,3,4)` fold, at every α, to
  the CONSTANT word `α` — computed by `decide` at `α = 3` and delivered in
  general by `fold_preserves_code`; completeness fires end-to-end.
* **teeth**: the spike word `(0,1,0,0)` is `1/5`-far from the level-0 code
  (proved via root counting, reusing `card_agreeSet_lt_of_ne`); the test
  ACCEPTS it exactly at the single bad challenge `α = 3` and rejects the other
  four — the acceptance set is computed EXACTLY, and `proximity_sound`'s bound
  `m·b·|F|^{m−1} = 1` is ATTAINED with equality, not slack.
* **premise inhabitation**: the `[PROX-fold-distance]` hypothesis of
  `proximity_sound` is discharged by the PROVED sub-quantization realizer
  (`foldDistancePreserving_of_lt_inv_card`, `b = 1`) — the end-to-end bound
  below carries NO residual hypothesis at all. -/

namespace ProximityExample

/-- Level types: `Fin 4`, `Fin 2`, then empty (`Fin 0`) — sizes must halve,
so the tower ends. An `abbrev` so instances see through it. -/
abbrev levels : ℕ → Type := fun n => Fin (if n = 0 then 4 else if n = 1 then 2 else 0)

/-- Level 0: the four units `{1, 2, 3, 4}` of F₅. -/
def dom0 : Fin 4 ↪ ZMod 5 :=
  ⟨fun i => ((i.val + 1 : ℕ) : ZMod 5), by decide⟩

/-- Level 1: the squares `{1, 4}`. -/
def dom1 : Fin 2 ↪ ZMod 5 :=
  ⟨![1, 4], by decide⟩

/-- The folding structure `{1,2,3,4} → {1,4}`: negation swaps `1↔4`, `2↔3`;
squaring sends `{1,4} ↦ 1`, `{2,3} ↦ 4`; the section picks roots `1` and `2`.
Every law is checked by `decide`. -/
def data0 : FoldingData (ZMod 5) dom0 dom1 where
  neg := ![3, 2, 1, 0]
  dom_neg := by decide
  sq := ![0, 1, 1, 0]
  domSq_sq := by decide
  sec := ![0, 1]
  sq_sec := by decide
  dom_ne_zero := by decide
  two_ne := by decide

/-- The level embeddings of the tower. -/
def levelDom : ∀ n, levels n ↪ ZMod 5
  | 0 => dom0
  | 1 => dom1
  | (_ + 2) => ⟨Fin.elim0, fun a => a.elim0⟩

/-- The one-round tower over F₅. -/
def ldtTower : FoldingTower (ZMod 5) levels 1 where
  dom := levelDom
  data := fun j hj =>
    match j, hj with
    | 0, _ => data0
    | (_ + 1), hj => absurd hj (by omega)

/-- Degree schedule `2 → 1`: lines fold to constants. -/
abbrev degSched : ℕ → ℕ := fun n => if n = 0 then 2 else 1

theorem degSched_halving : ∀ j, j < 1 → degSched j = 2 * degSched (j + 1) := by
  intro j hj
  have h0 : j = 0 := by omega
  subst h0
  rfl

/-! ### Satisfiable: a codeword folds to a codeword, and passes -/

/-- The evaluations of the line `X`: `(1, 2, 3, 4)`. -/
def xWord : Fin 4 → ZMod 5 := ![1, 2, 3, 4]

theorem xWord_mem : xWord ∈ reedSolomonCode dom0 2 := by
  refine mem_reedSolomonCode_iff.mpr ⟨X, by rw [degree_X]; decide, fun i => ?_⟩
  rw [eval_X]
  revert i
  decide

/-- The fold of the line at challenge `3` is the CONSTANT `3` — the
degree-halving computed on the nose. -/
example : fold data0 xWord 3 = fun _ => 3 := by decide

/-- `fold_preserves_code` FIRES: at every challenge the folded line is a
degree-<1 codeword. -/
example (α : ZMod 5) : fold data0 xWord α ∈ reedSolomonCode dom1 1 :=
  fold_preserves_code (d := 1) data0 xWord_mem α

/-- Completeness end-to-end: the honest codeword passes the whole test for
EVERY challenge stream. -/
example (αs : ℕ → ZMod 5) : proximityTest ldtTower degSched xWord αs :=
  proximity_complete ldtTower degSched_halving xWord_mem αs

/-! ### Teeth: a far word, its exact acceptance set, the bound attained -/

/-- The spike `(0, 1, 0, 0)` — value `1` at the point `2`, zero elsewhere. -/
def spikeWord : Fin 4 → ZMod 5 := ![0, 1, 0, 0]

/-- The spike is NOT a degree-<2 codeword: a line vanishing at the two points
`1` and `3` is the zero polynomial (root counting, reusing
`card_agreeSet_lt_of_ne`), but the spike is nonzero at `2`. -/
theorem spikeWord_notMem : spikeWord ∉ reedSolomonCode dom0 2 := by
  intro hmem
  obtain ⟨p, hdeg, hp⟩ := mem_reedSolomonCode_iff.mp hmem
  have hpne : p ≠ 0 := by
    intro h0
    have h2 := hp 1
    rw [h0, eval_zero] at h2
    exact absurd h2 (by decide)
  have hcard := card_agreeSet_lt_of_ne dom0 (d := 2) hdeg
    (q := 0) (by rw [degree_zero]; exact WithBot.bot_lt_coe _) hpne
  have hsub : ({0, 2} : Finset (Fin 4))
      ⊆ Finset.univ.filter fun i => p.eval (dom0 i) = (0 : Polynomial (ZMod 5)).eval (dom0 i) := by
    intro i hi
    have h0 := hp 0
    have h2 := hp 2
    fin_cases hi <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_zero] <;>
      [rw [← h0]; rw [← h2]] <;> decide
  have h2le : 2 ≤ (Finset.univ.filter fun i =>
      p.eval (dom0 i) = (0 : Polynomial (ZMod 5)).eval (dom0 i)).card :=
    le_trans (by decide) (Finset.card_le_card hsub)
  omega

/-- The spike is `1/5`-FAR from the level-0 code: any codeword within `1/5`
would be within the `1/4` quantization floor, hence equal to it. -/
theorem spikeWord_far :
    ¬ close (1 / 5 : ℝ) (reedSolomonCode dom0 2) spikeWord := by
  rintro ⟨u, huC, hrel⟩
  have hne : spikeWord ≠ u := fun h => spikeWord_notMem (h ▸ huC)
  have hfloor := one_div_card_le_relDist (F := ZMod 5) hne
  rw [Fintype.card_fin] at hfloor
  linarith

/-- **The acceptance set computed EXACTLY**: the test accepts the spike iff
the challenge is the single bad `α = 3` (where the fold `(0, 3+4α)` collapses
to the zero constant). Both directions by `decide` through
`mem_reedSolomonCode_one_iff`. -/
theorem spike_accept_iff (α : ZMod 5) :
    proximityTest ldtTower degSched spikeWord (chalExt ![α]) ↔ α = 3 := by
  show fold data0 spikeWord α ∈ reedSolomonCode dom1 1 ↔ α = 3
  rw [mem_reedSolomonCode_one_iff]
  revert α
  decide

/-- The test REJECTS the far spike at the good challenge `α = 1`. -/
example : ¬ proximityTest ldtTower degSched spikeWord (chalExt ![1]) := by
  rw [spike_accept_iff]
  decide

/-- The one bad challenge is REAL: the far spike is laundered at `α = 3` —
the soundness error is a genuine phenomenon, not slack in the bound. -/
example : proximityTest ldtTower degSched spikeWord (chalExt ![3]) := by
  rw [spike_accept_iff]

/-- `[PROX-fold-distance]` premise inhabitation, NO hypotheses: the
sub-quantization realizer discharges the fold-distance hypothesis of
`proximity_sound` at `δ = 1/5`, `b = 1`. -/
theorem ldtTower_hfold : ∀ (j : ℕ) (hj : j < 1),
    FoldDistancePreserving (ldtTower.data j hj) (degSched j) (degSched (j + 1))
      (1 / 5 : ℝ) 1 := by
  intro j hj
  have h0 : j = 0 := by omega
  subst h0
  haveI : Nonempty (levels (0 + 1)) := ⟨(0 : Fin 2)⟩
  exact foldDistancePreserving_of_lt_inv_card (ldtTower.data 0 hj) 1
    (by norm_num)
    (by rw [show Fintype.card (levels 1) = 2 from rfl]; norm_num)

/-- The acceptance set IS `{![3]}`. -/
theorem acceptSet_spike :
    acceptSet ldtTower degSched spikeWord = {![3]} := by
  ext r
  rw [mem_acceptSet, Finset.mem_singleton]
  have hr : r = ![r 0] := funext fun j => by fin_cases j; rfl
  conv_lhs => rw [hr]
  rw [spike_accept_iff (r 0)]
  constructor
  · intro h
    rw [hr, h]
  · intro h
    rw [h]
    rfl

/-- **`proximity_sound` fires end-to-end with ZERO residual hypotheses**: the
far spike's acceptance count is bounded by `m·b·|F|^{m−1} = 1`. Every
hypothesis is discharged — the fold-distance premise by the proved
sub-quantization realizer. -/
theorem spike_sound_bound :
    (acceptSet ldtTower degSched spikeWord).card ≤ 1 := by
  have h := proximity_sound ldtTower degSched (δ := 1 / 5) (by norm_num)
    ldtTower_hfold spikeWord_far
  simpa using h

/-- The bound is ATTAINED: acceptance count exactly `1` — `proximity_sound`
is tight on this instance (`1/5` acceptance probability, exactly `m·b/|F|`). -/
example : (acceptSet ldtTower degSched spikeWord).card = 1 := by
  rw [acceptSet_spike, Finset.card_singleton]

/-! ### Keystones for the doubling law and fold-chain consistency -/

/-- **TEETH: the factor `2` in `relDist_fold_le` is ATTAINED, not slack.** The spike
is `1/4`-far from the zero codeword on the 4-point level-0 domain; its fold at
`α = 0` is `1/2`-far from the zero codeword on the 2-point level-1 domain. The
disagreement COUNT is unchanged (1 → 1); it is the domain that halved. So no
sharpening of the constant is available, and the `(1−ρ)/3` band that
`fold_chain_consistent` needs is not an artifact of a lossy step. -/
theorem relDist_fold_le_tight :
    relDist (fold data0 spikeWord 0) (fold data0 (0 : Fin 4 → ZMod 5) 0)
      = 2 * relDist spikeWord (0 : Fin 4 → ZMod 5) := by
  have h1 : hammingDist (fold data0 spikeWord 0)
      (fold data0 (0 : Fin 4 → ZMod 5) 0) = 1 := by decide
  have h2 : hammingDist spikeWord (0 : Fin 4 → ZMod 5) = 1 := by decide
  rw [relDist, relDist, h1, h2]
  norm_num

/-- A one-position corruption of the line `X`'s codeword: `(1,2,3,0)` against
`xWord = (1,2,3,4)`. Relative distance exactly `1/4`. -/
def nearWord : Fin 4 → ZMod 5 := ![1, 2, 3, 0]

theorem nearWord_close : relDist nearWord xWord ≤ 1 / 4 := by
  have h : hammingDist nearWord xWord = 1 := by decide
  rw [relDist, h]
  norm_num

/-- At the challenge `α = 1` the corrupted word folds ONTO a level-1 codeword — the
constant `1` — so the verifier's level-1 decoding is at distance `0`. -/
theorem nearWord_fold_eq : fold data0 nearWord 1 = (fun _ => 1 : Fin 2 → ZMod 5) := by
  decide

/-- **`fold_chain_consistent_RS` FIRES, with every premise inhabited and none of them
degenerate.** `d = 1` so `d_C = 1 − 0/2 = 1`, and `δ = 1/4` gives `3δ = 3/4 < 1`: the
band is real, not empty. The verifier sees a level-0 word `1/4`-close to `xWord` and
a level-1 word `0`-close to the constant `1`; the theorem forces the level-1 codeword
to BE the fold of `xWord`. (The conclusion is independently computable here — that is
what makes this a check of the theorem rather than a use of it.) -/
theorem chain_consistent_fires :
    fold data0 xWord 1 = (fun _ => 1 : Fin 2 → ZMod 5) := by
  refine fold_chain_consistent_RS (d := 1) (δ := 1 / 4) (π := nearWord) data0 1
    xWord_mem ?_ nearWord_close ?_ ?_
  · exact mem_reedSolomonCode_one_iff.mpr fun _ _ => rfl
  · rw [nearWord_fold_eq, relDist, hammingDist_self]
    norm_num
  · norm_num

end ProximityExample

/-! ## Axiom pins for the doubling / chain-consistency block

(The rest of this file predates the pinning discipline and is unpinned; these are the
declarations added with it in force.) -/

/-- info: 'Minidregg.Selvage.relDist_fold_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relDist_fold_le
/-- info: 'Minidregg.Selvage.fold_chain_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_chain_consistent
/-- info: 'Minidregg.Selvage.fold_chain_consistent_RS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_chain_consistent_RS
/-- info: 'Minidregg.Selvage.ProximityExample.relDist_fold_le_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProximityExample.relDist_fold_le_tight
/-- info: 'Minidregg.Selvage.ProximityExample.chain_consistent_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProximityExample.chain_consistent_fires

end Minidregg.Selvage
