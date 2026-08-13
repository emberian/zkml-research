/-
# Selvage.BaseFoldCompleteness — the multilinear opening rides the FRI tower we have

BaseFold (ZCF23) opens a multilinear commitment by braiding a sumcheck with a FRI
descent: the round-`i` challenge is BOTH the sumcheck challenge and the folding
challenge, and the descent's terminal constant is the claimed evaluation. The
commitment is an ORDINARY Reed–Solomon codeword, Merkle-committed — no new opening
abstraction, no evaluation-point-indexed `openAt`.

**This file closes the completeness cone of that construction.** It is the answer to
one load-bearing question: *is the FRI fold of `Selvage/Proximity.lean` the same
operator as the MLE coefficient fold of `Selvage/MultiplicativeMleTerminal.lean`?*

**It is, definitionally.** `fold_eval` says the FRI fold of a polynomial's evaluations
is the evaluation of `evenPart p + C α * oddPart p`; `mleCoefficientFold p α` IS that
term. `fold_eval_mleCoefficientFold` below is proved by handing `fold_eval` straight
back — the two operators are not "corresponding", they are one term under two names.
Everything else in this file is the consequence of that, and no new proximity result,
conjecture or named hypothesis is used anywhere.

**PROVED here, no `sorry`, standard axioms only** (propext/choice/Quot.sound):

* **the operator identity** (`fold_eval_mleCoefficientFold`, by `fold_eval` verbatim);
* **degree bookkeeping through the coefficient fold**
  (`degree_mleCoefficientFold_lt`, `degree_foldMleVariables_lt`) and hence
  **the terminal of a degree-`< 2^m` polynomial is a CONSTANT**
  (`foldMleVariables_eq_C`) — the base check `mem_reedSolomonCode_one_iff` is met by
  construction, not by hypothesis;
* **the tower-fold induction** (`FoldingTower.word_eval_foldMleVariables`): the
  level-`n` word of the FRI descent on `p`'s codeword is the codeword of
  `foldMleVariables n p` — the challenge stream read LSB-first — via the snoc form
  `foldMleVariables_succ_last`;
* **the Möbius round trip** (`booleanMobiusPolynomial_injective`,
  `exists_table_booleanMobiusPolynomial`,
  `mem_range_booleanMobiusPolynomial_iff`): the Boolean Möbius transform is a
  BIJECTION from Boolean tables onto the degree-`< 2^m` window, with the inverse
  `tableOfPoly` read off by restricting the fold terminal to the cube;
* ⭐ **`basefold_terminal_word_eq`** — the terminal word of the descent on *any*
  degree-`< 2^m` committed polynomial is the constant word whose value is
  `mle (tableOfPoly m p) r`. Not just the honest Möbius packing: EVERY codeword in
  the window has a definite table, so "the terminal constant is the MLE of nothing in
  particular" is impossible. This is the clause the round-by-round knowledge state
  needs and it is a theorem, not a hypothesis;
* **`basefold_terminal_is_mle`** — the honest specialization, the completeness
  statement of BaseFold at Reed–Solomon, obtained by composing the above with the
  already-proved `foldMleVariables_booleanMobiusPolynomial`;
* **`basefold_opening_complete`** — the two halves together: the committed word passes
  `proximityTest` at EVERY challenge stream (`proximity_complete`, reused), and at the
  stream `chalExt r` its terminal word is the constant `mle table r`.

**Honest scope limits — what is NOT here.**

1. This is **completeness only**. Nothing here says an ACCEPTING transcript forces the
   claimed value: the keystone `raw_commit_terminal_differs_f5` exhibits a word that
   passes the whole descent and terminates at `2` while the honest commitment of the
   same table terminates at `4`. Acceptance pins the *committed polynomial*, and the
   soundness argument (fold-chain consistency at `δ < (1−ρ)/3`, then the sumcheck) is
   what turns that into the value. That work is `relDist_fold_le` + the degree-2
   sumcheck family + the `RbrKnowledgeSoundness` instance, and it is NOT in this file.
2. There is **no sumcheck here**. BaseFold braids one; this file establishes only the
   FRI leg's algebra. The braid is the `Reduction` instance.
3. The tower is the claim-resolution tower of `Selvage/Proximity.lean`: the verifier
   reads whole level words. The query/Merkle layer is `[DEC-open]`-adjacent, unchanged.

⚠ **A correction to the plan this file was built from.** The landscape note proposed
the Möbius inverse as `coeffsToTable p b := p.coeff (bitsToNat b)`. That is **not** the
inverse: `booleanMobiusPolynomial` maps a VALUE table to COEFFICIENTS, so reading the
coefficients back indexed by bits returns the Möbius coefficients, not the values. The
inverse is `tableOfPoly` — restrict the fold terminal to the cube — and it is the one
the knowledge state wants anyway, because it is defined for every polynomial in the
window rather than only for those in the image.
-/
import Selvage.MultiplicativeMleTerminal

namespace Minidregg.Selvage

open Polynomial

variable {F : Type*} [Field F]

/-! ## 1. The two folds are one operator

`Selvage/Proximity.lean`'s `fold` acts on WORDS over an evaluation domain;
`Selvage/MultiplicativeMleTerminal.lean`'s `mleCoefficientFold` acts on COEFFICIENT
polynomials. The claim that they are "the same operator" is exactly this: the second
is the first's action on the polynomial behind a codeword, and the identity is
definitional — `mleCoefficientFold p α` and `evenPart p + C α * oddPart p` are the
same term, so `fold_eval` proves the MLE-vocabulary statement verbatim. -/

section OneOperator

variable {ι κ : Type*} {dom : ι ↪ F} {domSq : κ ↪ F}

/-- The MLE coefficient fold is, on the nose, the FRI even/odd recombination. `rfl`:
`mleCoefficientFold`'s body IS `evenPart p + C r * oddPart p`. -/
theorem mleCoefficientFold_eq_evenPart_add_C_mul_oddPart (p : Polynomial F) (α : F) :
    mleCoefficientFold p α = evenPart p + C α * oddPart p := rfl

/-- ⭐ **THE OPERATOR IDENTITY.** One FRI fold of a codeword's word is the codeword of
one MLE coefficient fold of its polynomial. The proof is `fold_eval` handed back
unchanged: the two statements differ only by the name of the right-hand term. -/
theorem fold_eval_mleCoefficientFold (D : FoldingData F dom domSq)
    (p : Polynomial F) (α : F) (k : κ) :
    fold D (fun i => p.eval (dom i)) α k = (mleCoefficientFold p α).eval (domSq k) :=
  fold_eval D p α k

end OneOperator

/-! ## 2. Degree bookkeeping: the terminal of the window is a constant

`fold_preserves_code` halves the degree bound per FRI round; the same statement on the
coefficient side is `degree_mleCoefficientFold_lt`, and iterating it says a
degree-`< 2^m` polynomial folds, after `m` variables, into `degreeLT 1` — i.e. a
constant. So the base check of the LDT (`mem_reedSolomonCode_one_iff`: "the last word
is constant") is met by CONSTRUCTION for anything committed in the window. -/

theorem degree_mleCoefficientFold_lt {p : Polynomial F} {d : ℕ}
    (hp : p.degree < ((2 * d : ℕ) : WithBot ℕ)) (r : F) :
    (mleCoefficientFold p r).degree < (d : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (degree_evenPart_lt hp) ?_)
  calc (C r * oddPart p).degree ≤ (oddPart p).degree := by
        rw [← Polynomial.smul_eq_C_mul]; exact degree_smul_le _ _
    _ < (d : WithBot ℕ) := degree_oddPart_lt hp

/-- Folding `m` variables divides the degree window by `2^m`. -/
theorem degree_foldMleVariables_lt (d : ℕ) :
    ∀ (m : ℕ) (p : Polynomial F) (r : Fin m → F),
      p.degree < ((2 ^ m * d : ℕ) : WithBot ℕ) →
        (foldMleVariables m p r).degree < (d : WithBot ℕ) := by
  intro m
  induction m with
  | zero => intro p r hp; simpa [foldMleVariables] using hp
  | succ m ih =>
      intro p r hp
      rw [foldMleVariables]
      refine ih _ _ (degree_mleCoefficientFold_lt (d := 2 ^ m * d) ?_ (r 0))
      rw [show 2 * (2 ^ m * d) = 2 ^ (m + 1) * d by ring]
      exact hp

/-- **The terminal is a constant polynomial** — the LDT's base check, discharged for
every polynomial in the commitment window. -/
theorem foldMleVariables_eq_C (m : ℕ) (p : Polynomial F)
    (hp : p.degree < ((2 ^ m : ℕ) : WithBot ℕ)) (r : Fin m → F) :
    foldMleVariables m p r = C ((foldMleVariables m p r).coeff 0) := by
  refine Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp ?_)
  have h := degree_foldMleVariables_lt 1 m p r (by simpa using hp)
  exact_mod_cast h

/-- Consequently the terminal word is the CONSTANT word of the terminal coefficient. -/
theorem eval_foldMleVariables (m : ℕ) (p : Polynomial F)
    (hp : p.degree < ((2 ^ m : ℕ) : WithBot ℕ)) (r : Fin m → F) (x : F) :
    (foldMleVariables m p r).eval x = (foldMleVariables m p r).coeff 0 := by
  conv_lhs => rw [foldMleVariables_eq_C m p hp r]
  rw [eval_C]

/-! ## 3. The tower-fold induction

`FoldingTower.word` appends a fold at the BOTTOM of the descent; `foldMleVariables`
consumes challenges from the FRONT. The bridge is the snoc form. -/

/-- Folding `m+1` variables = folding the first `m`, then one more at the last
challenge. (`foldMleVariables`'s recursion peels the FIRST challenge; the tower's
recursion appends the LAST. This is the reassociation between them.) -/
theorem foldMleVariables_succ_last :
    ∀ (n : ℕ) (p : Polynomial F) (r : Fin (n + 1) → F),
      foldMleVariables (n + 1) p r
        = mleCoefficientFold (foldMleVariables n p (fun i => r i.castSucc))
            (r (Fin.last n)) := by
  intro n
  induction n with
  | zero => intro p r; rfl
  | succ n ih =>
      intro p r
      rw [foldMleVariables, ih]
      conv_rhs => rw [foldMleVariables]
      simp only [Fin.castSucc_zero, Fin.succ_castSucc, Fin.succ_last]

section Tower

variable {ι : ℕ → Type*} {m : ℕ}

/-- ⭐ **The FRI descent IS the coefficient fold, level by level.** The level-`n` word
of the tower run on `p`'s codeword is the codeword of `foldMleVariables n p` at the
challenge PREFIX `αs 0, …, αs (n−1)`, on the level-`n` domain. -/
theorem FoldingTower.word_eval_foldMleVariables (T : FoldingTower F ι m)
    (p : Polynomial F) (αs : ℕ → F) :
    ∀ (n : ℕ) (hn : n ≤ m),
      T.word (fun i => p.eval (T.dom 0 i)) αs n hn
        = fun k => (foldMleVariables n p (fun j : Fin n => αs j.val)).eval (T.dom n k) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      rw [T.word_succ, ih (Nat.le_of_succ_le hn)]
      funext k
      rw [fold_eval_mleCoefficientFold, foldMleVariables_succ_last]
      simp only [Fin.val_castSucc, Fin.val_last]

end Tower

/-! ## 4. The Möbius round trip

`booleanMobiusPolynomial` is a bijection from Boolean tables onto the degree-`< 2^m`
window. Injectivity is `mle_injective` composed with the terminal theorem;
surjectivity is the even/odd recomposition, by induction. The inverse is
`tableOfPoly`: restrict the fold terminal to the cube. -/

/-- Parity splitting is undone by interleaving — the polynomial-level recomposition
matching `evenPart_add_X_mul_oddPart_eval`. -/
theorem parityInterleave_evenPart_oddPart (p : Polynomial F) :
    parityInterleave (evenPart p) (oddPart p) = p := by
  ext n
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst hk; rw [coeff_parityInterleave_even, coeff_evenPart_terminal]
  · subst hk; rw [coeff_parityInterleave_odd, coeff_oddPart_terminal]

/-- The Möbius transform lands in the degree-`< 2^m` window. -/
theorem degree_booleanMobiusPolynomial_lt (m : ℕ) (f : (Fin m → Bool) → F) :
    (booleanMobiusPolynomial m f).degree < ((2 ^ m : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  exact booleanMobiusPolynomial_coeff_eq_zero_of_two_pow_le m f (by exact_mod_cast hn)

/-- **Surjectivity onto the window**: every degree-`< 2^m` polynomial is the Möbius
packing of a Boolean table. -/
theorem exists_table_booleanMobiusPolynomial :
    ∀ (m : ℕ) (p : Polynomial F), p.degree < ((2 ^ m : ℕ) : WithBot ℕ) →
      ∃ table : (Fin m → Bool) → F, booleanMobiusPolynomial m table = p := by
  intro m
  induction m with
  | zero =>
      intro p hp
      refine ⟨fun _ => p.coeff 0, ?_⟩
      have hle : p.degree ≤ 0 := Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hp)
      exact (Polynomial.eq_C_of_degree_le_zero hle).symm
  | succ m ih =>
      intro p hp
      have hp' : p.degree < ((2 * 2 ^ m : ℕ) : WithBot ℕ) := by
        rw [show 2 * 2 ^ m = 2 ^ (m + 1) by ring]; exact hp
      have hev : (evenPart p).degree < ((2 ^ m : ℕ) : WithBot ℕ) := degree_evenPart_lt hp'
      have hod : (oddPart p).degree < ((2 ^ m : ℕ) : WithBot ℕ) := degree_oddPart_lt hp'
      obtain ⟨f₀, hf₀⟩ := ih (evenPart p) hev
      obtain ⟨f₁, hf₁⟩ := ih (evenPart p + oddPart p)
        (lt_of_le_of_lt (degree_add_le _ _) (max_lt hev hod))
      refine ⟨fun b => if b 0 then f₁ (fun i => b i.succ) else f₀ (fun i => b i.succ), ?_⟩
      have e₀ : tableLsb false (fun b : Fin (m + 1) → Bool =>
          if b 0 then f₁ (fun i => b i.succ) else f₀ (fun i => b i.succ)) = f₀ := by
        funext tail; simp [tableLsb]
      have e₁ : tableLsb true (fun b : Fin (m + 1) → Bool =>
          if b 0 then f₁ (fun i => b i.succ) else f₀ (fun i => b i.succ)) = f₁ := by
        funext tail; simp [tableLsb]
      rw [booleanMobiusPolynomial]
      simp only [e₀, e₁, hf₀, hf₁]
      rw [show evenPart p + oddPart p - evenPart p = oddPart p by ring]
      exact parityInterleave_evenPart_oddPart p

/-- **Injectivity**: distinct Boolean tables have distinct Möbius packings — because
their fold terminals are their MLEs, and `mle` is injective. -/
theorem booleanMobiusPolynomial_injective (m : ℕ) :
    Function.Injective (booleanMobiusPolynomial (F := F) m) := by
  intro f g h
  apply mle_injective
  funext r
  have hfg := congrArg (fun q => (foldMleVariables m q r).coeff 0) h
  simpa only [coeff_zero_foldMleVariables_booleanMobiusPolynomial] using hfg

/-- **The image is EXACTLY the window** — the Möbius transform is a bijection from
Boolean tables onto `degreeLT F (2^m)`. -/
theorem mem_range_booleanMobiusPolynomial_iff (m : ℕ) (p : Polynomial F) :
    (∃ table : (Fin m → Bool) → F, booleanMobiusPolynomial m table = p)
      ↔ p.degree < ((2 ^ m : ℕ) : WithBot ℕ) := by
  constructor
  · rintro ⟨table, rfl⟩
    exact degree_booleanMobiusPolynomial_lt m table
  · exact exists_table_booleanMobiusPolynomial m p

/-- **The Möbius inverse**: read a Boolean table off a polynomial by restricting its
fold terminal to the cube. Defined for EVERY polynomial — that is the point: it is
what makes the knowledge state's "the decoded word's multilinear" a total function of
the decoded word, not a partial one. -/
noncomputable def tableOfPoly (m : ℕ) (p : Polynomial F) : (Fin m → Bool) → F :=
  fun b => (foldMleVariables m p (cubePt b)).coeff 0

/-- Round trip, one direction: the table read off a Möbius packing is the table. -/
@[simp] theorem tableOfPoly_booleanMobiusPolynomial (m : ℕ) (f : (Fin m → Bool) → F) :
    tableOfPoly m (booleanMobiusPolynomial m f) = f := by
  funext b
  rw [tableOfPoly, coeff_zero_foldMleVariables_booleanMobiusPolynomial, mle_agrees]

/-- Round trip, the other direction: on the window, `tableOfPoly` is a section. -/
theorem booleanMobiusPolynomial_tableOfPoly (m : ℕ) (p : Polynomial F)
    (hp : p.degree < ((2 ^ m : ℕ) : WithBot ℕ)) :
    booleanMobiusPolynomial m (tableOfPoly m p) = p := by
  obtain ⟨f, rfl⟩ := exists_table_booleanMobiusPolynomial m p hp
  rw [tableOfPoly_booleanMobiusPolynomial]

/-- ⭐ **Every codeword in the window has a definite multilinear.** The fold terminal
of any degree-`< 2^m` polynomial is the multilinear extension, at the challenge point,
of `tableOfPoly` applied to it. This is what forbids "the terminal constant is the MLE
of nothing in particular". -/
theorem coeff_zero_foldMleVariables_eq_mle (m : ℕ) (p : Polynomial F)
    (hp : p.degree < ((2 ^ m : ℕ) : WithBot ℕ)) (r : Fin m → F) :
    (foldMleVariables m p r).coeff 0 = mle (tableOfPoly m p) r := by
  obtain ⟨f, rfl⟩ := exists_table_booleanMobiusPolynomial m p hp
  rw [tableOfPoly_booleanMobiusPolynomial,
    coeff_zero_foldMleVariables_booleanMobiusPolynomial]

/-! ## 5. BaseFold's completeness at Reed–Solomon -/

section BaseFold

variable {ι : ℕ → Type*} {m : ℕ}

/-- BaseFold's degree schedule: `2^m` at the top, halving each round, `1` at the base
— so the base check is literally "the last word is constant". -/
def basefoldDegSched (m : ℕ) : ℕ → ℕ := fun j => 2 ^ (m - j)

@[simp] theorem basefoldDegSched_zero (m : ℕ) : basefoldDegSched m 0 = 2 ^ m := rfl

@[simp] theorem basefoldDegSched_self (m : ℕ) : basefoldDegSched m m = 1 := by
  simp [basefoldDegSched]

theorem basefoldDegSched_halving (m : ℕ) :
    ∀ j, j < m → basefoldDegSched m j = 2 * basefoldDegSched m (j + 1) := by
  intro j hj
  show 2 ^ (m - j) = 2 * 2 ^ (m - (j + 1))
  rw [show m - j = (m - (j + 1)) + 1 by omega, pow_succ]
  ring

/-- The committed word: the RS encoding of a polynomial in the window is a codeword at
the top of the schedule. No new commitment layer — this is `Commitment.lean`'s vector
commitment applied to an ordinary codeword. -/
theorem evalOnDomain_mem_reedSolomonCode {ιd : Type*} (dom : ιd ↪ F)
    (p : Polynomial F) (hp : p.degree < ((2 ^ m : ℕ) : WithBot ℕ)) :
    (fun i => p.eval (dom i)) ∈ reedSolomonCode dom (basefoldDegSched m 0) :=
  mem_reedSolomonCode_iff.mpr ⟨p, by rw [basefoldDegSched_zero]; exact_mod_cast hp,
    fun _ => rfl⟩

/-- ⭐ **The terminal word of the descent, for any committed polynomial in the
window**: the CONSTANT word whose value is the multilinear extension, at the challenge
point, of the table the polynomial encodes. -/
theorem basefold_terminal_word_eq (T : FoldingTower F ι m) (p : Polynomial F)
    (hp : p.degree < ((2 ^ m : ℕ) : WithBot ℕ)) (r : Fin m → F) (k : ι m) :
    T.word (fun i => p.eval (T.dom 0 i)) (chalExt r) m le_rfl k
      = mle (tableOfPoly m p) r := by
  have hr : (fun j : Fin m => chalExt r j.val) = r := funext fun j => chalExt_coe r j
  have hw := T.word_eval_foldMleVariables p (chalExt r) m le_rfl
  rw [hr] at hw
  simp only [hw]
  rw [eval_foldMleVariables m p hp r, coeff_zero_foldMleVariables_eq_mle m p hp r]

/-- **BaseFold completeness, honest case**: commit the Möbius packing of `table`; run
the FRI descent on the challenge stream `r`; the terminal word is the constant
`mle table r`. Composition of `word_eval_foldMleVariables` with the already-proved
`foldMleVariables_booleanMobiusPolynomial`. -/
theorem basefold_terminal_is_mle (T : FoldingTower F ι m)
    (table : (Fin m → Bool) → F) (r : Fin m → F) (k : ι m) :
    T.word (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i))
        (chalExt r) m le_rfl k = mle table r := by
  rw [basefold_terminal_word_eq T _ (degree_booleanMobiusPolynomial_lt m table) r k,
    tableOfPoly_booleanMobiusPolynomial]

/-- The terminal word is constant — the base check `mem_reedSolomonCode_one_iff` is
met on the nose, not by hypothesis. -/
theorem basefold_terminal_word_const (T : FoldingTower F ι m)
    (table : (Fin m → Bool) → F) (r : Fin m → F) :
    T.word (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i))
        (chalExt r) m le_rfl = fun _ => mle table r :=
  funext fun k => basefold_terminal_is_mle T table r k

/-- The descent ACCEPTS the honest commitment, at every challenge stream —
`proximity_complete` reused verbatim on the BaseFold schedule. -/
theorem basefold_proximityTest (T : FoldingTower F ι m)
    (table : (Fin m → Bool) → F) (αs : ℕ → F) :
    proximityTest T (basefoldDegSched m)
      (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i)) αs :=
  proximity_complete T (basefoldDegSched_halving m)
    (evalOnDomain_mem_reedSolomonCode (T.dom 0) _
      (degree_booleanMobiusPolynomial_lt m table)) αs

/-- ⭐ **THE COMPLETENESS STATEMENT.** The honest BaseFold prover's committed word
(1) passes the whole low-degree descent for EVERY challenge stream, and (2) at the
stream carrying the evaluation point `r`, terminates in the constant word whose value
is exactly `mle table r`. Both halves, one theorem, no residual hypothesis. -/
theorem basefold_opening_complete (T : FoldingTower F ι m)
    (table : (Fin m → Bool) → F) (r : Fin m → F) :
    proximityTest T (basefoldDegSched m)
        (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i)) (chalExt r)
      ∧ T.word (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i))
          (chalExt r) m le_rfl = fun _ => mle table r :=
  ⟨basefold_proximityTest T table (chalExt r), basefold_terminal_word_const T table r⟩

end BaseFold

/-! ## 6. Keystones over F₅ (ATLAS law 2: satisfiable + teeth + premise inhabitation)

One variable, on `Selvage/Proximity.lean`'s existing one-round F₅ tower: level 0 =
`{1,2,3,4}`, level 1 = `{1,4}`, degree schedule `2 → 1` — which is exactly
`basefoldDegSched 1`. The table `[1, 2]` has `mle table ![3] = 4`.

* **satisfiable**: the descent on the Möbius commitment terminates at `4`, and the
  proximity test accepts.
* **teeth (the Möbius transform is load-bearing)**: committing the RAW value table as
  coefficients gives a word that ALSO passes the descent at every challenge — it is a
  perfectly good codeword — and terminates at `2`. So `proximityTest` accepting does
  NOT by itself certify the evaluation; only the packing does. This is the honest
  boundary of a completeness result and the reason the soundness leg is separate work.
* **teeth (the degree window is load-bearing)**: `X^2` is outside the `m = 1` window,
  and its terminal word is NOT constant — it takes both values `1` and `4` — so
  `foldMleVariables_eq_C`'s hypothesis is a real constraint, not decoration. -/

namespace BaseFoldExample

open ProximityExample

/-- The one-variable table `[1, 2]`: `f false = 1`, `f true = 2`. -/
def table : (Fin 1 → Bool) → ZMod 5 := fun b => if b 0 then 2 else 1

/-- The BaseFold schedule at `m = 1` is the tower's own `2 → 1`. -/
theorem basefoldDegSched_one : basefoldDegSched 1 0 = 2 ∧ basefoldDegSched 1 1 = 1 := by
  constructor <;> rfl

/-- **FIRES**: the descent on the honest commitment terminates at the MLE value `4`. -/
theorem mobius_descent_terminal (k : levels 1) :
    ldtTower.word
        (fun i => (booleanMobiusPolynomial 1 table).eval (ldtTower.dom 0 i))
        (chalExt ![3]) 1 le_rfl k = 4 := by
  rw [basefold_terminal_is_mle ldtTower table ![3] k]
  decide

/-- **FIRES**: and it accepts, at every challenge stream. -/
theorem mobius_descent_accepts (αs : ℕ → ZMod 5) :
    proximityTest ldtTower (basefoldDegSched 1)
      (fun i => (booleanMobiusPolynomial 1 table).eval (ldtTower.dom 0 i)) αs :=
  basefold_proximityTest ldtTower table αs

/-- The tempting but wrong commitment: the raw values `[1, 2]` read as coefficients. -/
noncomputable def rawPoly : Polynomial (ZMod 5) := C 1 + C 2 * X

theorem rawPoly_degree : rawPoly.degree < ((2 ^ 1 : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  have hn2 : 2 ≤ n := by simpa using hn
  simp [rawPoly, Polynomial.coeff_one, Polynomial.coeff_X,
    show n ≠ 0 by omega, show (1 : ℕ) ≠ n by omega]

/-- **TEETH**: the raw commitment is a perfectly good codeword, so the descent accepts
it at every challenge stream too. -/
theorem raw_descent_accepts (αs : ℕ → ZMod 5) :
    proximityTest ldtTower (basefoldDegSched 1)
      (fun i => rawPoly.eval (ldtTower.dom 0 i)) αs :=
  proximity_complete ldtTower (basefoldDegSched_halving 1)
    (evalOnDomain_mem_reedSolomonCode (m := 1) (ldtTower.dom 0) rawPoly rawPoly_degree) αs

/-- The table the raw commitment actually encodes is `[1, 3]`, not `[1, 2]`. -/
theorem tableOfPoly_rawPoly (b : Fin 1 → Bool) :
    tableOfPoly 1 rawPoly b = 1 + 2 * ofBool (b 0) := by
  have h0 : rawPoly.coeff (2 * 0) = 1 := by
    simp [rawPoly, Polynomial.coeff_one, Polynomial.coeff_C]
  have h1 : rawPoly.coeff (2 * 0 + 1) = 2 := by
    simp [rawPoly, Polynomial.coeff_one, Polynomial.coeff_C]
  show (mleCoefficientFold rawPoly (cubePt b 0)).coeff 0 = _
  rw [coeff_mleCoefficientFold, h0, h1]
  show (1 : ZMod 5) + ofBool (b 0) * 2 = 1 + 2 * ofBool (b 0)
  ring

/-- **TEETH**: the raw commitment's descent terminates at `2`, not `4`. -/
theorem raw_descent_terminal (k : levels 1) :
    ldtTower.word (fun i => rawPoly.eval (ldtTower.dom 0 i))
        (chalExt ![3]) 1 le_rfl k = 2 := by
  rw [basefold_terminal_word_eq ldtTower rawPoly rawPoly_degree ![3] k, mle]
  simp only [tableOfPoly_rawPoly]
  decide

/-- **TEETH, stated**: two commitments of the "same" data, both accepted by the whole
low-degree descent, with DIFFERENT terminal constants. Completeness does not pin the
value; the soundness leg must. -/
theorem raw_commit_terminal_differs_f5 (k : levels 1) :
    ldtTower.word (fun i => rawPoly.eval (ldtTower.dom 0 i)) (chalExt ![3]) 1 le_rfl k
      ≠ ldtTower.word
          (fun i => (booleanMobiusPolynomial 1 table).eval (ldtTower.dom 0 i))
          (chalExt ![3]) 1 le_rfl k := by
  rw [raw_descent_terminal k, mobius_descent_terminal k]
  decide

/-! ### The degree window is a real hypothesis -/

/-- `X²` folds to `X` — it never becomes a constant. -/
theorem mleCoefficientFold_X_sq (r : ZMod 5) :
    mleCoefficientFold (X ^ 2 : Polynomial (ZMod 5)) r = X := by
  ext k
  rw [coeff_mleCoefficientFold, coeff_X_pow, coeff_X_pow, coeff_X]
  by_cases hk : k = 1
  · subst hk; norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring

/-- **TEETH**: `X²` is outside the `m = 1` window, and its terminal word is NOT
constant — it takes the value `1` at one point of the base domain and `4` at the
other. So `foldMleVariables_eq_C`'s degree hypothesis is a constraint. -/
theorem out_of_window_terminal_not_constant :
    ldtTower.word (fun i => (X ^ 2 : Polynomial (ZMod 5)).eval (ldtTower.dom 0 i))
        (chalExt ![3]) 1 le_rfl ⟨0, by decide⟩
      ≠ ldtTower.word (fun i => (X ^ 2 : Polynomial (ZMod 5)).eval (ldtTower.dom 0 i))
        (chalExt ![3]) 1 le_rfl ⟨1, by decide⟩ := by
  have hw := ldtTower.word_eval_foldMleVariables (X ^ 2 : Polynomial (ZMod 5))
    (chalExt ![3]) 1 le_rfl
  simp only [hw]
  rw [show foldMleVariables 1 (X ^ 2 : Polynomial (ZMod 5))
      (fun j : Fin 1 => chalExt ![3] j.val)
      = mleCoefficientFold (X ^ 2 : Polynomial (ZMod 5)) (chalExt ![3] 0) from rfl,
    mleCoefficientFold_X_sq, eval_X, eval_X]
  decide

end BaseFoldExample

/-- info: 'Minidregg.Selvage.fold_eval_mleCoefficientFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_eval_mleCoefficientFold
/-- info: 'Minidregg.Selvage.FoldingTower.word_eval_foldMleVariables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FoldingTower.word_eval_foldMleVariables
/-- info: 'Minidregg.Selvage.mem_range_booleanMobiusPolynomial_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_range_booleanMobiusPolynomial_iff
/-- info: 'Minidregg.Selvage.basefold_terminal_word_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefold_terminal_word_eq
/-- info: 'Minidregg.Selvage.basefold_opening_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefold_opening_complete
/-- info: 'Minidregg.Selvage.BaseFoldExample.raw_commit_terminal_differs_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BaseFoldExample.raw_commit_terminal_differs_f5
/-- info: 'Minidregg.Selvage.BaseFoldExample.out_of_window_terminal_not_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BaseFoldExample.out_of_window_terminal_not_constant

end Minidregg.Selvage
