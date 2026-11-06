/-
# Selvage.CollisionResistanceROM — collision resistance IS a ROM theorem: the
# birthday-bound adversary, and the `[COMMIT-CR]` discharge at the flat-hash
# resolution.

`Selvage/Commitment.lean` prices the deployed Merkle/sponge realizer as the named
residual `[COMMIT-CR]`: "binding is a theorem ONLY relative to
collision-resistance of the hash". This file SHRINKS that floor: in the
random-oracle model — the SAME lazy-sampling handler discipline as
`Selvage/FiatShamir.lean`'s `Oracle` — collision resistance is not a standalone
assumption but a PROVED probabilistic bound. A `q`-query adversary against an
oracle with range `Fin N` finds a collision with probability at most
`q·(q−1)/(2·N)` (the birthday bound), by the union bound over query pairs; so
the hash commitment instantiated from the RO is collision-resistant WITH A
NUMBER, and the CR leg of `[COMMIT-CR]` moves from "assumed" to "priced by a
theorem over the RO's coins".

What lands here:
* **The coin-space model.** A `q`-query adversary with pairwise-DISTINCT
  queries (`ROAdversary`; repeats are answered identically by the handler and
  are not collisions). Under lazy sampling, `q` distinct fresh queries consume
  exactly `q` independent uniform coins — and that is MACHINE-CHECKED against
  the landed handler, not assumed: `roAnswers_eq_coins` runs
  `Selvage/FiatShamir.lean`'s `Oracle.empty` over the adversary's query list and
  proves the response list IS the coin list. So `uniformProb (Fin q → Fin N)`
  is the RO's answer distribution on the adversary's queries, by theorem.
* **`birthday_bound`** — the core: the probability that two distinct queries
  receive equal answers is `≤ q·(q−1)/(2·N)`. Union bound over ordered pairs
  (`uniformProb_exists_le`, `Selvage/Depth.lean`), each pair colliding with
  probability EXACTLY `1/N` over the second coordinate's coin
  (`uniformProb_coords_eq`, via `splitCoord` + `uniformProb_prod_le` — the
  landed "condition on everything but the fresh coin" kernel), and the Gauss
  sum `∑_{j<q} j = q(q−1)/2` for the pair count. `birthday_bound_pow`
  specializes the range to `Fin (2^n)`: `≤ q·(q−1)/2^(n+1)`.
* **The RO hash commitment + the reduction, both directions.** `roScheme H` —
  commit a word by hashing it (`Root := Fin N`, opening = the word itself);
  `roScheme_break_iff_collision`: the scheme's `PositionBinding` FAILS iff `H`
  has a collision (equivocation ⇒ collision is `[COMMIT-CR]`(ii) at this
  resolution, and collision ⇒ equivocation makes the reduction lossless);
  `roBinding`: a collision-free `H` yields a full `BindingCommitment` — the
  exact "binding conditional on a NAMED CR hypothesis carried as structure"
  shape `[COMMIT-CR]` asked for.
* **`commitCR_of_RO`** — the discharge: a `BreakAdversary` (distinct queries
  + a claimed colliding pair chosen AFTER seeing the answers) wins — exhibits
  two distinct queried words with equal roots — with probability
  `≤ q·(q−1)/(2·N)`. `BreakAdversary.wins_breaks_binding` certifies the win
  event is a genuine `PositionBinding` break of `roScheme H` for EVERY oracle
  `H` consistent with the observed answers: the adversary's claim, pushed
  through `roScheme_break_iff_collision`'s collision direction, is a real
  equivocation, not a redefinition of "wins".

**Covered scope, in the same sentence as the claim** (the honest label): the
bound is proved for NON-ADAPTIVE query schedules (the `q` distinct queries are
fixed before the coins; only the CLAIMED PAIR is adaptive) against the FLAT
hash commitment (whole-word preimage as opening); adaptive schedules are
`[CR-ROM-adaptive]` and the Merkle-path structure stays inside `[COMMIT-CR]`
(i)/(iii) — the ledger at the bottom prices both.

**Keystones** (ATLAS: satisfiable + teeth + premise inhabitation, BUILT):
`collisionProb_two` computes the two-query probability EXACTLY (`1/N`);
`birthday_tight_two`: the bound is ATTAINED at `q = 2` — an inequality that is
an equality on a built instance is not slack; `A₂` is a concrete two-query
break adversary over one-symbol words whose win event has probability exactly
the bound (`A₂_winProb`, `A₂_attains`) and whose concrete win yields a
computed `PositionBinding` refutation through the bridge (`A₂_breaks`).
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Selvage.Commitment
import Selvage.FiatShamir

namespace Minidregg.Selvage

/-! ## The collision event and its probability -/

/-- The collision event on the coin space: some two (ordered) coins agree —
the RO answered two DISTINCT queries identically. `i < j` rather than `i ≠ j`
so each unordered pair is counted once; `collides_of_ne` below folds the
unordered form into it. -/
def Collides {q N : ℕ} (c : Fin q → Fin N) : Prop :=
  ∃ i j : Fin q, i < j ∧ c i = c j

/-- An unordered collision is a collision. -/
lemma collides_of_ne {q N : ℕ} {c : Fin q → Fin N} {i j : Fin q}
    (hij : i ≠ j) (hc : c i = c j) : Collides c := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, hc⟩
  · exact ⟨j, i, h, hc.symm⟩

/-- `Pr[collision]` for `q` independent uniform responses from `Fin N` — by
`roAnswers_eq_coins` below, exactly the RO's answers on `q` distinct fresh
queries. -/
noncomputable def collisionProb (q N : ℕ) : ℝ :=
  uniformProb (Fin q → Fin N) Collides

/-! ## The per-pair probability: one fresh coin hits a fixed value with
probability `1/N` -/

/-- Hitting a designated value: probability exactly `1/|C|`. -/
private lemma uniformProb_eq_left {C : Type} [Fintype C] (v : C) :
    uniformProb C (fun c => v = c) = 1 / (Fintype.card C : ℝ) := by
  unfold uniformProb
  haveI : Unique {c : C // v = c} := ⟨⟨⟨v, rfl⟩⟩, fun c => Subtype.ext c.2.symm⟩
  rw [Nat.card_unique, Nat.cast_one]

/-- **The per-pair bound**: two distinct coordinates of a uniform tuple agree
with probability at most `1/N` — split coordinate `j` out
(`splitCoord`, `Selvage/Depth.lean`) and condition on everything but its coin
(`uniformProb_prod_le`). This is the "fresh response is an independent uniform
coin" kernel the birthday argument sums. -/
lemma uniformProb_coords_eq {q N : ℕ} {i j : Fin q} (hij : i ≠ j) :
    uniformProb (Fin q → Fin N) (fun c => c i = c j) ≤ 1 / (N : ℝ) := by
  classical
  have key : uniformProb (({k : Fin q // k ≠ j} → Fin N) × Fin N)
      (fun x => x.1 ⟨i, hij⟩ = x.2) ≤ 1 / (N : ℝ) := by
    refine uniformProb_prod_le (div_nonneg zero_le_one (Nat.cast_nonneg N))
      fun rest => ?_
    rw [uniformProb_eq_left, Fintype.card_fin]
  have hxfer : uniformProb (Fin q → Fin N) (fun c => c i = c j)
      = uniformProb (({k : Fin q // k ≠ j} → Fin N) × Fin N)
          (fun x => x.1 ⟨i, hij⟩ = x.2) :=
    uniformProb_equiv (splitCoord j)
      (fun x : ({k : Fin q // k ≠ j} → Fin N) × Fin N => x.1 ⟨i, hij⟩ = x.2)
  rw [hxfer]
  exact key

/-! ## The pair count: Gauss -/

/-- `#{i < j} = j`, as an indicator sum over `Fin q`. -/
private lemma sum_indicator_lt {q : ℕ} (j : Fin q) :
    ∑ i : Fin q, (if (i : ℕ) < (j : ℕ) then (1 : ℝ) else 0) = ((j : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < (j : ℕ) then (1 : ℝ) else 0) q,
    Finset.sum_boole]
  have hfilter : (Finset.range q).filter (fun m => m < (j : ℕ)) =
      Finset.range (j : ℕ) := by
    ext m
    have := j.isLt
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.card_range]

/-- The Gauss sum over `Fin q`, in `ℝ`: `∑ j, j = q(q−1)/2`. -/
private lemma sum_fin_cast (q : ℕ) :
    (∑ j : Fin q, ((j : ℕ) : ℝ)) = (q : ℝ) * ((q : ℝ) - 1) / 2 := by
  cases q with
  | zero => simp
  | succ m =>
      rw [Fin.sum_univ_eq_sum_range (fun m => (m : ℝ)) (m + 1)]
      have h := Finset.sum_range_id_mul_two (m + 1)
      rw [Nat.succ_sub_one] at h
      have h2 : (∑ i ∈ Finset.range (m + 1), (i : ℝ)) * 2
          = ((m : ℝ) + 1) * (m : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast
      nlinarith [h2]

/-! ## The birthday bound -/

/-- **The birthday bound** — the union-bound core, a REAL probability theorem:
`q` independent uniform draws from `Fin N` collide with probability at most
`q·(q−1)/(2·N)`. Union bound over ordered pairs (`uniformProb_exists_le`,
twice), the per-pair kernel `uniformProb_coords_eq`, and the Gauss count. No
positivity side conditions: for `N = 0` both sides degenerate to `0 ≤ 0` under
the division-by-zero convention, and `q ∈ {0, 1}` makes the right side `0`
with the event empty. -/
theorem birthday_bound (q N : ℕ) :
    collisionProb q N ≤ (q : ℝ) * ((q : ℝ) - 1) / (2 * (N : ℝ)) := by
  classical
  have hev : collisionProb q N
      = uniformProb (Fin q → Fin N) (fun c => ∃ j i : Fin q, i < j ∧ c i = c j) :=
    uniformProb_congr fun c => exists_comm
  rw [hev]
  calc uniformProb (Fin q → Fin N) (fun c => ∃ j i : Fin q, i < j ∧ c i = c j)
      ≤ ∑ j : Fin q,
          uniformProb (Fin q → Fin N) (fun c => ∃ i : Fin q, i < j ∧ c i = c j) :=
        uniformProb_exists_le _
    _ ≤ ∑ j : Fin q, ∑ i : Fin q,
          uniformProb (Fin q → Fin N) (fun c => i < j ∧ c i = c j) :=
        Finset.sum_le_sum fun j _ => uniformProb_exists_le _
    _ ≤ ∑ j : Fin q, ∑ i : Fin q,
          (if (i : ℕ) < (j : ℕ) then (1 : ℝ) else 0) * (1 / (N : ℝ)) := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => ?_
        by_cases hij : i < j
        · rw [if_pos (Fin.lt_def.mp hij), one_mul]
          exact le_trans (uniformProb_mono fun c hc => hc.2)
            (uniformProb_coords_eq (ne_of_lt hij))
        · rw [if_neg (fun h => hij (Fin.lt_def.mpr h)), zero_mul]
          exact le_of_eq (uniformProb_false fun c hc => hij hc.1)
    _ = ∑ j : Fin q, ((j : ℕ) : ℝ) * (1 / (N : ℝ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, sum_indicator_lt]
    _ = (∑ j : Fin q, ((j : ℕ) : ℝ)) * (1 / (N : ℝ)) := by
        rw [Finset.sum_mul]
    _ = (q : ℝ) * ((q : ℝ) - 1) / 2 * (1 / (N : ℝ)) := by rw [sum_fin_cast]
    _ = (q : ℝ) * ((q : ℝ) - 1) / (2 * (N : ℝ)) := by ring

/-- The birthday bound at a power-of-two range — the `H : D → Fin (2^n)`
rendering: `Pr[collision] ≤ q·(q−1)/2^(n+1)`. -/
theorem birthday_bound_pow (q n : ℕ) :
    collisionProb q (2 ^ n) ≤ (q : ℝ) * ((q : ℝ) - 1) / (2 ^ (n + 1) : ℝ) :=
  calc collisionProb q (2 ^ n)
      ≤ (q : ℝ) * ((q : ℝ) - 1) / (2 * ((2 ^ n : ℕ) : ℝ)) :=
        birthday_bound q (2 ^ n)
    _ = (q : ℝ) * ((q : ℝ) - 1) / (2 ^ (n + 1) : ℝ) := by
        push_cast
        ring_nf

/-! ## The coin space IS the landed RO: running the handler

`uniformProb (Fin q → Fin N)` models "the RO's answers on `q` distinct
queries" — and that modeling step is a THEOREM against `Selvage/FiatShamir.lean`'s
lazy-sampling handler, not prose: run `Oracle.empty` over the query list with
the coin list, and the response list is the coin list, verbatim. Distinctness
is what makes every query fresh; a repeated query would replay its recorded
sample (`respond_consistent`) and consume no coin, which is exactly why
`ROAdversary` carries injectivity. -/

/-- A `q`-query collision-finding adversary against the RO: `q` pairwise
distinct queries, fixed in advance (the NON-ADAPTIVE schedule — the covered
scope; adaptive schedules are `[CR-ROM-adaptive]`). -/
structure ROAdversary (D : Type) (q : ℕ) where
  /-- The queries put to the oracle. -/
  query : Fin q → D
  /-- Pairwise distinct — repeats replay the recorded sample and are not
  collisions. -/
  query_inj : Function.Injective query

/-- Thread the lazy-sampling handler through a list of (query, coin) pairs,
collecting the responses — the sequential run of `Oracle.respond`. -/
noncomputable def oracleRun {D C : Type} (O : Oracle D C) :
    List (D × C) → Oracle D C × List C
  | [] => (O, [])
  | (x, coin) :: rest =>
      let r := O.respond x coin
      let t := oracleRun r.2 rest
      (t.1, r.1 :: t.2)

/-- On pairwise-distinct queries all fresh for `O`, the handler's responses
ARE the coins: every step lands in the sampling branch
(`respond_fresh_fst`), and freshness is preserved by the frame law
(`lookup_respond_ne`). -/
lemma oracleRun_fresh {D C : Type} (l : List (D × C)) (O : Oracle D C)
    (hnd : (l.map Prod.fst).Nodup) (hfresh : ∀ e ∈ l, O.lookup e.1 = none) :
    (oracleRun O l).2 = l.map Prod.snd := by
  induction l generalizing O with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨x, coin⟩ := e
      have hx : O.lookup x = none := hfresh (x, coin) (List.mem_cons_self ..)
      rw [List.map_cons] at hnd
      obtain ⟨hxrest, hndrest⟩ := List.nodup_cons.mp hnd
      show (O.respond x coin).1 :: (oracleRun (O.respond x coin).2 rest).2
          = coin :: rest.map Prod.snd
      have hfresh' : ∀ e ∈ rest, (O.respond x coin).2.lookup e.1 = none := by
        intro e he
        have hmem : e.1 ∈ rest.map Prod.fst := List.mem_map.mpr ⟨e, he, rfl⟩
        rw [Oracle.lookup_respond_ne O (fun h : e.1 = x => hxrest (h ▸ hmem))
          coin]
        exact hfresh e (List.mem_cons_of_mem _ he)
      rw [Oracle.respond_fresh_fst hx, ih (O.respond x coin).2 hndrest hfresh']

/-- **The modeling step, machine-checked**: the landed handler
(`Oracle.empty`, `Selvage/FiatShamir.lean`), run on an adversary's `q` distinct
queries with coins `c`, answers EXACTLY `c`. So the coin space
`Fin q → Fin N` under `uniformProb` — the space `birthday_bound` measures —
is the RO's answer distribution on the adversary's queries, one independent
uniform coin per distinct query. -/
theorem roAnswers_eq_coins {D C : Type} {q : ℕ} (A : ROAdversary D q)
    (c : Fin q → C) :
    (oracleRun Oracle.empty (List.ofFn fun i => (A.query i, c i))).2
      = List.ofFn c := by
  rw [oracleRun_fresh _ _ ?_ fun e _ => Oracle.lookup_empty e.1, List.map_ofFn]
  · rfl
  · rw [List.map_ofFn]
    exact List.nodup_ofFn.mpr fun a b h => A.query_inj h

/-! ## The RO hash commitment and the equivocation ⟺ collision reduction

`[COMMIT-CR]`'s realizer, at the flat resolution: commit a word by hashing it.
`Root := Fin N` (a SHORT digest — `commit` genuinely compresses whenever the
word space outnumbers `Fin N`, unlike `idealCommitment` whose root is the
word), the opening is the whole preimage word, verification re-hashes and
reads the symbol. The Merkle-path structure (log-size openings) stays in
`[COMMIT-CR]`(i)/(iii); the CR content is fully here. -/

/-- The hash commitment induced by an oracle function `H`: commit = hash,
open = reveal the word, verify = re-hash and compare + read the symbol. -/
def roScheme (F ι : Type*) {N : ℕ} (H : (ι → F) → Fin N) :
    OpeningScheme (Fin N) F ι (ι → F) where
  commit := H
  openAt := fun w _ => w
  verifyOpen := fun rt i v o => H o = rt ∧ o i = v
  verifyOpen_commit := fun _ _ => ⟨rfl, rfl⟩

/-- A retained `PositionEquivocation` against the flat RO scheme contains the
two colliding preimages directly: the submitted opening word and the honest
committed word.  This is the witness-level bridge needed by raw transcript
verifiers; it does not pass through a proof-by-negation of `PositionBinding`. -/
theorem roScheme_positionEquivocation_collision
    {F ι : Type*} {N : ℕ} (H : (ι → F) → Fin N)
    {rt : Fin N} {i : ι} {value : F} {opening word : ι → F}
    (hequiv : (roScheme F ι H).PositionEquivocation
      rt i value opening word) :
    opening ≠ word ∧ H opening = H word := by
  rcases hequiv with ⟨hopening, hword, hne⟩
  refine ⟨?_, hopening.1.trans hword.1.symm⟩
  intro heq
  apply hne
  rw [← hopening.2, heq]

/-- **The reduction, both directions**: `roScheme H` loses position-binding
IFF `H` has a collision. Break ⇒ collision is `[COMMIT-CR]`(ii) at the flat
resolution (an equivocation exhibits two distinct preimage words with equal
digests); collision ⇒ break makes the reduction lossless — the collision
event and the break event are THE SAME event, so the birthday bound prices
binding failure exactly, not merely from above. -/
theorem roScheme_break_iff_collision {F ι : Type*} {N : ℕ}
    (H : (ι → F) → Fin N) :
    ¬ (roScheme F ι H).PositionBinding ↔ ∃ x y : ι → F, x ≠ y ∧ H x = H y := by
  constructor
  · intro hb
    unfold OpeningScheme.PositionBinding at hb
    push Not at hb
    obtain ⟨rt, i, v, v', o, o', h1, h2, hne⟩ := hb
    refine ⟨o, o', fun heq => hne ?_, h1.1.trans h2.1.symm⟩
    rw [← h1.2, ← h2.2, heq]
  · rintro ⟨x, y, hne, hcol⟩ hbind
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
    exact ha (hbind (H x) a (x a) (y a) x y ⟨rfl, rfl⟩ ⟨hcol.symm, rfl⟩)

/-- The positive direction as carried structure — the exact `[COMMIT-CR]`
shape ("binding conditional on a NAMED CR hypothesis carried as structure,
never an axiom"): a collision-free oracle function yields a full
`BindingCommitment`. What this file adds is the PRICE of that hypothesis:
over the RO's coins it fails with probability `≤ q(q−1)/(2N)`
(`commitCR_of_RO`), so CR is no longer a standalone assumption. -/
def roBinding {F ι : Type*} {N : ℕ} (H : (ι → F) → Fin N)
    (hcr : ∀ x y : ι → F, H x = H y → x = y) :
    BindingCommitment (Fin N) F ι (ι → F) where
  toOpeningScheme := roScheme F ι H
  binding := fun _rt i v v' o o' h h' => by
    have ho : o = o' := hcr o o' (h.1.trans h'.1.symm)
    rw [← h.2, ← h'.2, ho]

/-! ## The break adversary and the `[COMMIT-CR]` discharge -/

/-- A binding-break adversary against the RO commitment: `q` distinct queries
(non-adaptive — the covered scope), plus a claimed colliding PAIR chosen
after seeing all `q` answers (`out` reads the full coin vector: the claim IS
adaptive). It wins if the claimed pair is two distinct queried words the RO
bound to equal digests — by `wins_breaks_binding`, a genuine equivocation. -/
structure BreakAdversary (D : Type) (q N : ℕ) extends ROAdversary D q where
  /-- The claimed colliding pair of query indices, a function of the answers. -/
  out : (Fin q → Fin N) → Fin q × Fin q

/-- The win event: the claimed pair is two distinct queries with equal
answers. -/
def BreakAdversary.Wins {D : Type} {q N : ℕ} (A : BreakAdversary D q N)
    (c : Fin q → Fin N) : Prop :=
  (A.out c).1 ≠ (A.out c).2 ∧ c (A.out c).1 = c (A.out c).2

/-- A win exhibits a collision among the coins. -/
theorem BreakAdversary.wins_collision {D : Type} {q N : ℕ}
    (A : BreakAdversary D q N) {c : Fin q → Fin N} (h : A.Wins c) :
    Collides c :=
  collides_of_ne h.1 h.2

/-- **A win is a REAL binding break** — the bridge into
`Selvage/Commitment.lean`'s vocabulary: for EVERY oracle function `H` consistent
with the answers the adversary saw, the winning pair refutes
`(roScheme H).PositionBinding` (through the collision direction of the
reduction). The win event is not a proxy: it is equivocation, exhibited. -/
theorem BreakAdversary.wins_breaks_binding {F ι : Type} {q N : ℕ}
    (A : BreakAdversary (ι → F) q N) {c : Fin q → Fin N} (hwin : A.Wins c)
    (H : (ι → F) → Fin N) (hH : ∀ i, H (A.query i) = c i) :
    ¬ (roScheme F ι H).PositionBinding := by
  rw [roScheme_break_iff_collision]
  refine ⟨A.query (A.out c).1, A.query (A.out c).2,
    fun h => hwin.1 (A.query_inj h), ?_⟩
  rw [hH, hH, hwin.2]

/-- **The `[COMMIT-CR]` discharge, at the covered scope**: every `q`-query
break adversary against the RO hash commitment wins with probability at most
`q·(q−1)/(2·N)` over the RO's coins. Collision resistance of the
RO-instantiated commitment is a THEOREM with a number — the CR leg of
`[COMMIT-CR]` is no longer a standalone assumption; what remains standalone
is only `[FS-ROM]`'s "the deployed sponge realizes the handler" (already
priced at deployment) plus this file's `[CR-ROM-adaptive]` residual. -/
theorem commitCR_of_RO {D : Type} (q N : ℕ) (A : BreakAdversary D q N) :
    uniformProb (Fin q → Fin N) A.Wins
      ≤ (q : ℝ) * ((q : ℝ) - 1) / (2 * (N : ℝ)) :=
  le_trans (uniformProb_mono fun _c => A.wins_collision) (birthday_bound q N)

/-- The discharge at the `2^n`-bit rendering: `≤ q·(q−1)/2^(n+1)`. -/
theorem commitCR_of_RO_pow {D : Type} (q n : ℕ)
    (A : BreakAdversary D q (2 ^ n)) :
    uniformProb (Fin q → Fin (2 ^ n)) A.Wins
      ≤ (q : ℝ) * ((q : ℝ) - 1) / (2 ^ (n + 1) : ℝ) :=
  le_trans (uniformProb_mono fun _c => A.wins_collision) (birthday_bound_pow q n)

/-! ## Keystones (ATLAS: satisfiable + teeth + premise inhabitation, BUILT) -/

namespace BirthdayExample

/-- The two-coordinate diagonal has probability exactly `1/N`: the counted
set is equinumerous with `Fin N` (choose the shared value), the space has
`N²` functions. -/
theorem uniformProb_diag (N : ℕ) :
    uniformProb (Fin 2 → Fin N) (fun c => c 0 = c 1) = 1 / (N : ℝ) := by
  classical
  unfold uniformProb
  have e : {c : Fin 2 → Fin N // c 0 = c 1} ≃ Fin N :=
    { toFun := fun c => c.1 0
      invFun := fun v => ⟨fun _ => v, rfl⟩
      left_inv := fun c => by
        refine Subtype.ext (funext fun i => ?_)
        fin_cases i
        · rfl
        · exact c.2
      right_inv := fun v => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; norm_num
  · have hN : ((N : ℝ)) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
    rw [pow_two, Nat.cast_mul, div_mul_eq_div_div, div_self hN]

/-- **Satisfiable, computed exactly**: the two-query collision probability IS
`1/N` — the `q = 2` event is `c 0 = c 1`, counted on the nose. -/
theorem collisionProb_two (N : ℕ) : collisionProb 2 N = 1 / (N : ℝ) := by
  have hev : collisionProb 2 N
      = uniformProb (Fin 2 → Fin N) (fun c => c 0 = c 1) := by
    refine uniformProb_congr fun c => ⟨?_, fun h => ⟨0, 1, by decide, h⟩⟩
    rintro ⟨i, j, hlt, hc⟩
    fin_cases i <;> fin_cases j <;> first
      | exact hc
      | exact absurd hlt (by decide)
  rw [hev, uniformProb_diag]

/-- **Teeth, non-vacuity**: for any real range the two-query collision
probability is strictly positive — the event `birthday_bound` prices is
POSSIBLE, the bound is not `0 ≤ 0` dressed up. -/
theorem collisionProb_two_pos (N : ℕ) (hN : 0 < N) : 0 < collisionProb 2 N := by
  rw [collisionProb_two]
  exact div_pos one_pos (by exact_mod_cast hN)

/-- **Teeth, tightness**: the birthday bound is ATTAINED at `q = 2` —
`2·(2−1)/(2·N) = 1/N = collisionProb 2 N`. The union bound's only slack is
double-counting joint collisions, and with one pair there is none. -/
theorem birthday_tight_two (N : ℕ) :
    collisionProb 2 N = (2 : ℝ) * ((2 : ℝ) - 1) / (2 * (N : ℝ)) := by
  rw [collisionProb_two]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; norm_num
  · have hN : ((N : ℝ)) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
    field_simp
    norm_num

/-- **Premise inhabitation**: a concrete break adversary — two one-symbol
words (`Fin 1 → Fin 2`, the constants `0` and `1`), claimed pair `(0, 1)`. -/
def A₂ : BreakAdversary (Fin 1 → Fin 2) 2 2 where
  query := fun i _ => i
  query_inj := fun _ _ h => congrFun h 0
  out := fun _ => (0, 1)

/-- `A₂` wins on the all-`0` answer vector: distinct words, equal digests. -/
theorem A₂_wins : A₂.Wins (fun _ => 0) := by
  refine ⟨?_, rfl⟩
  show (0 : Fin 2) ≠ 1
  decide

/-- The bridge FIRES on built objects: `A₂`'s concrete win refutes
`PositionBinding` of the RO scheme at the consistent oracle (the constant-`0`
hash) — the discharge chain runs end to end on a computed instance. -/
theorem A₂_breaks :
    ¬ (roScheme (Fin 2) (Fin 1) (fun _ => (0 : Fin 2))).PositionBinding :=
  A₂.wins_breaks_binding A₂_wins (fun _ => 0) (fun _ => rfl)

/-- `A₂`'s win probability, exactly: `1/2` — the claimed pair is always
`(0, 1)`, so winning is precisely the diagonal event. -/
theorem A₂_winProb : uniformProb (Fin 2 → Fin 2) A₂.Wins = 1 / 2 := by
  have hev : uniformProb (Fin 2 → Fin 2) A₂.Wins
      = uniformProb (Fin 2 → Fin 2) (fun c => c 0 = c 1) :=
    uniformProb_congr fun c =>
      ⟨fun h => h.2, fun h => ⟨(by decide : (0 : Fin 2) ≠ 1), h⟩⟩
  rw [hev, uniformProb_diag]
  norm_num

/-- **Teeth for the discharge**: `commitCR_of_RO`'s bound is an EQUALITY on
`A₂` — a built adversary attains `q(q−1)/(2N)` at `q = N = 2`. The theorem
gives away nothing on this instance. -/
theorem A₂_attains : uniformProb (Fin 2 → Fin 2) A₂.Wins
    = (2 : ℝ) * ((2 : ℝ) - 1) / (2 * ((2 : ℕ) : ℝ)) := by
  rw [A₂_winProb]
  norm_num

end BirthdayExample

/-! ## Residual ledger — prose, not stubs

**What CLOSED here.** (1) The union-bound birthday core, `birthday_bound` /
`birthday_bound_pow`: a real probability theorem over the same `uniformProb`
counting measure as the rest of the loom, with the per-pair `1/N` kernel
proved by coordinate-splitting, and tight at `q = 2` by a computed instance.
(2) The equivocation ⟺ collision reduction for the RO hash commitment
(`roScheme_break_iff_collision`) — `[COMMIT-CR]`(ii) at the flat resolution,
LOSSLESS (an iff, not a one-way inequality). (3) The discharge
`commitCR_of_RO`: binding breaks by query-bounded adversaries are priced by
the birthday bound, so the CR hypothesis `roBinding` carries is no longer
standalone — its failure probability is a theorem in the ROM. (4) The
modeling step "distinct fresh queries = independent uniform coins" is
machine-checked against the LANDED handler (`roAnswers_eq_coins`), not
narrated.

**[CR-ROM-adaptive]** — the adaptive-schedule reduction, owed. Covered scope
above is the non-adaptive schedule: `A.query` is fixed before the coins;
only the claimed pair (`out`) sees the answers. The full ROM adversary
chooses query `i+1` after answer `i`. The standard lazy-sampling argument
closes this: whatever query the adversary asks next, a FRESH query's answer
is one new independent uniform coin (`respond_fresh_fst` — the handler
machinery is already landed), so the event "coin `j` hits any of the `< j`
previously recorded values" keeps probability `≤ (j−1)/N` conditioned on any
history, and summing gives the same `q(q−1)/(2N)`. What the Lean proof needs
that this file does not yet have: the adaptive run as a coin-indexed process
(the `srTrace`/`stepFn` pattern of `Selvage/Rbr.lean` at query granularity) and
a conditioning lemma in the shape of `uniformProb_prod_le` applied per step
along it. Also folded here: the standard "wlog the adversary queries its
output" padding — an adversary claiming an UNQUERIED word costs `q ↦ q + 2`
in the bound, the usual bookkeeping, owed together with adaptivity since both
are schedule-shape arguments.

**Still `[COMMIT-CR]`(i)/(iii)** (unchanged, priced in
`Selvage/Commitment.lean`): the Merkle/sponge structure — tree-shaped `commit`,
log-size `openAt` (this file's flat opening is the whole word: sound, not
succinct), and the path-collision reduction from tree equivocation to
compression-function collision. This file supplies the CR endpoint that
reduction targets, with its ROM price; the tree walk itself is still owed.
**[FS-ROM]** (unchanged): that the deployed sponge realizes the lazy-sampling
handler remains the one modeling idealization, shared with the transcript
layer.

## Ledger

* `Collides` / `collisionProb` — the event and its counting probability.
* `uniformProb_coords_eq` — the per-pair `1/N` kernel (split + condition).
* `birthday_bound` / `birthday_bound_pow` — THE union-bound birthday core.
* `ROAdversary` / `oracleRun` / `roAnswers_eq_coins` — the coin space
  machine-checked to BE the landed handler's answers on distinct queries.
* `roScheme` / `roScheme_break_iff_collision` / `roBinding` — the RO hash
  commitment, the lossless equivocation ⟺ collision reduction, and CR as
  carried structure in `Selvage/Commitment.lean`'s `BindingCommitment` shape.
  `roScheme_positionEquivocation_collision` is the direct witness-level form
  consumed by raw transcript verifiers.
* `BreakAdversary` / `Wins` / `wins_breaks_binding` / `commitCR_of_RO` (+
  `_pow`) — the discharge: binding breaks priced at `q(q−1)/(2N)`.
* Keystones — `collisionProb_two` (exact), `collisionProb_two_pos`
  (possible), `birthday_tight_two` (attained), `A₂` + `A₂_wins` + `A₂_breaks`
  + `A₂_winProb` + `A₂_attains` (a built adversary running the whole chain,
  attaining the bound).
* Residuals — `[CR-ROM-adaptive]` (adaptive schedules + output padding),
  `[COMMIT-CR]`(i)/(iii) (Merkle structure/succinctness), `[FS-ROM]`
  (sponge realizes handler) — all prose above, none a `True` stub.
* `#print axioms`: `birthday_bound`, `commitCR_of_RO`,
  `roScheme_break_iff_collision`, `wins_breaks_binding`,
  `roAnswers_eq_coins`, and all keystones — `propext, Classical.choice,
  Quot.sound` only; `roBinding` — NO axioms. No `sorry` anywhere. -/

#check @birthday_bound
#check @commitCR_of_RO
#check @BreakAdversary.wins_breaks_binding
#check @roAnswers_eq_coins

end Minidregg.Selvage
