/-
# Selvage.ZkTriangular — [ZK-RBR-interleave] missing lemma 1 attacked: TRIANGULAR
joint hiding of the recommitted partial folds. The backward induction through
the ∀-witness quantifier CLOSES — both fields.

`Selvage/RbrZeroKnowledge.lean` proved the multi-round chain simulator for the
FRESH-MASK PRODUCT model (round `k` opens `mask (fs k) (γs k) (gs k)` — its
own pre-mask word, its own fresh draw) and named the deployed gap as
`[ZK-RBR-interleave]`'s first missing lemma: in the recommitment schedule,
round `k` opens the `k`-th PARTIAL FOLD, which contains every EARLIER round's
mask — the joint opening map is TRIANGULAR (round `k` reads `gs 0 … gs k`),
the joint fibers no longer factor into per-round fibers, and the
COORDINATEWISE translation of `chain_fiber_equinum` stops preserving them.
This file builds that triangular model and PROVES its joint hiding. The
residual's own prediction — "a backward induction over rounds (condition on
`gs 0 … gs (k−1)`, apply round `k`'s hiding at the resulting pre-mask word)
should recover joint uniformity" — is carried out and CLOSES, at the model
level, with no `sorry` and no vacuous `Prop := True`.

**The model.** `triPre γs fs gs k` is the pre-mask word at round `k` (the
first `k+1` rounds' words plus the EARLIER rounds' mask contributions);
`triFold γs fs gs k = mask (triPre …) (γs k) (gs k)` is the `k`-th
recommitted partial fold — round `k`'s own fresh draw enters BY the landed
fold word operation `mask`, at round `k`'s challenge, on top of a word that
already contains `gs 0 … gs (k−1)`. The recursion is exhibited, not just
asserted: `triPre_bot` (round 0's pre-mask word is its own word, mask-free)
and `triFold_succ` (each recommitted word is `mask` of (previous recommitted
word + new round word) at the round challenge with the round's fresh draw —
the `foldWords` step shape with the mask folded in). Two modeling choices,
stated honestly rather than hidden: (1) the REAL words' fold weights are
absorbed into `fs` — legal as a WLOG because every hiding field quantifies
over ALL word families `fs`, so `fs k := γᵏ-weighted real word` is an
instance, and the mask challenges `γs k` (which hiding dials on) are NOT
absorbed; (2) each recommitted word is opened at its OWN round only —
WARP's recommitment-schedule invariant, here true BY CONSTRUCTION of
`triOpen`, not derived from a protocol object. (2) is the honest boundary of
this file and heads the sharpened residual below.

**What closes, and how.**

* **`TriangularHiding`** — the deployed analog of `RbrZeroKnowledge`'s two
  chain fields, on the SAME `jointMasks` space: `tri_sim_support` (the joint
  opened tuples of all `n` triangular rounds reach ALL of
  `Fin n → Fin t → F`, for EVERY word family) and `tri_fiber_equinum` (any
  two triangular explaining fibers are carried onto each other by ONE
  translation from the joint mask space). Witness-freedom is again
  syntactic: `fs` universally quantified, absent from every right-hand side.
* **`triOpen_prefix_reach`** — THE induction. Round `m`'s draw is chosen by
  applying `MaskedOpeningHiding.sim_support_univ` AT the mask-dependent
  pre-mask word `triPre γs fs gs ⟨m,_⟩` — the word that contains the
  already-chosen `gs 0 … gs (m−1)`. This is exactly the application the
  ∀-WITNESS quantifier position of the landed field makes legal ("for EVERY
  witness `f`" — including one built from earlier mask draws); a
  fixed-witness hiding statement would not compose here. Earlier rounds are
  undisturbed because `triFold` at round `k` reads only `gs j`, `j ≤ k`
  (`triFold_congr`).
* **`triangularHiding_of_rounds`** — per-round hiding implies triangular
  joint hiding. Support is the induction at full depth. Fibers: the joint
  opening is AFFINE in the mask family — `triOpen q γs fs gs =
  triOpen q γs fs 0 + triOpen q γs 0 gs` (`triOpen_decomp`), a public
  word-part plus a lower-triangular LINEAR part `L := triOpen q γs 0` — so
  the translation between the fibers over `(fs₁,vs₁)` and `(fs₂,vs₂)` is ANY
  `cs ∈ jointMasks M` with `L cs` = the fiber-difference target, and such
  `cs` exists by the SUPPORT theorem applied at the ZERO word family. The
  triangular schedule broke the product FACTORING of the proof, not the
  THEOREM: joint fibers are cosets of one kernel, and the translation is
  BACK-SUBSTITUTED through the triangle instead of assembled coordinatewise.

**Honest consumption profile.** Only `sim_support_univ` is consumed — the
per-round `fiber_equinum` field is never used (the joint translation comes
from joint surjectivity, not from transporting per-round translations). And
NO transparency iff is claimed, in deliberate contrast to
`rbrZeroKnowledge_iff_rounds`: `TriangularHiding → ∀ k, MaskedOpeningHiding`
is not proved here (at a later round the per-round "witness" would have to
be reconstructed from a mask-dependent partial fold), so the composition is
stated one-directional, which is the direction deployment needs.

**Teeth — the γ-dial has TWO failure modes at depth, one of them new.**
Round 0 with a zero challenge publishes its word's opened symbols bare
(`not_triangularHiding_of_zero_first` — the product model's failure mode).
But a LATER round with a zero challenge fails differently: its opening
repeats the previous recommitted word — the earlier rounds' masks CANCEL in
the difference of successive openings, and the difference publishes the
round WORD's opened symbols (`triOpen_succ_zero_leak`, refutation
`not_triangularHiding_of_zero_succ`). Earlier masks do NOT save a maskless
later round; this leak-through-the-difference mode does not exist in the
product model, where round `k`'s opening never sees round `j < k` at all.

**Keystones** (F₅, the SAME instance as `RbrZkExample`: both rounds' masks
from `constrainedMaskSpace dom₅ 2 pt2`, opened at `qz`, base schedule
`(1,1)`): satisfiable — `triangularHiding_F5` fires by composition, and
`tri_reach_F5` COMPUTES the induction's choice at depth 2 (round 1's draw
`lineOf 4 2` picked at the mask-dependent partial fold, reaching the
all-zero tuple, membership included); teeth — `tri_dependence` computes that
round 1's opened symbols MOVE when only round 0's mask changes (own masks
equal) while `product_model_blind` computes that `jointOpen` cannot see the
difference — the fresh-mask product theorem `rbrZeroKnowledge_of_rounds`
does NOT apply to this opening map, and the triangular structure is real;
both zero-challenge refutation modes instantiated
(`not_tri_zero_round0_F5`, `not_tri_zero_round1_F5`, leaked value computed
`leak_value`). Residual `[ZK-RBR-triangular]` at the bottom: what remains is
the DEPLOYMENT BRIDGE (identify `triFold` with the mask-augmented
`foldWords`/`aggregate` chain word and DERIVE the opened-once schedule
invariant from the protocol object), plus `[ZK-RBR-interleave]`'s
extraction flank, untouched here and inherited unchanged.
-/
import Selvage.ZK
import Selvage.ZKHiding
import Selvage.RbrZeroKnowledge

namespace Minidregg.Selvage

variable {F : Type*} [Field F] {ι : Type*} {t n : ℕ}

/-! ## The triangular fold word

Round `k`'s recommitted word, as deployed: everything folded so far — the
first `k+1` rounds' words, the earlier rounds' masks at their challenges —
re-masked by round `k`'s own fresh draw at round `k`'s challenge. Defined in
closed form (sums over `j ≤ k` / `j < k`) so that the joint objects below
quantify over the SAME `Fin n`-indexed families as the landed product model;
the recursive fold structure is then a THEOREM (`triPre_bot`,
`triFold_succ`), not a definition swap. -/

/-- **The pre-mask word at round `k`**: the first `k+1` rounds' words plus
the EARLIER rounds' mask contributions — the word that round `k`'s fresh
draw is about to re-mask. Round `k`'s own mask does NOT occur (the `j < k`
filter); every earlier mask DOES. This is the mask-dependent "witness" the
backward induction feeds to `MaskedOpeningHiding.sim_support_univ`. -/
def triPre (γs : ℕ → F) (fs gs : Fin n → ι → F) (k : Fin n) : ι → F :=
  (∑ j ∈ Finset.univ.filter (fun j => j ≤ k), fs j)
    + ∑ j ∈ Finset.univ.filter (fun j => j < k), γs (j : ℕ) • gs j

/-- **The `k`-th recommitted partial fold**: the pre-mask word re-masked by
round `k`'s own draw at round `k`'s challenge — the landed `mask` operation,
nothing new. THIS is the word round `k` opens. -/
def triFold (γs : ℕ → F) (fs gs : Fin n → ι → F) (k : Fin n) : ι → F :=
  mask (triPre γs fs gs k) (γs (k : ℕ)) (gs k)

theorem triFold_def (γs : ℕ → F) (fs gs : Fin n → ι → F) (k : Fin n) :
    triFold γs fs gs k = mask (triPre γs fs gs k) (γs (k : ℕ)) (gs k) := rfl

/-- Round 0's pre-mask word is its own word alone — no earlier masks exist.
Base of the recursion exhibition. -/
theorem triPre_bot (γs : ℕ → F) (fs gs : Fin n → ι → F) {k : Fin n}
    (hk : (k : ℕ) = 0) : triPre γs fs gs k = fs k := by
  unfold triPre
  have h1 : Finset.univ.filter (fun j => j < k) = (∅ : Finset (Fin n)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, Fin.lt_def, hk]
    omega
  have h2 : Finset.univ.filter (fun j => j ≤ k) = {k} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Fin.le_def, hk, Fin.ext_iff]
    omega
  rw [h1, h2, Finset.sum_singleton, Finset.sum_empty, add_zero]

/-- The step of the recursion exhibition: round `k+1`'s pre-mask word IS the
previous RECOMMITTED word plus the new round's word — the `foldWords` step
shape, with the previous fold (mask included) carried whole. -/
theorem triPre_succ (γs : ℕ → F) (fs gs : Fin n → ι → F) (k : Fin n)
    (h : (k : ℕ) + 1 < n) :
    triPre γs fs gs ⟨(k : ℕ) + 1, h⟩
      = triFold γs fs gs k + fs ⟨(k : ℕ) + 1, h⟩ := by
  unfold triFold triPre
  rw [mask_apply]
  have h1 : Finset.univ.filter (fun j => j < (⟨(k : ℕ) + 1, h⟩ : Fin n))
      = Finset.univ.filter (fun j => j ≤ k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def,
      Fin.le_def]
    omega
  have h2 : Finset.univ.filter (fun j => j ≤ (⟨(k : ℕ) + 1, h⟩ : Fin n))
      = insert (⟨(k : ℕ) + 1, h⟩ : Fin n)
          (Finset.univ.filter (fun j => j ≤ k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Fin.le_def, Fin.ext_iff]
    omega
  have h3 : (⟨(k : ℕ) + 1, h⟩ : Fin n)
      ∉ Finset.univ.filter (fun j => j ≤ k) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  have h4 : Finset.univ.filter (fun j => j ≤ k)
      = insert k (Finset.univ.filter (fun j => j < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Fin.le_def, Fin.lt_def, Fin.ext_iff]
    omega
  have h5 : k ∉ Finset.univ.filter (fun j => j < k) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl k
  rw [h1, h2, Finset.sum_insert h3]
  simp only [h4, Finset.sum_insert h5]
  abel

/-- **The recursive fold word, exhibited**: each recommitted word is the
landed `mask` of (previous recommitted word + new round word), at the new
round's challenge, with the new round's fresh draw. The deployed
recommitment step, one theorem per round. -/
theorem triFold_succ (γs : ℕ → F) (fs gs : Fin n → ι → F) (k : Fin n)
    (h : (k : ℕ) + 1 < n) :
    triFold γs fs gs ⟨(k : ℕ) + 1, h⟩
      = mask (triFold γs fs gs k + fs ⟨(k : ℕ) + 1, h⟩) (γs ((k : ℕ) + 1))
          (gs ⟨(k : ℕ) + 1, h⟩) := by
  rw [triFold_def, triPre_succ γs fs gs k h]

/-- The pre-mask word reads STRICTLY earlier mask coordinates only — the
congruence that keeps already-chosen rounds undisturbed while the induction
extends the mask family. -/
theorem triPre_congr {γs : ℕ → F} {fs gs₁ gs₂ : Fin n → ι → F} {k : Fin n}
    (hg : ∀ j : Fin n, j < k → gs₁ j = gs₂ j) :
    triPre γs fs gs₁ k = triPre γs fs gs₂ k := by
  unfold triPre
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hg j (Finset.mem_filter.mp hj).2]

/-- The recommitted word at round `k` reads mask coordinates `j ≤ k` only —
the triangular reading pattern, made usable. -/
theorem triFold_congr {γs : ℕ → F} {fs gs₁ gs₂ : Fin n → ι → F} {k : Fin n}
    (hg : ∀ j : Fin n, j ≤ k → gs₁ j = gs₂ j) :
    triFold γs fs gs₁ k = triFold γs fs gs₂ k := by
  unfold triFold
  rw [triPre_congr fun j hj => hg j hj.le, hg k le_rfl]

/-- The recommitted word splits into a mask-free word part and a word-free
mask part — the affine structure the fiber argument runs on. -/
theorem triFold_decomp (γs : ℕ → F) (fs gs : Fin n → ι → F) (k : Fin n) :
    triFold γs fs gs k = triFold γs fs 0 k + triFold γs 0 gs k := by
  simp only [triFold, triPre, mask_apply, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, add_zero, zero_add]
  abel

/-- The mask part is ADDITIVE in the mask family — the lower-triangular
linear map `gs ↦ (∑_{j≤k} γs j • gs j)_k`, additivity form. -/
theorem triFold_zero_add (γs : ℕ → F) (gs cs : Fin n → ι → F) (k : Fin n) :
    triFold γs 0 (gs + cs) k = triFold γs 0 gs k + triFold γs 0 cs k := by
  simp only [triFold, triPre, mask_apply, Pi.add_apply, Pi.zero_apply,
    Finset.sum_const_zero, smul_add, Finset.sum_add_distrib, zero_add]
  abel

/-! ## The triangular joint opening and its fibers -/

/-- **The triangular joint opening**: what the verifier sees across all `n`
deployed rounds — round `k`'s `t` opened symbols OF THE `k`-TH RECOMMITTED
PARTIAL FOLD. Round `k` reads `gs 0 … gs k` (contrast `jointOpen`, where
round `k` reads `gs k` alone). Each recommitted word is opened at its own
round ONLY — the schedule invariant, true here by construction. -/
def triOpen (q : Fin n → Fin t → ι) (γs : ℕ → F) (fs gs : Fin n → ι → F) :
    Fin n → Fin t → F :=
  fun k => openSymbols (q k) (triFold γs fs gs k)

@[simp] theorem triOpen_apply (q : Fin n → Fin t → ι) (γs : ℕ → F)
    (fs gs : Fin n → ι → F) (k : Fin n) :
    triOpen q γs fs gs k = openSymbols (q k) (triFold γs fs gs k) := rfl

/-- The joint opening is affine in the mask family: a mask-free public word
part plus the lower-triangular linear part `triOpen q γs 0`. The fiber
translation below is built from this decomposition. -/
theorem triOpen_decomp (q : Fin n → Fin t → ι) (γs : ℕ → F)
    (fs gs : Fin n → ι → F) :
    triOpen q γs fs gs = triOpen q γs fs 0 + triOpen q γs 0 gs := by
  funext k
  simp only [triOpen, Pi.add_apply, triFold_decomp γs fs gs k, map_add]

/-- Additivity of the triangular linear part. -/
theorem triOpen_zero_add (q : Fin n → Fin t → ι) (γs : ℕ → F)
    (gs cs : Fin n → ι → F) :
    triOpen q γs 0 (gs + cs) = triOpen q γs 0 gs + triOpen q γs 0 cs := by
  funext k
  simp only [triOpen, Pi.add_apply, triFold_zero_add γs gs cs k, map_add]

/-- **The triangular explaining-mask fiber**: the mask families in the joint
mask space whose recommitted partial folds open to the tuple family `vs`.
Deliberately NOT presented as a product of per-round conditions — round
`k`'s opening equation reads `gs 0 … gs k`, and no product presentation
exists (`ZkTriangularExample.tri_dependence` computes the failure). -/
def triMaskFiber (M : Fin n → Submodule F (ι → F)) (q : Fin n → Fin t → ι)
    (γs : ℕ → F) (fs : Fin n → ι → F) (vs : Fin n → Fin t → F) :
    Set (Fin n → ι → F) :=
  {gs | gs ∈ jointMasks M ∧ triOpen q γs fs gs = vs}

@[simp] theorem mem_triMaskFiber {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F} {fs : Fin n → ι → F}
    {vs : Fin n → Fin t → F} {gs : Fin n → ι → F} :
    gs ∈ triMaskFiber M q γs fs vs
      ↔ gs ∈ jointMasks M ∧ triOpen q γs fs gs = vs := Iff.rfl

/-! ## `TriangularHiding` — the deployed analog of the chain simulator -/

/-- **Triangular joint hiding** — `RbrZeroKnowledge`'s chain fields for the
DEPLOYED opening schedule, where round `k` opens the `k`-th recommitted
partial fold:

* `tri_sim_support` — for EVERY word family, the joint opened tuples across
  all `n` triangular rounds are ALL of `Fin n → Fin t → F`: the simulator's
  support is the full public product space, witness-free.
* `tri_fiber_equinum` — any two triangular explaining fibers are carried
  onto each other by ONE explicit translation from the joint mask space:
  the joint distribution is uniform on that support, identically in the
  word family. Perfect, distribution-equality hiding of the whole deployed
  leakage surface.

Witness-freedom is syntactic (`fs` universally quantified, absent from
every right-hand side). NO transparency iff back to per-round hiding is
claimed — the composition below is one-directional, and that is the
direction deployment consumes. -/
structure TriangularHiding (M : Fin n → Submodule F (ι → F))
    (q : Fin n → Fin t → ι) (γs : ℕ → F) : Prop where
  tri_sim_support : ∀ fs : Fin n → ι → F,
    triOpen q γs fs '' jointMasks M = Set.univ
  tri_fiber_equinum : ∀ (fs₁ fs₂ : Fin n → ι → F)
    (vs₁ vs₂ : Fin n → Fin t → F), ∃ cs ∈ jointMasks M,
    Set.BijOn (· + cs) (triMaskFiber M q γs fs₁ vs₁)
      (triMaskFiber M q γs fs₂ vs₂)

/-- **The backward induction, made a theorem**: a mask family reaching any
prescribed opened tuples on the first `m` rounds exists in the joint mask
space. The step extends a family that handles rounds `< m` by choosing round
`m`'s draw through `MaskedOpeningHiding.sim_support_univ` applied AT THE
MASK-DEPENDENT PRE-MASK WORD `triPre γs fs gs ⟨m,_⟩` — the word containing
the already-chosen `gs 0 … gs (m−1)`. This application is legal precisely
because the landed field quantifies over EVERY witness word; earlier rounds
are undisturbed because round `k` reads only coordinates `j ≤ k`
(`triFold_congr`), so updating coordinate `m` changes nothing below it. -/
theorem triOpen_prefix_reach {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F}
    (H : ∀ k : Fin n, MaskedOpeningHiding (M k) (q k) (γs (k : ℕ)))
    (fs : Fin n → ι → F) (vs : Fin n → Fin t → F) :
    ∀ m : ℕ, m ≤ n → ∃ gs ∈ jointMasks M,
      ∀ k : Fin n, (k : ℕ) < m → triOpen q γs fs gs k = vs k := by
  intro m
  induction m with
  | zero =>
    exact fun _ => ⟨0, fun k => (M k).zero_mem,
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨gs, hgsM, hgs⟩ := ih (Nat.le_of_succ_le hm)
    have hmn : m < n := hm
    -- the ∀-witness application, at the mask-dependent partial fold
    have hv : vs ⟨m, hmn⟩ ∈ (fun r => openSymbols (q ⟨m, hmn⟩)
        (mask (triPre γs fs gs ⟨m, hmn⟩) (γs ((⟨m, hmn⟩ : Fin n) : ℕ)) r))
          '' (M ⟨m, hmn⟩) := by
      rw [(H ⟨m, hmn⟩).sim_support_univ (triPre γs fs gs ⟨m, hmn⟩)]
      trivial
    obtain ⟨r, hrM, hr⟩ := hv
    refine ⟨Function.update gs ⟨m, hmn⟩ r, fun k => ?_, fun k hk => ?_⟩
    · rcases eq_or_ne k ⟨m, hmn⟩ with hkm | hkm
      · rw [hkm, Function.update_self]
        exact hrM
      · rw [Function.update_of_ne hkm]
        exact hgsM k
    · rcases (Nat.lt_succ_iff.mp hk).lt_or_eq with hlt | heq
      · -- rounds below `m` never read the updated coordinate
        have hupd : ∀ j : Fin n, j ≤ k →
            Function.update gs ⟨m, hmn⟩ r j = gs j := by
          intro j hj
          refine Function.update_of_ne ?_ r gs
          intro he
          have hjm : (j : ℕ) = m := congrArg Fin.val he
          have hjk : (j : ℕ) ≤ (k : ℕ) := hj
          omega
        show openSymbols (q k)
            (triFold γs fs (Function.update gs ⟨m, hmn⟩ r) k) = vs k
        rw [triFold_congr hupd]
        exact hgs k hlt
      · -- round `m` itself: the freshly chosen draw fires
        have hkm : k = ⟨m, hmn⟩ := Fin.ext heq
        rw [hkm]
        have hupd : ∀ j : Fin n, j < (⟨m, hmn⟩ : Fin n) →
            Function.update gs ⟨m, hmn⟩ r j = gs j := by
          intro j hj
          refine Function.update_of_ne ?_ r gs
          intro he
          have hjm : (j : ℕ) = m := congrArg Fin.val he
          have hjk : (j : ℕ) < m := hj
          omega
        show openSymbols (q ⟨m, hmn⟩)
            (triFold γs fs (Function.update gs ⟨m, hmn⟩ r) ⟨m, hmn⟩)
          = vs ⟨m, hmn⟩
        rw [triFold_def, triPre_congr hupd, Function.update_self]
        exact hr

/-- **Triangular joint hiding from per-round hiding — the composition for
the DEPLOYED schedule.** Support is `triOpen_prefix_reach` at full depth.
Fibers: by `triOpen_decomp` the fiber over `(fsᵢ, vsᵢ)` is the solution set
of `L gs = vsᵢ − (word part)ᵢ` inside the joint mask space, `L` the
triangular linear part — so ONE `cs` with `L cs` equal to the difference of
the two targets (it exists: the SUPPORT theorem at the ZERO word family)
translates fiber onto fiber. Where the product model transported per-round
translations coordinatewise, the triangular translation is back-substituted
through the triangle — and only `sim_support_univ` is ever consumed. -/
theorem triangularHiding_of_rounds {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F}
    (H : ∀ k : Fin n, MaskedOpeningHiding (M k) (q k) (γs (k : ℕ))) :
    TriangularHiding M q γs where
  tri_sim_support fs := by
    refine Set.eq_univ_of_forall fun vs => ?_
    obtain ⟨gs, hgsM, hgs⟩ := triOpen_prefix_reach H fs vs n le_rfl
    exact ⟨gs, hgsM, funext fun k => hgs k k.isLt⟩
  tri_fiber_equinum fs₁ fs₂ vs₁ vs₂ := by
    obtain ⟨cs, hcsM, hcs⟩ := triOpen_prefix_reach H 0
      ((vs₂ - triOpen q γs fs₂ 0) - (vs₁ - triOpen q γs fs₁ 0)) n le_rfl
    have hcs' : triOpen q γs 0 cs
        = (vs₂ - triOpen q γs fs₂ 0) - (vs₁ - triOpen q γs fs₁ 0) :=
      funext fun k => hcs k k.isLt
    refine ⟨cs, hcsM, fun gs hgs => ?_,
      (add_left_injective cs).injOn, fun gs' hgs' => ?_⟩
    · obtain ⟨hgsM, hgsv⟩ := hgs
      refine ⟨fun k => (M k).add_mem (hgsM k) (hcsM k), ?_⟩
      have h1 : triOpen q γs 0 gs = vs₁ - triOpen q γs fs₁ 0 := by
        rw [triOpen_decomp] at hgsv
        exact eq_sub_of_add_eq' hgsv
      show triOpen q γs fs₂ (gs + cs) = vs₂
      rw [triOpen_decomp, triOpen_zero_add, h1, hcs']
      abel
    · obtain ⟨hgs'M, hgs'v⟩ := hgs'
      refine ⟨gs' - cs,
        ⟨fun k => (M k).sub_mem (hgs'M k) (hcsM k), ?_⟩,
        sub_add_cancel gs' cs⟩
      have h2 : triOpen q γs 0 gs' = vs₂ - triOpen q γs fs₂ 0 := by
        rw [triOpen_decomp] at hgs'v
        exact eq_sub_of_add_eq' hgs'v
      have hLsub : triOpen q γs 0 (gs' - cs)
          = triOpen q γs 0 gs' - triOpen q γs 0 cs := by
        have h3 := triOpen_zero_add q γs (gs' - cs) cs
        rw [sub_add_cancel] at h3
        exact eq_sub_of_add_eq h3.symm
      show triOpen q γs fs₁ (gs' - cs) = vs₁
      rw [triOpen_decomp, hLsub, h2, hcs']
      abel

/-- **Witness independence of the deployed schedule**: two provers holding
different word families produce identical joint opened-tuple supports across
all `n` triangular rounds — the distinguisher watching every recommitted
word's spot check learns nothing. `RbrZeroKnowledge.chain_witness_free`, at
the deployed opening map. -/
theorem TriangularHiding.tri_witness_free {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F} (H : TriangularHiding M q γs)
    (fs₁ fs₂ : Fin n → ι → F) :
    triOpen q γs fs₁ '' jointMasks M = triOpen q γs fs₂ '' jointMasks M := by
  rw [H.tri_sim_support fs₁, H.tri_sim_support fs₂]

/-- The counting corollary: every triangular explaining fiber has the same
size — `Pr[joint opened = vs]` is ONE constant across word families and
tuple families, for the deployed schedule. -/
theorem TriangularHiding.triMaskFiber_ncard_eq
    {M : Fin n → Submodule F (ι → F)} {q : Fin n → Fin t → ι} {γs : ℕ → F}
    (H : TriangularHiding M q γs) (fs₁ fs₂ : Fin n → ι → F)
    (vs₁ vs₂ : Fin n → Fin t → F) :
    (triMaskFiber M q γs fs₁ vs₁).ncard
      = (triMaskFiber M q γs fs₂ vs₂).ncard := by
  obtain ⟨cs, -, hbij⟩ := H.tri_fiber_equinum fs₁ fs₂ vs₁ vs₂
  rw [← hbij.image_eq, Set.ncard_image_of_injective _ (add_left_injective cs)]

/-! ## Teeth: the γ-dial has two failure modes at depth -/

/-- **Teeth, mode 1 — round 0 bare**: a zero challenge at round 0 publishes
round 0's word unmasked (its pre-mask word contains NO earlier masks to hide
behind), refuting triangular hiding outright. The product model's failure
mode, surviving the schedule change. -/
theorem not_triangularHiding_of_zero_first {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F} (hn : 0 < n) (h0 : γs 0 = 0)
    (ht : 0 < t) : ¬ TriangularHiding M q γs := by
  intro H
  have h := H.tri_sim_support 0
  have h1 : (fun _ _ => (1 : F)) ∈ triOpen q γs 0 '' jointMasks M := by
    rw [h]; trivial
  obtain ⟨gs, -, hgs⟩ := h1
  have hw : triFold γs 0 gs ⟨0, hn⟩ = 0 := by
    rw [triFold_def, triPre_bot γs 0 gs (k := ⟨0, hn⟩) rfl]
    show mask ((0 : Fin n → ι → F) ⟨0, hn⟩) (γs 0) (gs ⟨0, hn⟩) = 0
    rw [mask_apply, h0, zero_smul, add_zero, Pi.zero_apply]
  have h2 : openSymbols (q ⟨0, hn⟩) (triFold γs 0 gs ⟨0, hn⟩) ⟨0, ht⟩
      = (1 : F) := congrFun (congrFun hgs ⟨0, hn⟩) ⟨0, ht⟩
  rw [hw, map_zero] at h2
  exact zero_ne_one h2

/-- **The difference leak**: a zero challenge at a LATER round `k+1` makes
that round's opening repeat the previous recommitted word (plus the new
round's word) — every earlier mask contribution appears in BOTH successive
openings and CANCELS in their difference, which therefore publishes the
round-`(k+1)` WORD's opened symbols. Earlier masks do not save a maskless
later round. (Stated at a shared query selection so the two openings are
comparable coordinatewise.) -/
theorem triOpen_succ_zero_leak {q : Fin n → Fin t → ι} {γs : ℕ → F}
    (fs gs : Fin n → ι → F) (k : Fin n) (h : (k : ℕ) + 1 < n)
    (h0 : γs ((k : ℕ) + 1) = 0) (hq : q ⟨(k : ℕ) + 1, h⟩ = q k) :
    triOpen q γs fs gs ⟨(k : ℕ) + 1, h⟩
      = triOpen q γs fs gs k + openSymbols (q k) (fs ⟨(k : ℕ) + 1, h⟩) := by
  show openSymbols (q ⟨(k : ℕ) + 1, h⟩) (triFold γs fs gs ⟨(k : ℕ) + 1, h⟩)
    = _
  rw [triFold_succ γs fs gs k h, hq, h0, mask_apply, zero_smul, add_zero,
    map_add]
  rfl

/-- **Teeth, mode 2 — the new failure mode, refutation form**: one zero
challenge at a later round refutes triangular hiding — through the
difference relation, not through a bare coordinate. This leak mode does not
exist in the product model, where round `k+1`'s opening never contains
round `j ≤ k`'s masks in the first place. -/
theorem not_triangularHiding_of_zero_succ {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F} (k : Fin n)
    (h : (k : ℕ) + 1 < n) (h0 : γs ((k : ℕ) + 1) = 0)
    (hq : q ⟨(k : ℕ) + 1, h⟩ = q k) (ht : 0 < t) :
    ¬ TriangularHiding M q γs := by
  intro H
  have hs := H.tri_sim_support 0
  have hkne : k ≠ (⟨(k : ℕ) + 1, h⟩ : Fin n) := by
    intro he
    have hv : (k : ℕ) = (k : ℕ) + 1 := congrArg Fin.val he
    omega
  have h1 : (fun j => if j = (⟨(k : ℕ) + 1, h⟩ : Fin n)
        then (fun _ => 1) else 0 : Fin n → Fin t → F)
      ∈ triOpen q γs 0 '' jointMasks M := by
    rw [hs]; trivial
  obtain ⟨gs, -, hgs⟩ := h1
  have hleak := triOpen_succ_zero_leak (0 : Fin n → ι → F) gs k h h0 hq
  have e1 := congrFun hgs ⟨(k : ℕ) + 1, h⟩
  rw [if_pos rfl] at e1
  have e2 := congrFun hgs k
  rw [if_neg hkne] at e2
  rw [e1, e2] at hleak
  have hcontra := congrFun hleak ⟨0, ht⟩
  simp at hcontra

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Over `RS[F₅, {0,1,2,3}, 2]`, the SAME instance as `RbrZkExample`: two
rounds, both masks drawn from the landed `constrainedMaskSpace dom₅ 2 pt2`,
one symbol opened at `qz = 0`, base schedule `γbase = (1,1)`, honest word
family `(xWord, oneWord)` — but now round 1 opens the RECOMMITTED PARTIAL
FOLD, which contains round 0's mask. -/

namespace ZkTriangularExample

open RSExample AccExample ZkHidingExample ZkArgumentExample
  AccExtractChainExample RbrZkExample

/-- **THE INSTANCE — satisfiable / premise inhabitation**: triangular joint
hiding FIRES on the deployed 2-round schedule, by composition
(`triangularHiding_of_rounds` over the landed `hiding_rounds` — the same
per-round facts that fired the product model, now consumed through their
∀-witness quantifier at mask-dependent partial folds). -/
theorem triangularHiding_F5 :
    TriangularHiding roundMask roundQuery γbase :=
  triangularHiding_of_rounds hiding_rounds

/-- The chain simulator fired at the deployed opening map: for the honest
word family, the joint opened tuples of the two RECOMMITTED words reach the
full product space. -/
theorem tri_support_fired :
    triOpen roundQuery γbase ![xWord, oneWord] '' jointMasks roundMask
      = Set.univ :=
  triangularHiding_F5.tri_sim_support ![xWord, oneWord]

/-- A mask family with a NONZERO round-0 mask (the landed `lineOf 2 1`) and
zero round-1 mask... -/
def gsDep : Fin 2 → Fin 4 → ZMod 5 := ![lineOf 2 1, 0]

/-- ...and the all-zero mask family — SAME round-1 coordinate as `gsDep`. -/
def gsFree : Fin 2 → Fin 4 → ZMod 5 := ![0, 0]

theorem gsDep_mem : gsDep ∈ jointMasks roundMask := by
  intro k
  fin_cases k
  · exact maskWord_mem
  · exact Submodule.zero_mem _

theorem gsFree_mem : gsFree ∈ jointMasks roundMask := by
  intro k
  fin_cases k <;> exact Submodule.zero_mem _

/-- The two families agree on round 1's OWN mask draw. -/
theorem same_own_mask : gsDep 1 = gsFree 1 := by decide

/-- **Round 1 opens a word CONTAINING round 0's mask, computed**: with
`gsDep`, the recommitted word round 1 opens is
`xWord + lineOf 2 1 + oneWord = (3,3,3,3)` — the constant-3 word, visibly
shifted by the round-0 mask... -/
theorem triPre_computed :
    triPre γbase ![xWord, oneWord] gsDep 1 = ![3, 3, 3, 3] := by decide

/-- ...and it genuinely MOVES with round 0's mask: the mask-free partial
fold is a different word. -/
theorem triPre_moves_with_mask :
    triPre γbase ![xWord, oneWord] gsDep 1
      ≠ triPre γbase ![xWord, oneWord] gsFree 1 := by decide

/-- **Teeth — the triangular structure is real**: round 1's OPENED SYMBOLS
move when only round 0's mask changes (round 1's own draw held fixed,
`same_own_mask`). Round 1's opening is NOT a function of `gs 1` alone, so
the fresh-mask product theorem (`rbrZeroKnowledge_of_rounds`, whose joint
fiber conditions each read one coordinate) does NOT apply to this opening
map. -/
theorem tri_dependence :
    triOpen roundQuery γbase ![xWord, oneWord] gsDep 1
      ≠ triOpen roundQuery γbase ![xWord, oneWord] gsFree 1 := by
  show openSymbols (roundQuery 1) (triFold γbase ![xWord, oneWord] gsDep 1)
    ≠ openSymbols (roundQuery 1) (triFold γbase ![xWord, oneWord] gsFree 1)
  rw [openSymbols_eq_comp, openSymbols_eq_comp]
  decide

/-- **The product model is blind to the same change**: `jointOpen`'s round 1
reads `gs 1` alone, so the two families' product-model openings COINCIDE at
round 1. `tri_dependence` + `product_model_blind` is the precise sense in
which the deployed schedule left the product model. -/
theorem product_model_blind :
    jointOpen roundQuery γbase ![xWord, oneWord] gsDep 1
      = jointOpen roundQuery γbase ![xWord, oneWord] gsFree 1 := by
  rw [jointOpen_apply, jointOpen_apply, same_own_mask]

/-- The round-1 mask the induction's step picks at the MASK-DEPENDENT
partial fold below: the line `4 + 3X`, vanishing at `pt2` — a genuine
element of the landed constrained mask space. -/
theorem lineOf42_mem : lineOf 4 2 ∈ constrainedMaskSpace dom₅ 2 pt2 := by
  rw [mem_constrainedMaskSpace]
  exact ⟨lineOf_mem 4 2, by decide⟩

theorem reach_mem :
    ![(0 : Fin 4 → ZMod 5), lineOf 4 2] ∈ jointMasks roundMask := by
  intro k
  fin_cases k
  · exact Submodule.zero_mem _
  · exact lineOf42_mem

/-- **The backward induction's choice, computed at depth 2**: the mask
family `(0, lineOf 4 2)` — round 1's draw chosen AT the partial fold
`xWord + 0 + oneWord` — drives the deployed openings to the all-zero joint
tuple. The ∀-witness application of `triOpen_prefix_reach`, instantiated
and evaluated. -/
theorem tri_reach_F5 :
    triOpen roundQuery γbase ![xWord, oneWord] ![0, lineOf 4 2]
      = ![![0], ![0]] := by
  funext k
  fin_cases k
  · show openSymbols (roundQuery 0)
        (triFold γbase ![xWord, oneWord] ![0, lineOf 4 2] 0) = _
    rw [openSymbols_eq_comp]
    decide
  · show openSymbols (roundQuery 1)
        (triFold γbase ![xWord, oneWord] ![0, lineOf 4 2] 1) = _
    rw [openSymbols_eq_comp]
    decide

/-- **Teeth mode 1, instantiated**: the zero-round-0 schedule (the landed
`γzeroSched = (0,1)`) refutes triangular hiding — round 0 is published
bare. -/
theorem not_tri_zero_round0_F5 :
    ¬ TriangularHiding roundMask roundQuery γzeroSched :=
  not_triangularHiding_of_zero_first (by norm_num) (by decide) (by norm_num)

/-- The schedule whose ROUND-1 challenge is zero — round 0 is properly
masked. -/
def γlateZero : ℕ → ZMod 5 := padSched ![1, 0]

/-- **Teeth mode 2, instantiated**: with round 0 properly masked, a zero
challenge at round 1 STILL refutes triangular hiding — round 0's mask
appears in both openings and cancels in their difference. The new,
triangular-only failure mode, live on F₅. -/
theorem not_tri_zero_round1_F5 :
    ¬ TriangularHiding roundMask roundQuery γlateZero :=
  not_triangularHiding_of_zero_succ 0 (by decide) (by decide) rfl
    (by norm_num)

/-- The leak relation on the F₅ instance, for EVERY mask family: at
`γlateZero` the two successive opened symbols differ by exactly round 1's
WORD symbol — the mask contributions cancel. -/
theorem leak_computed (gs : Fin 2 → Fin 4 → ZMod 5) :
    triOpen roundQuery γlateZero ![xWord, oneWord] gs 1
      = triOpen roundQuery γlateZero ![xWord, oneWord] gs 0
        + openSymbols qz oneWord := by
  have h := triOpen_succ_zero_leak (q := roundQuery) (γs := γlateZero)
    ![xWord, oneWord] gs (0 : Fin 2) (by decide) (by decide) rfl
  exact h

/-- The leaked value, computed: the difference publishes `oneWord`'s opened
symbol `1` — witness-dependent data, readable by any observer of the two
openings. -/
theorem leak_value : openSymbols qz oneWord = ![1] := by
  rw [openSymbols_eq_comp]
  decide

end ZkTriangularExample

/-! ## Residual obligation — prose, not a stub

**`[ZK-RBR-triangular]`** — the sharpened remainder of
`[ZK-RBR-interleave]`'s missing lemma 1, after this file. The lemma's
MATHEMATICS is now closed: for the abstract triangular schedule — round `k`
opens the `k`-th recommitted partial fold, once — per-round
`MaskedOpeningHiding` composes into joint hiding of the whole deployed
leakage surface (`triangularHiding_of_rounds`), by the backward induction
the residual predicted, through exactly the ∀-witness quantifier it named.
What remains is the BRIDGE from this model to the deployed chain object,
and it is one named lemma plus one named invariant:

* **The deployment bridge.** Define the mask-AUGMENTED chain — each round's
  mask claim folded as its own link into `Selvage/LightClient.lean`'s
  `foldWords`/`aggregate` recursion (the fold step `f + γs 0 • w`,
  `foldWords_cons`) — and prove that its per-round recommitted word IS
  `triFold γs fs gs k`, where `fs k` absorbs the real links' fold weights.
  The absorption is a WLOG at the hiding statement (every field here
  quantifies over ALL `fs`), but the bridge equation itself is a real lemma
  about `foldWords`, not a quantifier remark; `triFold_succ` is its
  step-shape on this side. With the bridge, `TriangularHiding` transports
  verbatim to the deployed object.
* **The schedule invariant, derived not assumed.** `triOpen` opens round
  `k`'s recommitted word at round `k` ONLY — `Selvage/ZKHiding.lean`'s
  multi-step residual named this ("each committed word is opened at ONE
  step only", WARP's recommitment schedule) and this file CONSUMES it by
  construction. The bridge must derive it from the protocol's opening
  schedule: if some committed word were opened at two rounds, the joint
  opening map would repeat a row and `tri_sim_support` would be FALSE for
  it (the two coordinates would be correlated — the `γ = 0` teeth
  `not_triangularHiding_of_zero_succ` is exactly the degenerate case where
  round `k+1`'s opening IS a repeat of round `k`'s word). The invariant is
  load-bearing, not decorative.
* **What is NOT here and was not claimed.** The converse transparency
  (`TriangularHiding → ∀ k, MaskedOpeningHiding`) is unproved — the
  composition is one-directional. And `[ZK-RBR-interleave]`'s missing
  lemma 2 — masked-chain EXTRACTION through the `[ACC-extract-bind]`
  opened-column seam, the extractor and simulator consuming the same `t·n`
  symbols — is untouched by this file and inherited unchanged, along with
  the game packaging owed to `[ACC-sound-rbr-game]`.

## Ledger

* `triPre` / `triFold` (+ `triFold_def`, `triPre_bot`, `triPre_succ`,
  `triFold_succ`, `triPre_congr`, `triFold_congr`, `triFold_decomp`,
  `triFold_zero_add`) — DEFINED/PROVED: the recommitted partial fold as a
  recursive fold word (recursion exhibited as theorems), reading only
  coordinates `≤ k`, affine in the mask family.
* `triOpen` / `triMaskFiber` (+ `triOpen_decomp`, `triOpen_zero_add`,
  `mem_triMaskFiber`) — DEFINED: the deployed triangular leakage surface
  and its explaining fibers; the opening map's affine decomposition.
* `TriangularHiding` — DEFINED: the deployed analog of the chain simulator
  fields, witness-free by quantifier position; NO transparency iff claimed.
* `triOpen_prefix_reach` — PROVED: the backward induction; round `m`'s draw
  chosen by `sim_support_univ` AT the mask-dependent partial fold.
* `triangularHiding_of_rounds` — PROVED: per-round hiding ⇒ triangular
  joint hiding, BOTH fields; fibers via the back-substituted translation
  from the support theorem at the zero family. Only `sim_support_univ`
  consumed.
* `TriangularHiding.tri_witness_free` / `.triMaskFiber_ncard_eq` — PROVED:
  whole-schedule witness independence + the one-constant joint
  distribution, at the deployed opening map.
* `not_triangularHiding_of_zero_first` / `triOpen_succ_zero_leak` /
  `not_triangularHiding_of_zero_succ` — PROVED: both γ-dial failure modes,
  including the triangular-only difference leak (earlier masks cancel).
* Keystones — `triangularHiding_F5` + `tri_support_fired` (fired);
  `tri_reach_F5` + `reach_mem` (the induction's choice computed at the
  mask-dependent partial fold); `triPre_computed` /
  `triPre_moves_with_mask` / `tri_dependence` vs `product_model_blind`
  (round 1's opened word and symbols genuinely depend on round 0's mask;
  the product model cannot see it); `not_tri_zero_round0_F5` /
  `not_tri_zero_round1_F5` / `leak_computed` / `leak_value` (both failure
  modes live on F₅, the leaked witness symbol computed).
* Residual — `[ZK-RBR-triangular]` (prose above): the deployment bridge +
  the derived schedule invariant; interleave's extraction flank inherited
  unchanged.

`#print axioms` on `triangularHiding_of_rounds`, `triOpen_prefix_reach`,
`not_triangularHiding_of_zero_first`, `not_triangularHiding_of_zero_succ`,
`ZkTriangularExample.triangularHiding_F5`,
`ZkTriangularExample.tri_reach_F5`, `ZkTriangularExample.tri_dependence`,
`ZkTriangularExample.not_tri_zero_round1_F5`: `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
