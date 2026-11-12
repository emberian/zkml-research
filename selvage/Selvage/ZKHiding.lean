/-
# Selvage.ZKHiding — advancing [OB-4-hiding]: the opening-leakage layer's
provable core — MDS t-wise independence and masked-opening hiding.

`Selvage/ZK.lean` proved the folded-WORD hiding shell and confined the genuinely
open mathematics to its prose residual `[OB-4-hiding]`: the `t` spot-check
symbols the verifier opens per accumulation step are honest codeword
coordinates, and nothing in the word-level shell says they do not leak the
witness. This file advances THAT residual by building its provable core and
narrowing what remains to a sharper, named research edge.

**The route** (the portable idea, re-proved on our substrate — none of
2026/289's rewinding): augment the opening with a uniformly random MASK
codeword `r` and open the fold `f + γ • r` (literally `mask f γ r`, the
landed shell's map — the mask enters BY the fold, at the challenge). The `t`
opened symbols of the masked word are then EXACTLY uniform on `Fin t → F`,
because any `t ≤ d` symbols of a uniformly random RS codeword are jointly
uniform. That t-wise independence is the Reed–Solomon MDS property — the
interpolation/Vandermonde bijection between degree-`< d` polynomials and
their values on `d` distinct points — and it is genuinely PROVABLE. It is
proved here, in the same exact-counting idiom as the shell (bijections and
`∃!`, no probability scaffolding):

* **The MDS interpolation core.** `exists_codeword_open` (any `t ≤ d` symbol
  values are hit by a codeword — Lagrange interpolation),
  `open_determines` (`d` opened symbols determine the codeword — root
  counting via `card_agreeSet_lt_of_ne`), `exists_unique_codeword_open` /
  `open_bijOn` (at `t = d` the opening map is a BIJECTION code ≃ tuples:
  every tuple explained by exactly one codeword).
* **t-wise uniformity, exact counting form** — `t_symbols_uniform`: for
  `t ≤ d`, every opened tuple is reachable AND any two fibers of the opening
  map over the code are carried onto each other by an explicit codeword
  translation (`openFiber_translate`). Pushforward reading: a uniformly
  random codeword's `t` opened symbols are uniform on ALL of `Fin t → F`
  (`openFiber_ncard_eq` is the counting corollary).
* **`MaskedOpeningHiding`** — the opening-hiding property, keystone fields
  real: `sim_support_univ` (for EVERY witness the reachable opened tuples
  are ALL of `Fin t → F` — the simulator's support is public and
  witness-free) and `fiber_equinum` (explaining-mask fibers for any two
  witnesses and any two tuples are in explicit bijection — the opened
  distribution is uniform, independent of witness and tuple: perfect,
  distribution-equality hiding). PROVED for RS at every `t ≤ d`, `γ ≠ 0`
  (`rs_maskedOpeningHiding`), through the reduction theorem
  `maskedOpeningHiding_of_surj`: hiding follows from surjectivity of the
  opening map on the mask space — the exact interface a future
  CONSTRAINED-mask design must re-supply.
* **Soundness-coexistence hook** — `mask_mem`: the masked word stays in the
  code, so masking does not disturb the low-degree/proximity test. (What it
  does to the RBR soundness game is `[OB-4-hiding-rbr]` below.)
* **Teeth, both dials.** γ-dial: at `γ = 0` the opened support collapses to
  the witness's OWN symbols (`image_openMask_zero`) and the property is
  refuted (`not_maskedOpeningHiding_zero`). t-dial: at `t = d + 1` the extra
  symbol is DETERMINED by the others — the parity check — and the property
  is refuted at EVERY γ (`not_maskedOpeningHiding_of_gt`); over F₅ the
  parity relation is computed explicitly (`parity_F5`: `f 2 = 2·f 1 − f 0`
  for every codeword) with an unreachable tuple exhibited
  (`not_open_001_F5`). Sharp iff on the F₅ instance:
  `maskedOpeningHiding_F5_iff` — hiding holds IFF `γ ≠ 0`, at the mask
  bound `t ≤ d`; one query too many kills it at every challenge.

**Honest scope — what this file does NOT prove.** The mask here ranges over
the WHOLE code. In the protocol the mask word must ALSO satisfy the mask
claim's constraint channel (the shell's `satWords C B` — `mask_bijOn`
consumes a satisfying mask), so the mask space is an affine subspace of the
code, and opening-hiding for THAT mask needs surjectivity of the opening map
on the associated homogeneous space — which costs constraint budget
(realizer: `t + r ≤ d` for `r` evaluation constraints, by
vanishing-polynomial factorization; dual-distance bounds for general linear
channels). That, the JOINT word+opening simulator sharing one mask draw with
`mask_bijOn`, the multi-step leakage schedule, and the RBR re-proof are
`[OB-4-hiding-rbr]` — prose at the bottom, the remaining research edge.
No `sorry`, no vacuous `Prop := True`.
-/
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Lagrange
import Selvage.Accumulator
import Selvage.ZK

namespace Minidregg.Selvage

variable {F : Type*} [Field F] {ι : Type*} {t d : ℕ}

/-! ## The opening map

The verifier's spot check reads `t` coordinates of the committed word: the
map `f ↦ f ∘ q` for a query selection `q : Fin t → ι` — linear in the word
(`LinearMap.funLeft`), which is all the fiber algebra below uses. -/

/-- **The opening map**: the `t` spot-checked symbols of a word — coordinates
`q 0, …, q (t−1)`, as a linear map in the word. -/
def openSymbols (q : Fin t → ι) : (ι → F) →ₗ[F] (Fin t → F) :=
  LinearMap.funLeft F F q

@[simp] theorem openSymbols_apply (q : Fin t → ι) (f : ι → F) (j : Fin t) :
    openSymbols q f j = f (q j) := rfl

theorem openSymbols_eq_comp (q : Fin t → ι) (f : ι → F) :
    openSymbols q f = f ∘ q := rfl

/-- Openings commute with the fold's word operation: the opened symbols of
the masked word `mask f γ r = f + γ • r` are the γ-fold of the opened
symbols. This is the hinge `[OB-4-hiding-rbr]`'s round-by-round re-proof
will run on — the leakage surface respects the fold algebra. -/
theorem openSymbols_mask (q : Fin t → ι) (f : ι → F) (γ : F) (g : ι → F) :
    openSymbols q (mask f γ g) = openSymbols q f + γ • openSymbols q g := by
  rw [mask_apply, map_add, map_smul]

/-- The masked word stays in the code — the mask is a codeword, so opening
`f + γ • r` never disturbs the low-degree/proximity test. The
soundness-coexistence hook: hiding and the spot check live on the SAME
committed object. -/
theorem mask_mem {C : Submodule F (ι → F)} {f g : ι → F} (γ : F)
    (hf : f ∈ C) (hg : g ∈ C) : mask f γ g ∈ C :=
  C.add_mem hf (C.smul_mem γ hg)

/-! ## The MDS interpolation core

The load-bearing mathematics: for `t ≤ d` distinct evaluation points, the
opening map on `RS[F, dom, d]` is surjective (Lagrange interpolation), and
for `d ≤ t` it is injective (a degree-`< d` polynomial is determined by `d`
values — root counting). At `t = d` both: the Vandermonde/interpolation
BIJECTION between codewords and symbol tuples. -/

/-- **Surjectivity at `t ≤ d`** (Lagrange): any `t` symbol values at distinct
points are the opening of some codeword — interpolate a degree-`< t ≤ d`
polynomial through them. -/
theorem exists_codeword_open (dom : ι ↪ F) (ht : t ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) (v : Fin t → F) :
    ∃ f ∈ reedSolomonCode dom d, openSymbols q f = v := by
  classical
  refine ⟨evalOnDomain dom (Lagrange.interpolate Finset.univ (dom ∘ q) v),
    mem_reedSolomonCode_iff.mpr ⟨_, ?_, fun i => rfl⟩, funext fun j => ?_⟩
  · have hdeg := Lagrange.degree_interpolate_lt (s := Finset.univ)
      (v := dom ∘ q) v hq.injOn
    rw [Finset.card_univ, Fintype.card_fin] at hdeg
    exact lt_of_lt_of_le hdeg (by exact_mod_cast ht)
  · exact Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := dom ∘ q) v
      hq.injOn (Finset.mem_univ j)

/-- **Injectivity at `d ≤ t`** (root counting): `d` opened symbols DETERMINE
the codeword — two codewords agreeing on `d` distinct points are equal, their
difference polynomial having more roots than its degree admits
(`card_agreeSet_lt_of_ne` run at the query points). This is also the general
form of the `t = d + 1` teeth: any symbol beyond the `d`-th is a FUNCTION of
the others. -/
theorem open_determines (dom : ι ↪ F) (hd : d ≤ t)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q))
    {f g : ι → F} (hf : f ∈ reedSolomonCode dom d) (hg : g ∈ reedSolomonCode dom d)
    (h : openSymbols q f = openSymbols q g) : f = g := by
  classical
  obtain ⟨p, hp, hpf⟩ := mem_reedSolomonCode_iff.mp hf
  obtain ⟨p', hp', hpg⟩ := mem_reedSolomonCode_iff.mp hg
  suffices hpp : p = p' by
    funext i; rw [hpf i, hpg i, hpp]
  by_contra hne
  have hlt := card_agreeSet_lt_of_ne (⟨dom ∘ q, hq⟩ : Fin t ↪ F) hp hp' hne
  refine absurd hlt (not_lt.mpr ?_)
  calc d ≤ t := hd
    _ = (Finset.univ : Finset (Fin t)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := Finset.card_le_card fun j _ => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,
          ((hpf (q j)).symm.trans (congrFun h j)).trans (hpg (q j))⟩

/-- **The interpolation bijection, `∃!` form** (the MDS core at `t = d`):
every `d`-tuple of symbol values is the opening of EXACTLY ONE codeword.
This is the Vandermonde invertibility on distinct points, and the whole
uniformity story rests on it. -/
theorem exists_unique_codeword_open (dom : ι ↪ F)
    {q : Fin d → ι} (hq : Function.Injective (dom ∘ q)) (v : Fin d → F) :
    ∃! f, f ∈ reedSolomonCode dom d ∧ openSymbols q f = v := by
  obtain ⟨f, hf, hfv⟩ := exists_codeword_open dom le_rfl hq v
  exact ⟨f, ⟨hf, hfv⟩, fun g ⟨hg, hgv⟩ =>
    open_determines dom le_rfl hq hg hf (hgv.trans hfv.symm)⟩

/-- The bijection packaged: at `t = d` the opening map carries the code
bijectively onto ALL tuples — `RS[F, dom, d] ≃ (Fin d → F)` along openings. -/
theorem open_bijOn (dom : ι ↪ F)
    {q : Fin d → ι} (hq : Function.Injective (dom ∘ q)) :
    Set.BijOn (openSymbols q) (reedSolomonCode dom d : Set (ι → F)) Set.univ := by
  refine ⟨fun f _ => Set.mem_univ _,
    fun f hf g hg h => open_determines dom le_rfl hq hf hg h, fun v _ => ?_⟩
  obtain ⟨f, hf, hfv⟩ := exists_codeword_open dom le_rfl hq v
  exact ⟨f, hf, hfv⟩

/-! ## Fibers of the opening map: t-wise uniformity in exact counting form -/

/-- The fiber of the opening map over a submodule: the words of `C` opening
to the tuple `v`. For a uniformly random word of `C`, `Pr[opened = v]` is
this fiber's share of `C` — fiber equinumerosity IS uniformity. -/
def openFiber (C : Submodule F (ι → F)) (q : Fin t → ι) (v : Fin t → F) :
    Set (ι → F) :=
  {f | f ∈ C ∧ openSymbols q f = v}

@[simp] theorem mem_openFiber {C : Submodule F (ι → F)} {q : Fin t → ι}
    {v : Fin t → F} {f : ι → F} :
    f ∈ openFiber C q v ↔ f ∈ C ∧ openSymbols q f = v := Iff.rfl

/-- **Fiber translation** — the linear-algebra heart of uniformity: adding a
codeword `c` carries the fiber over `v` bijectively onto the fiber over
`v + openSymbols q c`. No hypotheses on `t`, `d`, or the code: fibers of a
linear map restricted to a submodule are translates of each other whenever a
translating element exists. -/
theorem openFiber_translate {C : Submodule F (ι → F)} (q : Fin t → ι)
    {c : ι → F} (hc : c ∈ C) (v : Fin t → F) :
    Set.BijOn (· + c) (openFiber C q v) (openFiber C q (v + openSymbols q c)) := by
  refine ⟨fun f hf => ⟨C.add_mem hf.1 hc, by rw [map_add, hf.2]⟩,
    (add_left_injective c).injOn, fun g hg => ?_⟩
  refine ⟨g - c, ⟨C.sub_mem hg.1 hc, ?_⟩, sub_add_cancel g c⟩
  rw [map_sub, hg.2]
  abel

/-- **MDS t-wise independence** — the core theorem: for `t ≤ d` distinct
evaluation points, (1) EVERY `t`-tuple of symbols is opened by some codeword,
and (2) any two fibers of the opening map over the code are in explicit
bijection (a codeword translation). Distribution reading: the `t` opened
symbols of a uniformly random RS codeword are JOINTLY UNIFORM on all of
`Fin t → F` — full support by (1), equal weights by (2) — with no
probability scaffolding needed to say so. This is the property the mask
codeword contributes to the opening, and the bound `t ≤ d` is load-bearing
(the teeth below break it at `t = d + 1`). -/
theorem t_symbols_uniform (dom : ι ↪ F) (ht : t ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) :
    (∀ v : Fin t → F, (openFiber (reedSolomonCode dom d) q v).Nonempty) ∧
      ∀ v₁ v₂ : Fin t → F, ∃ c ∈ reedSolomonCode dom d,
        Set.BijOn (· + c) (openFiber (reedSolomonCode dom d) q v₁)
          (openFiber (reedSolomonCode dom d) q v₂) := by
  constructor
  · intro v
    obtain ⟨f, hf, hfv⟩ := exists_codeword_open dom ht hq v
    exact ⟨f, hf, hfv⟩
  · intro v₁ v₂
    obtain ⟨c, hc, hcv⟩ := exists_codeword_open dom ht hq (v₂ - v₁)
    refine ⟨c, hc, ?_⟩
    have h := openFiber_translate (C := reedSolomonCode dom d) q hc v₁
    rwa [hcv, add_sub_cancel] at h

/-- The counting corollary: all opening fibers over the code have the same
size — the uniform denominator. -/
theorem openFiber_ncard_eq (dom : ι ↪ F) (ht : t ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) (v₁ v₂ : Fin t → F) :
    (openFiber (reedSolomonCode dom d) q v₁).ncard
      = (openFiber (reedSolomonCode dom d) q v₂).ncard := by
  obtain ⟨c, -, hbij⟩ := (t_symbols_uniform dom ht hq).2 v₁ v₂
  rw [← hbij.image_eq, Set.ncard_image_of_injective _ (add_left_injective c)]

/-! ## Masked-opening hiding: `MaskedOpeningHiding` -/

/-- The explaining-mask fiber: the mask words `r ∈ C` for which the masked
word `mask f γ r = f + γ • r` opens to the tuple `v`. For a uniformly random
mask, `Pr[opened = v]` is this fiber's share of `C`. -/
def maskFiber (C : Submodule F (ι → F)) (q : Fin t → ι) (γ : F)
    (f : ι → F) (v : Fin t → F) : Set (ι → F) :=
  {r | r ∈ C ∧ openSymbols q (mask f γ r) = v}

@[simp] theorem mem_maskFiber {C : Submodule F (ι → F)} {q : Fin t → ι}
    {γ : F} {f v r} :
    r ∈ maskFiber C q γ f v
      ↔ r ∈ C ∧ openSymbols q f + γ • openSymbols q r = v := by
  rw [maskFiber, Set.mem_setOf_eq, openSymbols_mask]

/-- At `γ ≠ 0` the explaining-mask fiber IS a plain opening fiber — of the
unmasked tuple `γ⁻¹ • (v − openSymbols q f)`. Masked-opening facts reduce to
the interpolation fibers above. -/
theorem maskFiber_eq_openFiber {C : Submodule F (ι → F)} (q : Fin t → ι)
    {γ : F} (hγ : γ ≠ 0) (f : ι → F) (v : Fin t → F) :
    maskFiber C q γ f v
      = openFiber C q (γ⁻¹ • (v - openSymbols q f)) := by
  ext r
  rw [mem_maskFiber, mem_openFiber, and_congr_right_iff]
  intro _
  constructor
  · rintro rfl
    rw [add_sub_cancel_left, inv_smul_smul₀ hγ]
  · intro h
    rw [h, smul_inv_smul₀ hγ, add_sub_cancel]

/-- **The opening-hiding property** — `[OB-4-hiding]`'s statement at the
opening layer, keystone fields real (mirroring `ZkAccScheme`'s two faces):

* `sim_support_univ` — for EVERY witness `f` (any word: hiding needs no
  membership hypothesis on the witness), the reachable opened tuples of the
  masked word are ALL of `Fin t → F`: the simulator's support is the full
  public tuple space, and cannot depend on the witness;
* `fiber_equinum` — for any two witnesses and any two tuples, the
  explaining-mask fibers are carried onto each other by an explicit codeword
  translation: the pushforward of the uniform mask is UNIFORM on that
  support, identically for every witness. Real and simulated distributions
  coincide exactly (perfect, not computational): the simulator samples the
  `t` symbols uniformly and never sees `f`. -/
structure MaskedOpeningHiding (C : Submodule F (ι → F)) (q : Fin t → ι)
    (γ : F) : Prop where
  sim_support_univ : ∀ f : ι → F,
    (fun r => openSymbols q (mask f γ r)) '' C = Set.univ
  fiber_equinum : ∀ (f₁ f₂ : ι → F) (v₁ v₂ : Fin t → F), ∃ c ∈ C,
    Set.BijOn (· + c) (maskFiber C q γ f₁ v₁) (maskFiber C q γ f₂ v₂)

/-- **The reduction theorem**: masked-opening hiding follows from ONE
property of the mask space — surjectivity of the opening map on it. This is
the exact interface `[OB-4-hiding-rbr]`'s constrained-mask design must
re-supply: when the mask is confined to a subspace (the mask claim's
homogeneous solution space), hiding holds iff openings still reach every
tuple from there. -/
theorem maskedOpeningHiding_of_surj (C : Submodule F (ι → F))
    (q : Fin t → ι) {γ : F} (hγ : γ ≠ 0)
    (hsurj : ∀ v : Fin t → F, ∃ r ∈ C, openSymbols q r = v) :
    MaskedOpeningHiding C q γ where
  sim_support_univ f := by
    refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨r, hrC, hrv⟩ := hsurj (γ⁻¹ • (v - openSymbols q f))
    refine ⟨r, hrC, ?_⟩
    show openSymbols q (mask f γ r) = v
    rw [openSymbols_mask, hrv, smul_inv_smul₀ hγ, add_sub_cancel]
  fiber_equinum f₁ f₂ v₁ v₂ := by
    obtain ⟨c, hc, hcv⟩ := hsurj
      (γ⁻¹ • ((v₂ - openSymbols q f₂) - (v₁ - openSymbols q f₁)))
    have hcv' : γ • openSymbols q c
        = (v₂ - openSymbols q f₂) - (v₁ - openSymbols q f₁) := by
      rw [hcv, smul_inv_smul₀ hγ]
    refine ⟨c, hc, fun r hr => ?_, (add_left_injective c).injOn, fun r' hr' => ?_⟩
    · rw [mem_maskFiber] at hr ⊢
      obtain ⟨hrC, hrv⟩ := hr
      have hr2 : γ • openSymbols q r = v₁ - openSymbols q f₁ := by
        rw [← hrv]; abel
      refine ⟨C.add_mem hrC hc, ?_⟩
      rw [map_add, smul_add, hr2, hcv']
      abel
    · rw [mem_maskFiber] at hr'
      obtain ⟨hr'C, hr'v⟩ := hr'
      have hr2 : γ • openSymbols q r' = v₂ - openSymbols q f₂ := by
        rw [← hr'v]; abel
      refine ⟨r' - c, ?_, sub_add_cancel r' c⟩
      rw [mem_maskFiber]
      refine ⟨C.sub_mem hr'C hc, ?_⟩
      rw [map_sub, smul_sub, hr2, hcv']
      abel

/-- **Masked-opening hiding for Reed–Solomon, PROVED**: at every `t ≤ d`
distinct query points and every nonzero challenge, the `t` opened symbols of
the masked word `f + γ • r` (uniform mask codeword `r`) are exactly
simulatable without the witness — the MDS surjectivity fed through the
reduction. The two dials `t ≤ d` and `γ ≠ 0` are both load-bearing (teeth
below). -/
theorem rs_maskedOpeningHiding (dom : ι ↪ F) (ht : t ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) {γ : F} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (reedSolomonCode dom d) q γ :=
  maskedOpeningHiding_of_surj _ q hγ (exists_codeword_open dom ht hq)

/-- **Witness independence at the opening layer**: two provers holding
different witnesses produce identical opened-symbol supports — the
distinguisher watching the spot check learns nothing about which witness is
held. (Mirrors `ZkAccScheme.witness_free` one layer down.) -/
theorem MaskedOpeningHiding.witness_free {C : Submodule F (ι → F)}
    {q : Fin t → ι} {γ : F} (H : MaskedOpeningHiding C q γ) (f₁ f₂ : ι → F) :
    (fun r => openSymbols q (mask f₁ γ r)) '' C
      = (fun r => openSymbols q (mask f₂ γ r)) '' C := by
  rw [H.sim_support_univ f₁, H.sim_support_univ f₂]

/-- The counting corollary: every explaining-mask fiber has the same size,
for every witness and every tuple — `Pr[opened = v]` is one constant. -/
theorem MaskedOpeningHiding.maskFiber_ncard_eq {C : Submodule F (ι → F)}
    {q : Fin t → ι} {γ : F} (H : MaskedOpeningHiding C q γ)
    (f₁ f₂ : ι → F) (v₁ v₂ : Fin t → F) :
    (maskFiber C q γ f₁ v₁).ncard = (maskFiber C q γ f₂ v₂).ncard := by
  obtain ⟨c, -, hbij⟩ := H.fiber_equinum f₁ f₂ v₁ v₂
  rw [← hbij.image_eq, Set.ncard_image_of_injective _ (add_left_injective c)]

/-! ## Teeth: both dials are load-bearing -/

/-- At `γ = 0` the opened support collapses to the witness's OWN symbols —
the spot check publishes `openSymbols q f` verbatim. -/
theorem image_openMask_zero (C : Submodule F (ι → F)) (q : Fin t → ι)
    (f : ι → F) :
    (fun r => openSymbols q (mask f 0 r)) '' C = {openSymbols q f} := by
  simp only [mask_zero]
  exact Set.Nonempty.image_const ⟨0, C.zero_mem⟩ _

/-- **γ-dial teeth**: without a genuine challenge there is no hiding — the
support is a witness-dependent singleton, not the public tuple space
(provided there is at least one query to leak through). -/
theorem not_maskedOpeningHiding_zero (C : Submodule F (ι → F))
    {q : Fin t → ι} (ht : 0 < t) :
    ¬ MaskedOpeningHiding C q (0 : F) := by
  intro H
  have h := H.sim_support_univ 0
  rw [image_openMask_zero] at h
  have h1 : (fun _ => (1 : F)) ∈ ({openSymbols q (0 : ι → F)} : Set (Fin t → F)) := by
    rw [h]; trivial
  have h2 := congrFun (Set.mem_singleton_iff.mp h1) ⟨0, ht⟩
  exact one_ne_zero (α := F) (h2.trans (by simp))

/-- **t-dial teeth, general**: one query beyond the degree bound kills hiding
at EVERY challenge. At `t = d + 1` the mask's symbols obey the parity check —
the `(d+1)`-st is determined by the first `d` (`open_determines`) — so the
tuple that is zero on the first `d` queries and `1` on the last is
unreachable, and the simulator's support is never full. The mask bound
`t ≤ d` of `rs_maskedOpeningHiding` is exactly load-bearing. -/
theorem not_maskedOpeningHiding_of_gt (dom : ι ↪ F) {d : ℕ}
    {q : Fin (d + 1) → ι} (hq : Function.Injective (dom ∘ q)) (γ : F) :
    ¬ MaskedOpeningHiding (reedSolomonCode dom d) q γ := by
  intro H
  have h := H.sim_support_univ 0
  have hv : Fin.snoc (0 : Fin d → F) 1
      ∈ (fun r => openSymbols q (mask (0 : ι → F) γ r)) ''
        (reedSolomonCode dom d) := by
    rw [h]; trivial
  obtain ⟨r, hrC, hrv⟩ := hv
  have hrv' : openSymbols q (mask (0 : ι → F) γ r) = Fin.snoc (0 : Fin d → F) 1 :=
    hrv
  have hmask : mask (0 : ι → F) γ r = γ • r := by rw [mask_apply, zero_add]
  rw [hmask] at hrv'
  have hmem : (γ • r : ι → F) ∈ reedSolomonCode dom d :=
    Submodule.smul_mem _ γ hrC
  have hagree : openSymbols (q ∘ Fin.castSucc) (γ • r)
      = openSymbols (q ∘ Fin.castSucc) (0 : ι → F) := by
    funext j
    have hj := congrFun hrv' (Fin.castSucc j)
    simpa [Fin.snoc_castSucc] using hj
  have h0 : (γ • r : ι → F) = 0 :=
    open_determines dom le_rfl (hq.comp (Fin.castSucc_injective d)) hmem
      (Submodule.zero_mem _) hagree
  have hlast := congrFun hrv' (Fin.last d)
  rw [h0] at hlast
  simp [Fin.snoc_last] at hlast

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Over `RS[F₅, {0,1,2,3}, 2]` (`RSExample` — lines over F₅, `d = 2`), with the
query pair `(0, 2)` at the mask bound `t = d = 2` and the query triple
`(0, 1, 2)` one beyond it:

* **satisfiable / premise inhabitation** — `maskedOpeningHiding_F5`: hiding
  FIRES at every nonzero challenge, all hypotheses concretely discharged.
  The interpolation bijection computes: `lineOf_open` opens the concrete
  line `3 + 2X` to the tuple `(3, 2)` by `decide`, and
  `exists_unique_open_F5` exhibits it as the UNIQUE codeword explaining that
  tuple. `masked_open_F5` computes a masked opening end-to-end
  (`xWord + 2 • (3 + 2X)`'s word opens to `(1, 1)`).
* **teeth** — γ-dial: `maskedOpeningHiding_F5_iff`, sharp — hiding holds IFF
  `γ ≠ 0`. t-dial: `parity_F5` computes the parity check (`f 2 = 2·f 1 − f 0`
  for EVERY codeword — the third queried symbol is a linear function of the
  first two, so `t = 3` symbols are never independent), `not_open_001_F5`
  exhibits the unreachable tuple `(0, 0, 1)`, and
  `not_maskedOpeningHiding_F5_triple` refutes hiding at the triple for EVERY
  challenge — the mask bound, not the challenge, is what fails. -/

/-- Degree bound for an explicit line `a + bX`: `< 2`. -/
theorem degree_C_add_C_mul_X_lt_two (a b : F) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).degree < (2 : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  · exact lt_of_le_of_lt (Polynomial.degree_mul_le _ _)
      (lt_of_le_of_lt (add_le_add Polynomial.degree_C_le Polynomial.degree_X_le)
        (by decide))

namespace ZkHidingExample

open RSExample

/-- The query pair `(0, 2)` — `t = d = 2` spot checks at the mask bound. -/
def qPair : Fin 2 → Fin 4 := ![0, 2]

/-- The query triple `(0, 1, 2)` — `t = d + 1 = 3`, one query too many. -/
def qTriple : Fin 3 → Fin 4 := ![0, 1, 2]

/-- The query pair `(0, 1)` used by the parity computation. -/
def qLow : Fin 2 → Fin 4 := ![0, 1]

theorem qPair_inj : Function.Injective (dom₅ ∘ qPair) := by decide

theorem qTriple_inj : Function.Injective (dom₅ ∘ qTriple) := by decide

theorem qLow_inj : Function.Injective (dom₅ ∘ qLow) := by decide

/-- The line through `(0, a)` and `(1, b)`, as a word: evaluations of
`a + (b − a)X`. -/
def lineOf (a b : ZMod 5) : Fin 4 → ZMod 5 :=
  fun i => a + (b - a) * (i.val : ZMod 5)

theorem lineOf_mem (a b : ZMod 5) : lineOf a b ∈ reedSolomonCode dom₅ 2 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.C a + Polynomial.C (b - a) * Polynomial.X,
      degree_C_add_C_mul_X_lt_two a (b - a),
      fun i => by simp [lineOf, dom₅]⟩

/-- The interpolation computes: the line `3 + 2X` (= `lineOf 3 0`, word
`(3, 0, 2, 4)`) opens at the query pair to the tuple `(3, 2)` — by `decide`. -/
theorem lineOf_open : openSymbols qPair (lineOf 3 0) = ![3, 2] := by
  rw [openSymbols_eq_comp]; decide

/-- **The interpolation bijection, computed**: the tuple `(3, 2)` at the
query pair is explained by EXACTLY ONE codeword — the concrete line
`lineOf 3 0`. Premise inhabitation for `exists_unique_codeword_open` with
the witness in hand. -/
theorem exists_unique_open_F5 :
    ∃! f, f ∈ reedSolomonCode dom₅ 2 ∧ openSymbols qPair f = ![3, 2] := by
  refine ⟨lineOf 3 0, ⟨lineOf_mem 3 0, lineOf_open⟩, fun g ⟨hg, hgv⟩ => ?_⟩
  exact open_determines dom₅ le_rfl qPair_inj hg (lineOf_mem 3 0)
    (hgv.trans lineOf_open.symm)

/-- A masked opening, computed end-to-end: masking the secret `xWord` with
the line at challenge `2` gives the word `(1, 1, 1, 1)`, whose opened
symbols are `(1, 1)` — by `decide`. -/
theorem masked_open_F5 :
    openSymbols qPair (mask xWord 2 (lineOf 3 0)) = ![1, 1] := by
  rw [openSymbols_eq_comp]; decide

/-- **Satisfiable / premise inhabitation**: masked-opening hiding FIRES on
the F₅ code at the mask bound, for every nonzero challenge. -/
theorem maskedOpeningHiding_F5 {γ : ZMod 5} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (reedSolomonCode dom₅ 2) qPair γ :=
  rs_maskedOpeningHiding dom₅ le_rfl qPair_inj hγ

/-- **Sharp**: on the F₅ instance at the mask bound, opening-hiding holds
IFF the challenge is nonzero — exactly the γ-dial of the word-level shell
(`zkAccScheme_F5_iff`), reproduced one layer down at the leakage surface. -/
theorem maskedOpeningHiding_F5_iff (γ : ZMod 5) :
    MaskedOpeningHiding (reedSolomonCode dom₅ 2) qPair γ ↔ γ ≠ 0 := by
  refine ⟨fun H h0 => ?_, maskedOpeningHiding_F5⟩
  subst h0
  exact not_maskedOpeningHiding_zero _ (by norm_num) H

/-- **The parity check, computed**: EVERY codeword's third queried symbol is
the fixed linear function `2·f 1 − f 0` of the first two — `t = 3` opened
symbols of a line over F₅ are never jointly uniform; the dependency is this
exact relation. -/
theorem parity_F5 {f : Fin 4 → ZMod 5} (hf : f ∈ reedSolomonCode dom₅ 2) :
    f 2 = 2 * f 1 - f 0 := by
  have hopen : openSymbols qLow f = openSymbols qLow (lineOf (f 0) (f 1)) := by
    funext j
    fin_cases j <;> simp [qLow, lineOf]
  have hfg : f = lineOf (f 0) (f 1) :=
    open_determines dom₅ le_rfl qLow_inj hf (lineOf_mem _ _) hopen
  have h2 := congrFun hfg 2
  rw [h2]
  show f 0 + (f 1 - f 0) * ((2 : Fin 4).val : ZMod 5) = 2 * f 1 - f 0
  norm_num
  ring

/-- The unreachable tuple: no codeword opens to `(0, 0, 1)` at the triple —
zero on the first two queries forces zero on the third (parity). The
`t = d + 1` leak, witnessed concretely. -/
theorem not_open_001_F5 :
    ¬ ∃ f ∈ reedSolomonCode dom₅ 2, openSymbols qTriple f = ![0, 0, 1] := by
  rintro ⟨f, hf, hv⟩
  have h0 : f 0 = 0 := by simpa [qTriple] using congrFun hv 0
  have h1 : f 1 = 0 := by simpa [qTriple] using congrFun hv 1
  have h2 : f 2 = 1 := by simpa [qTriple] using congrFun hv 2
  have hp := parity_F5 hf
  rw [h0, h1, h2] at hp
  simp at hp

/-- **t-dial teeth, instantiated**: at the query triple, hiding fails for
EVERY challenge — including all the nonzero ones that make the pair
instance hide. One spot check beyond the degree bound, and no challenge
saves the mask. -/
theorem not_maskedOpeningHiding_F5_triple (γ : ZMod 5) :
    ¬ MaskedOpeningHiding (reedSolomonCode dom₅ 2) qTriple γ :=
  not_maskedOpeningHiding_of_gt dom₅ qTriple_inj γ

end ZkHidingExample

/-! ## Residual obligations — prose, not stubs

**[OB-4-hiding-rbr]** — the remaining opening-leakage mathematics: what
stands between the core proved above and a full zk claim for the hash-based
straightline accumulator. This refines `Selvage/ZK.lean`'s `[OB-4-hiding]`: the
t-wise uniformity that residual named as "the masking subcode's
`t`-wise uniformity" is now a THEOREM (`t_symbols_uniform`,
`rs_maskedOpeningHiding`); what remains, precisely:

* **Constrained-mask surjectivity.** The shell's word-level simulator
  (`mask_bijOn`) consumes a mask SATISFYING the mask claim (`satWords C B`),
  an affine subspace of the code — not the whole code this file's mask
  ranges over. By `maskedOpeningHiding_of_surj` the opening-hiding question
  for that mask reduces to ONE statement: the opening map is surjective on
  the claim's homogeneous solution space `{g ∈ C | ∀ i, B.weights i g = 0}`.
  Realizer: for `r` evaluation-channel constraints, `t + r ≤ d` via
  vanishing-polynomial factorization (divide out the constrained points;
  the quotient is a free RS code of degree `d − r`, and the interpolation
  argument reruns); for general linear channels, the bound is the dual
  distance of the constrained code. This is real, bounded new mathematics —
  the next theorem to land, not an open problem.
* **The joint word+opening simulator.** `mask_bijOn` (folded word uniform on
  `simSupport`) and `rs_maskedOpeningHiding` (opened symbols uniform on
  tuples) each hold for a uniform mask — but ONE mask draw must do both
  jobs, so the joint distribution (folded word, opened symbols) needs a
  single simulator; `openSymbols_mask` (openings commute with the fold) is
  the hinge, and the conditional structure (word marginal × opening
  conditional) is where the two bijections must compose. Genuinely new.
* **The multi-step schedule.** Across `k` accumulation steps the verifier
  opens `t` symbols of EACH step's recommitted fold — `t·k` symbols of
  correlated words. The per-step mask spends its independence budget on its
  own step's openings; that each committed word is opened at ONE step only
  (WARP's recommitment schedule) is what should make fresh per-step masks
  sufficient. Stating and proving the schedule invariant is the
  accumulation-level half of this residual.
* **Hiding and soundness in one game.** `mask_mem` keeps the masked word in
  the code, so completeness and the proximity test survive masking; but the
  RBR soundness bounds (`Selvage/AccSound.lean`) and the extractor
  (`[ACC-extract]`) must be re-proved for the masked prover — the mask adds
  prover-chosen randomness the extractor must peel (it can: the mask is
  committed and folded at a public challenge, `unmask` is its inverse), and
  the simulator of the strengthened sense must also produce the
  recommitment roots (commitment-layer hiding — salted Merkle/BCS — joins
  from `[OB-4-hiding]` unchanged). The straightline law forbids shortcuts
  through rewinding here; this is the open research edge, with the
  zk-sumcheck side (idea (b)) still alongside it.

What this file settles: the leakage surface's mathematics at a single step,
for an unconstrained codeword mask, is CLOSED — uniformity is the MDS
bijection, the mask bound `t ≤ d` is sharp in both directions, and hiding
reduces to opening-map surjectivity on whatever mask space the final design
fixes. The contribution slot's open half is the composition: constrained
masks, one draw for two layers, many steps, one game.

`#print axioms` on `t_symbols_uniform`, `exists_unique_codeword_open`,
`open_bijOn`, `rs_maskedOpeningHiding`, `maskedOpeningHiding_of_surj`,
`MaskedOpeningHiding.witness_free`, `not_maskedOpeningHiding_zero`,
`not_maskedOpeningHiding_of_gt`, `ZkHidingExample.exists_unique_open_F5`,
`ZkHidingExample.maskedOpeningHiding_F5_iff`, `ZkHidingExample.parity_F5`,
`ZkHidingExample.not_open_001_F5`,
`ZkHidingExample.not_maskedOpeningHiding_F5_triple`: `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
