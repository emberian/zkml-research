/- Supplied BinaryMerkle paths for one injected arity-eight transition.
The verifier consumes eight source point openings, one input opening and
one next-word opening. This is not the packed p3 MMCS representation.
The commitment checkpoints are fixed before their relevant query randomness. -/
import Selvage.ArityEightSampling
import Selvage.EfficientRootOpening

namespace Minidregg.Selvage.ArityEight
open scoped Classical

variable {F Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest]

structure PointOpening (F Digest : Type) where
  value : F
  path : List Digest

/-- The supplied value and path are fed directly to the existing verifier. -/
def PointVerified (H : BinaryMerkle.HashSuite F Digest) {k : ℕ}
    (root : Digest) (i : Fin (2^k)) (o : PointOpening F Digest) : Prop :=
  (BinaryMerkle.openingScheme H k).verifyOpen root i o.value o.path

def PointLogged (H : BinaryMerkle.HashSuite F Digest) (L : EfficientRootOpening.Log F Digest)
    {k : ℕ} (i : Fin (2^k)) (o : PointOpening F Digest) : Prop :=
  ∀ e ∈ EfficientRootOpening.openingLog H o.value (binaryAddressBits k i) o.path, e ∈ L

omit [Field F] [DecidableEq F] in
/-- General finite execution-log version, retaining the supplied path. -/
theorem supplied_point_pins (H : BinaryMerkle.HashSuite F Digest)
    (P L : EfficientRootOpening.Log F Digest) (default : F) {k : ℕ} (root : Digest)
    (i : Fin (2^k)) (o : PointOpening F Digest)
    (hsub : ∀ e ∈ P, e ∈ L) (hgood : ¬EfficientRootOpening.Bad P L root)
    (hlogged : PointLogged H L i o) (hacc : PointVerified H root i o) :
    o.value = EfficientRootOpening.word P default k root i := by
  have hl : (EfficientRootOpening.Query.leaf o.value,H.leaf o.value) ∈ L :=
    hlogged _ (by simp [EfficientRootOpening.openingLog])
  have hn : ∀ e ∈ EfficientRootOpening.pathLog H (H.leaf o.value) (binaryAddressBits k i) o.path,
      e ∈ L := by
    intro e he
    exact hlogged e (by simp [EfficientRootOpening.openingLog,he])
  exact (EfficientRootOpening.extractedAt_eq_of_logged H P L default root hsub hgood o.value hl
    k root (binaryAddressBits k i) o.path (Or.inl rfl) hn hacc).symm

structure RowOpening (F Digest : Type) where
  source : Bool → Bool → Bool → PointOpening F Digest
  injected : PointOpening F Digest
  next : PointOpening F Digest

variable {k₀ k₁ k₂ k₃ : ℕ}
variable {dom₀ : Fin (2^k₀) ↪ F} {dom₁ : Fin (2^k₁) ↪ F}
variable {dom₂ : Fin (2^k₂) ↪ F} {dom₃ : Fin (2^k₃) ↪ F}

/-- All ten supplied paths and the actual eight-input fold equation. -/
def RowVerified (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (rs rg rn : Digest)
    (β : F) (i : Fin (2^k₃)) (o : RowOpening F Digest) : Prop :=
  (∀ c b a, PointVerified H rs (rowPoint D₀ D₁ D₂ i c b a) (o.source c b a)) ∧
  PointVerified H rg i o.injected ∧ PointVerified H rn i o.next ∧
  o.next.value = foldRow8 D₀ D₁ D₂ i (fun c b a => (o.source c b a).value) β +
    β^8*o.injected.value

/-- Executable supplied-point verification through the existing recomputation. -/
def pointCheck (H : BinaryMerkle.HashSuite F Digest) {k : ℕ}
    (root : Digest) (i : Fin (2^k)) (o : PointOpening F Digest) : Bool :=
  decide (BinaryMerkle.recompute H (H.leaf o.value) (binaryAddressBits k i) o.path = some root)

/-- Executable arity-eight row verifier, retaining every supplied path. -/
def rowCheck (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (rs rg rn : Digest)
    (β : F) (i : Fin (2^k₃)) (o : RowOpening F Digest) : Bool :=
  ([false,true].all fun c => [false,true].all fun b => [false,true].all fun a =>
    pointCheck H rs (rowPoint D₀ D₁ D₂ i c b a) (o.source c b a)) &&
  pointCheck H rg i o.injected && pointCheck H rn i o.next &&
  decide (o.next.value = foldRow8 D₀ D₁ D₂ i (fun c b a => (o.source c b a).value) β +
    β^8*o.injected.value)

/-- Exact Boolean/proposition interface for the supplied-path checker. -/
theorem rowCheck_eq_true_iff (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (rs rg rn : Digest)
    (β : F) (i : Fin (2^k₃)) (o : RowOpening F Digest) :
    rowCheck H D₀ D₁ D₂ rs rg rn β i o = true ↔
      RowVerified H D₀ D₁ D₂ rs rg rn β i o := by
  simp [rowCheck,pointCheck,RowVerified,PointVerified,BinaryMerkle.openingScheme,Bool.forall_bool,and_assoc]

/-- These are log-completeness conditions on the actual supplied paths. -/
def RowLogged (H : BinaryMerkle.HashSuite F Digest) (L : EfficientRootOpening.Log F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (i : Fin (2^k₃)) (o : RowOpening F Digest) : Prop :=
  (∀ c b a, PointLogged H L (rowPoint D₀ D₁ D₂ i c b a) (o.source c b a)) ∧
  PointLogged H L i o.injected ∧ PointLogged H L i o.next

/-- A finite observed failure, at exactly the three commitment checkpoints. -/
def RoundBad (Ps Pg Pn L : EfficientRootOpening.Log F Digest) (rs rg rn : Digest) : Prop :=
  EfficientRootOpening.Bad Ps L rs ∨ EfficientRootOpening.Bad Pg L rg ∨ EfficientRootOpening.Bad Pn L rn

omit [DecidableEq F] in
/-- On no observed failure, all supplied paths pin the computed equation to
three deterministically extracted words. -/
theorem supplied_row_pins (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃)
    (Ps Pg Pn L : EfficientRootOpening.Log F Digest) (default : F) (rs rg rn : Digest)
    (hs : ∀ e ∈ Ps, e ∈ L) (hg : ∀ e ∈ Pg, e ∈ L) (hn : ∀ e ∈ Pn, e ∈ L)
    (hgood : ¬RoundBad Ps Pg Pn L rs rg rn)
    (β : F) (i : Fin (2^k₃)) (o : RowOpening F Digest)
    (hlog : RowLogged H L D₀ D₁ D₂ i o)
    (ha : RowVerified H D₀ D₁ D₂ rs rg rn β i o) :
    EfficientRootOpening.word Pn default k₃ rn i =
      fold8 D₀ D₁ D₂ (EfficientRootOpening.word Ps default k₀ rs) β i +
        β^8*EfficientRootOpening.word Pg default k₃ rg i := by
  have hgs : ¬EfficientRootOpening.Bad Ps L rs := fun h => hgood (Or.inl h)
  have hgg : ¬EfficientRootOpening.Bad Pg L rg := fun h => hgood (Or.inr (Or.inl h))
  have hgn : ¬EfficientRootOpening.Bad Pn L rn := fun h => hgood (Or.inr (Or.inr h))
  have hp : (fun c b a => (o.source c b a).value) =
      fun c b a => EfficientRootOpening.word Ps default k₀ rs (rowPoint D₀ D₁ D₂ i c b a) := by
    funext c b a
    exact supplied_point_pins H Ps L default rs _ _ hs hgs (hlog.1 c b a) (ha.1 c b a)
  have hpi := supplied_point_pins H Pg L default rg i o.injected hg hgg hlog.2.1 ha.2.1
  have hpn := supplied_point_pins H Pn L default rn i o.next hn hgn hlog.2.2 ha.2.2.1
  rw [←hpn,ha.2.2.2,hp,foldRow8_eq_fold8,hpi]

/-- The raw supplied-path acceptance event. The next word is extracted from
its beta-dependent checkpoint, fixed before the query vector. -/
def SuppliedCrossing (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (d : ℕ) (δ : ℝ) (q : ℕ)
    (Pn : F → EfficientRootOpening.Log F Digest) (default : F)
    (rs rg : Digest) (rn : F → Digest)
    (openings : F × (Fin q → Fin (2^k₃)) → Fin q → RowOpening F Digest)
    (x : F × (Fin q → Fin (2^k₃))) : Prop :=
  close δ (reedSolomonCode dom₃ d) (EfficientRootOpening.word (Pn x.1) default k₃ (rn x.1)) ∧
  ∀ a, RowVerified H D₀ D₁ D₂ rs rg (rn x.1) x.1 (x.2 a) (openings x a)

/-- The supplied-opening reduction plus the actual degree-eight challenge
and sampling bounds. Ps and Pg are chosen before beta; Pn and rn depend only
on beta. No numerical ROM, hash-collision or Fiat--Shamir term is assumed. -/
theorem supplied_injected_crossing_sound [Fintype F]
    (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) {d : ℕ} (hd : 1 ≤ d) {θ δ τ : ℝ}
    (hθ : 0 < θ) (hrate : (d:ℝ) < (1-2*θ)*(2^k₃:ℕ))
    (hτ : τ ≤ 1) (hgap : δ+τ ≤ θ) (q : ℕ)
    (Ps Pg : EfficientRootOpening.Log F Digest) (Pn : F → EfficientRootOpening.Log F Digest) (default : F)
    (rs rg : Digest) (rn : F → Digest)
    (openings : F × (Fin q → Fin (2^k₃)) → Fin q → RowOpening F Digest)
    (logs : F × (Fin q → Fin (2^k₃)) → EfficientRootOpening.Log F Digest)
    (hsub : ∀ x, (∀ e ∈ Ps, e ∈ logs x) ∧ (∀ e ∈ Pg, e ∈ logs x) ∧
      (∀ e ∈ Pn x.1, e ∈ logs x))
    (hlog : ∀ x a, RowLogged H (logs x) D₀ D₁ D₂ (x.2 a) (openings x a))
    (hfar : EfficientRootOpening.Far_E θ k₀ (reedSolomonCode dom₀ (8*d)) Ps default rs) :
    uniformProb (F × (Fin q → Fin (2^k₃)))
      (SuppliedCrossing H D₀ D₁ D₂ d δ q Pn default rs rg rn openings) ≤
      ((8*2^k₃:ℕ):ℝ)/Fintype.card F + (1-τ)^q +
      uniformProb (F × (Fin q → Fin (2^k₃)))
        (fun x => RoundBad Ps Pg (Pn x.1) (logs x) rs rg (rn x.1)) := by
  classical
  let bad := fun x : F × (Fin q → Fin (2^k₃)) =>
    RoundBad Ps Pg (Pn x.1) (logs x) rs rg (rn x.1)
  let ideal := Crossing (reedSolomonCode dom₃ d) δ
    (fun β i => fold8 D₀ D₁ D₂ (EfficientRootOpening.word Ps default k₀ rs) β i +
      β^8*EfficientRootOpening.word Pg default k₃ rg i)
    (fun β => EfficientRootOpening.word (Pn β) default k₃ (rn β)) q
  have hcover : ∀ x, SuppliedCrossing H D₀ D₁ D₂ d δ q Pn default rs rg rn
      openings x → ideal x ∨ bad x := by
    intro x hx
    by_cases hb : bad x
    · exact Or.inr hb
    · refine Or.inl ⟨hx.1,?_⟩
      intro a
      exact supplied_row_pins H D₀ D₁ D₂ Ps Pg (Pn x.1) (logs x) default rs rg (rn x.1)
        (hsub x).1 (hsub x).2.1 (hsub x).2.2 hb x.1 (x.2 a) (openings x a)
        (hlog x a) (hx.2 a)
  have hideal : uniformProb (F × (Fin q → Fin (2^k₃))) ideal ≤
      ((8*2^k₃:ℕ):ℝ)/Fintype.card F + (1-τ)^q := by
    simpa [ideal,Fintype.card_fin] using fold8_injected_sampled_crossing D₀ D₁ D₂ hd hθ
      (by simpa using hrate) hτ hgap (EfficientRootOpening.word Ps default k₀ rs)
      (EfficientRootOpening.word Pg default k₃ rg) (fun β => EfficientRootOpening.word (Pn β) default k₃ (rn β)) q hfar
  exact le_trans (le_trans (uniformProb_mono hcover) (uniformProb_or_le ideal bad))
    (by dsimp [bad] at *; linarith)

end Minidregg.Selvage.ArityEight


/-- info: 'Minidregg.Selvage.ArityEight.supplied_point_pins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.supplied_point_pins

/-- info: 'Minidregg.Selvage.ArityEight.rowCheck_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.rowCheck_eq_true_iff

/-- info: 'Minidregg.Selvage.ArityEight.supplied_row_pins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.supplied_row_pins

/-- info: 'Minidregg.Selvage.ArityEight.supplied_injected_crossing_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.supplied_injected_crossing_sound

