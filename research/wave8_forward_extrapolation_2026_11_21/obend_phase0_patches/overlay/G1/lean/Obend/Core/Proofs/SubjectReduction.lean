module
/- Source subject reduction (lane Sound, pass 3, 2026-11-01).

A `Step` from a term that checks in a context checks again in that context (`step_preserves_typing`),
with uses no larger at any position that is not `unrestricted` (so the `safeUses` budget continues)
and equal at every `linear` one (`step_conserves_linear`). The type is kept up to `sameType`, with
two exceptions, both stated: the root `done` redex returns its value at the computation's result
type, and `extendRecord` drops the shadowed fields of the old record, whose type (`overlay`) keeps
them when they are not shareable (`Ty.insertCanonical`), so the new record is typed at a row that
answers every lookup of the old type with an equivalent member (`RowRefines`), not at a `sameType`
of it. Either way the reduct checks, which is what a reduction needs: `steps_conserve_linear'`
carries linear conservation along any reduction of a checked term, and `custody_conserved` is its
closed-program form. -/
public import Obend.Core.Proofs.SubjectReduction.Substitution
public import Obend.Core.Proofs.Preservation.Cases.Records
public import Obend.Core.Proofs.Preservation.Cases.Sums
import all Obend.Core.Proofs.SubjectReduction.Substitution
import all Obend.Core.Proofs.Conservation
import all Obend.Core.Proofs.Preservation.Cases.Records
import all Obend.Core.Proofs.Preservation.Cases.Sums
import all Obend.Core.Check

namespace Obend.Core.Proofs.SubjectReduction
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.MachineTyping
open Obend.Core.Proofs.Conservation
open Obend.Core.Proofs.Preservation (finiteRow_nonrow rowSyntax same_type_lookup_transport arms_uses_length
  fields_overlay_lookup fields_overlay_row lookup_not_computation isRow_not_computation callable_arrow_not_computation
  closure_callable_type specification_callable_type computation_same_type_inj reusable_mix_body source_weaken)
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences fieldOccurrences armOccurrences uses_determined)
set_option autoImplicit false

/-! ### Where the reduct's type stands -/

/-- `T'` serves wherever the record type `T` did: both are finite rows, every lookup of `T` is
answered by `T'` with an equivalent member, and `T'` is a closed explicit row answering no label `T`
does not (so a destructor that covers `T` covers `T'`). -/
@[expose] public def RowRefines (a : Assumptions) (T' T : Ty) : Prop :=
  TypeGraph.FiniteRow a T' ∧ TypeGraph.FiniteRow a T ∧
    (∀ fuel name member, T.lookup a.bounds fuel name = some member →
      ∃ depth member', T'.lookup a.bounds depth name = some member' ∧ sameType a member' member = true) ∧
    T'.tail = .emptyRow ∧
    ∀ fuel name member', T'.lookup a.bounds fuel name = some member' →
      ∃ depth member, T.lookup a.bounds depth name = some member

/-- Pointwise at most, at every position that is not `unrestricted`. -/
@[expose] public def Below (Γ : Context) (x y : Uses) : Prop :=
  ∀ j b, Γ[j]? = some b → b.quantity ≠ .unrestricted → x.getD j 0 ≤ y.getD j 0

theorem RowRefines.trans_same {a : Assumptions} {T' T T2 : Ty} (r : RowRefines a T' T)
    (s : sameType a T T2 = true) : RowRefines a T' T2 := by
  obtain ⟨f', f, h, closed, back⟩ := r
  refine ⟨f', (TypeGraph.equivalent_finite_row_iff ((sameType_iff a _ _).mp s)).mp f, fun fuel name m lk => ?_,
    closed, fun fuel name m' lk => ?_⟩
  · obtain ⟨depth, m1, lk1, s1⟩ := same_type_lookup_transport s fuel name m lk
    obtain ⟨depth', m2, lk2, s2⟩ := h depth name m1 lk1
    exact ⟨depth', m2, lk2, sameType_trans s2 s1⟩
  · obtain ⟨depth, m, lk1⟩ := back fuel name m' lk
    obtain ⟨depth', m2, lk2, _⟩ := same_type_lookup_transport (sameType_symm s) depth name m lk1
    exact ⟨depth', m2, lk2⟩

theorem not_row {a : Assumptions} {T : Ty} (h : rowSyntax T = false) (f : TypeGraph.FiniteRow a T) : False :=
  (finiteRow_nonrow h).mp f

theorem callable_not_row {a : Assumptions} {T : Ty} {r : Reuse} {q : Quantity} {D C : Ty}
    (h : callable T = .arrow r q D C) (f : TypeGraph.FiniteRow a T) : False := by
  cases T <;> simp [callable] at h <;> exact not_row rfl f

theorem done_absurd {a : Assumptions} {P R X T : Ty} (h : sameType a (.computation P R X) T = true)
    (pure : T.isComputation = false) : False := by
  have := sameType_isComputation h
  rw [pure] at this
  simp [Ty.isComputation] at this

theorem lookup_det {bounds : Bounds} {T : Ty} {name : String} {x y : Ty} {f g : Nat}
    (hx : T.lookup bounds f name = some x) (hy : T.lookup bounds g name = some y) : x = y := by
  have := Ty.lookup_mono hx (Nat.le_max_left f g)
  rw [Ty.lookup_mono hy (Nat.le_max_right f g)] at this
  exact (Option.some.inj this).symm

/-! ### Uses, pointwise -/

theorem uses_ext {x y : Uses} (hl : x.length = y.length) (h : ∀ i, x.getD i 0 = y.getD i 0) : x = y := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.getD_some] at this
  exact this

theorem below_of_le {Γ : Context} {x y : Uses} (h : ∀ i, x.getD i 0 ≤ y.getD i 0) : Below Γ x y :=
  fun j _ _ _ => h j

theorem below_trans {Γ : Context} {x y z : Uses} (h1 : Below Γ x y) (h2 : Below Γ y z) : Below Γ x z :=
  fun j b hb q => Nat.le_trans (h1 j b hb q) (h2 j b hb q)

theorem below_add_left {Γ : Context} {x x' y : Uses} (h : Below Γ x' x) (l' : x'.length = y.length)
    (l : x.length = y.length) : Below Γ (addUses x' y) (addUses x y) := by
  intro j b hb q; rw [getD_addUses l', getD_addUses l]; have := h j b hb q; omega

theorem below_add_right {Γ : Context} {x y y' : Uses} (h : Below Γ y' y) (l' : x.length = y'.length)
    (l : x.length = y.length) : Below Γ (addUses x y') (addUses x y) := by
  intro j b hb q; rw [getD_addUses l', getD_addUses l]; have := h j b hb q; omega

theorem safe_below {Γ : Context} {x y : Uses} (safe : safeUses Γ y = true) (len : x.length = Γ.length)
    (h : Below Γ x y) : safeUses Γ x = true := by
  obtain ⟨_, hs⟩ := safeUses_iff.mp safe
  refine safeUses_iff.mpr ⟨len, fun j b hb => ?_⟩
  by_cases q : b.quantity = .unrestricted
  · rw [q]; rfl
  · exact safeQuantity_mono (hs j b hb) (h j b hb q)

theorem safe_mono {Γ : Context} {x y : Uses} (safe : safeUses Γ y = true) (len : x.length = Γ.length)
    (h : ∀ i, x.getD i 0 ≤ y.getD i 0) : safeUses Γ x = true :=
  safe_below safe len (below_of_le h)

theorem linearFree_below {Γ : Context} {x y : Uses} (free : linearFree Γ y = true) (len : x.length = Γ.length)
    (h : Below Γ x y) : linearFree Γ x = true := by
  rw [linearFree_iff len]
  intro j b hb
  by_cases q : b.quantity = .linear
  · left
    have := h j b hb (by rw [q]; decide)
    rw [linearFree_getD free ⟨b, hb, q⟩] at this; omega
  · exact .inr q

theorem captures_below {V : List Nat} {Γ : Context} {x y : Uses} (valid : validContext V Γ = true)
    (cap : reusableCaptures V Γ y = true) (len : x.length = Γ.length) (h : Below Γ x y) :
    reusableCaptures V Γ x = true := by
  obtain ⟨_, hc⟩ := captures_iff.mp cap
  refine captures_iff.mpr ⟨len, fun j b hb => ?_⟩
  by_cases q : b.quantity = .unrestricted
  · by_cases z : x.getD j 0 = 0
    · exact .inl z
    · right
      refine ⟨q, ?_⟩
      unfold validContext at valid
      have := List.all_eq_true.mp valid b (List.mem_of_getElem? hb)
      have h' : b.type.shareableUnder V = true ∧ b.type.bearsCustody = false := by simpa [q] using this
      exact h'.1
  · rcases hc j b hb with z | r
    · left; have := h j b hb q; omega
    · exact absurd r.1 q

theorem caseAllowed_below {a : Assumptions} {q : Quantity} {Γ : Context} {x y : Uses}
    (valid : validContext a.shareableVariables Γ = true) (allowed : caseAllowed a q Γ y = true)
    (len : x.length = Γ.length) (h : Below Γ x y) : caseAllowed a q Γ x = true := by
  simp only [caseAllowed, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at allowed ⊢
  obtain ⟨lin, unr⟩ := allowed
  refine ⟨?_, ?_⟩
  · rcases lin with l | free
    · exact .inl l
    · exact .inr (linearFree_below free len h)
  · rcases unr with n | cap
    · exact .inl n
    · exact .inr (captures_below valid cap len h)

theorem captures_add {V : List Nat} {Γ : Context} {x y : Uses} (cx : reusableCaptures V Γ x = true)
    (cy : reusableCaptures V Γ y = true) : reusableCaptures V Γ (addUses x y) = true := by
  obtain ⟨lx, hx⟩ := captures_iff.mp cx
  obtain ⟨ly, hy⟩ := captures_iff.mp cy
  refine captures_iff.mpr ⟨by simp [addUses, lx, ly], fun j b hb => ?_⟩
  rw [getD_addUses (lx.trans ly.symm)]
  rcases hx j b hb with zx | rx
  · rcases hy j b hb with zy | ry
    · left; omega
    · exact .inr ry
  · exact .inr rx

theorem captures_zero_below {V : List Nat} {Γ : Context} {x y : Uses} (cx : reusableCaptures V Γ x = true) :
    Below Γ x y := by
  intro j b hb q
  rcases (captures_iff.mp cx).2 j b hb with z | r
  · rw [z]; exact Nat.zero_le _
  · exact absurd r.1 q

/-! ### Inversions, with types -/

local macro "inv_other" : tactic => `(tactic| (intros; first | trivial | (rename_i e; cases e)))

theorem specification_inv' {a : Assumptions} {Γ : Context} {m e : Term} {T : Ty} {u : Uses}
    (h : PartialTyping a Γ (.specification m e) T u) : ∃ M E mu eu,
      PartialTyping a Γ m M mu ∧ PartialTyping a Γ e E eu ∧ linearFree Γ mu = true ∧ u = addUses mu eu ∧
      sameType a (.specification M E) T = true := by
  generalize ht : Term.specification m e = t0 at h
  revert ht; revert m e
  apply PartialTyping.rec
    (motive_1 := fun Γ t T u _ => ∀ m e, Term.specification m e = t → ∃ M E mu eu,
      PartialTyping a Γ m M mu ∧ PartialTyping a Γ e E eu ∧ linearFree Γ mu = true ∧ u = addUses mu eu ∧
      sameType a (.specification M E) T = true)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case specification =>
    intro Γ m' e' M E mu eu hm he _ _ free _ _ m e eq
    cases eq; exact ⟨M, E, mu, eu, hm, he, free, rfl, sameType_refl _ _⟩
  case conversion =>
    intro Γ t actual expected u _ same ih m e eq
    obtain ⟨M, E, mu, eu, hm, he, free, eq', s⟩ := ih m e eq
    exact ⟨M, E, mu, eu, hm, he, free, eq', sameType_trans s same⟩
  all_goals inv_other

theorem prototype_inv' {a : Assumptions} {Γ : Context} {s t : Term} {T : Ty} {u : Uses}
    (h : PartialTyping a Γ (.prototype s t) T u) : ∃ S T0 su tu,
      PartialTyping a Γ s S su ∧ PartialTyping a Γ t T0 tu ∧ u = addUses su tu ∧
      sameType a (.prototype S T0) T = true := by
  generalize ht : Term.prototype s t = t0 at h
  revert ht; revert s t
  apply PartialTyping.rec
    (motive_1 := fun Γ term T u _ => ∀ s t, Term.prototype s t = term → ∃ S T0 su tu,
      PartialTyping a Γ s S su ∧ PartialTyping a Γ t T0 tu ∧ u = addUses su tu ∧
      sameType a (.prototype S T0) T = true)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case prototype =>
    intro Γ s' t' S T0 su tu hs ht _ _ _ _ s t eq
    cases eq; exact ⟨S, T0, su, tu, hs, ht, rfl, sameType_refl _ _⟩
  case conversion =>
    intro Γ term actual expected u _ same ih s t eq
    obtain ⟨S, T0, su, tu, hs, ht, eq', s'⟩ := ih s t eq
    exact ⟨S, T0, su, tu, hs, ht, eq', sameType_trans s' same⟩
  all_goals inv_other

theorem record_inv' {a : Assumptions} {Γ : Context} {fields : List (String × Term)} {T : Ty} {u : Uses}
    (h : PartialTyping a Γ (.record fields) T u) : ∃ row, FieldsTyping a Γ fields row u ∧ sameType a row T = true := by
  generalize ht : Term.record fields = t0 at h
  revert ht; revert fields
  apply PartialTyping.rec
    (motive_1 := fun Γ term T u _ => ∀ fields, Term.record fields = term →
      ∃ row, FieldsTyping a Γ fields row u ∧ sameType a row T = true)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case record =>
    intro Γ fields' row u hf _ _ fields eq
    cases eq; exact ⟨row, hf, sameType_refl _ _⟩
  case conversion =>
    intro Γ term actual expected u _ same ih fields eq
    obtain ⟨row, hf, s⟩ := ih fields eq
    exact ⟨row, hf, sameType_trans s same⟩
  all_goals inv_other

theorem inject_inv' {a : Assumptions} {Γ : Context} {l : String} {p : Term} {T : Ty} {u : Uses}
    (h : PartialTyping a Γ (.inject l p) T u) : ∃ P row fuel,
      PartialTyping a Γ p P u ∧ row.lookup a.bounds fuel l = some P ∧ sameType a (.variant row) T = true := by
  generalize ht : Term.inject l p = t0 at h
  revert ht; revert l p
  apply PartialTyping.rec
    (motive_1 := fun Γ term T u _ => ∀ l p, Term.inject l p = term → ∃ P row fuel,
      PartialTyping a Γ p P u ∧ row.lookup a.bounds fuel l = some P ∧ sameType a (.variant row) T = true)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case inject =>
    intro Γ tag payload P row u fuel hp lookup _ _ l p eq
    cases eq; exact ⟨P, row, fuel, hp, lookup, sameType_refl _ _⟩
  case conversion =>
    intro Γ term actual expected u _ same ih l p eq
    obtain ⟨P, row, fuel, hp, lookup, s⟩ := ih l p eq
    exact ⟨P, row, fuel, hp, lookup, sameType_trans s same⟩
  all_goals inv_other

/-! ### Fields -/

theorem fields_lookup {a : Assumptions} {Γ : Context} {fields : List (String × Term)} {row : Ty} {u : Uses}
    (typed : FieldsTyping a Γ fields row u) (fuel : Nat) (name : String) (m : Ty)
    (lookup : row.lookup a.bounds fuel name = some m) : ∃ body bu,
      fields.find? (fun field => field.1 == name) = some (name, body) ∧ PartialTyping a Γ body m bu ∧
      ∀ i, bu.getD i 0 ≤ u.getD i 0 := by
  induction fields generalizing row u fuel with
  | nil => cases typed; cases fuel <;> simp [Ty.lookup] at lookup
  | cons field rest ih =>
    obtain ⟨prior, body⟩ := field
    cases typed with
    | cons bodyTyped restTyped pure =>
      rename_i type tail bu ru
      have l := (source_uses_length bodyTyped).trans (fields_uses_length restTyped).symm
      cases fuel with
      | zero => simp [Ty.lookup] at lookup
      | succ fuel =>
        by_cases hit : prior = name
        · subst hit
          simp [Ty.lookup] at lookup; subst lookup
          exact ⟨body, bu, by simp, bodyTyped, add_le_left l⟩
        · simp only [Ty.lookup, if_neg hit] at lookup
          obtain ⟨b, bu', found, hb, le⟩ := ih restTyped fuel lookup
          refine ⟨b, bu', ?_, hb, fun i => Nat.le_trans (le i) (add_le_right l i)⟩
          have hb' : (prior == name) = false := by simpa using hit
          rw [List.find?_cons, hb']; exact found

theorem fields_isRow {a : Assumptions} {Γ : Context} {fields : List (String × Term)} {row : Ty} {u : Uses}
    (typed : FieldsTyping a Γ fields row u) : ∃ fuel, row.isRow a.bounds fuel = true := by
  induction fields generalizing row u with
  | nil => cases typed; exact ⟨1, rfl⟩
  | cons field rest ih =>
    cases typed with
    | cons _ restTyped _ =>
      obtain ⟨fuel, h⟩ := ih restTyped
      exact ⟨fuel + 1, by simpa [Ty.isRow] using h⟩

theorem zero_add_uses (Γ : Context) {y : Uses} (h : y.length = Γ.length) : addUses (zeroUses Γ) y = y :=
  uses_ext (by simp [addUses, zeroUses, h]) fun i => by
    rw [getD_addUses (by simp [zeroUses, h]), getD_zeroUses]; simp

theorem add_assoc_uses {x y z : Uses} (hxy : x.length = y.length) (hyz : y.length = z.length) :
    addUses (addUses x y) z = addUses x (addUses y z) :=
  uses_ext (by simp [addUses, hxy, hyz]) fun i => by
    rw [getD_addUses (by simp [addUses, hxy, hyz]), getD_addUses hxy, getD_addUses (by simp [addUses, hxy, hyz]),
      getD_addUses hyz]; omega

theorem fields_append {a : Assumptions} {Γ : Context} {ys : List (String × Term)} {ry : Ty} {uy : Uses}
    (ysTyped : FieldsTyping a Γ ys ry uy) {xs : List (String × Term)} {rx : Ty} {ux : Uses}
    (typed : FieldsTyping a Γ xs rx ux) : FieldsTyping a Γ (xs ++ ys) (overlay rx ry) (addUses ux uy) := by
  induction xs generalizing rx ux with
  | nil =>
    cases typed
    rw [zero_add_uses Γ (fields_uses_length ysTyped)]
    exact ysTyped
  | cons field rest ih =>
    cases typed with
    | cons bodyTyped restTyped pure =>
      rw [add_assoc_uses ((source_uses_length bodyTyped).trans (fields_uses_length restTyped).symm)
        ((fields_uses_length restTyped).trans (fields_uses_length ysTyped).symm)]
      exact .cons bodyTyped (ih restTyped) pure

theorem fields_filter {a : Assumptions} {Γ : Context} (p : String → Bool) {fields : List (String × Term)} {row : Ty}
    {u : Uses} (typed : FieldsTyping a Γ fields row u) :
    ∃ row' u', FieldsTyping a Γ (fields.filter fun field => p field.1) row' u' ∧ (∀ i, u'.getD i 0 ≤ u.getD i 0) ∧
      ∀ fuel name m, p name = true → row.lookup a.bounds fuel name = some m →
        ∃ depth, row'.lookup a.bounds depth name = some m := by
  induction fields generalizing row u with
  | nil =>
    cases typed
    exact ⟨_, _, .nil Γ, fun i => Nat.le_refl _, fun fuel name m _ lk => by cases fuel <;> simp [Ty.lookup] at lk⟩
  | cons field rest ih =>
    obtain ⟨n, body⟩ := field
    cases typed with
    | cons bodyTyped restTyped pure =>
      rename_i type tail bu ru
      have l := (source_uses_length bodyTyped).trans (fields_uses_length restTyped).symm
      obtain ⟨row', u', hr, le, lk⟩ := ih restTyped
      by_cases pn : p n = true
      · refine ⟨.field n type row', addUses bu u', ?_, ?_, ?_⟩
        · simp only [List.filter_cons, pn, if_true]; exact .cons bodyTyped hr pure
        · intro i
          rw [getD_addUses ((source_uses_length bodyTyped).trans (fields_uses_length hr).symm),
            getD_addUses l]
          have := le i; omega
        · intro fuel name m pm lookup
          cases fuel with
          | zero => simp [Ty.lookup] at lookup
          | succ fuel =>
            by_cases hit : n = name
            · subst hit; simp [Ty.lookup] at lookup; subst lookup; exact ⟨1, by simp [Ty.lookup]⟩
            · simp only [Ty.lookup, if_neg hit] at lookup
              obtain ⟨depth, h⟩ := lk fuel name m pm lookup
              exact ⟨depth + 1, by simp [Ty.lookup, hit, h]⟩
      · refine ⟨row', u', ?_, fun i => Nat.le_trans (le i) (add_le_right l i), ?_⟩
        · simp only [List.filter_cons, pn, Bool.false_eq_true, if_false]; exact hr
        · intro fuel name m pm lookup
          cases fuel with
          | zero => simp [Ty.lookup] at lookup
          | succ fuel =>
            by_cases hit : n = name
            · subst hit; exact absurd pm pn
            · simp only [Ty.lookup, if_neg hit] at lookup
              exact lk fuel name m pm lookup

theorem overlay_lookup_left {a : Assumptions} {Γ : Context} (X : Ty) {fields : List (String × Term)} {row : Ty}
    {u : Uses} (typed : FieldsTyping a Γ fields row u) (fuel : Nat) (name : String) (m : Ty)
    (lookup : row.lookup a.bounds fuel name = some m) : (overlay row X).lookup a.bounds fuel name = some m := by
  induction fields generalizing row u fuel with
  | nil => cases typed; cases fuel <;> simp [Ty.lookup] at lookup
  | cons field rest ih =>
    obtain ⟨n, body⟩ := field
    cases typed with
    | cons bodyTyped restTyped pure =>
      cases fuel with
      | zero => simp [Ty.lookup] at lookup
      | succ fuel =>
        by_cases hit : n = name
        · simpa [overlay, Ty.lookup, hit] using lookup
        · simp only [Ty.lookup, if_neg hit] at lookup
          simp only [overlay, Ty.lookup, if_neg hit]
          exact ih restTyped fuel lookup

theorem overlay_lookup_right {a : Assumptions} {Γ : Context} {X : Ty} {name : String} {m : Ty} {fuel : Nat}
    (lookup : X.lookup a.bounds fuel name = some m) {fields : List (String × Term)} {row : Ty} {u : Uses}
    (typed : FieldsTyping a Γ fields row u) (absent : fields.any (fun field => field.1 == name) = false) :
    ∃ depth, (overlay row X).lookup a.bounds depth name = some m := by
  induction fields generalizing row u with
  | nil => cases typed; exact ⟨fuel, lookup⟩
  | cons field rest ih =>
    obtain ⟨n, body⟩ := field
    cases typed with
    | cons bodyTyped restTyped pure =>
      have facts : n ≠ name ∧ rest.any (fun field => field.1 == name) = false := by
        simpa only [List.any_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] using absent
      obtain ⟨depth, h⟩ := ih restTyped facts.2
      exact ⟨depth + 1, by simp [overlay, Ty.lookup, facts.1, h]⟩

theorem fields_tail {a : Assumptions} {Γ : Context} {fields : List (String × Term)} {row : Ty} {u : Uses}
    (typed : FieldsTyping a Γ fields row u) (X : Ty) : (overlay row X).tail = X.tail := by
  induction fields generalizing row u with
  | nil => cases typed; rfl
  | cons field rest ih => cases typed with | cons _ restTyped _ => simpa [overlay, Ty.tail] using ih restTyped

theorem fields_row_tail {a : Assumptions} {Γ : Context} {fields : List (String × Term)} {row : Ty} {u : Uses}
    (typed : FieldsTyping a Γ fields row u) : row.tail = .emptyRow := by
  induction fields generalizing row u with
  | nil => cases typed; rfl
  | cons field rest ih => cases typed with | cons _ restTyped _ => simpa [Ty.tail] using ih restTyped

theorem overlay_refines {a : Assumptions} {Γ : Context} {fields : List (String × Term)} {row : Ty} {u : Uses}
    (fieldsTyped : FieldsTyping a Γ fields row u) {X X' : Ty} {fuelX : Nat}
    (isRowX : X.isRow a.bounds fuelX = true) (rowX' : TypeGraph.FiniteRow a X')
    (h : ∀ fuel name m, fields.any (fun field => field.1 == name) = false → X.lookup a.bounds fuel name = some m →
      ∃ depth m', X'.lookup a.bounds depth name = some m' ∧ sameType a m' m = true)
    (closedX' : X'.tail = .emptyRow)
    (back : ∀ fuel name m', X'.lookup a.bounds fuel name = some m' → ∃ depth m, X.lookup a.bounds depth name = some m) :
    RowRefines a (overlay row X') (overlay row X) := by
  obtain ⟨f', r'⟩ := rowX'
  refine ⟨fields_overlay_row fieldsTyped X' f' r', fields_overlay_row fieldsTyped X fuelX isRowX, fun fuel name m lk => ?_,
    by rw [fields_tail fieldsTyped]; exact closedX', fun fuel name m' lk => ?_⟩
  · rcases fields_overlay_lookup fieldsTyped X fuel name m lk with ⟨depth, hr⟩ | ⟨absent, depth, hx⟩
    · exact ⟨depth, m, overlay_lookup_left X' fieldsTyped depth name m hr, sameType_refl _ _⟩
    · obtain ⟨depth', m', hx', s⟩ := h depth name m absent hx
      obtain ⟨depth'', h''⟩ := overlay_lookup_right hx' fieldsTyped absent
      exact ⟨depth'', m', h'', s⟩
  · rcases fields_overlay_lookup fieldsTyped X' fuel name m' lk with ⟨depth, hr⟩ | ⟨absent, depth, hx⟩
    · exact ⟨depth, m', overlay_lookup_left X fieldsTyped depth name m' hr⟩
    · obtain ⟨depth', m, hx'⟩ := back depth name m' hx
      obtain ⟨depth'', h''⟩ := overlay_lookup_right hx' fieldsTyped absent
      exact ⟨depth'', m, h''⟩


/-! ### Redexes -/

theorem arms_find_typed {a : Assumptions} {Γ : Context} {l : String} {body : Term} {q : Quantity}
    {arms : List (String × Term)} {row result : Ty} {au : Uses} (typed : ArmsTyping a Γ q arms row result au)
    (found : arms.find? (fun arm => arm.1 == l) = some (l, body)) : ∃ payload bu fuel,
      PartialTyping a (⟨payload, q⟩ :: Γ) body result bu ∧ q.fits (bu.headD 0) = true ∧
      (∀ i, bu.tail.getD i 0 ≤ au.getD i 0) ∧ row.lookup a.bounds fuel l = some payload := by
  induction arms generalizing row au with
  | nil => simp at found
  | cons arm rest ih =>
    obtain ⟨name, b⟩ := arm
    cases typed with
    | cons hb safe share fits restTyped agreeing =>
      rename_i payload row' bu ru
      have bl : bu.tail.length = Γ.length := by simp [source_uses_length hb]
      have rl := arms_uses_length restTyped
      by_cases hit : name = l
      · subst hit
        simp at found; subst found
        exact ⟨payload, bu, 1, hb, fits, join_le_left (bl.trans rl.symm), by simp [Ty.lookup]⟩
      · have hn : (name == l) = false := by simpa using hit
        rw [List.find?_cons, hn] at found
        obtain ⟨payload', bu', fuel, hb', fits', le, lk⟩ := ih restTyped found
        exact ⟨payload', bu', fuel + 1, hb', fits', fun i => Nat.le_trans (le i) (join_le_right (bl.trans rl.symm) i),
          by simp [Ty.lookup, hit, lk]⟩

theorem allowed_parts {a : Assumptions} {q : Quantity} {Γ : Context} {X : Ty} {u : Uses}
    (allowed : argumentAllowed a q Γ X u = true) :
    (q = .linear ∨ linearFree Γ u = true) ∧ (q = .unrestricted → reusableCaptures a.shareableVariables Γ u = true) := by
  simp only [argumentAllowed, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at allowed
  obtain ⟨⟨_, lin⟩, unr⟩ := allowed
  exact ⟨lin, fun q' => by rcases unr with n | ⟨_, cap⟩; exact absurd q' n; exact cap⟩

theorem caseAllowed_parts {a : Assumptions} {q : Quantity} {Γ : Context} {u : Uses}
    (allowed : caseAllowed a q Γ u = true) :
    (q = .linear ∨ linearFree Γ u = true) ∧ (q = .unrestricted → reusableCaptures a.shareableVariables Γ u = true) := by
  simp only [caseAllowed, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at allowed
  obtain ⟨lin, unr⟩ := allowed
  exact ⟨lin, fun q' => by rcases unr with n | cap; exact absurd q' n; exact cap⟩

theorem fits_le {q : Quantity} {n : Nat} (fits : q.fits n = true) (qu : q ≠ .unrestricted) : n ≤ 1 := by
  cases q <;> simp [Quantity.fits] at fits qu ⊢ <;> omega

/-- The binder of a redex is used at most once unless it is `unrestricted`, in which case the
argument's captures are reusable: at a position that is not `unrestricted`, the substituted count
is at most the redex's. -/
theorem redex_le {V : List Nat} {Γ : Context} {q : Quantity} {ub ua : Uses} (fits : q.fits (ub.headD 0) = true)
    (unr : q = .unrestricted → reusableCaptures V Γ ua = true) {j : Nat} {b : Binding} (hb : Γ[j]? = some b)
    (nu : b.quantity ≠ .unrestricted) :
    ub.getD (j + 1) 0 + ub.getD 0 0 * ua.getD j 0 ≤ ub.getD (j + 1) 0 + ua.getD j 0 := by
  rw [headD_getD] at fits
  by_cases qu : q = .unrestricted
  · rcases (captures_iff.mp (unr qu)).2 j b hb with z | r
    · rw [z]; simp
    · exact absurd r.1 nu
  · have h1 := fits_le fits qu
    have := Nat.mul_le_mul_right (ua.getD j 0) h1
    omega

/-- Instantiation, typed. -/
theorem instantiate_typed {a : Assumptions} {Γ : Context} {x : Binding} {body A : Term} {T : Ty} {ub ua : Uses}
    (bodyTyped : PartialTyping a (x :: Γ) body T ub) (argTyped : PartialTyping a Γ A x.type ua)
    (lin : x.quantity = .linear ∨ linearFree Γ ua = true)
    (unr : x.quantity = .unrestricted → reusableCaptures a.shareableVariables Γ ua = true)
    (budget : ∀ j b, Γ[j]? = some b → safeQuantity b.quantity (ub.getD (j + 1) 0 + ub.getD 0 0 * ua.getD j 0) = true) :
    ∃ u', PartialTyping a Γ (instantiate body A) T u' ∧ ∀ j, u'.getD j 0 ≤ ub.getD (j + 1) 0 + ub.getD 0 0 * ua.getD j 0 := by
  have S : TSub a (x :: Γ) 0 (fun index => match index with | 0 => A | n + 1 => .bound n) A ua :=
    ⟨substAt_instantiate A, x, rfl, by simpa using argTyped, by simpa using lin, by simpa using unr⟩
  have B : Budget (x :: Γ) 0 ua ub := by
    intro j b hb
    rw [image_zero_index, getD_tail]
    exact budget j b (by simpa using hb)
  obtain ⟨u', h, le⟩ := subst_typed bodyTyped 0 _ _ _ S B
  simp only [List.eraseIdx_cons_zero] at h
  refine ⟨u', h, fun j => ?_⟩
  have := le j
  rwa [image_zero_index, getD_tail] at this

theorem primitive_typed {a : Assumptions} {Γ : Context} {p : Primitive} {l r res : Term} {input output : Ty}
    (types : primitiveTypes p = (input, output)) (h : primitiveResult p l r = some res) :
    PartialTyping a Γ res output (zeroUses Γ) := by
  unfold primitiveResult at h
  split at h <;> (try cases h) <;> simp [primitiveTypes] at types <;> (obtain ⟨-, rfl⟩ := types) <;>
    first | exact .natural Γ _ | exact .boolean Γ _

theorem primitive_input {p : Primitive} {input output : Ty} (types : primitiveTypes p = (input, output)) :
    rowSyntax input = false ∧ input.isComputation = false := by
  cases p <;> simp [primitiveTypes] at types <;> (obtain ⟨rfl, rfl⟩ := types) <;> exact ⟨rfl, rfl⟩

theorem callable_rowSyntax {T : Ty} {r : Reuse} {q : Quantity} {D C : Ty} (h : callable T = .arrow r q D C) :
    rowSyntax T = false := by
  cases T <;> simp [callable] at h <;> rfl

theorem shareable_not_computation {V : List Nat} {T : Ty} (h : T.shareableUnder V = true) :
    T.isComputation = false := by
  cases T <;> simp_all [Ty.shareableUnder, Ty.shareable, Ty.isComputation]

theorem captures_zero (V : List Nat) (Γ : Context) : reusableCaptures V Γ (zeroUses Γ) = true :=
  captures_iff.mpr ⟨by simp [zeroUses], fun j _ _ => .inl (getD_zeroUses Γ j)⟩

/-! ### Subject reduction -/

/-- The reduct's type `T'`, relative to the redex's `T`: the same up to `sameType`; a row answering
every lookup of `T` (`extendRecord` drops shadowed fields); or, at the root `done` redex, the
result type of the computation. -/
@[expose] public def Retyped (a : Assumptions) (t t' : Term) (T' T : Ty) : Prop :=
  sameType a T' T = true ∨ RowRefines a T' T ∨ (t = .done t' ∧ ∃ P R, sameType a (.computation P R T') T = true)

theorem retyped_conv {a : Assumptions} {t t' : Term} {T' T T2 : Ty} (r : Retyped a t t' T' T)
    (s : sameType a T T2 = true) : Retyped a t t' T' T2 := by
  rcases r with e | r | ⟨e, P, R, d⟩
  · exact .inl (sameType_trans e s)
  · exact .inr (.inl (r.trans_same s))
  · exact .inr (.inr ⟨e, P, R, sameType_trans d s⟩)

/-- A subterm in a position whose type is neither a row nor an activity keeps its type. -/
theorem congr_fixed {a : Assumptions} {Γ : Context} {s s' : Term} {S : Ty} {u : Uses}
    (h : ∃ T' u', PartialTyping a Γ s' T' u' ∧ Below Γ u' u ∧ Retyped a s s' T' S)
    (nr : rowSyntax S = false) (pure : S.isComputation = false) :
    ∃ u', PartialTyping a Γ s' S u' ∧ Below Γ u' u := by
  obtain ⟨T', u', h, b, r⟩ := h
  rcases r with e | r | ⟨_, P, R, d⟩
  · exact ⟨u', .conversion h e, b⟩
  · exact (not_row nr r.2.1).elim
  · exact (done_absurd d pure).elim

/-! ### The destructor -/

theorem spine_lookup {bounds : Bounds} : ∀ {row : Ty} {name : String}, name ∈ spineLabels row →
    ∃ fuel member, row.lookup bounds fuel name = some member
  | .field prior m tail, name, h => by
    by_cases hit : prior = name
    · exact ⟨1, m, by simp [Ty.lookup, hit]⟩
    · simp only [spineLabels, List.mem_cons] at h
      rcases h with e | h
      · exact (hit e.symm).elim
      · obtain ⟨fuel, member, l⟩ := spine_lookup (bounds := bounds) h
        exact ⟨fuel + 1, member, by simp [Ty.lookup, hit, l]⟩
  | .natural, _, h | .label, _, h | .boolean, _, h | .variable _, _, h | .arrow _ _ _ _, _, h
  | .emptyRow, _, h | .specification _ _, _, h | .prototype _ _, _, h | .custody _, _, h | .variant _, _, h
  | .computation _ _ _, _, h => by simp [spineLabels] at h

/-- A destructor that covers a row covers every row that refines it. -/
theorem covers_refine {a : Assumptions} {T' row : Ty} {names : List String} (r : RowRefines a T' row)
    (covers : SplitCovers row names = true) : SplitCovers T' names = true := by
  obtain ⟨_, _, _, closed', back⟩ := r
  simp only [SplitCovers, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at covers ⊢
  refine ⟨closed', fun name mem => ?_⟩
  obtain ⟨fuel, m', l'⟩ := spine_lookup (bounds := a.bounds) mem
  obtain ⟨depth, m, l⟩ := back fuel name m' l'
  exact covers.2 name (closed_lookup_spine covers.1 l)

/-- A destructor's spine over a row holds over every row that refines it. -/
theorem spine_refine {a : Assumptions} {Γ : Context} {u : Uses} {T' row : Ty} (r : RowRefines a T' row) :
    ∀ {names : List String} {functionType result : Ty},
      SplitSpine a Γ u row names functionType result → SplitSpine a Γ u T' names functionType result
  | [], _, _, h => h
  | _ :: _, _, _, ⟨rr, q, m, c, shape, ⟨fuel, found, l, same⟩, pure, allowed, share, rest⟩ => by
    obtain ⟨depth, found', l', same'⟩ := r.2.2.1 fuel _ found l
    exact ⟨rr, q, m, c, shape, ⟨depth, found', l', sameType_trans same' same⟩, pure, allowed, share,
      spine_refine r rest⟩

/-- The destructor's reduct, typed: each value is its field's body, typed at its parameter's member. -/
theorem split_apply_typed {a : Assumptions} {Γ : Context} {fields : List (String × Term)} {row' row : Ty} {tu : Uses}
    (hf : FieldsTyping a Γ fields row' tu) (s : sameType a row' row = true)
    (valid : validContext a.shareableVariables Γ = true) :
    ∀ {names : List String} {functionType result : Ty} {function : Term} {fu : Uses} {values : List Term},
      SplitSpine a Γ tu row names functionType result → PartialTyping a Γ function functionType fu →
      splitValues fields names = some values → ∃ u', PartialTyping a Γ (applyAll function values) result u'
  | [], _, _, _, fu, values, spine, hfun, found => by
    simp [splitValues] at found; subst found; cases spine; exact ⟨fu, hfun⟩
  | name :: names, _, _, function, fu, values, ⟨rr, q, m, c, shape, ⟨fuel, found, l, same⟩, noAct, allowed, share, rest⟩,
      hfun, hv => by
    simp only [splitValues, bind, Option.bind] at hv
    split at hv
    · cases hv
    · rename_i pair hp
      obtain ⟨label, value⟩ := pair
      simp only at hv
      split at hv
      · cases hv
      · rename_i vs hvs
        simp only [pure, Option.some.injEq] at hv
        subst hv
        obtain ⟨depth, m0, l0, s0⟩ := same_type_lookup_transport s fuel name found l
        obtain ⟨body, bu, found', hb, le⟩ := fields_lookup hf depth name m0 l0
        have hl : label = name := by have := List.find?_some hp; simpa using this
        subst hl
        rw [hp] at found'; cases found'
        have len := source_uses_length hb
        have below : Below Γ bu tu := below_of_le le
        obtain ⟨lin, unr⟩ := caseAllowed_parts allowed
        have argAllowed : argumentAllowed a q Γ m bu = true := by
          simp only [argumentAllowed, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
            Bool.not_eq_true']
          refine ⟨⟨noAct, lin.imp id (fun free => linearFree_below free len below)⟩, ?_⟩
          by_cases qu : q = .unrestricted
          · subst qu; simp [validContext] at share
            exact .inr ⟨share.1, captures_below valid (unr rfl) len below⟩
          · exact .inl qu
        have happ : PartialTyping a Γ (.app function value) c (addUses fu bu) :=
          .application hfun (.conversion hb (sameType_trans s0 same)) shape rfl argAllowed
        obtain ⟨u', h⟩ := split_apply_typed hf s valid rest happ hvs
        exact ⟨u', by simpa [applyAll] using h⟩

theorem step_typed {a : Assumptions} {Γ : Context} {t : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a Γ t T u) : validContext a.shareableVariables Γ = true → safeUses Γ u = true →
      ∀ t', Step t t' → ∃ T' u', PartialTyping a Γ t' T' u' ∧ Below Γ u' u ∧ Retyped a t t' T' T := by
  apply PartialTyping.rec
    (motive_1 := fun Γ t T u _ => validContext a.shareableVariables Γ = true → safeUses Γ u = true →
      ∀ t', Step t t' → ∃ T' u', PartialTyping a Γ t' T' u' ∧ Below Γ u' u ∧ Retyped a t t' T' T)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := typed)
  case conversion =>
    intro Γ term actual expected u prior same ih valid safe t' step
    obtain ⟨T', u', h, b, r⟩ := ih valid safe t' step
    exact ⟨T', u', h, b, retyped_conv r same⟩
  case application =>
    intro Γ fn arg functionType argumentType domain codomain fu au reuse quantity fnTyped argTyped
      callableEq same allowed ihFn ihArg valid safe t' step
    have fl := source_uses_length fnTyped
    have al := source_uses_length argTyped
    cases step with
    | application argument s' =>
      obtain ⟨fu', hf, bf⟩ := congr_fixed (ihFn valid (safe_mono safe fl (add_le_left (fl.trans al.symm))) _ s')
        (callable_rowSyntax callableEq) (callable_arrow_not_computation callableEq)
      exact ⟨codomain, _, .application hf argTyped callableEq same allowed,
        below_add_left bf ((source_uses_length hf).trans al.symm) (fl.trans al.symm), .inl (sameType_refl _ _)⟩
    | beta body _ =>
      obtain ⟨ann, ub, hb, fits, vb, same', eq⟩ := lam_inv fnTyped
      have ft := closure_callable_type ((sameType_iff a _ _).mp same') callableEq
      rw [ft] at same'
      obtain ⟨_, q, hd, hc⟩ := TypeGraph.arrow_components ((sameType_iff a _ _).mp same')
      subst eq
      have argT : PartialTyping a Γ arg ann.domain au :=
        .conversion argTyped (by rw [same]; exact sameType_symm ((sameType_iff a _ _).mpr hd))
      obtain ⟨lin, unr⟩ := allowed_parts allowed
      rw [← q] at lin unr
      have ul : ub.tail.length = au.length := fl.trans al.symm
      have bnd : ∀ j b, Γ[j]? = some b → b.quantity ≠ .unrestricted →
          ub.getD (j + 1) 0 + ub.getD 0 0 * au.getD j 0 ≤ (addUses ub.tail au).getD j 0 := fun j b hb nu => by
        rw [getD_addUses ul, getD_tail]; exact redex_le fits unr hb nu
      obtain ⟨u', h, le⟩ := instantiate_typed hb argT lin unr (fun j b hbj => by
        by_cases nu : b.quantity = .unrestricted
        · rw [nu]; rfl
        · exact safeQuantity_mono ((safeUses_iff.mp safe).2 j b hbj) (bnd j b hbj nu))
      exact ⟨codomain, u', .conversion h ((sameType_iff a _ _).mpr hc),
        fun j b hbj nu => Nat.le_trans (le j) (bnd j b hbj nu), .inl (sameType_refl _ _)⟩
    | applySpecification m e _ =>
      obtain ⟨M, E, mu, eu, hm, he, free, rfl, s⟩ := specification_inv' fnTyped
      obtain ⟨M0, E0, rfl⟩ := specification_callable_type ((sameType_iff a _ _).mp s) callableEq
      obtain ⟨_, hE⟩ := TypeGraph.specification_components ((sameType_iff a _ _).mp s)
      have he' : PartialTyping a Γ e E0 eu := .conversion he ((sameType_iff a _ _).mpr hE)
      have ml := source_uses_length hm
      have el := source_uses_length he
      refine ⟨codomain, _, .application he' argTyped callableEq same allowed, below_of_le fun i => ?_,
        .inl (sameType_refl _ _)⟩
      rw [getD_addUses (el.trans al.symm), getD_addUses (by simp [addUses, ml, el, al]), getD_addUses (ml.trans el.symm)]
      omega
  case get =>
    intro Γ target targetType member uses name fuel targetTyped lookup free ih valid safe t' step
    cases step with
    | target _ s' =>
      obtain ⟨T', u', h, b, r⟩ := ih valid safe _ s'
      have free' := linearFree_below free (source_uses_length h) b
      rcases r with e | r | ⟨rfl, P, R, d⟩
      · exact ⟨member, u', .get (.conversion h e) lookup free', b, .inl (sameType_refl _ _)⟩
      · obtain ⟨depth, m', lk, sm⟩ := r.2.2.1 fuel name member lookup
        exact ⟨member, u', .conversion (.get h lk free') sm, b, .inl (sameType_refl _ _)⟩
      · exact (done_absurd d (lookup_not_computation _ _ _ _ _ lookup)).elim
    | field fields _ body found =>
      obtain ⟨row0, hf, s⟩ := record_inv' targetTyped
      obtain ⟨depth, m0, lk0, sm⟩ := same_type_lookup_transport s fuel name member lookup
      obtain ⟨body', bu, found', hb, le⟩ := fields_lookup hf depth name m0 lk0
      rw [found] at found'; cases found'
      exact ⟨member, bu, .conversion hb sm, below_of_le le, .inl (sameType_refl _ _)⟩
  case extend =>
    intro Γ target fields targetType row tu fu rowFuel targetTyped fieldsTyped distinct isRow free ihTarget ihFields
      valid safe t' step
    have tl := source_uses_length targetTyped
    have fl := fields_uses_length fieldsTyped
    cases step with
    | extendTarget _ s' =>
      obtain ⟨T', u', h, b, r⟩ := ihTarget valid (safe_mono safe tl (add_le_left (tl.trans fl.symm))) _ s'
      have len := source_uses_length h
      have free' := linearFree_below free len b
      have bb := below_add_left b (len.trans fl.symm) (tl.trans fl.symm)
      rcases r with e | r | ⟨rfl, P, R, d⟩
      · exact ⟨_, _, .extend (.conversion h e) fieldsTyped distinct isRow free', bb, .inl (sameType_refl _ _)⟩
      · obtain ⟨⟨f', r'⟩, _, hl, tl, back⟩ := r
        exact ⟨_, _, .extend h fieldsTyped distinct r' free', bb,
          .inr (.inl (overlay_refines fieldsTyped isRow ⟨f', r'⟩ (fun fuel name m _ lk => hl fuel name m lk) tl back))⟩
      · exact (done_absurd d (isRow_not_computation _ _ _ isRow)).elim
    | extendRecord inherited _ =>
      obtain ⟨row0, hi, s, inheritedDistinct⟩ := record_inv_same targetTyped
      obtain ⟨rowF, uF, hF, leF, lkF⟩ := fields_filter (fun n => !(fields.any fun field => field.1 == n)) hi
      have happ := fields_append hF fieldsTyped
      have uFl := fields_uses_length hF
      refine ⟨overlay row rowF, addUses fu uF, .record happ (labelsDistinct_extendFields inheritedDistinct distinct),
        below_of_le fun i => ?_, .inr (.inl ?_)⟩
      · rw [getD_addUses (fl.trans uFl.symm), getD_addUses (tl.trans fl.symm)]; have := leF i; omega
      · refine overlay_refines fieldsTyped isRow (fields_isRow hF) (fun fuel name m absent lk => ?_)
          (fields_row_tail hF) (fun fuel name m' lk => ?_)
        · obtain ⟨depth, m0, lk0, sm⟩ := same_type_lookup_transport s fuel name m lk
          obtain ⟨depth', lk'⟩ := lkF depth name m0 (by simp [absent]) lk0
          exact ⟨depth', m0, lk', sm⟩
        · obtain ⟨body, bu, found, _, _⟩ := fields_lookup hF fuel name m' lk
          have mem := List.mem_of_find?_eq_some found
          obtain ⟨depth, m0, lk0⟩ := fields_member_lookup hi _ (List.mem_filter.mp mem).1
          obtain ⟨depth', m1, lk1, _⟩ := same_type_lookup_transport (sameType_symm s) depth name m0 lk0
          exact ⟨depth', m1, lk1⟩
  case reflect =>
    intro Γ target specType targetType uses prior free ih valid safe t' step
    cases step with
    | reflectPrototype spec target' =>
      obtain ⟨S, T0, su, tu, hs, ht, rfl, s⟩ := prototype_inv' prior
      obtain ⟨hS, _⟩ := TypeGraph.prototype_components ((sameType_iff a _ _).mp s)
      exact ⟨specType, su, .conversion hs ((sameType_iff a _ _).mpr hS),
        below_of_le (add_le_left ((source_uses_length hs).trans (source_uses_length ht).symm)), .inl (sameType_refl _ _)⟩
    | reflectStep s' =>
      obtain ⟨u', h, b⟩ := congr_fixed (ih valid safe _ s') rfl rfl
      exact ⟨specType, u', .reflect h (linearFree_below free (source_uses_length h) b), b, .inl (sameType_refl _ _)⟩
  case metadata =>
    intro Γ target metadataType extensionType uses prior free ih valid safe t' step
    cases step with
    | metadataSpecification m e =>
      obtain ⟨M, E, mu, eu, hm, he, mfree, rfl, s⟩ := specification_inv' prior
      obtain ⟨hM, _⟩ := TypeGraph.specification_components ((sameType_iff a _ _).mp s)
      exact ⟨metadataType, mu, .conversion hm ((sameType_iff a _ _).mpr hM),
        below_of_le (add_le_left ((source_uses_length hm).trans (source_uses_length he).symm)), .inl (sameType_refl _ _)⟩
    | metadataStep s' =>
      obtain ⟨u', h, b⟩ := congr_fixed (ih valid safe _ s') rfl rfl
      exact ⟨metadataType, u', .metadata h (linearFree_below free (source_uses_length h) b), b, .inl (sameType_refl _ _)⟩
  case project =>
    intro Γ target specType targetType uses prior free ih valid safe t' step
    cases step with
    | projectPrototype spec target' =>
      obtain ⟨S, T0, su, tu, hs, ht, rfl, s⟩ := prototype_inv' prior
      obtain ⟨_, hT⟩ := TypeGraph.prototype_components ((sameType_iff a _ _).mp s)
      exact ⟨targetType, tu, .conversion ht ((sameType_iff a _ _).mpr hT),
        below_of_le (add_le_right ((source_uses_length hs).trans (source_uses_length ht).symm)), .inl (sameType_refl _ _)⟩
    | projectStep s' =>
      obtain ⟨u', h, b⟩ := congr_fixed (ih valid safe _ s') rfl rfl
      exact ⟨targetType, u', .project h (linearFree_below free (source_uses_length h) b), b, .inl (sameType_refl _ _)⟩
  case mix =>
    intro Γ lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped
      lowerCallable upperCallable captures selfShare inheritedShare middleShare ihL ihU valid safe t' step
    cases step with
    | mix =>
      let R := reusable_mix_body lowerTyped upperTyped lowerCallable upperCallable captures selfShare inheritedShare
        middleShare valid
      exact ⟨_, R.uses, R.derivation, captures_zero_below R.captures, .inl (sameType_refl _ _)⟩
  case fix =>
    intro Γ spec inheritedTerm specType inherited target su iu specTyped callableEq inheritedTyped targetShare
      inheritedAllowed captures ihS ihI valid safe t' step
    cases step with
    | fix =>
      have fixTyped := PartialTyping.fix specTyped callableEq inheritedTyped targetShare inheritedAllowed captures
      have icap := (allowed_parts inheritedAllowed).2 rfl
      have cap := captures_add captures icap
      have allowed1 : argumentAllowed a .unrestricted Γ target (addUses su iu) = true := by
        simp [argumentAllowed, shareable_not_computation targetShare, linearFree_of_reusableCaptures cap, targetShare, cap]
      have inner := PartialTyping.application specTyped fixTyped callableEq rfl allowed1
      have outer := PartialTyping.application inner inheritedTyped rfl rfl inheritedAllowed
      exact ⟨target, _, outer, captures_zero_below (captures_add (captures_add captures cap) icap),
        .inl (sameType_refl _ _)⟩
  case binary =>
    intro Γ primitive left right input output lu ru primitiveEq leftTyped rightTyped ihL ihR valid safe t' step
    have ll := source_uses_length leftTyped
    have rl := source_uses_length rightTyped
    obtain ⟨nr, pure⟩ := primitive_input primitiveEq
    cases step with
    | binaryLeft _ _ s' =>
      obtain ⟨lu', hl, b⟩ := congr_fixed (ihL valid (safe_mono safe ll (add_le_left (ll.trans rl.symm))) _ s') nr pure
      exact ⟨output, _, .binary primitiveEq hl rightTyped,
        below_add_left b ((source_uses_length hl).trans rl.symm) (ll.trans rl.symm), .inl (sameType_refl _ _)⟩
    | binaryRight _ _ _ s' =>
      obtain ⟨ru', hr, b⟩ := congr_fixed (ihR valid (safe_mono safe rl (add_le_right (ll.trans rl.symm))) _ s') nr pure
      exact ⟨output, _, .binary primitiveEq leftTyped hr,
        below_add_right b (ll.trans (source_uses_length hr).symm) (ll.trans rl.symm), .inl (sameType_refl _ _)⟩
    | primitive _ _ _ _ _ _ h =>
      exact ⟨output, _, primitive_typed primitiveEq h,
        below_of_le fun i => by rw [getD_zeroUses]; exact Nat.zero_le _, .inl (sameType_refl _ _)⟩
  case ifZero =>
    intro Γ value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe agreeing
      ihV ihZ ihS valid safe t' step
    have vl := source_uses_length valueTyped
    have zl := source_uses_length zeroTyped
    have sl : su.tail.length = Γ.length := by simp [source_uses_length successorTyped]
    have jl : vu.length = (joinUses zu su.tail).length := by simp [joinUses, vl, zl, sl]
    cases step with
    | condition _ _ s' =>
      obtain ⟨vu', hv, b⟩ := congr_fixed (ihV valid (safe_mono safe vl (add_le_left jl)) _ s') rfl rfl
      exact ⟨result, _, .ifZero hv zeroTyped successorTyped successorSafe agreeing,
        below_add_left b ((source_uses_length hv).trans (vl.symm.trans jl)) jl, .inl (sameType_refl _ _)⟩
    | zero _ _ =>
      exact ⟨result, zu, zeroTyped,
        below_of_le fun i => Nat.le_trans (join_le_left (zl.trans sl.symm) i) (add_le_right jl i), .inl (sameType_refl _ _)⟩
    | successor n _ _ =>
      have bnd : ∀ j, su.getD (j + 1) 0 + su.getD 0 0 * (zeroUses Γ).getD j 0 ≤
          (addUses vu (joinUses zu su.tail)).getD j 0 := fun j => by
        rw [getD_zeroUses, Nat.mul_zero, Nat.add_zero, ← getD_tail]
        exact Nat.le_trans (join_le_right (zl.trans sl.symm) j) (add_le_right jl j)
      obtain ⟨u', h, le⟩ := instantiate_typed successorTyped (PartialTyping.natural Γ n)
        (.inr (linearFree_zeroUses Γ)) (fun _ => captures_zero _ Γ)
        (fun j b hb => safeQuantity_mono ((safeUses_iff.mp safe).2 j b hb) (bnd j))
      exact ⟨result, u', h, below_of_le fun j => Nat.le_trans (le j) (bnd j), .inl (sameType_refl _ _)⟩
  case case =>
    intro Γ scrutinee arms row result su au q scrutineeTyped armsTyped distinct allowed ihS ihA valid safe t' step
    have sl := source_uses_length scrutineeTyped
    have al := arms_uses_length armsTyped
    have l := sl.trans al.symm
    cases step with
    | caseTarget _ s' =>
      obtain ⟨su', hs, b⟩ := congr_fixed (ihS valid (safe_mono safe sl (add_le_left l)) _ s') rfl rfl
      exact ⟨result, _, .case hs armsTyped distinct (caseAllowed_below valid allowed (source_uses_length hs) b),
        below_add_left b ((source_uses_length hs).trans al.symm) l, .inl (sameType_refl _ _)⟩
    | caseInject lbl p _ body found =>
      obtain ⟨P, row0, fuel0, hp, lk0, s⟩ := inject_inv' scrutineeTyped
      obtain ⟨payload, bu, fuel1, hb, fits, le, lk1⟩ := arms_find_typed armsTyped found
      have hrow := TypeGraph.variant_components ((sameType_iff a _ _).mp s)
      obtain ⟨depth, m, lkm, sm⟩ := same_type_lookup_transport ((sameType_iff a _ _).mpr hrow) fuel1 lbl payload lk1
      have e := lookup_det lk0 lkm
      subst e
      obtain ⟨lin, unr⟩ := caseAllowed_parts allowed
      have bnd : ∀ j b, Γ[j]? = some b → b.quantity ≠ .unrestricted →
          bu.getD (j + 1) 0 + bu.getD 0 0 * su.getD j 0 ≤ (addUses su au).getD j 0 := fun j b hb nu => by
        rw [getD_addUses l]
        have := redex_le fits unr hb nu
        have := le j
        rw [getD_tail] at this; omega
      obtain ⟨u', h, le'⟩ := instantiate_typed (x := ⟨payload, q⟩) hb (.conversion hp sm) lin unr (fun j b hbj => by
        by_cases nu : b.quantity = .unrestricted
        · rw [nu]; rfl
        · exact safeQuantity_mono ((safeUses_iff.mp safe).2 j b hbj) (bnd j b hbj nu))
      exact ⟨result, u', h, fun j b hbj nu => Nat.le_trans (le' j) (bnd j b hbj nu), .inl (sameType_refl _ _)⟩
  case ifBool =>
    intro Γ condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped agreeing
      ihC ihT ihF valid safe t' step
    have cl := source_uses_length conditionTyped
    have tl := source_uses_length trueTyped
    have fl := source_uses_length falseTyped
    have jl : cu.length = (joinUses tu fu).length := by simp [joinUses, cl, tl, fl]
    cases step with
    | ifCondition _ _ s' =>
      obtain ⟨cu', hc, b⟩ := congr_fixed (ihC valid (safe_mono safe cl (add_le_left jl)) _ s') rfl rfl
      exact ⟨result, _, .ifBool hc trueTyped falseTyped agreeing,
        below_add_left b ((source_uses_length hc).trans (cl.symm.trans jl)) jl, .inl (sameType_refl _ _)⟩
    | ifTrue _ _ =>
      exact ⟨result, tu, trueTyped,
        below_of_le fun i => Nat.le_trans (join_le_left (tl.trans fl.symm) i) (add_le_right jl i), .inl (sameType_refl _ _)⟩
    | ifFalse _ _ =>
      exact ⟨result, fu, falseTyped,
        below_of_le fun i => Nat.le_trans (join_le_right (tl.trans fl.symm) i) (add_le_right jl i), .inl (sameType_refl _ _)⟩
  case split =>
    intro Γ target function names row functionType result tu fu targetTyped functionTyped nodup covers spine
      ihT ihF valid safe t' step
    have tl := source_uses_length targetTyped
    have fl := source_uses_length functionTyped
    cases step with
    | splitTarget _ _ s' =>
      obtain ⟨T', u', h, b, r⟩ := ihT valid (safe_mono safe tl (add_le_left (tl.trans fl.symm))) _ s'
      have len := source_uses_length h
      have spine' := spine.transport fun q allowed => caseAllowed_below valid allowed len b
      have bb := below_add_left b (len.trans fl.symm) (tl.trans fl.symm)
      rcases r with e | r | ⟨rfl, P, R, d⟩
      · exact ⟨_, _, .split (.conversion h e) functionTyped nodup covers spine', bb, .inl (sameType_refl _ _)⟩
      · exact ⟨_, _, .split h functionTyped nodup (covers_refine r covers) (spine_refine r spine'), bb,
          .inl (sameType_refl _ _)⟩
      · have closed : row.tail = .emptyRow := by
          simp only [SplitCovers, Bool.and_eq_true, beq_iff_eq] at covers; exact covers.1
        exact (done_absurd d (Obend.Core.Proofs.Preservation.tail_empty_not_computation closed)).elim
    | splitRecord fields _ _ values found =>
      obtain ⟨row', hf, s, _⟩ := record_inv_same targetTyped
      obtain ⟨u', h⟩ := split_apply_typed hf s valid spine functionTyped found
      obtain ⟨distinct, covered⟩ := record_covered targetTyped covers
      refine ⟨result, u', h, below_of_le fun j => ?_, .inl (sameType_refl _ _)⟩
      have counts := split_redex_counts Γ.length j function distinct nodup covered found
      rw [← uses_determined h] at counts
      have targetOcc := occ_of targetTyped j
      simp only [occurrences] at targetOcc
      rw [counts, occ_of functionTyped, targetOcc, getD_addUses (tl.trans fl.symm)]; omega
  case done =>
    intro Γ value planType response result uses valueTyped pure ih valid safe t' step
    cases step with
    | done _ =>
      exact ⟨result, uses, valueTyped, below_of_le fun _ => Nat.le_refl _,
        .inr (.inr ⟨rfl, planType, response, sameType_refl _ _⟩)⟩
  case effectCase =>
    intro Γ scrutinee arms planType response row result su au q scrutineeTyped armsTyped pure distinct allowed
      ihS ihA valid safe t' step
    have sl := source_uses_length scrutineeTyped
    have al := arms_uses_length armsTyped
    have l := sl.trans al.symm
    cases step with
    | caseTarget _ s' =>
      obtain ⟨T', su', hs, b, r⟩ := ihS valid (safe_mono safe sl (add_le_left l)) _ s'
      have allowed' := caseAllowed_below valid allowed (source_uses_length hs) b
      have bb := below_add_left b ((source_uses_length hs).trans al.symm) l
      rcases r with e | r | ⟨rfl, P, R, d⟩
      · exact ⟨_, _, .effectCase (.conversion hs e) armsTyped pure distinct allowed', bb, .inl (sameType_refl _ _)⟩
      · exact (not_row rfl r.2.1).elim
      · obtain ⟨_, _, hx⟩ := computation_same_type_inj d
        exact ⟨_, _, .case (.conversion hs hx) armsTyped distinct allowed', bb, .inl (sameType_refl _ _)⟩
    | caseInject l p _ body found =>
      obtain ⟨P, row0, fuel0, hp, lk0, s⟩ := inject_inv' scrutineeTyped
      exact (variant_not_activity s).elim
  all_goals (intros; first | trivial | (rename_i st; cases st))


/-- **Source subject reduction.** A `Step` from a term that checks in `Γ` (valid, and within its
`safeUses` budget) checks again in `Γ`, within the budget, using no position that is not
`unrestricted` more often (`Below`) and every `linear` one exactly as often. Its type is the old
one up to `sameType`, except that `extendRecord` (possibly under `extendTarget` congruences) may
type the new record at a row that answers every lookup of the old type (`RowRefines`), and the root
`done` redex returns its value at the computation's result type. -/
public theorem step_preserves_typing {a : Assumptions} {Γ : Context} {t : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a Γ t T u) (valid : validContext a.shareableVariables Γ = true)
    (safe : safeUses Γ u = true) {t' : Term} (step : Step t t') :
    ∃ T' u', PartialTyping a Γ t' T' u' ∧ safeUses Γ u' = true ∧ Below Γ u' u ∧
      (∀ j, LinearAt Γ j → u'.getD j 0 = u.getD j 0) ∧
      (sameType a T' T = true ∨ RowRefines a T' T ∨
        (t = .done t' ∧ ∃ P R, sameType a (.computation P R T') T = true)) := by
  obtain ⟨T', u', h, b, r⟩ := step_typed typed valid safe t' step
  refine ⟨T', u', h, safe_below safe (source_uses_length h) b, b, fun j lin => ?_, r⟩
  rw [uses_determined h]
  exact step_conserves_linear typed valid step lin

/-- Along any reduction of a term that checks (valid context, within budget), every term checks
again, within the budget, with every `linear` count the initial one. -/
public theorem steps_preserve_typing {a : Assumptions} {Γ : Context} {t t' : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a Γ t T u) (valid : validContext a.shareableVariables Γ = true)
    (safe : safeUses Γ u = true) (steps : Steps t t') :
    ∃ T' u', PartialTyping a Γ t' T' u' ∧ safeUses Γ u' = true ∧ (∀ j, LinearAt Γ j → u'.getD j 0 = u.getD j 0) := by
  induction steps generalizing T u with
  | refl => exact ⟨T, u, typed, safe, fun _ _ => rfl⟩
  | next step rest ih =>
    obtain ⟨T1, u1, h1, s1, _, e1, _⟩ := step_preserves_typing typed valid safe step
    obtain ⟨T2, u2, h2, s2, e2⟩ := ih h1 s1
    exact ⟨T2, u2, h2, s2, fun j lin => (e2 j lin).trans (e1 j lin)⟩

/-- **Linear conservation along a reduction**, with no typing premise on the intermediate terms:
a reduction from a term that checks uses every `linear` hypothesis exactly as often at its end as
at its start. -/
public theorem steps_conserve_linear' {a : Assumptions} {Γ : Context} {t t' : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a Γ t T u) (valid : validContext a.shareableVariables Γ = true)
    (safe : safeUses Γ u = true) (steps : Steps t t') {j : Nat} (lin : LinearAt Γ j) :
    (occurrences Γ.length t').getD j 0 = (occurrences Γ.length t).getD j 0 := by
  obtain ⟨T', u', h, _, e⟩ := steps_preserve_typing typed valid safe steps
  rw [← uses_determined h, ← uses_determined typed]
  exact e j lin

/-! ### Why `RowRefines`: `extendRecord` changes the type -/

theorem natural_inv {a : Assumptions} {Γ : Context} {n : Nat} {T : Ty} {u : Uses}
    (h : PartialTyping a Γ (.nat n) T u) : sameType a .natural T = true := by
  generalize ht : Term.nat n = t0 at h
  revert ht
  apply PartialTyping.rec
    (motive_1 := fun _ t T _ _ => Term.nat n = t → sameType a .natural T = true)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case natural => intros; exact sameType_refl _ _
  case conversion =>
    intro Γ t actual expected u _ same ih e; exact sameType_trans (ih e) same
  all_goals (intros; first | trivial | (rename_i e; cases e))

/-- `extendRecord` is not type-preserving up to `sameType`. With `h` an `affine` custody handle,
`{a = h} with {a = 0}` checks at `{a : ℕ, a : custody 0}` (`overlay`: the shadowed member is not
shareable, so the type keeps it), it steps to `{a = 0}`, and no type of `{a = 0}` is `sameType` to
the old one (the old type is not shareable, every type of the reduct is). The reduct's type answers
every lookup of the old one (`RowRefines`); that is what `step_preserves_typing` states. -/
public theorem extendRecord_changes_type :
    (∃ u, PartialTyping {} [⟨.custody 0, .affine⟩] (.extend (.record [("a", .bound 0)]) [("a", .nat 0)])
        (.field "a" .natural (.field "a" (.custody 0) .emptyRow)) u) ∧
      Step (.extend (.record [("a", .bound 0)]) [("a", .nat 0)]) (.record [("a", .nat 0)]) ∧
      ∀ T' u', PartialTyping {} [⟨.custody 0, .affine⟩] (.record [("a", .nat 0)]) T' u' →
        sameType {} T' (.field "a" .natural (.field "a" (.custody 0) .emptyRow)) = false := by
  refine ⟨?_, by simpa [extendFields] using Step.extendRecord [("a", .bound 0)] [("a", .nat 0)], ?_⟩
  · refine ⟨_, PartialTyping.extend (fuel := 2) (context := [⟨.custody 0, .affine⟩])
      (.record (.cons (.bound (index := 0) rfl) (.nil _) rfl) rfl) (.cons (.natural _ 0) (.nil _) rfl) rfl rfl ?_⟩
    decide
  intro T' u' h
  obtain ⟨row, hf, s⟩ := record_inv' h
  cases hf with
  | cons hb hr _ =>
    cases hr
    rename_i τ _ _
    have hτ := (sameType_iff _ _ _).mp (natural_inv hb)
    have row_eq : TypeGraph.Equivalent {} (.field "a" .natural .emptyRow) (.field "a" τ .emptyRow) :=
      TypeGraph.field_congruence hτ ((sameType_iff _ _ _).mp (sameType_refl _ _))
    apply Bool.eq_false_iff.mpr
    intro same
    have chain := (sameType_iff _ _ _).mp
      (sameType_trans ((sameType_iff _ _ _).mpr row_eq) (sameType_trans s same))
    have := TypeGraph.equivalent_shareable chain
    simp [Obend.Core.RecursiveRows.shareable_field] at this

/-! ### Closed programs over custody handles -/

/-- `k` custody handles the kernel holds, each a free `linear` variable: handle `n` at index `n`. -/
@[expose] public def custodyContext (k : Nat) : Context :=
  (List.range k).map fun n => ⟨.custody n, .linear⟩

theorem custodyContext_length (k : Nat) : (custodyContext k).length = k := by simp [custodyContext]

theorem custodyContext_valid (V : List Nat) (k : Nat) : validContext V (custodyContext k) = true := by
  simp [validContext, custodyContext]

theorem custodyContext_linear {k j : Nat} (h : j < k) : LinearAt (custodyContext k) j :=
  ⟨⟨.custody j, .linear⟩, by simp [custodyContext, List.getElem?_range, h], rfl⟩

/-- **Custody is conserved.** A program checked in the context of `k` custody handles, using each
at most once (`safeUses`), keeps each handle's count over any reduction: no `Step` drops or copies a
handle. (A bound variable never blocks or is consumed by a `Step`, since no rule eliminates a
variable; the handles are the free variables.) -/
public theorem custody_conserved {a : Assumptions} {k : Nat} {t t' : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a (custodyContext k) t T u) (safe : safeUses (custodyContext k) u = true)
    (steps : Steps t t') {j : Nat} (hj : j < k) :
    (occurrences k t').getD j 0 = u.getD j 0 := by
  have := steps_conserve_linear' typed (custodyContext_valid _ k) safe steps (custodyContext_linear hj)
  rw [custodyContext_length] at this
  rw [this, ← custodyContext_length k, ← uses_determined typed]

end Obend.Core.Proofs.SubjectReduction
