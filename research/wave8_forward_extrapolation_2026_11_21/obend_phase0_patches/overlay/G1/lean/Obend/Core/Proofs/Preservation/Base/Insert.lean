module
/- Inserting a binding: uses vectors and `source_insert_binding`. -/
public import Obend.Core.MachineTyping
public import Obend.Core.RuntimeOrigins
public import Obend.Core.EquiRecursiveLookup
public import Obend.Core.TypeGraphHead
public import Obend.Core.Proofs.Adequacy.Defs
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Check
namespace Obend.Core.Proofs.Preservation
open Obend.Core.Ty Obend.Core.Check Obend.Core.Term Obend.Core.Machine Obend.Core.MachineTyping
set_option autoImplicit false

/-- Inserting a lexical slot shifts precisely the indices at/after its depth.
This is independent of rigid future-type variables in annotations. -/
@[expose] public def shiftIndex (depth index : Nat) : Nat := if index < depth then index else index+1

theorem lift_shift_index (depth : Nat) : liftRename (shiftIndex depth) = shiftIndex (depth+1) := by
  funext index
  cases index <;> simp [liftRename,shiftIndex]
  split <;> omega

theorem binding_insert_shift {context : Context} {index depth : Nat} {declared binding : Binding}
    (found : context[index]? = some declared) :
    (context.insertIdx depth binding)[shiftIndex depth index]? = some declared := by
  by_cases before : index < depth
  · simpa [shiftIndex,before,List.getElem?_insertIdx_of_lt before] using found
  · have after : depth < index+1 := by omega
    simpa [shiftIndex,before,List.getElem?_insertIdx_of_gt after] using found

theorem zero_uses_insert (context : Context) (binding : Binding) (depth : Nat)
    (bound : depth ≤ context.length) :
    zeroUses (context.insertIdx depth binding) = (zeroUses context).insertIdx depth 0 := by
  induction depth generalizing context with
  | zero => simp [zeroUses,List.insertIdx_zero,List.replicate_succ]
  | succ depth ih =>
      cases context with
      | nil => simp at bound
      | cons first rest =>
          have tailBound : depth ≤ rest.length := by simpa using bound
          simpa [zeroUses,List.insertIdx_succ_cons,List.replicate_succ] using congrArg (List.cons 0) (ih rest tailBound)

theorem add_uses_insert (first second : Uses) (depth : Nat)
    (lengths : first.length = second.length) (bound : depth ≤ first.length) :
    addUses (first.insertIdx depth 0) (second.insertIdx depth 0) = (addUses first second).insertIdx depth 0 := by
  induction depth generalizing first second with
  | zero => rfl
  | succ depth ih =>
      cases first with
      | nil => simp at bound
      | cons a first =>
          cases second with
          | nil => simp at lengths
          | cons b second =>
              simp only [List.length_cons,Nat.add_le_add_iff_right] at bound
              have lengths' : first.length = second.length := Nat.succ.inj lengths
              simpa [addUses,List.insertIdx_succ_cons,List.zipWith] using congrArg (List.cons (a+b)) (ih first second lengths' bound)

theorem join_uses_insert (first second : Uses) (depth : Nat)
    (lengths : first.length = second.length) (bound : depth ≤ first.length) :
    joinUses (first.insertIdx depth 0) (second.insertIdx depth 0) = (joinUses first second).insertIdx depth 0 := by
  induction depth generalizing first second with
  | zero => rfl
  | succ depth ih =>
      cases first with
      | nil => simp at bound
      | cons a first =>
          cases second with
          | nil => simp at lengths
          | cons b second =>
              simp only [List.length_cons,Nat.add_le_add_iff_right] at bound
              have lengths' : first.length = second.length := Nat.succ.inj lengths
              simpa [joinUses,List.insertIdx_succ_cons,List.zipWith] using congrArg (List.cons (max a b)) (ih first second lengths' bound)

theorem branches_agree_insert (context : Context) (first second : Uses) (depth : Nat) (binding : Binding)
    (agreeing : branchesAgree context first second = true) (bound : depth ≤ context.length)
    (firstLength : first.length = context.length) (secondLength : second.length = context.length) :
    branchesAgree (context.insertIdx depth binding) (first.insertIdx depth 0) (second.insertIdx depth 0) = true := by
  induction depth generalizing context first second with
  | zero =>
      simp only [List.insertIdx_zero, branchesAgree, Bool.and_eq_true]
      exact ⟨by cases binding.quantity <;> rfl, agreeing⟩
  | succ depth ih =>
      cases context with
      | nil => simp at bound
      | cons d context =>
          cases first with
          | nil => simp at firstLength
          | cons a first =>
              cases second with
              | nil => simp at secondLength
              | cons b second =>
                  simp only [branchesAgree, Bool.and_eq_true] at agreeing
                  simp only [List.insertIdx_succ_cons, branchesAgree, Bool.and_eq_true]
                  exact ⟨agreeing.1, ih context first second agreeing.2 (by simpa using bound)
                    (by simpa using firstLength) (by simpa using secondLength)⟩

theorem variable_uses_lookup (context : Context) (index query : Nat) :
    (variableUses context index)[query]? =
      if query < context.length then some (if query = index then 1 else 0) else none := by
  by_cases inside : query < context.length <;> simp [variableUses,inside]

theorem variable_uses_insert (context : Context) (binding : Binding) (index depth : Nat)
    (bound : depth ≤ context.length) :
    variableUses (context.insertIdx depth binding) (shiftIndex depth index) =
      (variableUses context index).insertIdx depth 0 := by
  apply List.ext_getElem?
  intro query
  rw [variable_uses_lookup,List.length_insertIdx_of_le_length bound binding,List.getElem?_insertIdx]
  by_cases before : query < depth
  · have inside : query < context.length := by omega
    have shifted : query = shiftIndex depth index ↔ query = index := by
      by_cases prior : index < depth <;> simp [shiftIndex,prior] <;> omega
    have newInside : query < context.length+1 := by omega
    simp [before,inside,newInside,variable_uses_lookup,shifted]
  · by_cases inserted : query = depth
    · subst query
      have notShifted : depth ≠ shiftIndex depth index := by
        by_cases prior : index < depth <;> simp [shiftIndex,prior] <;> omega
      have newInside : depth < context.length+1 := by omega
      simp [before,bound,newInside,notShifted,variableUses]
    · have positive : 0 < query := by omega
      have shifted : query = shiftIndex depth index ↔ query-1 = index := by
        by_cases prior : index < depth <;> simp [shiftIndex,prior] <;> omega
      have range : query < context.length+1 ↔ query-1 < context.length := by omega
      simp [before,inserted,variable_uses_lookup,range,shifted]

theorem safe_quantity_zero (quantity : Quantity) : safeQuantity quantity 0 = true := by
  cases quantity <;> rfl

theorem safe_uses_insert (context : Context) (uses : Uses) (depth : Nat) (binding : Binding)
    (safe : safeUses context uses = true) (bound : depth ≤ context.length) :
    safeUses (context.insertIdx depth binding) (uses.insertIdx depth 0) = true := by
  induction depth generalizing context uses with
  | zero => simpa [safeUses,List.insertIdx_zero,safe_quantity_zero] using safe
  | succ depth ih =>
      cases context with
      | nil => simp at bound
      | cons first context =>
          cases uses with
          | nil => simp [safeUses] at safe
          | cons count uses =>
              have tailBound : depth ≤ context.length := by simpa using bound
              have facts : safeQuantity first.quantity count = true ∧ safeUses context uses = true := by
                simpa [safeUses,List.zip,List.all_cons,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm,and_assoc,and_left_comm,and_comm] using safe
              have tail := ih context uses facts.2 tailBound
              simpa [safeUses,List.insertIdx_succ_cons,List.zip,List.all_cons,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm,and_assoc,and_left_comm,and_comm] using And.intro facts.1 tail

public theorem reusable_captures_insert (variables : List Nat) (context : Context) (uses : Uses)
    (depth : Nat) (binding : Binding)
    (captures : reusableCaptures variables context uses = true) (bound : depth ≤ context.length) :
    reusableCaptures variables (context.insertIdx depth binding) (uses.insertIdx depth 0) = true := by
  induction depth generalizing context uses with
  | zero => simpa [reusableCaptures,List.insertIdx_zero] using captures
  | succ depth ih =>
      cases context with
      | nil => simp at bound
      | cons first context =>
          cases uses with
          | nil => simp [reusableCaptures] at captures
          | cons count uses =>
              have tailBound : depth ≤ context.length := by simpa using bound
              have facts : (count == 0 || (first.quantity == .unrestricted && first.type.shareableUnder variables)) = true ∧
                  reusableCaptures variables context uses = true := by
                simpa [reusableCaptures,List.zip,List.all_cons,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm,and_assoc,and_left_comm,and_comm] using captures
              have tail := ih context uses facts.2 tailBound
              simpa [reusableCaptures,List.insertIdx_succ_cons,List.zip,List.all_cons,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm,and_assoc,and_left_comm,and_comm] using And.intro facts.1 tail

theorem headD_insert_succ {uses : Uses} {depth : Nat} : (uses.insertIdx (depth + 1) 0).headD 0 = uses.headD 0 := by
  cases uses with
  | nil => simp [List.insertIdx_succ_nil]
  | cons => simp [List.insertIdx_succ_cons]

theorem linear_free_insert (context : Context) (uses : Uses) (depth : Nat) (binding : Binding)
    (free : linearFree context uses = true) (bound : depth ≤ context.length) :
    linearFree (context.insertIdx depth binding) (uses.insertIdx depth 0) = true := by
  induction depth generalizing context uses with
  | zero => simpa [linearFree,List.insertIdx_zero] using free
  | succ depth ih =>
      cases context with
      | nil => simp at bound
      | cons first context =>
          cases uses with
          | nil => simp [linearFree, List.insertIdx_succ_nil]
          | cons count uses =>
              have tailBound : depth ≤ context.length := by simpa using bound
              have facts : (count == 0 || first.quantity != .linear) = true ∧ linearFree context uses = true := by
                simpa [linearFree,List.zip,List.all_cons] using free
              have tail := ih context uses facts.2 tailBound
              simp only [linearFree, List.insertIdx_succ_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
              exact ⟨facts.1, tail⟩

theorem valid_context_insert (variables : List Nat) (context : Context) (depth : Nat) (binding : Binding)
    (valid : validContext variables context = true) (bindingValid : validContext variables [binding] = true)
    (bound : depth ≤ context.length) : validContext variables (context.insertIdx depth binding) = true := by
  induction depth generalizing context with
  | zero => simpa [validContext,List.insertIdx_zero] using And.intro bindingValid valid
  | succ depth ih =>
      cases context with
      | nil => simp at bound
      | cons first context =>
          have tailBound : depth ≤ context.length := by simpa using bound
          have facts : ((first.quantity != .unrestricted || first.type.shareableUnder variables) &&
              mustBeLinear first) = true ∧ validContext variables context = true := by
            simpa [validContext] using valid
          simpa [validContext,List.insertIdx_succ_cons] using And.intro facts.1 (ih context facts.2 tailBound)

theorem reusable_allowed_insert (assumptions : Assumptions) (reuse : Reuse)
    (context : Context) (uses : Uses) (depth : Nat) (binding : Binding)
    (allowed : reusableAllowed assumptions reuse context uses = true) (bound : depth ≤ context.length) :
    reusableAllowed assumptions reuse (context.insertIdx depth binding) (uses.insertIdx depth 0) = true := by
  cases reuse with
  | once => rfl
  | reusable =>
      have captures : reusableCaptures assumptions.shareableVariables context uses = true := by simpa [reusableAllowed] using allowed
      simpa [reusableAllowed] using reusable_captures_insert assumptions.shareableVariables context uses depth binding captures bound

theorem case_allowed_insert (assumptions : Assumptions) (quantity : Quantity)
    (context : Context) (uses : Uses) (depth : Nat) (binding : Binding)
    (allowed : caseAllowed assumptions quantity context uses = true) (bound : depth ≤ context.length) :
    caseAllowed assumptions quantity (context.insertIdx depth binding) (uses.insertIdx depth 0) = true := by
  simp only [caseAllowed, Bool.and_eq_true, Bool.or_eq_true] at allowed ⊢
  exact ⟨allowed.1.imp id (fun free => linear_free_insert context uses depth binding free bound),
    allowed.2.imp id (fun captures => reusable_captures_insert assumptions.shareableVariables context uses depth binding captures bound)⟩

theorem argument_allowed_insert (assumptions : Assumptions) (quantity : Quantity)
    (context : Context) (type : Ty) (uses : Uses) (depth : Nat) (binding : Binding)
    (allowed : argumentAllowed assumptions quantity context type uses = true) (bound : depth ≤ context.length) :
    argumentAllowed assumptions quantity (context.insertIdx depth binding) type (uses.insertIdx depth 0) = true := by
  have pure : type.isComputation = false := argumentAllowed_not_computation allowed
  cases quantity with
  | unrestricted =>
      have facts : type.shareableUnder assumptions.shareableVariables = true ∧
          reusableCaptures assumptions.shareableVariables context uses = true := by
        have := allowed
        simp [argumentAllowed, pure] at this
        exact this.2
      have captures := reusable_captures_insert assumptions.shareableVariables context uses depth binding facts.2 bound
      simp [argumentAllowed, pure, facts.1, captures, linearFree_of_reusableCaptures captures]
  | linear => simp [argumentAllowed,pure]
  | _ =>
      have free : linearFree context uses = true := by simpa [argumentAllowed,pure] using allowed
      simp [argumentAllowed, pure, linear_free_insert context uses depth binding free bound]

/-- Under a lambda/conditional binder the inserted free slot is one place
farther down; dropping that original binder restores the outer use vector. -/
theorem uses_tail_insert {uses : Uses} (nonempty : 0 < uses.length) (depth : Nat) :
    (uses.insertIdx (depth+1) 0).tail = uses.tail.insertIdx depth 0 := by
  cases uses with
  | nil => simp at nonempty
  | cons head tail => rfl

theorem insert_usage_bound {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses} (typed : PartialTyping assumptions context term type uses)
    {depth : Nat} (bound : depth ≤ context.length) : depth ≤ uses.length := by rw [source_uses_length typed]; exact bound

/-- Arms account for every lexical slot of the enclosing context. -/
public theorem arms_uses_length {assumptions : Assumptions} {context : Context}
    {q : Quantity} {arms : List (String × Term)} {row result : Ty} {uses : Uses}
    (typed : ArmsTyping assumptions context q arms row result uses) : uses.length = context.length := by
  induction arms generalizing row uses with
  | nil => cases typed; simp [zeroUses]
  | cons arm rest ih =>
      cases typed with
      | cons bodyTyped safe shareable _ restTyped _ =>
          have bodyLength := source_uses_length bodyTyped
          have restLength := ih restTyped
          simp_all [addUses,joinUses,List.length_zipWith,List.length_tail]

/-- General capture-sensitive lexical weakening over EVERY source constructor,
including nested fields and conditional/lambda binders. The inserted slot is
unused; its declared context validity is checked rather than assumed pure. -/
public theorem source_insert_binding {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping assumptions context term type uses) :
    ∀ depth binding, depth ≤ context.length → validContext assumptions.shareableVariables [binding] = true →
      PartialTyping assumptions (context.insertIdx depth binding) (term.rename (shiftIndex depth)) type (uses.insertIdx depth 0) := by
  apply PartialTyping.rec
    (motive_1 := fun context term type uses _ => ∀ depth binding,
      depth ≤ context.length → validContext assumptions.shareableVariables [binding] = true →
      PartialTyping assumptions (context.insertIdx depth binding) (term.rename (shiftIndex depth)) type (uses.insertIdx depth 0))
    (motive_2 := fun context fields row uses _ => ∀ depth binding,
      depth ≤ context.length → validContext assumptions.shareableVariables [binding] = true →
      FieldsTyping assumptions (context.insertIdx depth binding)
        (fields.map fun field => (field.1,field.2.rename (shiftIndex depth))) row (uses.insertIdx depth 0))
    (motive_3 := fun context q arms row result uses _ => ∀ depth binding,
      depth ≤ context.length → validContext assumptions.shareableVariables [binding] = true →
      ArmsTyping assumptions (context.insertIdx depth binding) q
        (arms.map fun arm => (arm.1,arm.2.rename (shiftIndex (depth+1)))) row result (uses.insertIdx depth 0))
    (t := typed)
  case bound =>
    intro context index declared found depth binding bound bindingValid
    simpa only [Term.rename,← variable_uses_insert context binding index depth bound] using
      (PartialTyping.bound (binding_insert_shift found) : PartialTyping assumptions (context.insertIdx depth binding)
        (.bound (shiftIndex depth index)) declared.type (variableUses (context.insertIdx depth binding) (shiftIndex depth index)))
  case natural =>
    intro context value depth binding bound bindingValid
    simpa only [Term.rename,← zero_uses_insert context binding depth bound] using
      (PartialTyping.natural (context.insertIdx depth binding) value : PartialTyping assumptions _ (.nat value) .natural _)
  case boolean =>
    intro context value depth binding bound bindingValid
    simpa only [Term.rename,← zero_uses_insert context binding depth bound] using
      (PartialTyping.boolean (context.insertIdx depth binding) value : PartialTyping assumptions _ (.boolean value) .boolean _)
  case label =>
    intro context value depth binding bound bindingValid
    simpa only [Term.rename,← zero_uses_insert context binding depth bound] using
      (PartialTyping.label (context.insertIdx depth binding) value : PartialTyping assumptions _ (.label value) (literalType value) _)
  case lambda =>
    intro context body annotation uses bodyTyped safe valid captures fits ih depth binding bound bindingValid
    have bodyBound : depth+1 ≤ (⟨annotation.domain,annotation.parameter⟩ :: context).length := by simpa using bound
    have nonempty : 0 < uses.length := by rw [source_uses_length bodyTyped]; simp
    have bodyNext := ih (depth+1) binding bodyBound bindingValid
    have safeNext := safe_uses_insert _ uses (depth+1) binding safe bodyBound
    have validNext := valid_context_insert _ _ (depth+1) binding valid bindingValid bodyBound
    have capturesNext := reusable_allowed_insert assumptions annotation.reuse context uses.tail depth binding captures bound
    rw [List.insertIdx_succ_cons] at bodyNext safeNext validNext
    simpa only [Term.rename,lift_shift_index,uses_tail_insert nonempty] using
      (PartialTyping.lambda bodyNext safeNext validNext (by rw [uses_tail_insert nonempty]; exact capturesNext)
        (by rw [headD_insert_succ]; exact fits))
  case conversion =>
    intro context term actual expected uses prior agreement ih depth binding bound bindingValid
    exact .conversion (ih depth binding bound bindingValid) agreement
  case application =>
    intro context fn arg functionType argumentType domain codomain fu au reuse quantity fnTyped argTyped callableEq same allowed ihFn ihArg depth binding bound bindingValid
    have counts := add_uses_insert fu au depth ((source_uses_length fnTyped).trans (source_uses_length argTyped).symm) (insert_usage_bound fnTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.application (ihFn depth binding bound bindingValid) (ihArg depth binding bound bindingValid) callableEq same
        (argument_allowed_insert assumptions quantity context argumentType au depth binding allowed bound))
  case record =>
    intro context fields row uses fieldsTyped distinct ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.record (ih depth binding bound bindingValid) (by simpa using distinct))
  case get =>
    intro context target targetType member uses name fuel targetTyped lookup free ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.get (ih depth binding bound bindingValid) lookup
      (linear_free_insert context uses depth binding free bound))
  case extend =>
    intro context target fields targetType row tu fu rowFuel targetTyped fieldsTyped distinct isRow free ihTarget ihFields depth binding bound bindingValid
    have fieldLength := fields_uses_length fieldsTyped
    have counts := add_uses_insert tu fu depth ((source_uses_length targetTyped).trans fieldLength.symm) (insert_usage_bound targetTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.extend (ihTarget depth binding bound bindingValid) (ihFields depth binding bound bindingValid)
        (by simpa using distinct) isRow (linear_free_insert context tu depth binding free bound))
  case specification =>
    intro context metadata extension metadataType extensionType mu eu metadataTyped extensionTyped mPure ePure free ihMetadata ihExtension depth binding bound bindingValid
    have counts := add_uses_insert mu eu depth ((source_uses_length metadataTyped).trans (source_uses_length extensionTyped).symm) (insert_usage_bound metadataTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.specification (ihMetadata depth binding bound bindingValid) (ihExtension depth binding bound bindingValid) mPure ePure
        (linear_free_insert context mu depth binding free bound))
  case prototype =>
    intro context spec target specType targetType su tu specTyped targetTyped sPure tPure ihSpec ihTarget depth binding bound bindingValid
    have counts := add_uses_insert su tu depth ((source_uses_length specTyped).trans (source_uses_length targetTyped).symm) (insert_usage_bound specTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.prototype (ihSpec depth binding bound bindingValid) (ihTarget depth binding bound bindingValid) sPure tPure)
  case reflect =>
    intro context target specType targetType uses prior free ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.reflect (ih depth binding bound bindingValid)
      (linear_free_insert context uses depth binding free bound))
  case metadata =>
    intro context target metadataType extensionType uses prior free ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.metadata (ih depth binding bound bindingValid)
      (linear_free_insert context uses depth binding free bound))
  case project =>
    intro context target specType targetType uses prior free ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.project (ih depth binding bound bindingValid)
      (linear_free_insert context uses depth binding free bound))
  case mix =>
    intro context lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped lowerCallable upperCallable captures selfShare inheritedShare middleShare ihLower ihUpper depth binding bound bindingValid
    have counts := add_uses_insert lu uu depth ((source_uses_length lowerTyped).trans (source_uses_length upperTyped).symm) (insert_usage_bound lowerTyped bound)
    have capturesNext := reusable_captures_insert assumptions.shareableVariables context (addUses lu uu) depth binding captures bound
    simpa only [Term.rename,counts] using
      (PartialTyping.mix (ihLower depth binding bound bindingValid) (ihUpper depth binding bound bindingValid)
        lowerCallable upperCallable (by simpa only [counts] using capturesNext) selfShare inheritedShare middleShare)
  case fix =>
    intro context spec inheritedTerm specType inherited target su iu specTyped callableEq inheritedTyped targetShare inheritedAllowed captures ihSpec ihInherited depth binding bound bindingValid
    have counts := add_uses_insert su iu depth ((source_uses_length specTyped).trans (source_uses_length inheritedTyped).symm) (insert_usage_bound specTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.fix (ihSpec depth binding bound bindingValid) callableEq (ihInherited depth binding bound bindingValid) targetShare
        (argument_allowed_insert assumptions .unrestricted context inherited iu depth binding inheritedAllowed bound)
        (reusable_captures_insert assumptions.shareableVariables context su depth binding captures bound))
  case binary =>
    intro context primitive left right input output lu ru primitiveEq leftTyped rightTyped ihLeft ihRight depth binding bound bindingValid
    have counts := add_uses_insert lu ru depth ((source_uses_length leftTyped).trans (source_uses_length rightTyped).symm) (insert_usage_bound leftTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.binary primitiveEq (ihLeft depth binding bound bindingValid) (ihRight depth binding bound bindingValid))
  case ifZero =>
    intro context value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe agreeing ihValue ihZero ihSuccessor depth binding bound bindingValid
    have successorBound : depth+1 ≤ (⟨.natural,.unrestricted⟩ :: context).length := by simpa using bound
    have nonempty : 0 < su.length := by rw [source_uses_length successorTyped]; simp
    have tailLength : su.tail.length = context.length := by simp [List.length_tail,source_uses_length successorTyped]
    have zeroLength := source_uses_length zeroTyped
    have firstCounts := join_uses_insert zu su.tail depth (zeroLength.trans tailLength.symm) (insert_usage_bound zeroTyped bound)
    have sumLength : (joinUses zu su.tail).length = context.length := by simp [joinUses,List.length_zipWith,zeroLength,tailLength]
    have allCounts := add_uses_insert vu (joinUses zu su.tail) depth ((source_uses_length valueTyped).trans sumLength.symm) (insert_usage_bound valueTyped bound)
    have agreeNext := branches_agree_insert context zu su.tail depth binding agreeing bound zeroLength tailLength
    rw [← uses_tail_insert nonempty] at agreeNext
    simpa only [Term.rename,lift_shift_index,List.insertIdx_succ_cons,uses_tail_insert nonempty,firstCounts,allCounts] using
      (PartialTyping.ifZero (ihValue depth binding bound bindingValid) (ihZero depth binding bound bindingValid)
        (ihSuccessor (depth+1) binding successorBound bindingValid)
        (safe_uses_insert _ su (depth+1) binding successorSafe successorBound) (by simpa only [List.insertIdx_succ_cons] using agreeNext))
  case inject =>
    intro context tag payload payloadType row uses fuel payloadTyped lookup pure ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.inject (ih depth binding bound bindingValid) lookup pure)
  case case =>
    intro context scrutinee arms row result su au q scrutineeTyped armsTyped distinct allowed ihScrutinee ihArms depth binding bound bindingValid
    have counts := add_uses_insert su au depth ((source_uses_length scrutineeTyped).trans (arms_uses_length armsTyped).symm) (insert_usage_bound scrutineeTyped bound)
    simpa only [Term.rename,lift_shift_index,counts] using
      (PartialTyping.case (ihScrutinee depth binding bound bindingValid) (ihArms depth binding bound bindingValid)
        (by simpa using distinct) (case_allowed_insert assumptions q context su depth binding allowed bound))
  case ifBool =>
    intro context condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped agreeing ihCondition ihTrue ihFalse depth binding bound bindingValid
    have trueLength := source_uses_length trueTyped
    have falseLength := source_uses_length falseTyped
    have firstCounts := join_uses_insert tu fu depth (trueLength.trans falseLength.symm) (insert_usage_bound trueTyped bound)
    have sumLength : (joinUses tu fu).length = context.length := by simp [joinUses,List.length_zipWith,trueLength,falseLength]
    have allCounts := add_uses_insert cu (joinUses tu fu) depth ((source_uses_length conditionTyped).trans sumLength.symm) (insert_usage_bound conditionTyped bound)
    simpa only [Term.rename,firstCounts,allCounts] using
      (PartialTyping.ifBool (ihCondition depth binding bound bindingValid) (ihTrue depth binding bound bindingValid)
        (ihFalse depth binding bound bindingValid)
        (branches_agree_insert context tu fu depth binding agreeing bound trueLength falseLength))
  case perform =>
    intro context plan planType response uses planTyped isPlan isData ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.perform (ih depth binding bound bindingValid) isPlan isData)
  case done =>
    intro context value planType response result uses valueTyped pure ih depth binding bound bindingValid
    simpa only [Term.rename] using
      (PartialTyping.done (planType := planType) (response := response) (ih depth binding bound bindingValid) pure)
  case effectCase =>
    intro context scrutinee arms planType response row result su au q scrutineeTyped armsTyped pure distinct allowed ihScrutinee ihArms depth binding bound bindingValid
    have counts := add_uses_insert su au depth ((source_uses_length scrutineeTyped).trans (arms_uses_length armsTyped).symm) (insert_usage_bound scrutineeTyped bound)
    simpa only [Term.rename,lift_shift_index,counts] using
      (PartialTyping.effectCase (ihScrutinee depth binding bound bindingValid) (ihArms depth binding bound bindingValid) pure
        (by simpa using distinct) (case_allowed_insert assumptions q context su depth binding allowed bound))
  case split =>
    intro context target function names row functionType result tu fu targetTyped functionTyped nodup covers spine ihTarget ihFunction depth binding bound bindingValid
    have counts := add_uses_insert tu fu depth ((source_uses_length targetTyped).trans (source_uses_length functionTyped).symm) (insert_usage_bound targetTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.split (ihTarget depth binding bound bindingValid) (ihFunction depth binding bound bindingValid) nodup covers
        (spine.transport fun q allowed => case_allowed_insert assumptions q context tu depth binding allowed bound))
  case hole =>
    intro context n σ decl args found hσ hctx typedArgs allowed ih depth binding bound bindingValid
    subst hσ
    have counts : (args.map fun arg => arg.2.2.insertIdx depth 0).foldr addUses
        (zeroUses (context.insertIdx depth binding)) =
        ((args.map (·.2.2)).foldr addUses (zeroUses context)).insertIdx depth 0 :=
      (foldr_addUses_rel (R := fun x' x => x' = x.insertIdx depth 0 ∧ x.length = context.length)
        (fun ⟨h1, l1⟩ ⟨h2, l2⟩ => ⟨by rw [h1, h2, add_uses_insert _ _ depth (l1.trans l2.symm) (l1 ▸ bound)],
          by simp [addUses, List.length_zipWith, l1, l2]⟩)
        ⟨zero_uses_insert context binding depth bound, by simp [zeroUses]⟩ (fun arg => arg.2.2)
        (fun arg => arg.2.2.insertIdx depth 0) args
        (fun arg h => ⟨rfl, source_uses_length (typedArgs arg h)⟩)).1
    have typed := PartialTyping.hole (assumptions := assumptions) (context := context.insertIdx depth binding)
      (σ := (args.map (·.1)).map fun t => t.rename (shiftIndex depth))
      (args := args.map fun arg => (arg.1.rename (shiftIndex depth), arg.2.1, arg.2.2.insertIdx depth 0))
      found (by simp [Function.comp_def]) (by rw [← hctx]; simp [Function.comp_def])
      (fun a ha => by obtain ⟨arg, h, rfl⟩ := List.mem_map.mp ha; exact ih arg h depth binding bound bindingValid)
      (fun a ha => by
        obtain ⟨arg, h, rfl⟩ := List.mem_map.mp ha
        exact argument_allowed_insert assumptions _ context _ _ depth binding (allowed arg h) bound)
    simp only [List.map_map, Function.comp_def] at typed
    rw [counts] at typed
    simpa only [Term.rename, List.map_map, Function.comp_def] using typed
  case nil =>
    intro context depth binding bound bindingValid
    simpa only [List.map_nil,← zero_uses_insert context binding depth bound] using (FieldsTyping.nil (context.insertIdx depth binding) : FieldsTyping assumptions _ [] .emptyRow _)
  case cons =>
    intro context name body rest type row bu ru bodyTyped restTyped pure ihBody ihRest depth binding bound bindingValid
    have restLength := fields_uses_length restTyped
    have counts := add_uses_insert bu ru depth ((source_uses_length bodyTyped).trans restLength.symm) (insert_usage_bound bodyTyped bound)
    simpa only [List.map_cons,counts] using
      (FieldsTyping.cons (ihBody depth binding bound bindingValid) (ihRest depth binding bound bindingValid) pure)
  case nil =>
    intro context q result depth binding bound bindingValid
    simpa only [List.map_nil,← zero_uses_insert context binding depth bound] using
      (ArmsTyping.nil (context.insertIdx depth binding) q result : ArmsTyping assumptions _ q [] .emptyRow result _)
  case cons =>
    intro context q name body rest payload row result bu ru bodyTyped safe shareable fits restTyped agreeing ihBody ihRest depth binding bound bindingValid
    have bodyBound : depth+1 ≤ (⟨payload,q⟩ :: context).length := by simpa using bound
    have nonempty : 0 < bu.length := by rw [source_uses_length bodyTyped]; simp
    have tailLength : bu.tail.length = context.length := by simp [List.length_tail,source_uses_length bodyTyped]
    have counts := join_uses_insert bu.tail ru depth (tailLength.trans (arms_uses_length restTyped).symm)
      (by rw [tailLength]; exact bound)
    have bodyNext := ihBody (depth+1) binding bodyBound bindingValid
    have safeNext := safe_uses_insert _ bu (depth+1) binding safe bodyBound
    simp only [List.insertIdx_succ_cons] at bodyNext safeNext
    have agreeNext : ((rest.map fun arm => (arm.1, arm.2.rename (shiftIndex (depth+1)))).isEmpty ||
        branchesAgree (context.insertIdx depth binding) (bu.insertIdx (depth+1) 0).tail (ru.insertIdx depth 0)) = true := by
      rw [uses_tail_insert nonempty]
      simp only [List.isEmpty_map, Bool.or_eq_true] at agreeing ⊢
      exact agreeing.imp id (fun a => branches_agree_insert context bu.tail ru depth binding a bound tailLength
        (arms_uses_length restTyped))
    have combined := ArmsTyping.cons (name := name) bodyNext safeNext shareable (by rw [headD_insert_succ]; exact fits)
      (ihRest depth binding bound bindingValid) agreeNext
    rw [uses_tail_insert nonempty,counts] at combined
    simpa only [List.map_cons] using combined

theorem shift_zero : shiftIndex 0 = Nat.succ := by funext index; simp [shiftIndex,Nat.succ_eq_add_one]

public theorem source_weaken {assumptions : Assumptions} {context : Context} {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping assumptions context term type uses) (binding : Binding)
    (bindingValid : validContext assumptions.shareableVariables [binding] = true) :
    PartialTyping assumptions (binding :: context) (term.rename Nat.succ) type (0 :: uses) := by
  simpa only [shift_zero,List.insertIdx_zero] using source_insert_binding typed 0 binding (Nat.zero_le _) bindingValid

theorem reusable_zero_uses (variables : List Nat) (context : Context) :
    reusableCaptures variables context (zeroUses context) = true := by
  induction context with
  | nil => rfl
  | cons binding context ih => simpa [reusableCaptures,zeroUses,List.replicate_succ,List.zip] using ih

theorem variable_uses_cons_zero (context : Context) (binding : Binding) :
    variableUses (binding :: context) 0 = 1 :: zeroUses context := by
  simp [variableUses,zeroUses,List.range_succ_eq_map,List.map_map,Function.comp_def,List.map_const']

theorem variable_uses_cons_succ (context : Context) (binding : Binding) (index : Nat) :
    variableUses (binding :: context) (index+1) = 0 :: variableUses context index := by
  simp [variableUses,List.range_succ_eq_map,List.map_map,Function.comp_def]

public theorem reusable_variable {variables : List Nat} {context : Context} {index : Nat} {binding : Binding}
    (found : context[index]? = some binding) (quantity : binding.quantity = .unrestricted)
    (shareable : binding.type.shareableUnder variables = true) :
    reusableCaptures variables context (variableUses context index) = true := by
  induction context generalizing index with
  | nil => simp at found
  | cons first rest ih =>
      cases index with
      | zero =>
          have same : first = binding := by simpa using found
          subst first
          have head : (1 == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true := by simp [quantity,shareable]
          simpa [variable_uses_cons_zero,reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using And.intro head (reusable_zero_uses variables rest)
      | succ index =>
          have tail : rest[index]? = some binding := by simpa using found
          simpa [variable_uses_cons_succ,reusableCaptures,List.zip] using ih tail

theorem reusable_count_add (quantity : Quantity) (shareable : Bool) (first second : Nat)
    (left : (first == 0 || (quantity == .unrestricted && shareable)) = true)
    (right : (second == 0 || (quantity == .unrestricted && shareable)) = true) :
    (first+second == 0 || (quantity == .unrestricted && shareable)) = true := by
  by_cases firstZero : first = 0
  · simpa [firstZero] using right
  · simpa [firstZero] using left

theorem reusable_count_add_left (quantity : Quantity) (shareable : Bool) (first second : Nat)
    (combined : (first+second == 0 || (quantity == .unrestricted && shareable)) = true) :
    (first == 0 || (quantity == .unrestricted && shareable)) = true := by
  by_cases firstZero : first = 0
  · simp [firstZero]
  · have sumNonzero : first+second ≠ 0 := by omega
    simpa [firstZero,sumNonzero] using combined

public theorem reusable_add_uses (variables : List Nat) (context : Context) (first second : Uses)
    (left : reusableCaptures variables context first = true)
    (right : reusableCaptures variables context second = true) :
    reusableCaptures variables context (addUses first second) = true := by
  induction context generalizing first second with
  | nil =>
      have firstEmpty : first = [] := by simpa [reusableCaptures] using left
      subst first; rfl
  | cons binding context ih =>
      cases first with
      | nil => simp [reusableCaptures] at left
      | cons first firsts =>
        cases second with
        | nil => simp [reusableCaptures] at right
        | cons second seconds =>
          have lf : (first == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true ∧ reusableCaptures variables context firsts = true := by
            simpa [reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using left
          have rf : (second == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true ∧ reusableCaptures variables context seconds = true := by
            simpa [reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using right
          simpa [reusableCaptures,addUses,List.zipWith,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using
            And.intro (reusable_count_add _ _ first second lf.1 rf.1) (ih firsts seconds lf.2 rf.2)

public theorem reusable_add_uses_left (variables : List Nat) (context : Context) (first second : Uses)
    (firstLength : first.length = context.length) (secondLength : second.length = context.length)
    (combined : reusableCaptures variables context (addUses first second) = true) :
    reusableCaptures variables context first = true := by
  induction context generalizing first second with
  | nil => cases first with | nil => rfl | cons head tail => simp at firstLength
  | cons binding context ih =>
      cases first with
      | nil => simp at firstLength
      | cons first firsts =>
        cases second with
        | nil => simp at secondLength
        | cons second seconds =>
          have fl : firsts.length = context.length := Nat.succ.inj firstLength
          have sl : seconds.length = context.length := Nat.succ.inj secondLength
          have facts : (first+second == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true ∧
              reusableCaptures variables context (addUses firsts seconds) = true := by
            simpa [reusableCaptures,addUses,List.zipWith,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm,fl,sl] using combined
          simpa [reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using
            And.intro (reusable_count_add_left _ _ first second facts.1) (ih firsts seconds fl sl facts.2)

public theorem reusable_uses_safe (variables : List Nat) (context : Context) (uses : Uses)
    (captures : reusableCaptures variables context uses = true) : safeUses context uses = true := by
  induction context generalizing uses with
  | nil => cases uses <;> simp_all [safeUses,reusableCaptures]
  | cons binding context ih =>
      cases uses with
      | nil => simp [reusableCaptures] at captures
      | cons count uses =>
          have facts : (count == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true ∧ reusableCaptures variables context uses = true := by
            simpa [reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using captures
          have head : safeQuantity binding.quantity count = true := by
            simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at facts
            rcases facts.1 with zero | ⟨unrestricted,share⟩
            · subst count; exact safe_quantity_zero _
            · rw [unrestricted]; rfl
          simpa [safeUses,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using And.intro head (ih uses facts.2)

public theorem reusable_tail {variables : List Nat} {binding : Binding} {context : Context} {uses : Uses}
    (captures : reusableCaptures variables (binding :: context) uses = true) :
    reusableCaptures variables context uses.tail = true := by
  cases uses with
  | nil => simp [reusableCaptures] at captures
  | cons head tail =>
      have facts : (head == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true ∧ reusableCaptures variables context tail = true := by
        simpa [reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using captures
      exact facts.2

end Obend.Core.Proofs.Preservation
