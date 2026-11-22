module
/- Preservation cases: Functions. Imports only the shared Base; the dispatcher in
Obend/Core/DemandPreservation.lean assembles every case module. -/
public import Obend.Core.Proofs.Preservation.Base.Focus
public import Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Check
namespace Obend.Core.Proofs.Preservation
open Obend.Core.Ty Obend.Core.Check Obend.Core.Term Obend.Core.Machine Obend.Core.MachineTyping
set_option autoImplicit false

/-- Immediate weak-head values are precisely scalars and lexical lambdas.
Records still allocate suspended fields through the actual machine. -/
@[expose] public def immediateValue (term : Term) (environment : Environment) : Option RuntimeValue :=
  match term with
  | .lam body => some (.closure body environment)
  | other => scalarValue other

/-- All source derivations, including finite row/alias conversions, preserve
immediate value typing. Reusable lambdas retain the actual body capture proof. -/
theorem immediate_value_typed {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    ∀ (types : AddressTypes) (environment : Environment),
      EnvironmentTyping types context environment →
      ∀ value, immediateValue term environment = some value →
        ValueTyping assumptions types value type := by
  apply PartialTyping.rec
    (motive_1 := fun context term type _ _ => ∀ types environment,
      EnvironmentTyping types context environment →
      ∀ value, immediateValue term environment = some value →
        ValueTyping assumptions types value type)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := source)
  case natural =>
    intro context n types env envTyped value found
    simp only [immediateValue,scalarValue,Option.some.injEq] at found
    subst value; exact .natural n
  case boolean =>
    intro context boolean types env envTyped value found
    simp only [immediateValue,scalarValue,Option.some.injEq] at found
    subst value; exact .boolean boolean
  case label =>
    intro context label types env envTyped value found
    simp only [immediateValue,scalarValue,Option.some.injEq] at found
    subst value; exact .label label
  case lambda =>
    intro context body annotation uses bodyTyped safe valid captures _fits ih types env envTyped value found
    simp only [immediateValue,Option.some.injEq] at found
    subst value; exact .closure envTyped bodyTyped safe valid captures
  case conversion =>
    intro context term actual expected uses prior agreement ih types env envTyped value found
    exact .conversion (ih types env envTyped value found) agreement
  case nil =>
    intros; trivial
  case cons =>
    intros; trivial
  case nil =>
    intros; trivial
  case cons =>
    intros; trivial
  all_goals (intros; simp [immediateValue,scalarValue] at *)

/-- Demanding ANY well-typed address preserves its assigned type in all three
cell phases. A cyclic active demand may become blackhole, never missingCell.
Suspended origins retain their source derivation and capture quantities. -/
public theorem typed_enter_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {address : Address}
    (typed : StateTyping assumptions types state result)
    (enter : state.control = .enter address) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have assigned : types[address]? = some typed.current := by
    have control := typed.control
    rw [enter] at control
    cases control with | enter assigned => exact assigned
  obtain ⟨cell,found,cellTyped⟩ := typed.heap.cell address typed.current assigned
  cases cellTyped with
  | suspended origin _ =>
    refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
    · simpa [stepRaw,enter,found] using heap_typed_set typed.heap assigned (.evaluating origin (heap_type_pure typed.heap assigned))
    · simpa [stepRaw,enter,found] using (ControlTyping.evaluate origin)
    · simpa [stepRaw,enter,found] using (StackTyping.cons (.update assigned (heap_type_pure typed.heap assigned)) typed.stack)
  | evaluating origin _ =>
    refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
    · simpa [stepRaw,enter,found] using typed.heap
    · simpa [stepRaw,enter,found] using (ControlTyping.blackhole assigned)
    · simpa [stepRaw,enter,found] using typed.stack
  | cached origin value _ =>
    refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
    · simpa [stepRaw,enter,found] using typed.heap
    · simpa [stepRaw,enter,found] using (ControlTyping.returned value)
    · simpa [stepRaw,enter,found] using typed.stack

/-- Calling a lexical closure allocates the actual argument source at the
closure's authored domain representative. Its body keeps the original capture
and quantity evidence; component conversions remain in the continuation. A
first-class specification enters its stored extension without consuming the
argument frame. This follows the actual machine's two application branches. -/
public theorem typed_argument_return_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {argument : Term}
    {environment : Environment} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .argument argument environment :: rest) :
    ∃ after, TypeExtension types after ∧ Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control; rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨ft,domain,codomain,reuse,quantity,argumentOrigin,callableEq,copyAllowed,fnTyped,restTyped⟩ :=
    stack_argument_value typed.stack valueTyped argument environment rest stack
  rcases callable_value_form fnTyped callableEq with ⟨body,capturedEnvironment,rfl⟩ | ⟨metadata,extension,rfl⟩
  · obtain ⟨captured,normal⟩ := Obend.Core.MachineTyping.Next.value_closure_origin
      (fun a b h => (sameType_iff assumptions a b).mp h) fnTyped body capturedEnvironment rfl
    have ftEq := closure_callable_type normal callableEq
    rw [ftEq] at normal
    obtain ⟨_,_,domainEq,codomainEq⟩ := TypeGraph.arrow_components normal
    let after := types ++ [captured.annotation.domain]
    have extension : TypeExtension types after := type_extension_append types _
    have assigned : after[state.heap.size]? = some captured.annotation.domain := by rw [← typed.heap.length]; simp [after]
    let argumentNext : ClosureTyping assumptions after ⟨argument,environment⟩ captured.annotation.domain :=
      ⟨argumentOrigin.context,argumentOrigin.uses,argumentOrigin.environment.weaken extension,
        .conversion argumentOrigin.source ((sameType_iff assumptions _ _).mpr ((TypeGraph.equivalent_equivalence assumptions).symm domainEq)),argumentOrigin.safe,argumentOrigin.contextValid⟩
    let bodyNext : ClosureTyping assumptions after ⟨body,state.heap.size :: capturedEnvironment⟩ captured.annotation.codomain :=
      ⟨⟨captured.annotation.domain,captured.annotation.parameter⟩ :: captured.context,captured.uses,
        (captured.environmentTyped.weaken extension).cons assigned,captured.bodyTyped,captured.safe,captured.valid⟩
    refine ⟨after,extension,⟨step_alloc_certificate typed after captured.annotation.codomain ?_ ?_ ?_⟩⟩
    · have domainPure : captured.annotation.domain.isComputation = false := by
        rw [TypeGraph.equivalent_isComputation domainEq]
        exact argumentAllowed_not_computation copyAllowed
      simpa [stepRaw,returned,stack] using heap_typed_push typed.heap (.suspended argumentNext domainPure)
    · simpa [stepRaw,returned,stack] using (ControlTyping.evaluate bodyNext)
    · simpa [stepRaw,returned,stack] using
        (StackTyping.weaken extension (.conversion ((sameType_iff assumptions _ _).mpr codomainEq) restTyped))
  · obtain ⟨actualMetadata,actualExtension,metadataAssigned,extensionAssigned,related⟩ :=
      Obend.Core.MachineTyping.Next.value_specification_origin
        (fun a b h => (sameType_iff assumptions a b).mp h) fnTyped metadata extension rfl
    obtain ⟨metadataType,extensionType,ftEq⟩ := specification_callable_type related callableEq
    rw [ftEq] at related callableEq
    have extensionEq := (TypeGraph.specification_components related).2
    have extensionCallable : callable extensionType = .arrow reuse quantity domain codomain := callableEq
    refine ⟨types,type_extension_refl types,⟨step_certificate typed actualExtension ?_ ?_ ?_⟩⟩
    · simpa [stepRaw,returned,stack] using typed.heap
    · simpa [stepRaw,returned,stack] using (ControlTyping.enter extensionAssigned)
    · simpa [stepRaw,returned,stack] using
        (StackTyping.conversion ((sameType_iff assumptions _ _).mpr extensionEq)
          (.cons (.argument argumentOrigin extensionCallable copyAllowed) restTyped))

/-- The actual mix-generated lexical body is reusable under the checked operand
capture premise. Both generated parameters retain their shareability evidence;
composition does not make an affine captured environment duplicable. -/
@[expose] public def reusable_mix_body {assumptions : Assumptions} {context : Context} {lower upper : Term}
    {lowerType upperType self inherited middle provided : Ty} {lu uu : Uses}
    (lowerTyped : PartialTyping assumptions context lower lowerType lu)
    (upperTyped : PartialTyping assumptions context upper upperType uu)
    (lowerCallable : callable lowerType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle))
    (upperCallable : callable upperType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted middle provided))
    (captures : reusableCaptures assumptions.shareableVariables context (addUses lu uu) = true)
    (selfShare : self.shareableUnder assumptions.shareableVariables = true)
    (inheritedShare : inherited.shareableUnder assumptions.shareableVariables = true)
    (middleShare : middle.shareableUnder assumptions.shareableVariables = true)
    (contextValid : validContext assumptions.shareableVariables context = true) :
    ReusableTerm assumptions context (mixBody lower upper)
      (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided)) := by
  let selfBinding : Binding := ⟨self,.unrestricted⟩
  let inheritedBinding : Binding := ⟨inherited,.unrestricted⟩
  have selfValid : validContext assumptions.shareableVariables [selfBinding] = true := by
    simp [validContext,selfBinding,selfShare,Ty.bearsCustody_of_shareableUnder selfShare]
  have inheritedValid : validContext assumptions.shareableVariables [inheritedBinding] = true := by
    simp [validContext,inheritedBinding,inheritedShare,Ty.bearsCustody_of_shareableUnder inheritedShare]
  have oneValid : validContext assumptions.shareableVariables (selfBinding :: context) = true := by
    simpa [validContext,selfBinding,selfShare,Ty.bearsCustody_of_shareableUnder selfShare] using contextValid
  have twoValid : validContext assumptions.shareableVariables (inheritedBinding :: selfBinding :: context) = true := by
    simpa [validContext,inheritedBinding,inheritedShare,Ty.bearsCustody_of_shareableUnder inheritedShare] using oneValid
  have lowerCaptures := reusable_add_uses_left assumptions.shareableVariables context lu uu (source_uses_length lowerTyped) (source_uses_length upperTyped) captures
  have upperCaptures := reusable_add_uses_left assumptions.shareableVariables context uu lu (source_uses_length upperTyped) (source_uses_length lowerTyped) (by simpa only [add_uses_comm] using captures)
  let lowerReusable : ReusableTerm assumptions context lower lowerType := ⟨lu,lowerTyped,lowerCaptures⟩
  let upperReusable : ReusableTerm assumptions context upper upperType := ⟨uu,upperTyped,upperCaptures⟩
  let lowerShifted := lowerReusable.shiftTwo selfBinding inheritedBinding selfValid inheritedValid
  let upperShifted := upperReusable.shiftTwo selfBinding inheritedBinding selfValid inheritedValid
  let selfTerm : ReusableTerm assumptions (inheritedBinding :: selfBinding :: context) (.bound 1) self :=
    ReusableTerm.«variable» (binding := selfBinding) rfl rfl selfShare
  let inheritedTerm : ReusableTerm assumptions (inheritedBinding :: selfBinding :: context) (.bound 0) inherited :=
    ReusableTerm.«variable» (binding := inheritedBinding) rfl rfl inheritedShare
  let lowerSelf := lowerShifted.apply selfTerm lowerCallable selfShare
  let upperSelf := upperShifted.apply selfTerm upperCallable selfShare
  let lowerInherited := lowerSelf.apply inheritedTerm rfl inheritedShare
  let body := upperSelf.apply lowerInherited rfl middleShare
  exact (body.abstraction twoValid).abstraction oneValid

/-- The suspended knot created by Fix is typed using the same recursive address
as both the lexical self binding and the resulting target. No evaluation or
termination of that knot is required by this construction. -/
@[expose] public def reusable_fix_body {assumptions : Assumptions} {context : Context} {spec seed : Term}
    {specType inherited target : Ty} {su iu : Uses}
    (specTyped : PartialTyping assumptions context spec specType su)
    (specCallable : callable specType = .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited target))
    (seedTyped : PartialTyping assumptions context seed inherited iu)
    (targetShare : target.shareableUnder assumptions.shareableVariables = true)
    (seedAllowed : argumentAllowed assumptions .unrestricted context inherited iu = true)
    (specCaptures : reusableCaptures assumptions.shareableVariables context su = true) :
    ReusableTerm assumptions (⟨target,.unrestricted⟩ :: context)
      (.app (.app (spec.rename Nat.succ) (.bound 0)) (seed.rename Nat.succ)) target := by
  obtain ⟨-,seedFacts⟩ : (inherited.isComputation = false ∧ linearFree context iu = true) ∧
      (inherited.shareableUnder assumptions.shareableVariables = true ∧
      reusableCaptures assumptions.shareableVariables context iu = true) := by
    simpa [argumentAllowed] using seedAllowed
  let binding : Binding := ⟨target,.unrestricted⟩
  have valid : validContext assumptions.shareableVariables [binding] = true := by
    simp [validContext,binding,targetShare,Ty.bearsCustody_of_shareableUnder targetShare]
  let specReusable : ReusableTerm assumptions context spec specType := ⟨su,specTyped,specCaptures⟩
  let seedReusable : ReusableTerm assumptions context seed inherited := ⟨iu,seedTyped,seedFacts.2⟩
  let selfTerm : ReusableTerm assumptions (binding :: context) (.bound 0) target :=
    ReusableTerm.«variable» (binding := binding) rfl rfl targetShare
  exact ((specReusable.weaken binding valid).apply selfTerm specCallable targetShare).apply
    (seedReusable.weaken binding valid) rfl seedFacts.1

theorem source_mix_expansion {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .mix lower upper => validContext assumptions.shareableVariables context = true →
        Nonempty (ReusableTerm assumptions context (mixBody lower upper) type)
    | _ => True := by
  apply PartialTyping.rec
    (motive_1 := fun context term type _ _ => match term with
      | .mix lower upper => validContext assumptions.shareableVariables context = true →
          Nonempty (ReusableTerm assumptions context (mixBody lower upper) type)
      | _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := source)
  case conversion =>
    intro context term actual expected uses prior agreement ih
    cases term <;> try trivial
    intro valid
    obtain ⟨expanded⟩ := ih valid
    exact ⟨⟨expanded.uses,.conversion expanded.derivation agreement,expanded.captures⟩⟩
  case mix =>
    intro context lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped lowerCallable upperCallable captures selfShare inheritedShare middleShare ihLower ihUpper valid
    exact ⟨reusable_mix_body lowerTyped upperTyped lowerCallable upperCallable captures selfShare inheritedShare middleShare valid⟩
  all_goals (intros; trivial)

/-- Evaluating every checked mix, including source result conversions, preserves
its actual lexical capture qualification and the executor's generated body. -/
public theorem typed_mix_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {lower upper : Term} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    obtain ⟨expanded⟩ := source_mix_expansion origin.source origin.contextValid
    let next : ClosureTyping assumptions types ⟨mixBody lower upper,environment⟩ typed.current :=
      ⟨origin.context,expanded.uses,origin.environment,expanded.derivation,
        reusable_uses_safe _ _ _ expanded.captures,origin.contextValid⟩
    refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
    · simpa [stepRaw,evaluate] using typed.heap
    · simpa [stepRaw,evaluate] using (ControlTyping.evaluate next)
    · simpa [stepRaw,evaluate] using typed.stack

theorem source_fix_expansion {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .fix spec seed => ∃ target,
        target.shareableUnder assumptions.shareableVariables = true ∧
        Nonempty (ReusableTerm assumptions (⟨target,.unrestricted⟩ :: context)
          (.app (.app (spec.rename Nat.succ) (.bound 0)) (seed.rename Nat.succ)) target) ∧
        ConversionPath assumptions target type
    | _ => True := by
  apply PartialTyping.rec
    (motive_1 := fun context term type _ _ => match term with
      | .fix spec seed => ∃ target,
          target.shareableUnder assumptions.shareableVariables = true ∧
          Nonempty (ReusableTerm assumptions (⟨target,.unrestricted⟩ :: context)
            (.app (.app (spec.rename Nat.succ) (.bound 0)) (seed.rename Nat.succ)) target) ∧
          ConversionPath assumptions target type
      | _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := source)
  case conversion =>
    intro context term actual expected uses prior agreement ih
    cases term <;> try trivial
    obtain ⟨target,share,expanded,path⟩ := ih
    exact ⟨target,share,expanded,.step path agreement⟩
  case fix =>
    intro context spec seed specType inherited target su iu specTyped callableEq seedTyped share allowed captures ihSpec ihSeed
    exact ⟨target,share,⟨reusable_fix_body specTyped callableEq seedTyped share allowed captures⟩,.refl target⟩
  all_goals (intros; trivial)

/-- Generic Fix preserves typed address assignments at its actual cyclic
allocation. The suspended origin contains the new address, preserving the
recursive self type and capture quantities without any termination premise. -/
public theorem typed_fix_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {spec seed : Term} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.fix spec seed) environment) :
    ∃ after, TypeExtension types after ∧
      Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    obtain ⟨target,share,⟨expanded⟩,path⟩ := source_fix_expansion origin.source
    let after := types ++ [target]
    have extension : TypeExtension types after := type_extension_append types [target]
    have assigned : after[state.heap.size]? = some target := by
      rw [← typed.heap.length]
      simp [after]
    have valid : validContext assumptions.shareableVariables (⟨target,.unrestricted⟩ :: origin.context) = true := by
      simpa [validContext,share,Ty.bearsCustody_of_shareableUnder share] using origin.contextValid
    let next : ClosureTyping assumptions after
        ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (seed.rename Nat.succ),state.heap.size :: environment⟩ target :=
      ⟨⟨target,.unrestricted⟩ :: origin.context,expanded.uses,
        (origin.environment.weaken extension).cons assigned,expanded.derivation,
        reusable_uses_safe _ _ _ expanded.captures,valid⟩
    refine ⟨after,extension,⟨step_alloc_certificate typed after target ?_ ?_ ?_⟩⟩
    · simpa [stepRaw,evaluate] using
        heap_typed_push typed.heap (CellTyping.suspended next (Ty.shareableUnder_not_computation _ _ share))
    · simpa [stepRaw,evaluate] using (ControlTyping.enter assigned)
    · simpa [stepRaw,evaluate] using
        (StackTyping.weaken extension (stack_convert_path path typed.stack))

/-- Bound-variable demand preserves the actual immutable address type; source
conversions move into the continuation instead of retyping the heap identity. -/
public theorem typed_bound_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {index : Nat} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.bound index) environment) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    obtain ⟨binding,found,path⟩ := source_bound_assignment origin.source
    obtain ⟨address,environmentFound,assigned⟩ := origin.environment.binding index binding found
    refine ⟨step_certificate typed binding.type ?_ ?_ ?_⟩
    · simpa [stepRaw,evaluate,environmentFound] using typed.heap
    · simpa [stepRaw,evaluate,environmentFound] using (ControlTyping.enter assigned)
    · simpa [stepRaw,evaluate,environmentFound] using (stack_convert_path path typed.stack)

/-- Application inversion retains the actual copy-argument guard and a finite
conversion path for the authored result type. -/
theorem source_application_decomposition {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .app function argument => ∃ functionType domain codomain functionUses argumentUses reuse quantity,
        PartialTyping assumptions context function functionType functionUses ∧
        PartialTyping assumptions context argument domain argumentUses ∧
        callable functionType = .arrow reuse quantity domain codomain ∧
        argumentAllowed assumptions quantity context domain argumentUses = true ∧
        uses = addUses functionUses argumentUses ∧ ConversionPath assumptions codomain type
    | _ => True := by
  apply PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .app function argument => ∃ functionType domain codomain functionUses argumentUses reuse quantity,
          PartialTyping assumptions context function functionType functionUses ∧
          PartialTyping assumptions context argument domain argumentUses ∧
          callable functionType = .arrow reuse quantity domain codomain ∧
          argumentAllowed assumptions quantity context domain argumentUses = true ∧
          uses = addUses functionUses argumentUses ∧ ConversionPath assumptions codomain type
      | _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := source)
  case conversion =>
    intro context term actual expected uses prior agreement ih
    cases term <;> try trivial
    obtain ⟨ft,domain,codomain,fu,au,reuse,quantity,fn,arg,callable,copyAllowed,counts,path⟩ := ih
    exact ⟨ft,domain,codomain,fu,au,reuse,quantity,fn,arg,callable,copyAllowed,counts,.step path agreement⟩
  case application =>
    intro context function argument functionType argumentType domain codomain fu au reuse quantity fn arg callable same copyAllowed ihFn ihArg
    subst argumentType
    exact ⟨functionType,domain,codomain,fu,au,reuse,quantity,fn,arg,callable,copyAllowed,rfl,.refl codomain⟩
  all_goals (intros; trivial)

/-- Focusing the function of ANY well-typed application keeps both lexical
origins, safely splits the usage vector, and retains copy/shareability evidence
on the actual argument continuation. -/
public theorem typed_application_focus_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {function argument : Term} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.app function argument) environment) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    obtain ⟨ft,domain,codomain,fu,au,reuse,quantity,fn,arg,callable,copyAllowed,counts,path⟩ :=
      source_application_decomposition origin.source
    have safe : safeUses origin.context (addUses fu au) = true := by simpa [counts] using origin.safe
    have fnSafe := safe_add_uses_left origin.context fu au (source_uses_length fn) (source_uses_length arg) safe
    have argSafe := safe_add_uses_right origin.context fu au (source_uses_length fn) (source_uses_length arg) safe
    let fnOrigin : ClosureTyping assumptions types ⟨function,environment⟩ ft :=
      ⟨origin.context,fu,origin.environment,fn,fnSafe,origin.contextValid⟩
    let argOrigin : ClosureTyping assumptions types ⟨argument,environment⟩ domain :=
      ⟨origin.context,au,origin.environment,arg,argSafe,origin.contextValid⟩
    refine ⟨step_certificate typed ft ?_ ?_ ?_⟩
    · simpa [stepRaw,evaluate] using typed.heap
    · simpa [stepRaw,evaluate] using (ControlTyping.evaluate fnOrigin)
    · simpa [stepRaw,evaluate] using
        (StackTyping.cons (FrameTyping.argument argOrigin callable copyAllowed) (stack_convert_path path typed.stack))

/-- Evaluating any immediate source value preserves its assigned result type,
including captured reusable/once lambdas and both String and Bool scalars. -/
public theorem typed_immediate_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {term : Term} {environment : Environment} {value : RuntimeValue}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate term environment)
    (immediate : immediateValue term environment = some value) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [evaluate] at control
    cases control with
    | evaluate closure => exact immediate_value_typed closure.source types environment closure.environment value immediate
  have next : stepRaw state = {state with control := .returned value} := by
    cases term <;> simp [immediateValue,scalarValue] at immediate
    all_goals subst value; simp [stepRaw,evaluate]
  refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
  · simpa [next] using typed.heap
  · simpa [next] using (ControlTyping.returned valueTyped)
  · simpa [next] using typed.stack

/-- Updating a demanded thunk stores a value of the thunk's original assigned
source type. BusyInvariant supplies the actual evaluating origin; no arbitrary
update-validity oracle is needed. -/
public theorem typed_update_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {address : Address} {value : RuntimeValue} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .update address :: rest) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨addressType,assigned,addressValue,restTyped⟩ :=
    stack_update_value typed.stack valueTyped address rest stack
  obtain ⟨origin,found⟩ := Obend.Core.Invariant.busy_update_exists typed.busy stack
  obtain ⟨cell,found',cellTyped⟩ := typed.heap.cell address addressType assigned
  have same : cell = .evaluating origin := Option.some.inj (found'.symm.trans found)
  rw [same] at cellTyped
  cases cellTyped with
  | evaluating originTyped addressPure =>
    refine ⟨step_certificate typed addressType ?_ ?_ ?_⟩
    · simpa [stepRaw,returned,stack,found] using
        heap_typed_set typed.heap assigned (.cached originTyped addressValue addressPure)
    · simpa [stepRaw,returned,stack,found] using (ControlTyping.returned addressValue)
    · simpa [stepRaw,returned,stack,found] using restTyped

/-- A returned value with no pending demand frames completes at the promised
result type. Completion itself makes no termination assertion about the source. -/
public theorem typed_completion_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value) (empty : state.stack = []) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
  · simpa [stepRaw,returned,empty] using typed.heap
  · simpa [stepRaw,returned,empty] using (ControlTyping.complete valueTyped)
  · simpa [stepRaw,returned,empty] using typed.stack

/-! ## Sums: injection, case and Boolean branching -/

end Obend.Core.Proofs.Preservation
