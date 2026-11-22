module
/- Preservation case: the record destructor's frame. A typed record returned to a `split` frame has
every named field (no `missingField`, no `wrongValue`); the destructor allocates one indirection cell
per field, typed at the parameter's declared member, and pushes one argument frame per parameter. -/
public import Obend.Core.Proofs.Preservation.Cases.Records
import all Obend.Core.Check
import all Obend.Core.Proofs.Preservation.Cases.Records
namespace Obend.Core.Proofs.Preservation
open Obend.Core.Ty Obend.Core.Check Obend.Core.Term Obend.Core.Machine Obend.Core.MachineTyping
set_option autoImplicit false

/-- Two lists related entry by entry. -/
inductive Both {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Both R [] []
  | cons {x : α} {y : β} {xs : List α} {ys : List β} : R x y → Both R xs ys → Both R (x :: xs) (y :: ys)

theorem closed_isRow {bounds : Bounds} : ∀ {row : Ty}, row.tail = .emptyRow →
    ∃ fuel, row.isRow bounds fuel = true
  | .emptyRow, _ => ⟨1, rfl⟩
  | .field _ _ tail, h => by
    obtain ⟨fuel, r⟩ := closed_isRow (bounds := bounds) (row := tail) (by simpa [Ty.tail] using h)
    exact ⟨fuel + 1, by simpa [Ty.isRow] using r⟩
  | .natural, h | .label, h | .boolean, h | .variable _, h | .arrow _ _ _ _, h | .specification _ _, h
  | .prototype _ _, h | .custody _, h | .variant _, h | .computation _ _ _, h => by simp [Ty.tail] at h

theorem stack_split_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ names function environment rest, stack = .split names function environment :: rest →
      ∃ row functionType output members, ValueTyping assumptions types value row ∧ row.tail = .emptyRow ∧
        Nonempty (ClosureTyping assumptions types ⟨function, environment⟩ functionType) ∧
        SplitShape assumptions row names members functionType output ∧
        StackTyping assumptions types rest output result := by
  induction continuation with
  | nil => intro names function environment rest impossible; simp at impossible
  | cons frame restTyped =>
      intro names function environment rest same
      cases same
      cases frame with
      | split functionTyped closed shape =>
          exact ⟨_, _, _, _, valueTyped, closed, ⟨functionTyped⟩, shape, restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro names function environment rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

/-- Every name a typed destructor names is a field of the returned record: the destructor finds an
address for each, typed along a conversion path to the parameter's member. -/
theorem split_lookups {assumptions : Assumptions} {types : AddressTypes} {fields : List (String × Address)}
    {row : Ty} (rowTyped : ValueTyping assumptions types (.record fields) row) :
    ∀ {names : List String} {members : List Ty} {functionType output : Ty},
      SplitShape assumptions row names members functionType output →
      ∃ cells : List (Address × Ty), splitValues fields names = some (cells.map Prod.fst) ∧
        Both (fun cell member => types[cell.1]? = some cell.2 ∧ ConversionPath assumptions cell.2 member)
          cells members
  | [], [], _, _, _ => ⟨[], rfl, .nil⟩
  | name :: names, member :: members, _, _, ⟨_, _, _, _, ⟨fuel, found, lookup, same⟩, _, _, rest⟩ => by
    obtain ⟨fields', address, actual, shape, hit, assigned, path⟩ :=
      value_record_member rowTyped fuel name found lookup
    cases shape
    obtain ⟨cells, values, related⟩ := split_lookups rowTyped rest
    refine ⟨(address, actual) :: cells, ?_, .cons ⟨assigned, .step path same⟩ related⟩
    simp [splitValues, hit, values]
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => h.elim

/-- Allocation of cells each typed in a fixed context, at the listed types. -/
theorem split_cells_allocated {assumptions : Assumptions} {types : AddressTypes} {context : Context}
    {environment : Environment} (environmentTyped : EnvironmentTyping types context environment)
    (valid : validContext assumptions.shareableVariables context = true) :
    ∀ (cells : List (String × Term)) (cellTypes : List Ty) (before : AddressTypes) (heap : Array Cell),
      TypeExtension types before → HeapTyping assumptions before heap →
      Both (fun cell type => ∃ uses, PartialTyping assumptions context cell.2 type uses ∧
        safeUses context uses = true ∧ type.isComputation = false) cells cellTypes →
      HeapTyping assumptions (before ++ cellTypes) (allocateFields heap environment cells).1 ∧
        (allocateFields heap environment cells).2.map Prod.snd = (List.range cells.length).map (heap.size + ·)
  | [], [], before, heap, _, heapTyped, .nil => by
    simpa [allocateFields] using heapTyped
  | (name, body) :: cells, type :: cellTypes, before, heap, extension, heapTyped, .cons ⟨uses, typed, safe, pure⟩ rest => by
    have extension' : TypeExtension types (before ++ [type]) :=
      type_extension_trans extension (type_extension_append before [type])
    let origin : ClosureTyping assumptions (before ++ [type]) ⟨body, environment⟩ type :=
      ⟨context, uses, environmentTyped.weaken extension', typed, safe, valid⟩
    have pushed := heap_typed_push heapTyped (CellTyping.suspended origin pure)
    obtain ⟨tailHeap, tailAddresses⟩ :=
      split_cells_allocated environmentTyped valid cells cellTypes (before ++ [type]) _ extension' pushed rest
    refine ⟨by simpa only [allocate_fields_cons, List.append_assoc, List.singleton_append] using tailHeap, ?_⟩
    simp only [allocate_fields_cons, List.map_cons, tailAddresses, Array.size_push, List.length_cons,
      List.range_succ_eq_map, List.map_map]
    congr 1
    apply List.map_congr_left; intro i _; simp; omega

/-- The argument frames a destructor pushes, one per parameter, typed against the function's spine. -/
theorem split_frames_typed {assumptions : Assumptions} {types : AddressTypes} {row result : Ty}
    {rest : List Frame} :
    ∀ {names : List String} {members : List Ty} {functionType output : Ty} (fresh : List Address),
      SplitShape assumptions row names members functionType output →
      Both (fun address member => types[address]? = some member) fresh members →
      StackTyping assumptions types rest output result →
      StackTyping assumptions types (splitFrames fresh ++ rest) functionType result
  | [], [], _, _, [], shape, .nil, restTyped => by cases shape; simpa [splitFrames] using restTyped
  | _ :: _, member :: _, _, _, address :: fresh, ⟨reuse, quantity, codomain, callable, _, pure, share, shape⟩,
      .cons assigned related, restTyped => by
    let binder : Quantity := if quantity = .erased then .affine else quantity
    let context : Context := [⟨member, binder⟩]
    have valid : validContext assumptions.shareableVariables context = true := by
      cases quantity <;> simp_all [context, binder, validContext]
    have safe : safeUses context (variableUses context 0) = true := by
      cases quantity <;> simp [context, binder, safeUses, variableUses, safeQuantity]
    let argument : ClosureTyping assumptions types ⟨.bound 0, [address]⟩ member :=
      ⟨context, variableUses context 0, (EnvironmentTyping.empty types).cons assigned,
        PartialTyping.bound (binding := ⟨member, binder⟩) rfl, safe, valid⟩
    have allowed : argumentAllowed assumptions quantity argument.context member argument.uses = true := by
      change argumentAllowed assumptions quantity context member (variableUses context 0) = true
      cases quantity
      · simp [argumentAllowed, context, binder, pure, linearFree, variableUses]
      · simp [argumentAllowed, context, binder, pure, linearFree, variableUses]
      · simp [argumentAllowed, context, binder, pure, linearFree, variableUses]
      · simp [validContext] at share
        simp [argumentAllowed, context, binder, pure, share.1, linearFree, reusableCaptures, variableUses]
    exact .cons (.argument argument callable allowed)
      (by simpa [splitFrames] using split_frames_typed fresh shape related restTyped)
  | [], _ :: _, _, _, _, h, _, _ | _ :: _, [], _, _, _, h, _, _ => h.elim
  | [], [], _, _, _ :: _, _, h, _ => by cases h
  | _ :: _, _ :: _, _, _, [], _, h, _ => by cases h

theorem forall2_length' {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β},
    Both R xs ys → xs.length = ys.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ rest => by simp [forall2_length' rest]

/-- The destructor's cells, typed: cell `i` is `bound i` in the field addresses' context, at member `i`. -/
theorem split_cells_typed {assumptions : Assumptions} {types : AddressTypes} :
    ∀ (cells : List (Address × Ty)) (members : List Ty) (offset : Nat) (context : Context),
      Both (fun cell member => types[cell.1]? = some cell.2 ∧ ConversionPath assumptions cell.2 member)
        cells members →
      (∀ i cell, cells[i]? = some cell → context[offset + i]? = some ⟨cell.2, .linear⟩) →
      (∀ binding ∈ context, binding.quantity = .linear) →
      (∀ member ∈ members, member.isComputation = false) →
      Both (fun cell type => ∃ uses, PartialTyping assumptions context cell.2 type uses ∧
        safeUses context uses = true ∧ type.isComputation = false)
        ((List.range' offset cells.length).map fun index => ("", Term.bound index)) members
  | [], [], _, _, .nil, _, _, _ => by simp only [List.length_nil, List.range'_zero, List.map_nil]; exact .nil
  | cell :: cells, member :: members, offset, context, .cons ⟨_, path⟩ rest, at_, linear, pure => by
    simp only [List.length_cons, List.range'_succ, List.map_cons]
    refine .cons ⟨variableUses context offset, source_convert_path (.bound (by simpa using at_ 0 cell rfl)) path,
      ?_, ?_⟩ ?_
    · have bound : offset < context.length := by
        have := at_ 0 cell rfl; simp at this; exact (List.getElem?_eq_some_iff.mp this).1
      simp only [safeUses, variableUses, List.length_map, List.length_range, beq_self_eq_true, Bool.true_and]
      refine List.all_eq_true.mpr fun pair member => ?_
      obtain ⟨⟨binding, count⟩, hm, rfl⟩ : ∃ p ∈ context.zip ((List.range context.length).map
          fun position => if position = offset then 1 else 0), p = pair := ⟨pair, member, rfl⟩
      have q := linear binding (List.of_mem_zip hm).1
      have c : count ≤ 1 := by
        obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp (List.of_mem_zip hm).2
        rw [← he]; simp; split <;> omega
      simp [safeQuantity, q, c]
    · exact pure member (by simp)
    · exact split_cells_typed cells members (offset + 1) context rest
        (fun i c h => by simpa [Nat.add_assoc, Nat.add_comm 1] using at_ (i + 1) c h) linear
        (fun m hm => pure m (by simp [hm]))
  | [], _ :: _, _, _, h, _, _, _ | _ :: _, [], _, _, h, _, _, _ => by cases h

theorem Both.get {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β} {i : Nat} {x : α},
    Both R xs ys → xs[i]? = some x → ∃ y, ys[i]? = some y ∧ R x y
  | _ :: _, _ :: _, 0, _, .cons r _, h => by simp at h; subst h; exact ⟨_, rfl, r⟩
  | _ :: _, _ :: _, i + 1, _, .cons _ rest, h => by simpa using Both.get rest (by simpa using h)
  | [], [], _, _, .nil, h => by simp at h

theorem SplitShape.pure {assumptions : Assumptions} {row : Ty} :
    ∀ {names : List String} {members : List Ty} {functionType output : Ty},
      SplitShape assumptions row names members functionType output → ∀ member ∈ members, member.isComputation = false
  | [], [], _, _, _ => by simp
  | _ :: _, _ :: _, _, _, ⟨_, _, _, _, _, pure, _, rest⟩ => by
    intro m hm; simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact pure
    · exact SplitShape.pure rest m hm
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => h.elim

theorem fresh_assigned {types : AddressTypes} :
    ∀ (members : List Ty) (offset : Nat), types.length = offset →
      ∀ (prefix_ : List Ty), Both (fun address member => (types ++ prefix_ ++ members)[address]? = some member)
        ((List.range members.length).map (offset + prefix_.length + ·)) members
  | [], _, _, _ => by simp; exact .nil
  | member :: members, offset, length, prefix_ => by
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine .cons ?_ ?_
    · simp [List.getElem?_append_right, length]
    · have := fresh_assigned members offset length (prefix_ ++ [member])
      simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at this
      have e : (List.range members.length).map ((fun x => offset + prefix_.length + x) ∘ Nat.succ) =
          (List.range members.length).map (fun x => offset + (prefix_.length + 1) + x) := by
        apply List.map_congr_left; intro i _; simp; omega
      rw [e, List.append_assoc]; exact this

/-- A typed record returned to a destructor's frame: every named field is present, the cells and
argument frames it pushes are typed, and the function is evaluated against its spine. -/
public theorem typed_split_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {names : List String} {function : Term}
    {environment : Environment} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .split names function environment :: rest) :
    ∃ after, TypeExtension types after ∧ Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨row, functionType, output, members, rowTyped, closed, ⟨functionTyped⟩, shape, restTyped⟩ :=
    stack_split_value typed.stack valueTyped names function environment rest stack
  obtain ⟨fuel, isRow⟩ := closed_isRow (bounds := assumptions.bounds) closed
  obtain ⟨fields, rfl⟩ := record_value_form rowTyped fuel isRow
  obtain ⟨cells, values, related⟩ := split_lookups rowTyped shape
  let context : Context := cells.map fun cell => ⟨cell.2, .linear⟩
  have environmentTyped : EnvironmentTyping types context (cells.map Prod.fst) := by
    refine ⟨by simp [context], fun i binding found => ?_⟩
    simp only [context, List.getElem?_map, Option.map_eq_some_iff] at found
    obtain ⟨cell, hc, rfl⟩ := found
    obtain ⟨_, _, assigned, _⟩ := Both.get related hc
    exact ⟨cell.1, by simp [hc], assigned⟩
  have valid : validContext assumptions.shareableVariables context = true := by
    simp [context, validContext]
  have cellsTyped := split_cells_typed (types := types) cells members 0 context related
    (fun i cell h => by simp [context, h]) (fun b hb => by simp [context] at hb; obtain ⟨_, _, _, rfl⟩ := hb; rfl)
    (SplitShape.pure shape)
  have cellsEq : splitCells (cells.map Prod.fst).length =
      (List.range' 0 cells.length).map fun index => ("", Term.bound index) := by
    simp [splitCells, List.range_eq_range']
  rw [← cellsEq] at cellsTyped
  obtain ⟨heapTyped, freshEq⟩ := split_cells_allocated environmentTyped valid _ members types state.heap
    (type_extension_refl types) typed.heap cellsTyped
  let after := types ++ members
  have extension : TypeExtension types after := type_extension_append types members
  have lengthEq : (splitCells (cells.map Prod.fst).length).length = members.length := by
    rw [splitCells_length, List.length_map, forall2_length' related]
  have freshTyped := fresh_assigned (types := types) members state.heap.size typed.heap.length []
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at freshTyped
  rw [← lengthEq, ← freshEq] at freshTyped
  have stackTyped := split_frames_typed _ shape freshTyped (StackTyping.weaken extension restTyped)
  refine ⟨after, extension, ⟨step_alloc_certificate typed after functionType ?_ ?_ ?_⟩⟩
  · simpa [stepRaw, returned, stack, values, after] using heapTyped
  · simpa [stepRaw, returned, stack, values] using ControlTyping.evaluate (ClosureTyping.weaken extension functionTyped)
  · simpa [stepRaw, returned, stack, values] using stackTyped

end Obend.Core.Proofs.Preservation
