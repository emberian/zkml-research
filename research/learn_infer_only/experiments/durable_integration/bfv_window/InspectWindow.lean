/- Public finite-vector execution of the actual Lean window checker/step.
Not BFV encryption, Rust serialization, a noise experiment or a timing claim. -/
import Assurance.CiphertextWindowWitness
open Minidregg.Theory.CiphertextWindow
open Minidregg.Assurance.CiphertextWindowCell
open Minidregg.Assurance.CiphertextWindowCell (ciphertextStream)

namespace WindowAudit

def Q83 : Nat := 2199023190017*4398046486529
instance : NeZero Q83 := ⟨by decide⟩
abbrev Ct := Fin 2 → Fin 1 → ZMod Q83
def ct := ciphertextStream Q83 1
def source (id : Nat) : Ct := fun i _=>
  (if i=0 then id*id+17*id+5 else 19*id+8 : Nat)
def admit (id : Nat) (bytes : List UInt8) : Bool := decide (bytes=ct.encode (source id))

@[noinline] def compact (x : Ct) : Ct :=
  let values := #[x 0 0,x 1 0]
  fun i _=>values[i.val]!

theorem compact_eq (x : Ct) : compact x=x := by
  funext i j
  have hj : j=0 := Subsingleton.elim _ _
  subst j
  rcases i with ⟨i,hi⟩
  have h : i=0 ∨ i=1 := by omega
  rcases h with h|h <;> subst i <;> rfl

/-- Force a finite array after each transition, instead of retaining an
unbounded evaluation closure for the mathematical function-valued group. -/
def run (n : Nat) : Except String (State Ct × Nat × Nat) :=
  (List.range n).foldlM (fun (state,expired,codecChecks) id=>do
    let fresh : Entry Ct := ⟨id,source id⟩
    let expiry := if state.queue.length<2 then none else state.queue.head?
    let cmd : Command Ct := ⟨fresh,expiry⟩
    let some after := step ct.toLawful admit 2 state cmd | throw "valid step refused"
    if after.accumulator≠queueSum after.queue then throw "exact sum failed"
    if after.queue.length>2 then throw "window bound failed"
    if after.nextId≠id+1 then throw "counter failed"
    let codecCheck := (id+1)%1=0
    if codecCheck then
      if (stateStream ct).toLawful.decode ((stateStream ct).encode after)≠some after then
        throw "canonical state roundtrip failed"
    pure ({after with accumulator:=compact after.accumulator},expired+(if expiry.isSome then 1 else 0),codecChecks+(if codecCheck then 1 else 0)))
    (initial,0,0)

def summary (n : Nat) := (run n).map fun (s,expired,codecChecks)=>
  (n,expired,codecChecks,s.queue.length,s.nextId,
   decide (s.accumulator=queueSum s.queue),
   decide (s.queue.map Entry.admissionId=List.range' (n-2) (min n 2)))

#eval summary 16

end WindowAudit
