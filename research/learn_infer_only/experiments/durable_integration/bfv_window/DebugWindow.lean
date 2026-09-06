import Assurance.CiphertextWindowWitness
open Minidregg.Assurance.CiphertextWindowCell
open Minidregg.Theory.CiphertextWindow
namespace DebugWindow
def Q83 : Nat := 2199023190017*4398046486529
instance : NeZero Q83 := ⟨by decide⟩
#eval Q83
abbrev Ct := Fin 2 → Fin 1 → ZMod Q83
def ct := ciphertextStream Q83 1
#eval ct.encode (0 : Ct)
#eval (stateStream ct).encode (initial : State Ct)
#eval decide ((0 : Ct)=(0 : Ct))
def src : Ct := fun i _=>(if i=0 then 5 else 8 : Nat)
def admit (id : Nat) (bytes : List UInt8) : Bool := decide (bytes=ct.encode src)
#eval check ct.toLawful admit 128 initial ⟨⟨0,src⟩,none⟩
#eval (step ct.toLawful admit 128 initial ⟨⟨0,src⟩,none⟩).map (stateStream ct).encode
end DebugWindow
