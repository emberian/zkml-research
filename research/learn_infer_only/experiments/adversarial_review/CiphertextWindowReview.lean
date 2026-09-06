/- Independent composition check and codec-domain tooth. All implementation
phase/source/range premises stay explicit; no Rust or encryption theorem. -/
import Assurance.CiphertextWindowCell
import Theory.CiphertextWindowNoise

namespace CiphertextWindowReview
open Minidregg.Theory
open Minidregg.Theory.CiphertextWindow
open Minidregg.Theory.CiphertextWindowNoise
open Minidregg.Theory.IntegerWindowNoise
open Minidregg.Assurance.CiphertextWindowCell
open Minidregg.Assurance.ResidentDurableIntegration (Selection)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Kernel.DurableDataIntent (DataSnapshot)
set_option autoImplicit false

/-- The two reviewed lanes compose on one installed logical state, with no
independent substitute queue or detached durable history. -/
theorem installed_signed_readout {Ct : Type} [AddCommGroup Ct]
    (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (admit : Nat → List UInt8 → Bool) (q r W : Nat) (t E L : Int)
    (selected : Selection) (initialData data : DataSnapshot hash) (logical : State Ct)
    (history : ExecutedHistory ct hash admit W selected initialData data logical)
    (phase : Ct →+ ZMod q) (interpret : Entry Ct → Row r)
    (query : Fin r → Int) (outputLift : Int)
    (hp : PhasePremises q r phase interpret query logical outputLift)
    (hf : ∀ e ∈ logical.queue, Fresh (q : Int) t E (interpret e))
    (hq : 0 < (q : Int)) (ht : 0 < t) (hE : 0 ≤ E)
    (margin : 2*t*(W : Int)*L*(E+1) < (q : Int))
    (hL : queryL1 query ≤ L)
    (hm : 2*|readoutScore query (logical.queue.map interpret)| < t) :
    data.canonicalBytes selected.stateId=(stateStream ct).encode logical ∧
    centered t (rounded (q : Int) t outputLift)=readoutScore query (logical.queue.map interpret) := by
  have h := executed_history_invariant ct hash admit W selected initialData data logical history
  exact ⟨h.1, reachable_signed_decode q r W t E L hq ht hE margin
    ct.toLawful admit phase interpret query logical outputLift h.2.2.1 hp hf hL hm⟩

/-- A left-inverse codec has an injective canonical encoder, but does not by
that law alone reject noncanonical input byte strings. -/
theorem coefficient_decoder_accepts_alias :
    (coeffStream 17).toLawful.decode (StreamCodec.nat.encode 18)=some (1 : ZMod 17) ∧
    StreamCodec.nat.encode 18 ≠ (coeffStream 17).encode (1 : ZMod 17) := by
  decide +kernel

def badFreshCommand : Command (ZMod 17) := ⟨⟨0,3⟩,none⟩
def badFreshState : State (ZMod 17) := advance 1 initial badFreshCommand
def badFreshRow : Row 1 := ⟨fun _=>0,fun _=>3,fun _=>3⟩

/-- Public admission and an exact modular phase map do not establish the
issuer's fresh-error contract. The advertised E=0 margin is satisfied here;
only the missing Fresh premise blocks the wrong result. -/
theorem admission_does_not_supply_fresh :
    Reachable (coeffStream 17).toLawful (fun _ _=>true) 1 badFreshState ∧
    PhasePremises 17 1 (AddMonoidHom.id (ZMod 17)) (fun _=>badFreshRow)
      (fun _=>1) badFreshState 3 ∧
    2*(3 : Int)*1*1*(0+1)<17 ∧
    queryL1 (fun _ : Fin 1=> (1 : Int))=1 ∧
    ¬Fresh 17 3 0 badFreshRow ∧
    centered 3 (rounded 17 3 3) ≠ readoutScore (fun _=>1) [badFreshRow] := by
  have checked : check (coeffStream 17).toLawful (fun _ _=>true) 1 initial badFreshCommand=true := by
    decide +kernel
  refine ⟨.next .start badFreshCommand checked,?_,by decide,by decide,?_,by decide⟩
  · constructor
    · intro e he
      have same : e=badFreshCommand.fresh := by
        simpa [badFreshState,advance,initial] using he
      subst e
      decide +kernel
    · decide +kernel
  · unfold Fresh
    decide +kernel

/-- info: 'CiphertextWindowReview.installed_signed_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CiphertextWindowReview.installed_signed_readout
/-- info: 'CiphertextWindowReview.coefficient_decoder_accepts_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CiphertextWindowReview.coefficient_decoder_accepts_alias
/-- info: 'CiphertextWindowReview.admission_does_not_supply_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CiphertextWindowReview.admission_does_not_supply_fresh

end CiphertextWindowReview
