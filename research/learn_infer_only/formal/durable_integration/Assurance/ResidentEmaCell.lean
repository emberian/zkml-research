/- [DERIVED target] Canonical PUBLIC biased-byte cell. A present byte b means
signed integer b-128; absent is a distinct encoding. The root function remains
arbitrary, including constant: all logical claims use exact canonical bytes. -/
import Assurance.ResidentDurableIntegration
import Compiler.ResidentEmaCertificate

namespace Minidregg.Assurance.ResidentEmaCell
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Assurance.ResidentDurableIntegration
open Minidregg.Compiler.ResidentEmaCertificate (ema)
set_option autoImplicit false

def schema : Schema.{0,0,0,0} where
  Field := Unit
  FieldType := fun _ => UInt8
  Resource := Empty
  ResourceType := fun r => r.elim
  Authority := fun r => r.elim
  Evidence := fun r => r.elim
instance : DecidableEq schema.Field := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq schema.Resource := fun r => r.elim

def stateOf (b : UInt8) : LogicalState schema where
  fields := (0 : FieldStore schema).write () b
  resources := fun r => r.elim

def stateOfOption : Option UInt8 → LogicalState schema
  | none => ⟨0, fun r => r.elim⟩
  | some b => stateOf b

def byteOption (s : LogicalState schema) : Option UInt8 := s.fields ()
def signedValue (s : LogicalState schema) : Int := ((byteOption s).getD 0).toNat-128


/-- The HE gate program stores two's-complement bits; this public canonical
codec stores the sign-bit-biased byte. The transform is specified explicitly. -/
def biasedOfTwos (b : UInt8) : UInt8 := UInt8.ofNat (b.toNat+128)
def signedOfTwos (b : UInt8) : Int :=
  if b.toNat<128 then (b.toNat : Int) else (b.toNat : Int)-256

theorem biased_representation_exact (b : UInt8) :
    signedValue (stateOf (biasedOfTwos b))=signedOfTwos b := by
  change (((UInt8.ofNat (b.toNat+128)).toNat : Int)-128)=signedOfTwos b
  rw [UInt8.toNat_ofNat']
  have hb : b.toNat<256 := b.toNat_lt_size
  unfold signedOfTwos
  split_ifs <;> omega

theorem state_ext (s : LogicalState schema) : s = stateOfOption (byteOption s) := by
  cases s with
  | mk fields resources =>
    have hr : resources = fun r => r.elim := funext fun r => r.elim
    cases present : fields () with
    | none =>
      have hf : fields = (0 : FieldStore schema) := by
        apply DFinsupp.ext; intro field; cases field; simpa using present
      rw [hf,hr]; rfl
    | some b =>
      have hf : fields = (0 : FieldStore schema).write () b := by
        apply DFinsupp.ext; intro field; cases field; simp [present]
      rw [hf,hr]; rfl

def codec : LawfulCodec (LogicalState schema) where
  encode := fun s => match byteOption s with | none => [] | some b => [b]
  decode := fun bs => match bs with
    | [] => some (stateOfOption none)
    | [b] => some (stateOf b)
    | _ => none
  decode_encode := fun s => by
    rw [state_ext s]
    cases h : byteOption s <;> simp [byteOption,stateOfOption,stateOf]

def materializer (hash : List UInt8 → Digest) : Materializer schema Digest := ⟨codec,hash⟩
def cell (hash : List UInt8 → Digest) (b : UInt8) := materialize (materializer hash) (stateOf b)

theorem cell_bytes (hash : List UInt8 → Digest) (b : UInt8) : (cell hash b).bytes=[b] := rfl

theorem canonical_opens (hash : List UInt8 → Digest)
    (s : Materialized (materializer hash)) (b : UInt8) (h : s.bytes=[b]) :
    s.logical = stateOf b := by
  have decoded := congrArg codec.decode h
  change codec.decode (codec.encode s.logical)=codec.decode [b] at decoded
  rw [codec.decode_encode] at decoded
  exact Option.some.inj decoded

theorem signed_opening (hash : List UInt8 → Digest)
    (s : Materialized (materializer hash)) (b : UInt8) (h : s.bytes=[b]) :
    signedValue s.logical = (b.toNat : Int)-128 := by
  rw [canonical_opens hash s b h]; rfl

def writePatch (hash : List UInt8 → Digest) (b n : UInt8) : Patch schema Digest where
  expectedPreRoot := (cell hash b).root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{field:=(),value:=some n}]
  resourceWrites := []

theorem writePatch_accepted (hash : List UInt8 → Digest) (b n : UInt8) :
    ∃ v : ValidatedPatch (materializer hash) (cell hash b) (writePatch hash b n),
      validate (materializer hash) (cell hash b) (writePatch hash b n)=.accepted v := by
  unfold validate
  rw [dif_pos (show (writePatch hash b n).expectedPreRoot=(cell hash b).root from rfl)]
  rw [dif_pos (show (writePatch hash b n).fieldFootprint=(writePatch hash b n).namedFields by rfl)]
  rw [dif_pos (show (writePatch hash b n).resourceFootprint=(writePatch hash b n).namedResources by rfl)]
  exact ⟨_,rfl⟩

theorem patch_post (hash : List UInt8 → Digest) (b n : UInt8)
    (v : ValidatedPatch (materializer hash) (cell hash b) (writePatch hash b n)) :
    v.apply.logical=stateOf n ∧ v.apply.bytes=[n] := by
  constructor
  · apply (state_ext v.apply.logical).trans
    rfl
  · rfl

/-- Exact source/post bytes, not equal digest labels, are the semantic boundary. -/
structure OpenedPlan (hash : List UInt8 → Digest) where
  plan : Plan (materializer hash)
  preByte : UInt8
  postByte : UInt8
  preOpening : plan.pre.bytes=[preByte]
  postOpening : plan.post.bytes=[postByte]

def LogicalStep {hash : List UInt8 → Digest} (p : OpenedPlan hash) : Prop :=
  signedValue p.plan.post.logical =
    ema (signedValue p.plan.pre.logical) ((p.plan.context.command : Int)-128)

end Minidregg.Assurance.ResidentEmaCell

/- Exact-output axiom pins, observed from the recorded matching Lean check. -/

/-- info: 'Minidregg.Assurance.ResidentEmaCell.biased_representation_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaCell.biased_representation_exact

/-- info: 'Minidregg.Assurance.ResidentEmaCell.state_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaCell.state_ext

/-- info: 'Minidregg.Assurance.ResidentEmaCell.cell_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaCell.cell_bytes

/-- info: 'Minidregg.Assurance.ResidentEmaCell.canonical_opens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaCell.canonical_opens

/-- info: 'Minidregg.Assurance.ResidentEmaCell.signed_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaCell.signed_opening

/-- info: 'Minidregg.Assurance.ResidentEmaCell.writePatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaCell.writePatch_accepted

/-- info: 'Minidregg.Assurance.ResidentEmaCell.patch_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaCell.patch_post
