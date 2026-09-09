/- Composition of the actual compiler-owned basis extension, square tensor and
nine-to-four directed rescale. Array aliases carry no output-arithmetic premise.
NTT callbacks, decoding and exact public table/index bindings remain explicit TCB.
Actual public-layout acceptance is inhabited by the retained runtime proofs;
predecessor kernel exhibits inhabit generic arithmetic sources. This helper does
not reduce a giant actual-layout witness or prove a Rust NTT correspondence. -/
import Compiler.BfvInferLinear
import Compiler.BasisExtensionPublic
import Compiler.BfvTensorRow
import Compiler.NonlinearRnsProfiled
namespace Minidregg.Compiler.BfvSquareComposition
open Minidregg.Compiler
open Minidregg.Compiler.BfvInferLinear (Slot)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000

abbrev InputDot := Fin 2 → Fin 4 → Slot → Nat
abbrev ExtendedInput := Fin 2 → Fin 9 → Slot → Nat
abbrev ExtendedProduct := Fin 3 → Fin 9 → Slot → Nat
abbrev KernelCiphertext := Fin 3 → Fin 4 → Slot → Nat

def baseIndex (i : Fin 4) : Fin 9 := i.castAdd 5
def newIndex (i : Fin 5) : Fin 9 := i.natAdd 4
def tensorIndex (i : Fin 3) : Fin 5 := ⟨2+i.val,by omega⟩

structure SquareTransforms where
  inverseBase : Fin 4 → (Slot → Nat) → Slot → Nat
  forwardExtended : Fin 9 → (Slot → Nat) → Slot → Nat
  inverseExtended : Fin 9 → (Slot → Nat) → Slot → Nat
  forwardBase : Fin 4 → (Slot → Nat) → Slot → Nat

/-- Only the supplied input arrays require a roundtrip. Native common-modulus
rows are copied in NTT representation; no unrelated callback laws are hidden. -/
def BaseRoundTrip (op : SquareTransforms) (inputDot : InputDot) : Prop :=
  ∀ c l,op.forwardExtended (baseIndex l) (op.inverseBase l (inputDot c l))=inputDot c l

def expectedBasis (op : SquareTransforms) (inputDot : InputDot) : ExtendedInput :=
  fun c l => Fin.addCases (m:=4) (n:=5) (motive:=fun _ => Slot → Nat) (fun l => op.inverseBase l (inputDot c l))
    (fun l j => (ActualBasisExtension.nativeOutput
      (fun i => (op.inverseBase i (inputDot c i) j : Int)) l).toNat) l

def forwardAll (op : SquareTransforms) (coefficients : ExtendedInput) : ExtendedInput :=
  fun c l => op.forwardExtended l (coefficients c l)

/-- Exact native branch: four unchanged base NTT arrays and five newly extended
arrays transformed forwards. Accepted copied coefficient rows meet this branch
through BaseRoundTrip, not by silently redefining the input representation. -/
def nativeExtended (op : SquareTransforms) (inputDot : InputDot) : ExtendedInput :=
  fun c l => Fin.addCases (m:=4) (n:=5) (motive:=fun _ => Slot → Nat) (inputDot c)
    (fun l => op.forwardExtended (newIndex l) (expectedBasis op inputDot c (newIndex l))) l

def tensorProduct (input : ExtendedInput) : ExtendedProduct :=
  fun c l j => (![input 0 l j*input 0 l j,2*input 0 l j*input 1 l j,
    input 1 l j*input 1 l j] : Fin 3 → Nat) c % BfvTensorRow.primes l

def directedProjection (op : SquareTransforms) (product : ExtendedProduct) : KernelCiphertext :=
  fun c l j => (NonlinearRnsInstance.nativeProjectedOutput
    (fun i => (op.inverseExtended i (product c i) j : Int)) l).toNat

def finish (op : SquareTransforms) (coefficients : KernelCiphertext) : KernelCiphertext :=
  fun c l => op.forwardBase l (coefficients c l)

def exactDirectedSquare (op : SquareTransforms) (inputDot : InputDot) : KernelCiphertext :=
  finish op (directedProjection op (tensorProduct (nativeExtended op inputDot)))

/-- One full public basis-extension tensor. Index aliases include all four copies
and all five new residues at every one of the two component/coefficient slots. -/
def BasisChecked (op : SquareTransforms) (inputDot : InputDot) (coefficients : ExtendedInput) : Prop :=
  ∀ c j,∃ asg : Nat → BabyBear,
    systemAccepts asg (AirSimplify.simplifySystem ActualBasisExtension.system) ∧
    (∀ l,ActualBasisExtension.publicInput asg l=op.inverseBase l (inputDot c l) j) ∧
    (∀ l,ActualBasisExtension.publicCopy asg l=coefficients c (baseIndex l) j) ∧
    (∀ l,ActualBasisExtension.publicNew asg l=coefficients c (newIndex l) j)

/-- The two tensor inputs are the very same shared extended arrays at all nine
primes. Its three outputs are the same array later supplied to inverseExtended. -/
def TensorChecked (input : ExtendedInput) (product : ExtendedProduct) : Prop :=
  ∀ l j,∃ asg : Fin BfvTensorRow.nVars → BabyBear,
    systemAccepts asg (BfvTensorRow.emittedSystem (BfvTensorRow.primes l)) ∧
    BfvTensorRow.value asg 0=input 0 l j ∧ BfvTensorRow.value asg 1=input 1 l j ∧
    ∀ c,BfvTensorRow.value asg (tensorIndex c)=product c l j

/-- All nine source residues and all four target residues are aliased for every
coefficient of each of the three tensor components. -/
def RescaleChecked (op : SquareTransforms) (product : ExtendedProduct) (coefficients : KernelCiphertext) : Prop :=
  ∀ c j,∃ asg : Nat → BabyBear,
    systemAccepts asg (AirSimplify.simplifySystem NonlinearRnsProfiled.system) ∧
    (∀ l,NonlinearRnsPublic.publicResidues asg l=(op.inverseExtended l (product c l) j : Int)) ∧
    (∀ l,NonlinearRnsPublic.publicOutput asg l=coefficients c l j)

/-- The final equality binds representation only: forward NTT of the same
accepted coefficient arrays. It does not assume a square or any arithmetic. -/
def SquareChecked (op : SquareTransforms) (inputDot : InputDot) (kernelCiphertext : KernelCiphertext) : Prop :=
  ∃ extendedCoefficients productNtt projectedCoefficients,
    BasisChecked op inputDot extendedCoefficients ∧
    TensorChecked (forwardAll op extendedCoefficients) productNtt ∧
    RescaleChecked op productNtt projectedCoefficients ∧
    kernelCiphertext=finish op projectedCoefficients

def SquareSound : Prop := ∀ op inputDot kernelCiphertext,
  BaseRoundTrip op inputDot → SquareChecked op inputDot kernelCiphertext →
  kernelCiphertext=exactDirectedSquare op inputDot

theorem basisChecked_sound (op : SquareTransforms) (inputDot : InputDot) (coefficients : ExtendedInput)
    (hc : BasisChecked op inputDot coefficients) : coefficients=expectedBasis op inputDot := by
  funext c l j
  obtain ⟨asg,hs,hi,hcopy,hnew⟩ := hc c j
  have h := ActualBasisExtension.simplifiedSource_sound asg hs
  refine Fin.addCases (m:=4) (n:=5) (fun i => ?_) (fun i => ?_) l
  · simp only [expectedBasis,Fin.addCases_left]
    change coefficients c (baseIndex i) j=op.inverseBase i (inputDot c i) j
    rw [←hcopy i,h.2.1 i,hi i]
  · simp only [expectedBasis,Fin.addCases_right]
    change coefficients c (newIndex i) j=(ActualBasisExtension.nativeOutput
      (fun k => (op.inverseBase k (inputDot c k) j : Int)) i).toNat
    have hin : (fun k : Fin 4 => (ActualBasisExtension.publicInput asg k : Int))=
        (fun k => (op.inverseBase k (inputDot c k) j : Int)) := by funext k; rw [hi k]
    have hh := congrArg Int.toNat (h.2.2 i)
    rw [hin] at hh
    simpa only [Int.toNat_natCast,hnew] using hh

theorem basisRoundTrip (op : SquareTransforms) (inputDot : InputDot) (h : BaseRoundTrip op inputDot) :
    forwardAll op (expectedBasis op inputDot)=nativeExtended op inputDot := by
  funext c l
  refine Fin.addCases (m:=4) (n:=5) (fun i => ?_) (fun i => ?_) l
  · simpa only [forwardAll,expectedBasis,nativeExtended,Fin.addCases_left,baseIndex] using h c i
  · simp only [forwardAll,nativeExtended,Fin.addCases_right,newIndex]

theorem tensorChecked_sound (input : ExtendedInput) (product : ExtendedProduct)
    (hc : TensorChecked input product) : product=tensorProduct input := by
  funext c l j
  obtain ⟨asg,hs,h0,h1,ho⟩ := hc l j
  have h := BfvTensorRow.emittedSystem_sound l asg hs
  have ho0 : BfvTensorRow.value asg 2=product 0 l j := ho 0
  have ho1 : BfvTensorRow.value asg 3=product 1 l j := ho 1
  have ho2 : BfvTensorRow.value asg 4=product 2 l j := ho 2
  rw [h0,h1,ho0,ho1,ho2] at h
  fin_cases c
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem rescaleChecked_sound (op : SquareTransforms) (product : ExtendedProduct) (coefficients : KernelCiphertext)
    (hc : RescaleChecked op product coefficients) : coefficients=directedProjection op product := by
  funext c l j
  obtain ⟨asg,hs,hi,ho⟩ := hc c j
  have h := NonlinearRnsProfiled.simplifiedSource_sound asg hs l
  have hin : NonlinearRnsPublic.publicResidues asg=
      (fun i => (op.inverseExtended i (product c i) j : Int)) := funext hi
  have hh := congrArg Int.toNat h
  rw [hin] at hh
  simpa only [Int.toNat_natCast,ho,directedProjection] using hh

theorem squareChecked_sound : SquareSound := by
  intro op inputDot kernelCiphertext hrt hc
  obtain ⟨extended,product,projected,hb,ht,hr,hk⟩ := hc
  have he := basisChecked_sound op inputDot extended hb
  have hn : forwardAll op extended=nativeExtended op inputDot := by rw [he,basisRoundTrip op inputDot hrt]
  have hp : product=tensorProduct (nativeExtended op inputDot) := by rw [←hn];exact tensorChecked_sound _ _ ht
  have hproj := rescaleChecked_sound op product projected hr
  rw [hk,hproj,hp]
  rfl

/-- The certificate constructor only packages independently supplied accepted
sources and explicit representation/index links; there is no desired-result leg. -/
theorem checked_of_sources (op : SquareTransforms) (inputDot : InputDot)
    (extended : ExtendedInput) (product : ExtendedProduct) (projected : KernelCiphertext)
    (hb : BasisChecked op inputDot extended) (ht : TensorChecked (forwardAll op extended) product)
    (hr : RescaleChecked op product projected) : SquareChecked op inputDot (finish op projected) :=
  ⟨extended,product,projected,hb,ht,hr,rfl⟩

/-- A concrete inhabitant of the callback law, distinct from claiming native
NTT correctness or actual-layout source acceptance. -/
def identityTransforms : SquareTransforms where
  inverseBase := fun _ x => x
  forwardExtended := fun _ x => x
  inverseExtended := fun _ x => x
  forwardBase := fun _ x => x

theorem roundtrip_inhabited (inputDot : InputDot) : BaseRoundTrip identityTransforms inputDot := by
  intro c l
  rfl

theorem wrong_kernel_refused (op : SquareTransforms) (inputDot : InputDot)
    (kernelCiphertext : KernelCiphertext) (hrt : BaseRoundTrip op inputDot)
    (hwrong : kernelCiphertext≠exactDirectedSquare op inputDot) :
    ¬SquareChecked op inputDot kernelCiphertext := by
  intro hc
  exact hwrong (squareChecked_sound op inputDot kernelCiphertext hrt hc)

def zeroSlot : Slot := ⟨0,by decide⟩

/-- A concrete wrong sibling changes one supplied kernel coefficient. Its
rejection follows for every possible source witness, rather than a producer test. -/
theorem one_coefficient_refused (op : SquareTransforms) (inputDot : InputDot)
    (hrt : BaseRoundTrip op inputDot) :
    ¬SquareChecked op inputDot (fun c l j =>
      if c=0 ∧ l=0 ∧ j=zeroSlot then exactDirectedSquare op inputDot c l j+1
      else exactDirectedSquare op inputDot c l j) := by
  apply wrong_kernel_refused op inputDot _ hrt
  intro h
  have hh := congrArg (fun p : KernelCiphertext => p 0 0 zeroSlot) h
  dsimp only at hh
  simp only [ite_true,and_self] at hh
  omega
end Minidregg.Compiler.BfvSquareComposition

/-- info: 'Minidregg.Compiler.BfvSquareComposition.basisChecked_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvSquareComposition.basisChecked_sound

/-- info: 'Minidregg.Compiler.BfvSquareComposition.basisRoundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvSquareComposition.basisRoundTrip

/-- info: 'Minidregg.Compiler.BfvSquareComposition.tensorChecked_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvSquareComposition.tensorChecked_sound

/-- info: 'Minidregg.Compiler.BfvSquareComposition.rescaleChecked_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvSquareComposition.rescaleChecked_sound

/-- info: 'Minidregg.Compiler.BfvSquareComposition.squareChecked_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvSquareComposition.squareChecked_sound

/-- info: 'Minidregg.Compiler.BfvSquareComposition.checked_of_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvSquareComposition.checked_of_sources

/-- info: 'Minidregg.Compiler.BfvSquareComposition.roundtrip_inhabited' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvSquareComposition.roundtrip_inhabited

/-- info: 'Minidregg.Compiler.BfvSquareComposition.wrong_kernel_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvSquareComposition.wrong_kernel_refused

/-- info: 'Minidregg.Compiler.BfvSquareComposition.one_coefficient_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvSquareComposition.one_coefficient_refused
