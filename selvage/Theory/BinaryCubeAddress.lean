/-
# Theory.BinaryCubeAddress -- the LSB-first Boolean-cube address convention

One equivalence between Boolean address words and table indices `Fin (2^k)`,
shared by the Merkle controller (`Compiler.Tower256CshakeMerkleController`) and
the lookup arguments (`Selvage.BinaryLookup` re-exports it). It needs only
Mathlib, so a module that commits to cube addresses does not import the proof
system to get them.
-/
import Mathlib.Algebra.BigOperators.Fin

namespace Minidregg.Theory.BinaryCubeAddress

/-- LSB-first equivalence between Boolean address words and table indices. -/
def binaryCubeIndexEquiv (k : ℕ) :
    (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Boolean address bits decoded from a table index. -/
def binaryAddressBits (k : ℕ) (i : Fin (2 ^ k)) : Fin k → Bool :=
  (binaryCubeIndexEquiv k).symm i

@[simp] theorem binaryAddressBits_encode (k : ℕ) (b : Fin k → Bool) :
    binaryAddressBits k (binaryCubeIndexEquiv k b) = b := by
  simp [binaryAddressBits]

@[simp] theorem binaryCubeIndexEquiv_decode (k : ℕ) (i : Fin (2 ^ k)) :
    binaryCubeIndexEquiv k (binaryAddressBits k i) = i := by
  simp [binaryAddressBits]

end Minidregg.Theory.BinaryCubeAddress
