/-
Statement first: a certificate must FORCE the pinned engine's selected Garner
index and directed fixed correction, including the observed nearest+1 case.
Two exact integer quotient/remainder relations fix those roundings; the final
integer quotient relation fixes the canonical output modulo Q. There is no
allowed {nearest,nearest+1} choice. The compiler lowering reuses the existing
weighted-column and range gadgets; no replacement AIR is defined here.

This is a source scalar certificate. Committed-residue provenance and the Rust
NTT/modular implementation refinement remain separate obligations.
-/
import Compiler.FheRnsScaleDecomposition
import Compiler.IntegerCertificateEmission

namespace Minidregg.Compiler.FheSourceCertificate
open Minidregg.Compiler
open Minidregg.Compiler.FheRnsScale
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 10000

structure Certificate where
  v : ℤ
  w : ℤ
  garnerRemainder : ℤ
  correctionRemainder : ℤ
  outputQuotient : ℤ

def accepts (r : Fin 6 → ℤ) (output : ℤ) (c : Certificate) : Prop :=
  (∀ i, 0 ≤ r i ∧ r i < deployedBase i) ∧
  0 ≤ c.garnerRemainder ∧ c.garnerRemainder < 2*(2^126) ∧
  0 ≤ c.correctionRemainder ∧ c.correctionRemainder < 2*(2^127) ∧
  0 ≤ output ∧ output < deployedQ ∧
  2*(∑ i, r i*deployedThetaG i)+(2^126) = 2*(2^126)*c.v+c.garnerRemainder ∧
  2*(∑ i, r i*deployedThetaF i)+(2^127) = 2*(2^127)*c.w+c.correctionRemainder ∧
  integerPart r deployedOmega c.v deployedGamma+c.w = deployedQ*c.outputQuotient+output

def SourceCertificateSound : Prop := ∀ r output c, accepts r output c →
  output = deployedOutput r % deployedQ

/-- Exact Euclidean QR, including signed quotients, forces its quotient. -/
theorem qr_forced (x d q rem : ℤ) (hd : 0 < d)
    (h0 : 0 ≤ rem) (h1 : rem < d) (he : x=d*q+rem) : q=x/d := by
  have h := BFVScaleLift.quotient_forced d 1 0 x q rem hd ⟨h0,h1,by simpa using he⟩
  simpa [BFVScaleLift.scale] using h

theorem forced_roundings (r : Fin 6 → ℤ) (output : ℤ) (c : Certificate)
    (h : accepts r output c) : c.v=deployedV r ∧ c.w=deployedW r := by
  rcases h with ⟨hr,hg0,hg1,hf0,hf1,ho0,ho1,hg,hf,hy⟩
  have hv := qr_forced _ _ _ _ (by positivity) hg0 hg1 hg
  have hw := qr_forced _ _ _ _ (by positivity) hf0 hf1 hf
  rw [deployedV_correct r hr, deployedW_correct r hr]
  exact ⟨hv,hw⟩

/-- Main source refinement: output is unique even on exact rounding boundaries. -/
theorem sourceCertificateSound : SourceCertificateSound := by
  intro r output c h
  have forced := forced_roundings r output c h
  rcases h with ⟨hr,hg0,hg1,hf0,hf1,ho0,ho1,hg,hf,hy⟩
  rw [forced.1,forced.2] at hy
  change deployedOutput r = deployedQ*c.outputQuotient+output at hy
  have hq := qr_forced _ _ _ _ (by decide : 0 < deployedQ) ho0 ho1 hy
  rw [hq] at hy
  have he := Int.mul_ediv_add_emod (deployedOutput r) deployedQ
  omega

def honestCertificate (r : Fin 6 → ℤ) : Certificate where
  v := deployedV r
  w := deployedW r
  garnerRemainder := (2*(∑ i, r i*deployedThetaG i)+(2^126)) % (2*(2^126))
  correctionRemainder := (2*(∑ i, r i*deployedThetaF i)+(2^127)) % (2*(2^127))
  outputQuotient := deployedOutput r / deployedQ

/-- Every canonical input has an exact semantic certificate; no promise that either
rounded neighbor may be selected enters the relation. -/
theorem honest_accepts (r : Fin 6 → ℤ) (hr : ∀ i, 0 ≤ r i ∧ r i < deployedBase i) :
    accepts r (deployedOutput r % deployedQ) (honestCertificate r) := by
  refine ⟨hr,Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by positivity),
    Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by positivity),
    Int.emod_nonneg _ (by decide),Int.emod_lt_of_pos _ (by decide),?_,?_,?_⟩
  · dsimp [honestCertificate]
    rw [deployedV_correct r hr]
    exact (Int.mul_ediv_add_emod _ _).symm
  · dsimp [honestCertificate]
    rw [deployedW_correct r hr]
    exact (Int.mul_ediv_add_emod _ _).symm
  · change deployedOutput r = deployedQ*(deployedOutput r/deployedQ)+deployedOutput r%deployedQ
    exact (Int.mul_ediv_add_emod _ _).symm

/-- The actual +1 source output inhabits the accepting relation. -/
theorem actual_plus_one_inhabited : accepts capturedResidues 172481 (honestCertificate capturedResidues) := by
  have h := honest_accepts capturedResidues deployed_witness_inhabited.1
  rw [deployed_witness_inhabited.2.2.1] at h
  norm_num [deployedQ] at h
  exact h

/-- The tempting exact-nearest neighbor is refused for EVERY auxiliary certificate. -/
theorem wrong_neighbor_refused (c : Certificate) : ¬ accepts capturedResidues 172480 c := by
  intro h
  have hs := sourceCertificateSound capturedResidues 172480 c h
  rw [deployed_witness_inhabited.2.2.1] at hs
  norm_num [deployedQ] at hs

/-- Both neighbors pass the loose envelope, so it is not a replacement for this certificate. -/
theorem loose_envelope_falsifier :
    (172480 : ℤ) ≤ 172480 ∧ 172480 ≤ 172480+1 ∧
    (∀ c, ¬ accepts capturedResidues 172480 c) :=
  ⟨by omega,by omega,wrong_neighbor_refused⟩

end Minidregg.Compiler.FheSourceCertificate

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheSourceCertificate.qr_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.qr_forced

/-- info: 'Minidregg.Compiler.FheSourceCertificate.forced_roundings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.forced_roundings

/-- info: 'Minidregg.Compiler.FheSourceCertificate.sourceCertificateSound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.sourceCertificateSound

/-- info: 'Minidregg.Compiler.FheSourceCertificate.honest_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.honest_accepts

/-- info: 'Minidregg.Compiler.FheSourceCertificate.actual_plus_one_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.actual_plus_one_inhabited

/-- info: 'Minidregg.Compiler.FheSourceCertificate.wrong_neighbor_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.wrong_neighbor_refused

/-- info: 'Minidregg.Compiler.FheSourceCertificate.loose_envelope_falsifier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.loose_envelope_falsifier
