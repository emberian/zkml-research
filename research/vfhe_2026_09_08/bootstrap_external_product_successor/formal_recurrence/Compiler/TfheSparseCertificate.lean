import Compiler.TfheSparseRow
import Theory.SparseNegacyclic
namespace Minidregg.Compiler.TfheSparseCertificate
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.TfheSparseRow Minidregg.Compiler.TfheSparseWrap
open Minidregg.Theory.SparseNegacyclic
set_option autoImplicit false
set_option maxHeartbeats 3000000

def read (rows : Fin 512 → Fin nVars → BabyBear) (j : Fin 512) (g : Fin 8) : SmallRing := value (rows j) g
/-- Shared public arrays and exact index/flag transport, supplied by the canonical
reader. No arithmetic transition or convolution conclusion appears here. -/
def Linked (G S C : ℕ → SmallRing) (rows : Fin 512 → Fin nVars → BabyBear) : Prop :=
  ∀ j : Fin 512,
    read rows j 0=G j.val ∧
    read rows j 1=G ((j.val+512-44)%512) ∧
    read rows j 2=G ((j.val+512-162)%512) ∧
    read rows j 3=C j.val ∧
    read rows j 4=(if j.val=0 then -C 511 else C (j.val-1)) ∧
    read rows j 5=S j.val ∧ read rows j 6=S (j.val+1) ∧ read rows j 7=S 512 ∧
    fval (rows j) 0=(if j.val=0 then 1 else 0) ∧
    fval (rows j) 1=(if j.val<44 then 1 else 0) ∧
    fval (rows j) 2=(if j.val<162 then 1 else 0) ∧
    fval (rows j) 3=(if j.val<351 then 1 else 0) ∧
    fval (rows j) 4=(if 469≤j.val then 1 else 0)

def WholeSound : Prop := ∀ (G S C : ℕ → SmallRing) (rows : Fin 512 → Fin nVars → BabyBear),
  Linked G S C rows → (∀ j,systemAccepts (rows j) emittedSystem) →
  (∀ j : Fin 512,C j.val=convolution 512 44 162 G j.val) ∧
  (∀ j : Fin 512,rawValue (rows j)=256*value (rows j) 3)

theorem cell_index {R : Type*} [CommRing R] (G : ℕ → R) (j k : ℕ)
    (hj : j<512) (hk : k<512) :
    cell 512 G j k=(if j<k then -G ((j+512-k)%512) else G ((j+512-k)%512)) := by
  by_cases h : j<k
  · have hh : j+512-k<512 := by omega
    simp [cell,h,show ¬k≤j by omega,Nat.mod_eq_of_lt hh,show 512+j-k=j+512-k by omega]
  · have hh : j-k<512 := by omega
    have hm : (j+512-k)%512=j-k := by
      rw [show j+512-k=(j-k)+512 by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hh]
    simp [cell,h,show k≤j by omega,hm]

theorem whole_sound : WholeSound := by
  intro G S C rows hl hs
  have hm (j : Fin 512) := emitted_sound (rows j) (hs j)
  have hp : PrefixCertificate G S C := by
    have h0 := hl 0
    simp only [Fin.val_zero] at h0
    have ha := (hm 0).2.2.2.2.1 (by simpa using h0.2.2.2.2.2.2.2.2.1)
    have hz : S 0=0 := by
      rw [←h0.2.2.2.2.2.1]
      unfold read
      rw [ha.1]
      simp
    have hanchor : C 0=S 512 := by
      rw [←h0.2.2.2.1,←h0.2.2.2.2.2.2.2.1]
      unfold read
      rw [ha.2]
    refine ⟨hz,?_,hanchor,?_⟩
    · intro j hj
      let t : Fin 512 := ⟨j,hj⟩
      obtain ⟨l0,l1,l2,l3,l4,l5,l6,l7,f0,f1,f2,f3,f4⟩ := hl t
      have hh := (hm t).2.2.1
      change read rows t 5+(fval (rows t) 3 : SmallRing)*read rows t 0 =
        read rows t 6+(fval (rows t) 4 : SmallRing)*read rows t 0 at hh
      rw [l0,l5,l6,f3,f4] at hh
      dsimp only [t] at hh
      by_cases h1 : j<351
      · simp only [if_pos h1,if_neg (show ¬469≤j by omega),Nat.cast_one,Nat.cast_zero,one_mul,zero_mul,add_zero] at hh
        simpa [digits,h1] using hh.symm
      · by_cases h2 : j<469
        · simp only [if_neg h1,if_neg (show ¬469≤j by omega),Nat.cast_zero,zero_mul,add_zero] at hh
          simpa [digits,h1,h2] using hh.symm
        · simp only [if_neg h1,if_pos (show 469≤j by omega),Nat.cast_one,Nat.cast_zero,one_mul,zero_mul,add_zero] at hh
          simp only [digits,if_neg h1,if_neg h2,neg_one_mul]
          linear_combination -hh
    · intro j hj
      let t : Fin 512 := ⟨j+1,hj⟩
      obtain ⟨l0,l1,l2,l3,l4,l5,l6,l7,f0,f1,f2,f3,f4⟩ := hl t
      have hh := (hm t).2.2.2.1
      change read rows t 4+2*(fval (rows t) 1 : SmallRing)*read rows t 1+
        2*(fval (rows t) 2 : SmallRing)*read rows t 2=read rows t 3+read rows t 1+read rows t 2 at hh
      rw [l1,l2,l3,l4,f1,f2] at hh
      dsimp only [t] at hh
      simp only [show ¬j+1=0 by omega,if_false,Nat.add_sub_cancel] at hh
      rw [cell_index G (j+1) 44 hj (by decide),cell_index G (j+1) 162 hj (by decide)]
      simp only [show j+1+512-44=j+469 by omega,show j+1+512-162=j+351 by omega] at hh ⊢
      split_ifs at hh ⊢ <;> push_cast at hh <;> linear_combination -hh
  exact ⟨fun j => prefix_certificate_sound G S C hp j.val j.isLt,fun j => (hm j).2.2.2.2.2⟩
end Minidregg.Compiler.TfheSparseCertificate

/-- info: 'Minidregg.Compiler.TfheSparseCertificate.cell_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseCertificate.cell_index

/-- info: 'Minidregg.Compiler.TfheSparseCertificate.whole_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseCertificate.whole_sound
