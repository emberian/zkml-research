/- Generic anchored certificate for a two-break signed negacyclic convolution.
The selected application has N=512, a=44, b=162 and uses ZMod(2^24). -/
import Mathlib
namespace Minidregg.Theory.SparseNegacyclic
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSimpArgs false
variable {R : Type*} [CommRing R]

def cell (N : ℕ) (G : ℕ → R) (i j : ℕ) : R :=
  if j  ≤  i then G (i-j) else -G (N+i-j)
def window (N : ℕ) (G : ℕ → R) (i a n : ℕ) : R :=
  ∑ t ∈ Finset.range n, cell N G i (a+t)
def digits (a b j : ℕ) : R := if j < a then 1 else if j < b then 0 else -1
def convolution (N a b : ℕ) (G : ℕ → R) (i : ℕ) : R :=
  ∑ j ∈ Finset.range N, digits a b j * cell N G i j
def prefixSum (G : ℕ → R) (n : ℕ) : R := ∑ j ∈ Finset.range n, G j

def Anchored (N a b : ℕ) (G C : ℕ → R) : Prop :=
  C 0 = prefixSum G (N-b+1) + prefixSum G (N-a+1) - prefixSum G N ∧
  ∀ i, i+1 < N → C (i+1)=C i-cell N G (i+1) a-cell N G (i+1) b

def CertificateSound : Prop :=
  ∀ (N a b : ℕ) (G C : ℕ → R), 0 < a → a ≤ b → b ≤ N →
    Anchored N a b G C → ∀ i, i < N → C i=convolution N a b G i

theorem cell_shift (N : ℕ) (G : ℕ → R) (i j : ℕ) :
    cell N G (i+1) (j+1)=cell N G i j := by
  unfold cell
  have h₁ : (j+1 ≤ i+1)  ↔  j ≤ i := by omega
  simp only [h₁]
  split
  · congr 1; omega
  · congr 2; omega

theorem sum_difference (f : ℕ → R) (a n : ℕ) :
    (∑ t ∈ Finset.range n, f (a+t))-(∑ t ∈ Finset.range n, f (a+t+1)) = f a-f (a+n) := by
  induction n with
  | zero =>  simp
  | succ n ih => 
    simp only [Finset.sum_range_succ]
    rw [show a+(n+1)=a+n+1 by omega]
    linear_combination ih

theorem window_step (N : ℕ) (G : ℕ → R) (i a n : ℕ) :
    window N G (i+1) a n-window N G i a n =
      cell N G (i+1) a-cell N G (i+1) (a+n) := by
  unfold window
  have h : (∑ t ∈ Finset.range n, cell N G i (a+t)) =
      ∑ t ∈ Finset.range n, cell N G (i+1) (a+t+1) := by
    apply Finset.sum_congr rfl
    intro t _
    exact (cell_shift N G i (a+t)).symm
  rw [h]
  exact sum_difference (cell N G (i+1)) a n

theorem convolution_windows (N a b : ℕ) (G : ℕ → R) (i : ℕ)
    (hab : a ≤ b) (hbN : b ≤ N) :
    convolution N a b G i=window N G i 0 a-window N G i b (N-b) := by
  unfold convolution
  conv_lhs => rw [show N=a+((b-a)+(N-b)) by omega]
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have h₁ : (∑ x ∈ Finset.range a, digits a b x * cell (a+(b-a+(N-b))) G i x) = window N G i 0 a := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Finset.mem_range.mp hx
    simp [digits,hx',window,show a+(b-a+(N-b))=N by omega]
  have h₂ : (∑ x ∈ Finset.range (b-a), digits a b (a+x) * cell (a+(b-a+(N-b))) G i (a+x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx' := Finset.mem_range.mp hx
    simp [digits,show ¬a+x < a by omega,show a+x < b by omega]
  have h₃ : (∑ x ∈ Finset.range (N-b), digits a b (a+(b-a+x)) * cell (a+(b-a+(N-b))) G i (a+(b-a+x))) = -window N G i b (N-b) := by
    rw [window,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    simp [digits,show ¬(b+x < a) by omega,show ¬(b+x < b) by omega,
      show a+(b-a+x)=b+x by omega,show a+(b-a+(N-b))=N by omega]
  rw [h₁,h₂,h₃]
  ring

theorem convolution_step (N a b : ℕ) (G : ℕ → R) (i : ℕ)
    (hab : a ≤ b) (hbN : b ≤ N) (hi : i+1 < N) :
    convolution N a b G (i+1)=convolution N a b G i-cell N G (i+1) a-cell N G (i+1) b := by
  rw [convolution_windows N a b G (i+1) hab hbN,convolution_windows N a b G i hab hbN]
  have h₁ := window_step N G i 0 a
  have h₂ := window_step N G i b (N-b)
  have hleft : cell N G (i+1) 0=G (i+1) := by simp [cell]
  have hright : cell N G (i+1) N= -G (i+1) := by
    simp [cell,show ¬N ≤ i+1 by omega,show N+(i+1)-N=i+1 by omega]
  simp only [Nat.zero_add,show b+(N-b)=N by omega,hleft,hright] at h₁ h₂
  linear_combination h₁-h₂

theorem window_zero (N a n : ℕ) (G : ℕ → R) (ha : 0 < a) (h : a+n ≤ N) :
    window N G 0 a n = -(∑ t ∈ Finset.range n, G (N-a-n+1+t)) := by
  unfold window
  rw [←Finset.sum_neg_distrib]
  calc
    _ = ∑ t ∈ Finset.range n, -G (N-(a+t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [cell,show ¬a+t ≤ 0 by omega]
    _ = ∑ t ∈ Finset.range n, -G (N-a-n+1+(n-1-t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_range.mp ht
      congr 2; omega
    _ = _ := Finset.sum_range_reflect (fun t =>  -G (N-a-n+1+t)) n

theorem interval_prefixSum (G : ℕ → R) (a n : ℕ) :
    (∑ t ∈ Finset.range n, G (a+t))=prefixSum G (a+n)-prefixSum G a := by
  simp [prefixSum,Finset.sum_range_add]

theorem convolution_anchor (N a b : ℕ) (G : ℕ → R)
    (ha : 0 < a) (hab : a ≤ b) (hbN : b ≤ N) :
    convolution N a b G 0=prefixSum G (N-b+1)+prefixSum G (N-a+1)-prefixSum G N := by
  rw [convolution_windows N a b G 0 hab hbN]
  have hsplit : window N G 0 0 a=G 0+window N G 0 1 (a-1) := by
    unfold window
    conv_lhs => rw [show a=(a-1)+1 by omega]
    rw [Finset.sum_range_succ']
    simp only [Nat.zero_add,cell,le_refl,ite_true,Nat.sub_self]
    have hsum : (∑ k ∈ Finset.range (a-1), if k+1 ≤ 0 then G (0-(k+1)) else -G (N+0-(k+1))) =
        ∑ k ∈ Finset.range (a-1), if 1+k ≤ 0 then G (0-(1+k)) else -G (N+0-(1+k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_comm 1 k]
    rw [hsum]
    ring
  rw [hsplit,window_zero N 1 (a-1) G (by omega) (by omega),window_zero N b (N-b) G (by omega) (by omega)]
  rw [interval_prefixSum,interval_prefixSum]
  have h₁ : N-1-(a-1)+1=N-a+1 := by omega
  have h₂ : N-b-(N-b)+1=1 := by omega
  rw [h₁,h₂,show N-a+1+(a-1)=N by omega,show 1+(N-b)=N-b+1 by omega]
  simp [prefixSum,Finset.sum_range_succ]
  ring

theorem certificate_sound : CertificateSound (R:=R) := by
  intro N a b G C ha hab hbN hc i hi
  induction i with
  | zero =>  exact hc.1.trans (convolution_anchor N a b G ha hab hbN).symm
  | succ i ih => 
    rw [hc.2 i hi,ih (by omega),convolution_step N a b G i hab hbN hi]

def PrefixCertificate (G S C : ℕ → R) : Prop :=
  S 0=0 ∧ (∀ j, j<512 → S (j+1)=S j+digits 351 469 j*G j) ∧
  C 0=S 512 ∧ (∀ j, j+1<512 → C (j+1)=C j-cell 512 G (j+1) 44-cell 512 G (j+1) 162)

theorem prefix_recurrence (f S : ℕ → R) (N : ℕ) (h0 : S 0=0)
    (hstep : ∀ j,j<N → S (j+1)=S j+f j) :
    ∀ j,j≤N → S j=prefixSum f j := by
  intro j hj
  induction j with
  | zero => simpa [prefixSum] using h0
  | succ j ih => rw [hstep j (by omega),ih (by omega)]; simp [prefixSum,Finset.sum_range_succ]

theorem signed_blocks_sum (N a b : ℕ) (G : ℕ → R) (hab : a≤b) (hbN : b≤N) :
    prefixSum (fun j => digits a b j*G j) N=prefixSum G a+prefixSum G b-prefixSum G N := by
  have hg (i : ℕ) (hi : i<N) : cell N (fun t => G (N-t)) N i=G i := by
    simp [cell,show i≤N by omega,show N-(N-i)=i by omega]
  have hconv : convolution N a b (fun t => G (N-t)) N=prefixSum (fun j => digits a b j*G j) N := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hg j (Finset.mem_range.mp hj)]
  have hw (start len : ℕ) (h : start+len≤N) :
      window N (fun t => G (N-t)) N start len=prefixSum G (start+len)-prefixSum G start := by
    rw [←interval_prefixSum]
    apply Finset.sum_congr rfl
    intro t ht
    exact hg (start+t) (by have := Finset.mem_range.mp ht; omega)
  rw [←hconv,convolution_windows N a b _ N hab hbN,hw 0 a (by omega),hw b (N-b) (by omega)]
  simp [prefixSum,show b+(N-b)=N by omega]
  ring

theorem prefix_certificate_sound (G S C : ℕ → R) (h : PrefixCertificate G S C) :
    ∀ i,i<512 → C i=convolution 512 44 162 G i := by
  apply certificate_sound 512 44 162 G C (by decide) (by decide) (by decide)
  refine ⟨?_,h.2.2.2⟩
  rw [h.2.2.1,prefix_recurrence _ S 512 h.1 h.2.1 512 (by omega),signed_blocks_sum 512 351 469 G (by decide) (by decide)]

theorem prefix_certificate_inhabited (G : ℕ → R) :
    PrefixCertificate G (prefixSum (fun j => digits 351 469 j*G j)) (convolution 512 44 162 G) := by
  refine ⟨by simp [prefixSum],?_,?_,?_⟩
  · intro j _; simp [prefixSum,Finset.sum_range_succ]
  · rw [convolution_anchor 512 44 162 G (by decide) (by decide) (by decide),signed_blocks_sum 512 351 469 G (by decide) (by decide)]
  · intro j hj; exact convolution_step 512 44 162 G j (by decide) (by decide) hj

/-- A constant half-modulus satisfies even the signed wrap recurrence for zero
input, yet is not its convolution. An anchor cannot be recovered by cancelling2. -/
def AnchorOmissionFails : Prop :=
  (∀ j,j<512 → (8388608 : ZMod 16777216) =
    (if j=0 then -(8388608 : ZMod 16777216) else 8388608)) ∧
  (8388608 : ZMod 16777216) ≠ convolution 512 44 162 (fun _ => 0) 0

theorem anchor_omission_fails : AnchorOmissionFails := by
  constructor
  · intro j _; split <;> decide +kernel
  · simp [convolution,cell]
    decide +kernel

theorem scale_mod (x : ℤ) : (256*x)%4294967296=256*(x%16777216) := by
  have hr := Int.emod_nonneg x (by norm_num : (16777216 : ℤ)≠0)
  have hb := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ)<16777216)
  have hd := Int.emod_add_mul_ediv x 16777216
  have he : 256*x=256*(x%16777216)+4294967296*(x/16777216) := by linear_combination 256*hd.symm
  rw [he,Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by omega) (by omega)

end Minidregg.Theory.SparseNegacyclic

/-- info: 'Minidregg.Theory.SparseNegacyclic.cell_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.cell_shift

/-- info: 'Minidregg.Theory.SparseNegacyclic.sum_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.sum_difference

/-- info: 'Minidregg.Theory.SparseNegacyclic.window_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.window_step

/-- info: 'Minidregg.Theory.SparseNegacyclic.convolution_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.convolution_windows

/-- info: 'Minidregg.Theory.SparseNegacyclic.convolution_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.convolution_step

/-- info: 'Minidregg.Theory.SparseNegacyclic.window_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.window_zero

/-- info: 'Minidregg.Theory.SparseNegacyclic.interval_prefixSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.interval_prefixSum

/-- info: 'Minidregg.Theory.SparseNegacyclic.convolution_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.convolution_anchor

/-- info: 'Minidregg.Theory.SparseNegacyclic.certificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.certificate_sound

/-- info: 'Minidregg.Theory.SparseNegacyclic.prefix_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.prefix_recurrence

/-- info: 'Minidregg.Theory.SparseNegacyclic.signed_blocks_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.signed_blocks_sum

/-- info: 'Minidregg.Theory.SparseNegacyclic.prefix_certificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.prefix_certificate_sound

/-- info: 'Minidregg.Theory.SparseNegacyclic.prefix_certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.prefix_certificate_inhabited

/-- info: 'Minidregg.Theory.SparseNegacyclic.anchor_omission_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.anchor_omission_fails

/-- info: 'Minidregg.Theory.SparseNegacyclic.scale_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.SparseNegacyclic.scale_mod
