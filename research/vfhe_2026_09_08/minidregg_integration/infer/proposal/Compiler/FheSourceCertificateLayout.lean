/- Generated pinned linear balance matrix. Every row becomes TWO EXISTING weighted
accumulators with shared result limbs. Uniform 22-digit groups are a conservative
baseline, not an optimized layout or a mandatory lower bound. -/
import Compiler.FheSourceCertificate

namespace Minidregg.Compiler.FheSourceCertificate
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

def wOffset : ℕ := 36893488147419103232
def uOffset : ℕ := 1329227995784915872903807060280344576
def leftConstant (row : Fin 12) : ℕ := match row.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 85070591730234615865843651857942052864
  | 7 => 0
  | 8 => 12554203470773361527841720029875802063936398192643953131520
  | 9 => 0
  | 10 => 862713459717704035650365311846944737656111791604218977383885431635968
  | 11 => 0
  | _ => 0
def rightConstant (row : Fin 12) : ℕ := match row.val with
  | 0 => 68719403008
  | 1 => 68719230976
  | 2 => 137438822400
  | 3 => 4611686018427322368
  | 4 => 4611686018427289600
  | 5 => 4611686018427215872
  | 6 => 0
  | 7 => 170141183460469231731687303715884105727
  | 8 => 0
  | 9 => 340282366920938463463374607431768211455
  | 10 => 36893488147419103232
  | 11 => 649033470896967801447398927572992
  | _ => 0
def leftMatrix (row : Fin 12) (col : Fin 21) : ℕ := match row.val,col.val with
  | 0,0 => 1
  | 0,6 => 1
  | 1,1 => 1
  | 1,7 => 1
  | 2,2 => 1
  | 2,8 => 1
  | 3,3 => 1
  | 3,9 => 1
  | 4,4 => 1
  | 4,10 => 1
  | 5,5 => 1
  | 5,11 => 1
  | 6,0 => 131065419633086522241372289381823572106
  | 6,1 => 4485488741573124986325697124100386762
  | 6,2 => 169336339963779992772213565866202100270
  | 6,3 => 43688450512502976537252365005556546662
  | 6,4 => 111342366693413055201354910647205661904
  | 6,5 => 50505484837052023456543083122764049482
  | 7,13 => 1
  | 7,14 => 1
  | 8,0 => 80472655973117157476048213043941515826
  | 8,1 => 53347334390297183354149788280129557170
  | 9,16 => 1
  | 9,17 => 1
  | 10,0 => 77986382591119874064921855321526527381868595827415916824020267
  | 10,1 => 2668949918962272755740805946941502886286373228576567292954653
  | 10,2 => 100758297894020147554024975409120330178423098053670234523689029
  | 10,3 => 25995447357658063166494866421566043447166475144685359547976399
  | 10,4 => 66250796219640414915292195382615713228017713407091191535059741
  | 10,5 => 30051710622670116563016618864449112911308518409102424717649034
  | 10,15 => 1
  | 11,18 => 1
  | 11,19 => 1
  | _,_ => 0
def rightMatrix (row : Fin 12) (col : Fin 21) : ℕ := match row.val,col.val with
  | 6,12 => 170141183460469231731687303715884105728
  | 6,13 => 1
  | 8,2 => 133819990363414340830198000782901637350
  | 8,15 => 340282366920938463463374607431768211456
  | 8,16 => 1
  | 10,12 => 101237194868023629673163772448739743344356924690180564813783041
  | 10,18 => 1
  | 10,20 => 649033470896967801447398927572993
  | _,_ => 0

def dot (a : Fin 21 → ℕ) (x : Fin 21 → ℕ) : ℕ := ∑ i, a i*x i

def Balanced (x : Fin 21 → ℕ) : Prop := ∀ j,
  leftConstant j+dot (leftMatrix j) x = rightConstant j+dot (rightMatrix j) x

def readResidues (x : Fin 21 → ℕ) (i : Fin 6) : ℤ := match i.val with
  | 0 => x 0 | 1 => x 1 | 2 => x 2 | 3 => x 3 | 4 => x 4 | _ => x 5
def readCertificate (x : Fin 21 → ℕ) : Certificate where
  v := x 12
  w := (x 15 : ℤ)-wOffset
  garnerRemainder := x 13
  correctionRemainder := x 16
  outputQuotient := (x 20 : ℤ)-uOffset

/-- Finite coefficient/capacity facts, proved about the generated pinned matrix. -/
theorem matrix_capacities :
    (∀ row col, leftMatrix row col < 2^210 ∧ rightMatrix row col < 2^210) ∧
    (∀ row, leftConstant row < 64^57 ∧ rightConstant row < 64^57) := by decide

/-- The generated nonnegative balances imply the exact signed source certificate. -/
theorem balanced_source_accepts (x : Fin 21 → ℕ) (h : Balanced x) :
    accepts (readResidues x) (x 18) (readCertificate x) := by
  have rows (i : Fin 12) := h i
  have h0 := rows 0
  simp only [dot,Fin.sum_univ_succ] at h0
  change 0+(1*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(1*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 68719403008+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h0
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h0
  have h1 := rows 1
  simp only [dot,Fin.sum_univ_succ] at h1
  change 0+(0*x 0+(1*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(1*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 68719230976+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h1
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h1
  have h2 := rows 2
  simp only [dot,Fin.sum_univ_succ] at h2
  change 0+(0*x 0+(0*x 1+(1*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(1*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 137438822400+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h2
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h2
  have h3 := rows 3
  simp only [dot,Fin.sum_univ_succ] at h3
  change 0+(0*x 0+(0*x 1+(0*x 2+(1*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(1*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 4611686018427322368+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h3
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h3
  have h4 := rows 4
  simp only [dot,Fin.sum_univ_succ] at h4
  change 0+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(1*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(1*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 4611686018427289600+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h4
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h4
  have h5 := rows 5
  simp only [dot,Fin.sum_univ_succ] at h5
  change 0+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(1*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(1*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 4611686018427215872+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h5
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h5
  have h6 := rows 6
  simp only [dot,Fin.sum_univ_succ] at h6
  change 85070591730234615865843651857942052864+(131065419633086522241372289381823572106*x 0+(4485488741573124986325697124100386762*x 1+(169336339963779992772213565866202100270*x 2+(43688450512502976537252365005556546662*x 3+(111342366693413055201354910647205661904*x 4+(50505484837052023456543083122764049482*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 0+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(170141183460469231731687303715884105728*x 12+(1*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h6
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h6
  have h7 := rows 7
  simp only [dot,Fin.sum_univ_succ] at h7
  change 0+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(1*x 13+(1*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 170141183460469231731687303715884105727+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h7
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h7
  have h8 := rows 8
  simp only [dot,Fin.sum_univ_succ] at h8
  change 12554203470773361527841720029875802063936398192643953131520+(80472655973117157476048213043941515826*x 0+(53347334390297183354149788280129557170*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 0+(0*x 0+(0*x 1+(133819990363414340830198000782901637350*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(340282366920938463463374607431768211456*x 15+(1*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h8
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h8
  have h9 := rows 9
  simp only [dot,Fin.sum_univ_succ] at h9
  change 0+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(1*x 16+(1*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 340282366920938463463374607431768211455+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h9
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h9
  have h10 := rows 10
  simp only [dot,Fin.sum_univ_succ] at h10
  change 862713459717704035650365311846944737656111791604218977383885431635968+(77986382591119874064921855321526527381868595827415916824020267*x 0+(2668949918962272755740805946941502886286373228576567292954653*x 1+(100758297894020147554024975409120330178423098053670234523689029*x 2+(25995447357658063166494866421566043447166475144685359547976399*x 3+(66250796219640414915292195382615713228017713407091191535059741*x 4+(30051710622670116563016618864449112911308518409102424717649034*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(1*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) = 36893488147419103232+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(101237194868023629673163772448739743344356924690180564813783041*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(1*x 18+(0*x 19+(649033470896967801447398927572993*x 20+0))))))))))))))))))))) at h10
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h10
  have h11 := rows 11
  simp only [dot,Fin.sum_univ_succ] at h11
  change 0+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(1*x 18+(1*x 19+(0*x 20+0))))))))))))))))))))) = 649033470896967801447398927572992+(0*x 0+(0*x 1+(0*x 2+(0*x 3+(0*x 4+(0*x 5+(0*x 6+(0*x 7+(0*x 8+(0*x 9+(0*x 10+(0*x 11+(0*x 12+(0*x 13+(0*x 14+(0*x 15+(0*x 16+(0*x 17+(0*x 18+(0*x 19+(0*x 20+0))))))))))))))))))))) at h11
  norm_num only [zero_mul,one_mul,zero_add,add_zero] at h11
  have hr : ∀ i : Fin 6, 0 ≤ readResidues x i ∧ readResidues x i < FheRnsScale.deployedBase i := by
    intro i
    fin_cases i <;> norm_num [readResidues,FheRnsScale.deployedBase,Fin.succ] <;> omega
  refine ⟨hr,Int.natCast_nonneg (x 13),?_,Int.natCast_nonneg (x 16),?_,Int.natCast_nonneg (x 18),?_,?_,?_,?_⟩
  · dsimp [readCertificate]
    exact_mod_cast (show x 13 < 2*(2^126) by omega)
  · dsimp [readCertificate]
    exact_mod_cast (show x 16 < 2*(2^127) by omega)
  · norm_num [FheRnsScale.deployedQ]
    omega
  · have hi := congrArg (fun n : ℕ => (n : ℤ)) h6
    norm_num [Nat.cast_add,Nat.cast_mul] at hi
    norm_num [readResidues,readCertificate,FheRnsScale.deployedThetaG,Fin.sum_univ_succ,Fin.succ]
    linear_combination hi
  · have hi := congrArg (fun n : ℕ => (n : ℤ)) h8
    norm_num [Nat.cast_add,Nat.cast_mul] at hi
    norm_num [readResidues,readCertificate,FheRnsScale.deployedThetaF,Fin.sum_univ_succ,Fin.succ,wOffset]
    linear_combination hi
  · have hi := congrArg (fun n : ℕ => (n : ℤ)) h10
    norm_num [Nat.cast_add,Nat.cast_mul] at hi
    norm_num [readResidues,readCertificate,FheRnsScale.integerPart,
      FheRnsScale.deployedOmega,FheRnsScale.deployedGamma,FheRnsScale.deployedQ,
      Fin.sum_univ_succ,Fin.succ,wOffset,uOffset]
    linear_combination hi

/-- Matrix acceptance fixes one output, even where the source is nearest+1. -/
theorem balanced_output_forced (x : Fin 21 → ℕ) (h : Balanced x) :
    (x 18 : ℤ) = FheRnsScale.deployedOutput (readResidues x) % FheRnsScale.deployedQ :=
  sourceCertificateSound _ _ _ (balanced_source_accepts x h)

end Minidregg.Compiler.FheSourceCertificate

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheSourceCertificate.matrix_capacities' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.matrix_capacities

/-- info: 'Minidregg.Compiler.FheSourceCertificate.balanced_source_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.balanced_source_accepts

/-- info: 'Minidregg.Compiler.FheSourceCertificate.balanced_output_forced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.balanced_output_forced
