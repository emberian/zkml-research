import Theory.HorizonComposition

namespace Minidregg.Theory.HorizonComposition

def zeroFrame : Frame := ⟨0,0,0,0⟩
def halfFrame : Frame := ⟨1/2,0,0,0⟩
def bridgeFrame : Frame := ⟨1/2,1/2,0,0⟩

/-- Root middle gap 1/2 is supplied entirely by the first child's left gap. -/
def witness : Node 2 1 → Frame
  | Sum.inl _ => bridgeFrame
  | Sum.inr (b,_) => if b=0 then halfFrame else zeroFrame

def ProbabilityWitnessClaim : Prop :=
  Coherent witness ∧ (∀ n, (witness n).probabilities) ∧
  (witness (root 2 1)).gap = 1/2 ∧ uniformGap witness = 1/12

theorem witness_coherent : Coherent witness := by
  constructor
  · norm_num [root,sub,witness,bridgeFrame,halfFrame,zeroFrame,
      Frame.middleGap,Frame.gap,Fin.sum_univ_succ]
  · intro b
    fin_cases b <;> norm_num [Coherent,root,sub,witness,halfFrame,zeroFrame,Frame.middleGap]

theorem witness_probabilities : ∀ n, (witness n).probabilities := by
  intro n
  cases n with
  | inl u => norm_num [witness,bridgeFrame,Frame.probabilities,Set.mem_Icc]
  | inr p =>
    rcases p with ⟨b,u⟩
    fin_cases b <;> norm_num [witness,halfFrame,zeroFrame,Frame.probabilities,Set.mem_Icc]

theorem witness_nonzero : ProbabilityWitnessClaim := by
  refine ⟨witness_coherent,witness_probabilities,?_,?_⟩
  · norm_num [witness,root,bridgeFrame,Frame.gap]
  · rw [uniform_side_average 2 1 witness witness_coherent]
    norm_num [witness,root,bridgeFrame,Frame.gap,nodeCount,Finset.sum_range_succ]

theorem premise_inhabited : ∃ f : Node 2 1 → Frame,
    Coherent f ∧ (∀ n, (f n).probabilities) ∧ (f (root 2 1)).gap ≠ 0 := by
  refine ⟨witness,witness_coherent,witness_probabilities,?_⟩
  norm_num [witness,root,bridgeFrame,Frame.gap]

theorem witness_probability_pair :
    average (fun x : Node 2 1 × Bool => (witness x.1).realTest x.2) = 2/3 ∧
    average (fun x : Node 2 1 × Bool => (witness x.1).idealTest x.2) = 7/12 := by
  constructor <;> norm_num [average,Fintype.sum_prod_type,sum_nodes_succ,sub,root,
    witness,bridgeFrame,halfFrame,zeroFrame,Frame.realTest,Frame.idealTest,
    Fin.sum_univ_succ,Fintype.card_prod,card_nodes,nodeCount,Node]

/-- The two depths have 1 and 2 nodes; each side still has half of that mass. -/
theorem witness_depth_weights : depthWeight 2 1 0 = 1/3 ∧ depthWeight 2 1 1 = 2/3 := by
  constructor <;> norm_num [depthWeight,levelCount_zero,levelCount_succ,nodeCount,Finset.sum_range_succ]

def biasedDepthGap {B H : ℕ} (f : Node B H → Frame) : ℚ :=
  average (fun d : Fin (H+1) => depthSideMean f d)

/-- Uniform depths and uniform nodes differ, despite valid rational probabilities. -/
theorem biased_depth_falsifier : biasedDepthGap witness = 1/16 ∧
    biasedDepthGap witness ≠ uniformGap witness := by
  have hb : biasedDepthGap witness = 1/16 := by
    norm_num [biasedDepthGap,average,Fin.sum_univ_succ,depthSideMean,
      depthGapSum,sum_nodes_succ,sub,root,depth,witness,halfFrame,bridgeFrame,zeroFrame,
      Frame.leftGap,Frame.rightGap,levelCount_zero,levelCount_succ,Node,card_nodes,nodeCount]
  refine ⟨hb,?_⟩
  rw [hb,witness_nonzero.2.2.2]
  norm_num

/-- Dropping the sole nonzero child term leaves zero but root gap is 1/2. -/
theorem omitted_node_falsifier :
    (witness (root 2 1)).gap ≠
      (witness (root 2 1)).leftGap - (witness (root 2 1)).rightGap := by
  norm_num [witness,root,bridgeFrame,Frame.gap,Frame.leftGap,Frame.rightGap]

def missingTerminal : Node 2 0 → Frame := fun _ => bridgeFrame

/-- Without terminal ideal equality, all local SIM gaps can vanish while the
root gap remains nonzero. Every frame is still a valid rational probability. -/
theorem terminal_zero_falsifier :
    (∀ n, (missingTerminal n).probabilities) ∧ ¬ Coherent missingTerminal ∧
    uniformGap missingTerminal = 0 ∧ (missingTerminal (root 2 0)).gap = 1/2 := by
  norm_num [missingTerminal,Coherent,root,bridgeFrame,Frame.probabilities,Set.mem_Icc,
    Frame.middleGap,Frame.gap,uniformGap,average,Fintype.sum_prod_type,
    Frame.realTest,Frame.idealTest,Node]

def balancedFrame : Frame := ⟨3/4,1/2,1/2,1/4⟩

/-- Failing to complement the right test destroys the sign. -/
theorem right_orientation_falsifier :
    balancedFrame.probabilities ∧ balancedFrame.middleGap = 0 ∧
    (balancedFrame.leftGap + balancedFrame.rightGap)/2 = 0 ∧
    balancedFrame.gap/2 = 1/4 := by
  norm_num [balancedFrame,Frame.probabilities,Set.mem_Icc,Frame.middleGap,
    Frame.leftGap,Frame.rightGap,Frame.gap]

/-- Six meaningful positions require eight dyadic positions, so padding changes
the exact loss to 1/16. It preserves neither 1/12 nor uniform node probabilities. -/
theorem witness_dyadic_padding :
    dyadicSize 2 1 = 8 ∧ paddedGap witness 2 = 1/16 ∧ paddedGap witness 2 ≠ uniformGap witness := by
  have hm : dyadicSize 2 1 = 8 := by decide
  have hp : paddedGap witness 2 = 1/16 := by
    rw [padded_uniform_average witness witness_coherent]
    norm_num [witness,root,bridgeFrame,Frame.gap,nodeCount,Finset.sum_range_succ]
  refine ⟨hm,hp,?_⟩
  rw [hp,witness_nonzero.2.2.2]
  norm_num

theorem polynomial_envelope_inhabited :
    2^1 ≤ 4^1 ∧ dyadicSize 2 1 < 8 * 4^1 := by
  constructor
  · norm_num
  · exact polynomial_obligation_envelope 2 1 4 1 (by omega) (by norm_num)

end Minidregg.Theory.HorizonComposition

/-- info: 'Minidregg.Theory.HorizonComposition.witness_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.witness_coherent
/-- info: 'Minidregg.Theory.HorizonComposition.witness_probabilities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.witness_probabilities
/-- info: 'Minidregg.Theory.HorizonComposition.witness_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.witness_nonzero
/-- info: 'Minidregg.Theory.HorizonComposition.premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.premise_inhabited
/-- info: 'Minidregg.Theory.HorizonComposition.witness_probability_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.witness_probability_pair
/-- info: 'Minidregg.Theory.HorizonComposition.witness_depth_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.witness_depth_weights
/-- info: 'Minidregg.Theory.HorizonComposition.biased_depth_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.biased_depth_falsifier
/-- info: 'Minidregg.Theory.HorizonComposition.omitted_node_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.omitted_node_falsifier
/-- info: 'Minidregg.Theory.HorizonComposition.terminal_zero_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.terminal_zero_falsifier
/-- info: 'Minidregg.Theory.HorizonComposition.right_orientation_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.right_orientation_falsifier
/-- info: 'Minidregg.Theory.HorizonComposition.witness_dyadic_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.witness_dyadic_padding
/-- info: 'Minidregg.Theory.HorizonComposition.polynomial_envelope_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.HorizonComposition.polynomial_envelope_inhabited
