/- Exact axiom census. Kept separate so the runtime source freeze remains byte-identical. -/
import Compiler.BfvTensorWitnessPlan
import Compiler.BfvTensorExhibits

/-- info: 'Minidregg.Compiler.BfvTensorMul.canonicalSystem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.canonicalSystem_sound

/-- info: 'Minidregg.Compiler.BfvTensorMul.sumTerm_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.sumTerm_eval

/-- info: 'Minidregg.Compiler.BfvTensorMul.convolutionTerm_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.convolutionTerm_eval

/-- info: 'Minidregg.Compiler.BfvTensorMul.convolution_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.convolution_denote

/-- info: 'Minidregg.Compiler.BfvTensorMul.padded_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.padded_denote

/-- info: 'Minidregg.Compiler.BfvTensorMul.convolution_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.convolution_bound

/-- info: 'Minidregg.Compiler.BfvTensorMul.column_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.column_correct

/-- info: 'Minidregg.Compiler.BfvTensorMul.radix_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.radix_balance

/-- info: 'Minidregg.Compiler.BfvTensorMul.denote_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.denote_add

/-- info: 'Minidregg.Compiler.BfvTensorMul.denote_scale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.denote_scale

/-- info: 'Minidregg.Compiler.BfvTensorMul.convolution_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.convolution_cast

/-- info: 'Minidregg.Compiler.BfvTensorMul.padded_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.padded_cast

/-- info: 'Minidregg.Compiler.BfvTensorMul.rowSystem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorMul.rowSystem_sound

/-- info: 'Minidregg.Compiler.BfvTensorCore.factor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.factor_bound

/-- info: 'Minidregg.Compiler.BfvTensorCore.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.sound

/-- info: 'Minidregg.Compiler.BfvTensorRow.prime_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorRow.prime_capacity

/-- info: 'Minidregg.Compiler.BfvTensorRow.wholeRowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorRow.wholeRowSound

/-- info: 'Minidregg.Compiler.BfvTensorRow.emittedSystem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorRow.emittedSystem_sound

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.canonical_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.canonical_accepts

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.weighted_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.weighted_accepts

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.nonzero_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.nonzero_premise

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.premise_inhabited

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.wrong_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.wrong_canonical

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.wrong_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.wrong_values

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.missing_cross_factor_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.missing_cross_factor_refused

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.wrong_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.wrong_refused

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.capacity_inhabited' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.capacity_inhabited

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.quotient_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.quotient_capacity

/-- info: 'Minidregg.Compiler.BfvTensorCore.Exhibits.field_column_capacity' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.field_column_capacity

