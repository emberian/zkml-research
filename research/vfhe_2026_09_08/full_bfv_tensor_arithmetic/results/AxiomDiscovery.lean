import Compiler.BfvTensorMul
import Compiler.BfvTensorCore
import Compiler.BfvTensorRow
import Compiler.BfvTensorExhibits
import Compiler.BfvTensorWitnessPlan
set_option pp.width 10000
#print axioms Minidregg.Compiler.BfvTensorMul.canonicalSystem_sound
#print axioms Minidregg.Compiler.BfvTensorMul.sumTerm_eval
#print axioms Minidregg.Compiler.BfvTensorMul.convolutionTerm_eval
#print axioms Minidregg.Compiler.BfvTensorMul.convolution_denote
#print axioms Minidregg.Compiler.BfvTensorMul.padded_denote
#print axioms Minidregg.Compiler.BfvTensorMul.convolution_bound
#print axioms Minidregg.Compiler.BfvTensorMul.column_correct
#print axioms Minidregg.Compiler.BfvTensorMul.radix_balance
#print axioms Minidregg.Compiler.BfvTensorMul.denote_add
#print axioms Minidregg.Compiler.BfvTensorMul.denote_scale
#print axioms Minidregg.Compiler.BfvTensorMul.convolution_cast
#print axioms Minidregg.Compiler.BfvTensorMul.padded_cast
#print axioms Minidregg.Compiler.BfvTensorMul.rowSystem_sound
#print axioms Minidregg.Compiler.BfvTensorCore.factor_bound
#print axioms Minidregg.Compiler.BfvTensorCore.sound
#print axioms Minidregg.Compiler.BfvTensorRow.prime_capacity
#print axioms Minidregg.Compiler.BfvTensorRow.wholeRowSound
#print axioms Minidregg.Compiler.BfvTensorRow.emittedSystem_sound
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.canonical_accepts
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.weighted_accepts
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.nonzero_premise
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.premise_inhabited
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.wrong_canonical
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.wrong_values
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.missing_cross_factor_refused
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.wrong_refused
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.capacity_inhabited
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.quotient_capacity
#print axioms Minidregg.Compiler.BfvTensorCore.Exhibits.field_column_capacity
