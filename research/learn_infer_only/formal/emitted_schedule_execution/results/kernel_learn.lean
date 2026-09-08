import Compiler.EmittedScheduleExecution
open Minidregg.Compiler.PrivateAddressEmaSchedule
open Minidregg.Compiler.EmittedScheduleExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem learn_valid_kernel : validCheck learnSchedule = true := by
  decide +kernel
#print axioms learn_valid_kernel
