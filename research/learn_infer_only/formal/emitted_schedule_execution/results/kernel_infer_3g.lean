import Compiler.EmittedScheduleExecution
open Minidregg.Compiler.PrivateAddressEmaSchedule
open Minidregg.Compiler.EmittedScheduleExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem infer_valid_kernel : validCheck inferSchedule = true := by
  decide +kernel
#print axioms infer_valid_kernel
