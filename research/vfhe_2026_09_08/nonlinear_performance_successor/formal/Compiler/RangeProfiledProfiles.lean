import Compiler.RangeProfiledCompact
import Compiler.BasisExtensionPublic
import Compiler.NonlinearRnsProfiled
namespace Minidregg.Compiler.RangeProfiledActual
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.RangeProfiledCompact
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def extension : Profile where
  layout := ActualBasisExtension.profile
  rowsLayout := ActualBasisExtension.rowLayout
  rows := ActualBasisExtension.rows
  publicArity := 84
  oldMap := ActualBasisExtension.wireMap
def rescale : Profile where
  layout := NonlinearRnsInstance.profile
  rowsLayout := NonlinearRnsProfiled.rowLayout
  rows := NonlinearRnsInstance.rows
  publicArity := 88
  oldMap := NonlinearRnsPublic.wireMap

end Minidregg.Compiler.RangeProfiledActual
