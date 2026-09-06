import Assurance.ResidentEmaWitness
open Minidregg.Compiler.ResidentEmaCertificate
open Minidregg.Compiler
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.DescriptorEval
#eval (descriptor.nPublic,descriptor.nVars,descriptor.nWires,descriptor.gates.length,descriptor.zeros.length)
#eval descriptorHoldsCheck descriptor (fun i => (candidate 128 248 143 0).getD i 0)
#eval descriptorHoldsCheck descriptor (fun i => (candidate 128 248 144 0).getD i 0)
#eval descriptorHoldsCheck descriptor (fun i => (candidate 0 0 0 0).getD i 0)
#eval descriptorHoldsCheck descriptor (fun i => (candidate 0 255 31 7).getD i 0)
