# Boolean schedule v1

[DERIVED interface, frozen before emitter work] The emitted JSON has this shape:

```json
{
  "schema": "private-address-ema-bool-schedule-v1",
  "operation": "learn",
  "nInputs": 42,
  "nWires": 100,
  "gates": [
    {"op": "xor", "a": {"w": 0}, "b": {"c": true}, "out": 42},
    {"op": "and", "a": {"w": 42}, "b": {"w": 1}, "out": 45}
  ],
  "outputs": [{"w": 45}]
}
```

[DERIVED illustrative only] The numbers and short output vector in the example
illustrate the schema; this is not the EMA descriptor. Exact Lean-generated
artifacts will be `artifacts/learn.json` and `artifacts/infer.json`.

[DERIVED contract] `wire` is exactly one of `{"w": nonnegative_integer}` and
`{"c": Boolean}`. Operators are exactly `xor` and `and`. These are the addition
and multiplication of `ZMod 2`; NOT is XOR with true, and
`MUX(c,t,f) = f XOR (c AND (t XOR f))`. The source operations and their lowering
must be proved before the descriptor is called semantically checked.

[DERIVED contract] Learn has 42 input bits and 32 output bits. Infer has 34 input
bits and one output bit. Inputs 0–31 are the four state bytes, register-major and
least-significant-bit first within each byte. Inputs 32 and 33 are the address,
least-significant-bit first. Learn inputs 34–41 are the signed label byte,
least-significant-bit first. Learn outputs follow the same state order. Infer's
single Boolean means that the addressed register is negative; zero is false.

[DERIVED interpreter contract] Allocate `nWires` optional ciphertext slots and
initialize exactly slots below `nInputs`. Process gates in listed order. Require
`out >= nInputs`, `out < nWires`, strictly increasing output indices, no duplicate
write, and each operand/output reference in range. A referenced wire must
already be initialized. A constant operand uses an internal public trivial
Boolean ciphertext. Evaluate one generic TFHE XOR/AND call and store at `out`.
Read the listed outputs in order, requiring each reference initialized.
Existing artifact outputs must still satisfy the Encrypted-variant requirement.

[DERIVED numbering] The existing proved CSE pass keeps original output wire
numbers and may leave holes. Do not require contiguous gate output indices.
The generic interpreter authors no EMA arithmetic, address equality, MUX or
inference schedule. The saved preceding workload and binaries remain unchanged.

[OPEN formal/runtime boundary] The proposed Lean theorem will identify any
gate-satisfying valuation's output with the source-term evaluation, using the
existing fold and sharing proofs. JSON parsing, Rust memory/loop semantics,
TFHE gate correctness/noise and ciphertext serialization remain the runtime
TCB; independent plain-Boolean interpreter comparisons and actual encrypted
smoke execution are separate evidence.
