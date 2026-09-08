# Exact integer witness instruction format

[EXECUTED] `lean-bigint-witness-plan-v1` is consumed by the owned generic native executor. It is witness-generation data; it is not an AIR descriptor, proof, or trusted executor certificate.

The object fields are `schema`, `trace_width`, `input_arity`, `input_digit_radix`, `field_modulus`, `register_count`, and `instructions`. Each instruction is `[destination, opcode, aMode, aValue, bMode, bValue]`. Mode0 is an arbitrary signed decimal string literal; mode1 is a natural register index. All registers begin at integer zero for each row. Operands are read before the destination is written.

| Opcode | Operation |
|---:|---|
| 0 | copy a |
| 1 | a+b |
| 2 | a*b |
| 3 | max(a-b,0) |
| 4 | a-b |
| 5 | Euclidean quotient a/b, requiring b>0 |
| 6 | Euclidean remainder a%b, requiring b>0 |
| 7 | max(a,0) |
| 8 | public input at index a |
| 9 | assert a=b, then copy a; failure aborts witness production |

[EXECUTED] The actual plan has96,624 instructions,96,625 registers,24,575 trace columns,88 public columns, radix512 and field2013265921. The first88 registers must equal the complete caller row after execution. Caller row IDs are preserved and need not start at zero; each must be a canonical field value. All other public columns must be radix512 digits. Output is the first24,575 registers reduced modulo the field and serialized as little-endian u32 words.

[EXECUTED] CLI: `lean-bigint-witness PLAN TEMPLATE PUBLIC_ROWS NEW_OUT_DIR`. The output directory must be new. Output files are `trace.leu32`, `template_ir2.json` (an opaque byte-for-byte copy), and `emission.json`. Descriptor parsing and width matching belong to the proof backend. No AIR is constructed or evaluated here. Exact plan, executable, template and source hashes are in READY.json.

[OPEN] The native interpreter and plan compiler have no language-refinement proof. The generated relation's existing soundness theorem constrains every accepted witness regardless of how this untrusted producer computes it.
