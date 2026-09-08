# Source and exact integer relation

[SOURCE] Local sources only; web/Kagi/Scry/PDF downloads:0. The inherited motivating paper2026/1127 remains scoped in `../bootstrap_successor/README.md`; this successor implements the actual deployed TFHE integer path, not that paper's different parameter set. TFHE root is `/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/tfhe-1.6.3/src/core_crypto/`. Individual source hashes and the reusable compiler/backend dependencies are in `execution_pins.json`.

| Source under TFHE root | Actual construction seen |
|---|---|
| `fft_impl/fft64/crypto/bootstrap.rs:294–357` | Initial accumulator rotation, first nonzero mask's `(X^a−1)*ct0`, then external product. This package stops before the latter. |
| `algorithms/polynomial_algorithms.rs:77,608,662` | Public wrapping subtraction and monomial multiplication; crate-private fused multiplication/subtraction. Native sign negation and subtraction wrap in u32. |
| `commons/math/decomposition/decomposer.rs:25–50,154–184` | Nearest representable value; balanced initial20-bit state, with input bit11 selecting the exact midpoint tie. |
| `commons/math/decomposition/iter.rs:130–155` | Remainder extraction, arithmetic right shift, carry bit trick, wrapping signed digit; reverse-level iteration. |
| `commons/numeric/unsigned.rs:108` | Arithmetic right shift through the associated signed type. |
| `fft_impl/fft64/math/decomposition.rs:1,77` | Tensor decomposition calls the same `decompose_one_level` used by the captured scalar decomposition. |

[DERIVED] Let Q=2^32,N=512,0≤a<1024,0≤j<512. Multiplication by X^a reads index `s=(j+1024−a)%512`, with sign `((j+1024−a)/512)%2`; the signed result is `ct0[s]` or `(Q−ct0[s])%Q`. The new component reuses the *entire* previous division-rotation system at `negA=(1024−a)%1024`. Both10-bit exponents and `a+negA=1024*negCarry` force that substitution; no source index or sign is an unchecked witness. `source_injective` proves the map is a permutation. Two distinct exact-public table IDs hold the same complete input rows, so both the permuted source and original destination are bound once each.

[DERIVED] Splitting all words into low/high16-bit limbs, the new equations are

```
deltaLo +baseLo =rotatedLo +65536*carryLo
deltaHi +baseHi +carryLo =rotatedHi +65536*carryHi
```

[EXECUTED kernel] Limb ranges and Boolean carries make both sides smaller than BabyBear. Field equality therefore lifts to Nat equality and forces `delta=(rotated+Q−base)%Q`. `TfheCmuxDecomposition.rowSound` proves this for every accepted assignment and transports acceptance through the existing compiler's `renameS` to both reused systems. It also proves the positive monomial source/sign laws.

[DERIVED] For native u32 x, the exact deployed decomposition is:

```
R = floor((x+2048)/4096) mod1048576
L = R mod1024; H = floor(R/1024)
rb = floor(x/2048) mod2
I = [R>524288 or (R=524288 and rb=1)]
C = [L>512 or (L=512 and H>=512)]
digit2 = L−1024*C
digit1 = H+C−1024*I
```

[EXECUTED kernel] `TfheSignedDecomposition.rowSound` forces R,rb,I,C and both offset digit equations. The20 ranged values include low/high16-bit input, L/H, the offset digits E2/E1, discarded11 bits, rounding bit, wrap bit, low9/top-bit splits of L/H, two exact zero indicators, and the carry auxiliaries. Two additional field wires supply inverse witnesses. The existing `Minidregg.Compiler.isZero` combinator forces the indicators for `L+1024*Hlow9` and `Llow9`. The source file is named `PredCompile.lean`, but its declarations are in `Minidregg.Compiler`, not a `PredCompile` namespace.

[EXECUTED kernel] The relation's equations are:

```
xLo =discardLow11 +2048*rb +4096*xLoHigh4
16*xHi+xLoHigh4+rb =L+1024*H+1048576*roundWrap
H =Hlow9+512*Htop; L =Llow9+512*Ltop
tieInit+zeroLower19*rb =zeroLower19
I+Htop*tieInit =Htop
tieDigit+zeroLow9*Htop =zeroLow9
C+Ltop*tieDigit =Ltop
E2+1024*C =L+512
E1+1024*I =H+C+512
```

[EXECUTED kernel] `initial_state` proves the balanced state has low remainder L, arithmetic quotient `H−1024I`, and quotient modulo1024 equal to H. Thus the library's first carry bit trick reads exactly H at its tie. `next_state_range` proves the resulting state `H+C−1024I` lies in[-512,512]; `final_step` proves that the library's last balanced quotient/remainder step returns that state, including both endpoints. E2/E1 encode the signed digits by adding512. These are exact tie choices, not just any bounded decomposition that recomposes to R.

[EXECUTED kernel] The two owned modules have17 guarded axiom prints. Sixteen depend only on `[propext, Classical.choice, Quot.sound]`; `TfheCmuxDecomposition.source_injective` uses `[propext, Quot.sound]`. No `sorry`, custom axiom, native-decision oracle or host-computed theorem is used. `zero_witness`, `negative_midpoint_witness`, `low_digit_tie_witness`, and `changed_zero_refused` are inhabited kernel checks/universal falsifiers. Focused final compile commands/logs are `results/signed-final-002.*` and `results/combined-final-002.*`; both exit0 with empty stdout/stderr. No full closure build was run.

[EXECUTED compiler boundary] `EmitTfheCmuxDecomposition.lean` emits IR2 through the existing term fold and simplifier. Public tuple columns are `[0,1,2,250,111,112,113,114,115,116]`; input source columns `[1,6,7,8]`; original input columns `[1,2,251,252]`. All3 tables have2,048 rows. The Rust runner decodes public bytes and uses the one existing shared proof backend; it contains no duplicate arithmetic AIR or witness generator.

[EXECUTED export repair] Three partial interpreted exports were terminated before any proof after showing poor throughput. A one-second retained native profile isolated recursive `Fin.cases` in the20-entry `![...]` width/offset lookup representation. Switching those two constant maps to indexed arrays retained the same values and universal proof and completed the final export with every row checked. `results/emit-004.*` is the successful output. Partial traces are retained locally, ignored, and are not proof inputs. Earlier compile diagnostics and unsuccessful build attempts are retained; none produced extra proofs.

[EXECUTED source isolation] `src/prior_rotation.rs` starts with all8,455 bytes of the frozen predecessor consumer, byte for byte, and appends only a public helper calling its existing decoder, public-table construction and verifiers. The new main crate shares `../proved_operation/backend`. Main companion trees, both predecessor packages and existing browser/site consumers were not edited. The pin helper's post-run inventory and final comparison provide the precise retained-source boundary; no host-integrity claim is inferred from them.
