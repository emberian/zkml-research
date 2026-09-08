# Historical construction plan

[EXECUTED] Completed; README.md and STATUS.md describe the final result. The design below records the starting plan.

[OPEN] Root assigned complete first CMUX integer input and exact deployed signed decomposition. Prior packages remain frozen. Own this directory only; no new keys/encryption, no FFT/external product, no broad formatter/build/review queue. One meaningful new complete proof plus fresh joined acceptance/changed-output refusal.

[SOURCE] Actual prior mask row0 is `[0,6878,25207,394]`; it is the first nonzero mask. Prior verified body row805 is `[805,56149,55195,862]`. Reuse the actual saved `body_rotated_lut.ct` from `../bootstrap_rotation_successor/fixtures/normal_001/`.

[SOURCE] TFHE1.6.3 fused `polynomial_wrapping_monic_monomial_mul_and_subtract` at core_crypto/algorithms/polynomial_algorithms.rs:662 is crate-private. Existing public `polynomial_wrapping_monic_monomial_mul` at608 and `polynomial_wrapping_sub_assign` at77 compute the same exact native-u32 relation in two calls. Generate this necessary new public delta once; no FFT or bootstrapping key needed. Call existing `SignedDecomposer::<u32>::new(base10,levels2)` on all2048 delta coefficients, retaining ordered level2 then level1 digits and closest_representable output. The FFT tensor iterator calls the same `decompose_one_level` as the public scalar iterator (fft64/math/decomposition.rs).

[DERIVED] Exact native two-digit model for arbitrary u32 x:

```
R = floor((x+2048)/4096) mod2^20
L = R mod1024; H = floor(R/1024); rb = floor(x/2048) mod2
I = [R>2^19 or (R=2^19 and rb=1)]
C = [L>512 or (L=512 and H>=512)]
digit2 = L-1024*C
digit1 = H+C-1024*I
```

[SOURCE] Init balancing is decomposer.rs:150–184; scalar iterator's `decomposition_bit_trick`/`decompose_one_level` is iter.rs:145–180. The second-step signed state lies in[-512,512], so its last digit is exactly that state. This includes the deployed ±512 tie choices; do not weaken to just a valid recomposition.

[OPEN planned compiler] Build an independent `Compiler/TfheSignedDecomposition.lean` first. Relative layout139 wires:22 values plus117 range bits. Values0..19 widths `[16,16,10,10,11,11,11,1,4,1,9,1,9,1,1,1,1,1,1,1]`; values20,21 are unconstrained field inverse witnesses. Interpret values as xLo,xHi,L,H,digit2+512,digit1+512,discardLow11,rb,xLoHigh4,roundWrap,Hlow9,Htop,Llow9,Ltop,zeroLower19,zeroLow9,tieInit,I,tieDigit,C,invLower19,invLow9. Use exact equations:

```
xLo = discardLow11+2048*rb+4096*xLoHigh4
16*xHi+xLoHigh4+rb = L+1024*H+1048576*roundWrap
H = Hlow9+512*Htop
L = Llow9+512*Ltop
tieInit+zeroLower19*rb = zeroLower19
I+Htop*tieInit = Htop
tieDigit+zeroLow9*Htop = zeroLow9
C+Ltop*tieDigit = Ltop
(digit2+512)+1024*C = L+512
(digit1+512)+1024*I = H+C+512
```

[SOURCE reusable] `Compiler.PredCompile.isZero` at234, `isZero_forced` at238, `isZero_complete` at255 supplies exact indicator/inverse constraints; use it on term `L+1024*Hlow9` and on `Llow9`. The same module has `renameS`, `systemAccepts_renameS`, and `renameT` at144–180. formal_runtime_bridge confirmed cached PredCompile.olean in its generic rescale overlay. This avoids a new variable-renaming or zero-test implementation.

[OPEN planned combined relation] Reuse the entire previous111-wire initial-rotation relation through `PredCompile.renameS`, with its exponent set to negA=(1024-a)%1024, thereby obtaining X^a*ct0. Constrain `a+negA=1024*negCarry` with both exponents10-bit and carry Boolean. Embed the139-wire decomposition at offset111 so its xLo/xHi are delta limbs. Append baseLo/baseHi and two subtraction carries, with limb equations `deltaLo+baseLo=rotLo+65536*cLo`, `deltaHi+baseHi+cLo=rotHi+65536*cHi`; each side small, forcing delta=(rot-base) mod2^32. Append range wires (about51 total extra). Expected total301 wires. Two copies of the input public table can be separate ExactPublic tables to bind rotated-source and original-destination reads once each; one complete output table binds delta/rounded/digits/a. Lean produces all witnesses; Rust only decodes ciphertexts, captures native output and invokes shared prover.

[OPEN join] New consumer must verify the existing prior modulus-switch and initial-rotation proofs and their native input binding, then use the verified first nonzero mask exponent394 and exact prior output ciphertext as ct0. Use copied full public fixture/proofs for standalone replay. No recursion/wholePBS/security-bit claim.
