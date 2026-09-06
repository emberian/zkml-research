# Integer certificate emission — a compiler-native signed QR slice

[DERIVED] The integer certificate now reaches the existing descriptor compiler.
Accepted range gadgets force local radix/carry equalities to be integer equalities;
the emitted descriptor consequently forces the signed quotient and a remainder in
`[0,Q)`. This is proved at Q31/t4 and at the recorded 109-bit Q/t2²⁰, over deployed
BabyBear. Existing generic common-subexpression elimination (CSE) preserves the
large certificate and reduces its emitted gate count from 52,378 to 21,279.

[EXECUTED] Two proposed Compiler modules, 20 exact axiom pins, the isolated Compiler
umbrella, the companion import-boundary script, and patch applicability are green.
The patch is `formal/integer_certificate_emission/minidregg-integer-certificate-emission.patch`;
it has not been applied. Exact commands/results and hashes are in the lane's
`experiments/integer_certificate_emission/compile_*.json` and `review_01.json`.
No minidregg, breadstuffs, VERDICTS, shared ledger or index was edited by this lane.

[DERIVED scope] This is a quotient/remainder certificate-emission slice. It does
not establish source-ciphertext provenance, integer convolution, actual runtime
engine rounding, relinearization, decryption noise, private release or the proof
protocol's soundness. In particular the large descriptor has **zero public inputs**:
it is an internal arithmetic relation whose represented z/y/r still need binding to
the surrounding computation. Do not call this deployed BFV Hole B closure.

## The existing path that was reused

[SOURCE: Lean source, local inspection] All references in this paragraph are under
`/Users/ember/dev/minidregg/`. `Compiler/BfvSignedAccumulatorAir.lean:177`,
`weightedSumGadget_sound`, already proves a natural weighted sum from range gadgets,
zero boundary carries and radix-column terms. It leaves local no-wrap inequalities
to the caller. `Compiler/Emit.lean:398`, `emit_accepts_iff_fin`, connects the source
constraint system to the actual emitted descriptor. `Compiler/DescriptorEval.lean:277`,
`fillAux_emit_holds`, supplies the existing auxiliary-wire evaluator's completeness.
`Compiler/NativeKernelPlan.lean:265`, `descriptorHoldsCheck_eq_true_iff`, identifies
the executed Boolean checker with descriptor satisfaction. No twin AIR, descriptor
emitter, auxiliary evaluator or checker was authored here.

[DERIVED] The new reusable theorem is
`formal/integer_certificate_emission/Compiler/IntegerCertificateEmission.lean:49`,
`Minidregg.Compiler.IntegerCertificateEmission.ranged_weighted_sound`.
For radix `B=2^limbBits`, scalar bound `S=2^scalarBits`, carry bound `C=2^carryBits`
and n terms, checked range gadgets give the two compile-time sufficient budgets:

```
left column  <= (B-1) + n*(B-1)*(S-1) + (C-1)
right column <= (B-1) + B*(C-1)
```

[DERIVED] Each side is proved strictly below BabyBear before a field equality is
lifted to a natural equality. The existing carry-telescoping theorem then produces
the wide natural equality. This prevents the earlier p-field counterexample in
BFV_LIFT_REFINEMENT.md: reducing an unbounded integer certificate modulo p does not
make it sound. The new helper derives bounds from **accepted constraints**, rather
than accepting the prover's asserted range as a hypothesis.

## Small signed witness and its teeth

[DERIVED] Four 6-bit scalar words hold `Z=z+32`, `Y=y+8`, `r`, `s`. Two existing
weighted accumulators share three radix16 result digits and use 8-bit carries:

```
4Z+263 = 31Y+r+128
r+s = 30
```

[DERIVED] The second equation and nonnegative scalar ranges force r<31; cancelling
the offsets gives `4z+15=31y+r`. The theorem
`IntegerCertificateEmission.certificateDescriptor_quotient` at:183 forces
`y=(4z+15)/31`, including negative z and the declared nearest/ties-up convention.
`forged_quotient_refused` at:192 refuses claimed y=0 when z=−8 for **every** auxiliary
assignment. `signed_premise_inhabited` at:250 is a kernel-checked actual negative
inhabitant: z−8, y−1, r14. The small descriptor's three public variables are Z,Y,r.

[EXECUTED] The existing generated evaluator/checker accepts all 64 signed z values
in [-32,31], and refuses all 685 single-wire +1 mutations of the negative witness.
Additional fresh-aux forgeries change the quotient, or use remainder 31; carry and
aux-wire mutations are also retained as concrete vectors in `checker_vectors.json`.
These are executed checks, not a claim of exhaustive cryptographic security.

## Full-modulus relation and representation

[SOURCE: local note and preceding lane] `notes/cross-limb-binding.md:56–57` records
the three RNS moduli `[0xffffee001,0xffffc4001,0x1ffffe0001]` and N4096.
Their exact product is `Q=649033470896967801447398927572993`.
BFV_LIFT_REFINEMENT.md records the integer QR reference and its unrelinearized
middle-component bound `Zmax=2*N*(Q-1)^2`; this lane does not reinterpret that
reference as a theorem about the live engine.

[DERIVED] The large source uses radix64, 43 columns and 13-bit carries. Its 101 six-bit
scalar digits comprise 39 for offset z, 24 for offset y, 19 for r and 19 for the
remainder complement. Offsets are `Z0=2^231`, `Y0=2^142`. Four existing weighted
accumulators enforce two shared-result equalities:

```
t*Z + floor(Q/2) + Q*Y0 = Q*Y + R + t*Z0
R+S = Q-1
```

[DERIVED] `LargeIntegerCertificateEmission.descriptor_sound` at:83 proves the
signed integer equation and `R<Q` for every satisfying descriptor vector.
`descriptor_quotient` at:126 forces the declared quotient; `forged_quotient_refused`
at:142 refuses the wrong quotient at represented z=−Q.
`coefficient_capacities` discharges every public coefficient's 43-column capacity.
The range-derived column ceilings are 409,123 and 524,287, both below 2,013,265,921.
The wider digit capacity does not itself prove that z is a true convolution or
lies within the preceding lane's convolution bound.

[EXECUTED] Seven generated full-modulus witnesses cover−Zmax,−Zmax+1,−1,0,1,
Zmax−1,Zmax. All pass; 14 fresh-aux quotient/remainder mutations refuse, including
`y←y−1,r←r+Q`, which preserves the integer QR equation but violates r<Q.
The same 21 verdicts hold after existing compiler CSE. `large_results.json` records
each exact signed value. The large positive witnesses are **compiled checks**;
they are not advertised as kernel-proved inhabitants.

[EXECUTED limitation] An optional attempt to kernel-reduce the full 3,773-variable
positive assignment was interrupted after approximately 65 seconds when the inspected
Lean process used roughly 20GB RSS. `compile_LargeIntegerCertificateEmission_03.json`
retains signal exit −2 (shell status 254). That failed attempt supplied no theorem. The final large universal
soundness/refusal proofs pass without it; the small kernel-proved inhabitant and
large compiled positive witnesses remain distinct evidence classes.

## The emitted bill, before surrounding BFV obligations

[EXECUTED] These counts come from the actual Lean-emitted descriptors and existing
checker; they are operation counts, not latency or proof-security estimates.

| Relation | Gates | Add / multiply gates | Zero checks | Variables | Wire header |
|---|---:|---:|---:|---:|---:|
| Q31/t4 | 570 | 292 /278 | 141 | 115 | 685 |
| 109-bit Q, raw | 52,378 | 26,361 /26,017 | 4,555 | 3,773 | 56,151 |
| 109-bit Q, existing CSE | 21,279 | 13,262 /8,017 | 4,555 | 3,773 | 56,151 |

[SOURCE + DERIVED] `Compiler/EmitShare.lean:588`, `cse_emit_accepts_iff`, is the
existing generic semantics-preserving compiler pass used here. The new
`LargeIntegerCertificateEmission.sharedDescriptor_sound` at:155 transports the
exact certificate theorem through that pass. It authors no hand-tuned descriptor.
CSE retains the original wire numbering and zero checks, as the source's residual
`EMIT-share-compact` says. Dropped auxiliary slots are no longer individually
constrained; the raw all-wire mutation count must not be copied onto the CSE result.

[EXECUTED] Raw emission contains 16,868 multiplication gates with a zero constant
operand and 22,091 with at least one constant operand, including those zero products.
`large_CSE_costs.json` preserves the census. Structural sharing alone removes 31,099
gates. Algebraic constant simplification, sparse weighted-term emission and dead-wire
compaction remain possible generic compiler work, with separate faithfulness proofs.

[DERIVED baseline] Replicating this unchanged coefficient relation across 3×4096
unrelinearized coefficients costs 643,620,864 raw gates, or 261,476,352 CSE gates,
plus 55,971,840 zero checks either way. This deliberately unoptimized replication
does not include convolution verification, operand-source bindings, input/output
residue consistency, commitments, witness generation, proof protocol, relinearization
or noise. It is not a lower bound and not a measured full BFV circuit.

## Handoff

[EXECUTED] Reproduction and exact source/patch hashes are in
`formal/integer_certificate_emission/VALIDATION.md`. Large emitted JSON descriptors
are retained in deterministic gzip form; the scripts regenerate their plain JSON.
Metered search queries: 0; all source inspection was local.

[OPEN] Next decisive seam: use this reusable range-derived weighted-sum theorem
for a concrete resident numerical update and bind its source/public boundary to
the durable pre/post materialization. The root-assigned durable EMA lane has the
interface and the signed-byte normalization `7C+U=8C'+r`, with r three-bit ranged.
For BFV itself, bind lifted convolution and the selected engine's correction terms
before presenting this certificate as its authorized multiplication step.
