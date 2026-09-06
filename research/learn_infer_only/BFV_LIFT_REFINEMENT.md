# BFV integer-lift and actual-engine refinement

[EXECUTED + DERIVED] **The actual engine is now pinned and its scalar mismatch is concrete.** Breadstuffs calls vendored fhe-dregg/fhe.rs0.1.1, whose RNS scaler uses selected lifts and directed fixed-point correction. A literal source model matches **86,208 full unrelinearized output coefficients** from11 real Rust tensor evaluations. Constructed boundary ciphertexts expose three coefficients where the engine returns **exact nearest+1**, including172481 instead of172480; one boundary input also receives a lift shifted by Q from the strictly centered representative. These are refutations of strict coefficient-reference equivalence on those inputs, not BFV decryption failures or cryptographic breaks.

[DERIVED] A second, separately checked **33-theorem patch** proves the exact scalar decomposition, the source's wrapping/truncation formulas under discharged range bounds, and the actual six-limb deterministic output formula for **all canonical residue vectors** at the N4096/Q109/t1032193 instance. The sharp nearest-or-nearest+1 envelope is proved relative to the **source-selected lift**; its exact numeric witness is inhabited and checked in Lean. The target for a proof circuit is the deterministic formula, never a choice of either nearby output. Rust's modular arithmetic/NTT/array interpretation and the emitted checker remain separate seams.

[DERIVED] The useful positive result is a complete **integer certificate relation for a stated reference**: canonical operand lifts, verified integer negacyclic convolution, and a bounded integer quotient/remainder certificate force nearest, ties toward +infinity scaling. This closes the logical implication named `BFVScaleLiftRefinement` in `docs/VERDICTS.md:1644`; it does not instantiate a proof-system checker or prove SEAL implementation refinement. Those are still separate obligations.

[EXECUTED] The module and isolated Compiler umbrella pass with 27 exact axiom pins, alongside patch applicability and the existing import-boundary check. Final commands are recorded in `formal/bfv_lift_refinement/VALIDATION.md`. This lane edits only this note and its two owned subdirectories; it does not edit `docs/VERDICTS.md`, minidregg, or breadstuffs. The root agent owns STATUS/NEXT integration and independent review.

[EXECUTED] Metering across both tranches: **0 metered search queries**; two pinned primary-source SEAL code fetches plus their MIT license, listed in `experiments/bfv_lift_refinement/sources.json`. The actual-engine tranche uses local source and the local2021/204 PDF only; its source hashes, toolchain and commands are in `engine-run.json`. No Scry credential was needed or read. No PDF downloads.

## What the theorem actually says

[DERIVED] The patch's namespace is `Minidregg.Compiler.BFVScaleLift`. `convolution a b k` is the N-term integer coefficient of `a*b` in `Z[X]/(X^N+1)`. No modulus reduction occurs inside that convolution. The companion `tensorScaleLiftRefinement` covers the full unrelinearized size2×size2 three-component tensor, with a universal honest-certificate theorem and nonzero premise inhabitation. The middle component adds its two integer cross terms before scaling. The declared representative convention is **each operand coefficient in `[0,Q)`**; a centered-lift implementation would need its own input mapping/refinement. `canonical_lift_unique` proves this lift is forced by its range and a congruence to the bound source coefficient.

[DERIVED] `accepts Q t a b out w` checks `Q>0`, `0<t<Q`, canonical input ranges, `w.lifted k = convolution a b k`, and, for every coefficient,

```
0 <= r < Q
t*z + floor(Q/2) = Q*y + r        (integer equality)
out = y mod Q
```

[DERIVED] `bfvScaleLiftRefinement` proves accepted output equals `reference Q t a b`. `quotient_complete` and `honest_accepts` supply certificates for **every** canonical input, including negative convolution coefficients. `nearest_eq_doubled` proves `(tz+floor(Q/2))/Q = (2tz+Q)/(2Q)` for every integer z and Q>0, explicitly including even Q and negative ties. `quotient_range` derives a signed quotient bound from numeric inequalities; no prover-supplied quotient bound is silently trusted.

[DERIVED] `convolution_bound` proves `|z_k| <= N*A*B` for signed operands bounded by A and B. This is the coefficient range needed for certificate representation. It does **not** discharge the noise propagation, relinearization noise, or decryption correspondence gaps in `/Users/ember/dev/breadstuffs/metatheory/Bfv/Mul.lean:25–57`.

[DERIVED] The carrier permits arbitrary forged lifts, quotients, remainders and outputs. `premise_inhabited` supplies a nonempty acceptance set on a nonzero N=2 example: `[1,2]*[3,4] = [-5,10]`, scaled mod31 with t4 to `[30,1]`. `forged_output_refused` refuses `[0,1]` for **every witness**. This is an implication about checked arithmetic and cannot by itself authenticate which ciphertext source the verifier uses; Hole A's shared-opening provenance remains a separate premise.

## Failure controls that remain live

[DERIVED] The module includes each of the following as a theorem; the executable independently checks their arithmetic.

| Scoped falsifier | Concrete witness | Failed premise |
|---|---|---|
| Residue-only multiplication | Q31,t4: products 1 and 32 share residue1, scale to0 and4 | Full integer product was discarded |
| Wrong integer lift | For true product32, lift1 has its own valid `(y=0,r=19)` certificate | Lift must equal the convolution |
| Certificate checked modQ | z1,y17,r19 passes mod31 | ModQ deletes y |
| Missing remainder range | z1,y1,r−12 satisfies the integer equation | Range forces the quotient |
| Smaller proof field wraps | Q31,p7,z1,y7,r19; y,r both in `[0,Q)` | Integer residual not bounded below p |
| Wrong rounding rule | Q31,t4,z4: floor=0, nearest=1 | Floor and nearest are distinct specifications |
| Wrong tie convention | Q4,t1,z−2: nearest ties-up=0, ties-away=−1 | Negative ties matter |
| Separately scaled tensor cross terms | Q31,t4: scaling4+4 gives1; scaling each4 then adding gives2 | Sum must precede scaling |

[DERIVED] `no_residue_factor` goes beyond the two evaluations: **no function of `z mod31` can equal the correct scaled residue for all integer z**. `nearest_shift` proves the general Q-shift law. These are refutations of the residue-only relation, not of BFV or FHE.

[DERIVED] `residual_lift` names the exact finite-field seam: if `e mod p = 0` and `|e| < p`, then e=0. A prover field equation is not the integer certificate until such a residual bound or a sound digit/carry decomposition has been proved. Merely bounding y and r below Q does not help when Q exceeds the proof field.

## The SEAL distinction sharpened

[SOURCE: implementation] Pinned Microsoft SEAL **v4.1.2**, `native/src/seal/evaluator.cpp:432–442`, describes BFV multiplication as basis extension, Montgomery correction, NTT product, multiplication by t, fast divide-and-floor, and Shenoy–Kumaresan conversion. Actual calls are at `:466–469` and `:548–565`. Sources were fetched in full; the relevant functions were inspected. [Primary source](https://github.com/microsoft/SEAL/blob/v4.1.2/native/src/seal/evaluator.cpp#L432).

[SOURCE: implementation] `native/src/seal/util/rns.cpp:404–462`, `BaseConverter::fast_convert[_array]`, computes a CRT sum without subtracting its multiple of Q. `RNSTool::fast_floor`, `:1041–1083`, subtracts that conversion from the Bsk input and multiplies by Q inverse. `sm_mrq`, `:979–1038`, and `fastbconv_sk`, `:903–976`, separately perform centered corrections. [Primary source](https://github.com/microsoft/SEAL/blob/v4.1.2/native/src/seal/util/rns.cpp#L1041).

[DERIVED] Let x be the full pre-division integer, r=x modQ, and let fast conversion produce `r+alpha*Q`. Its result is **`floor(x/Q)-alpha`**, represented in Bsk. `fast_floor_correction` proves the conditional integer identity. Thus merely switching the certificate bias from Q/2 to zero is insufficient to claim SEAL fidelity; the selected input lifts and conversion correction must also be bound. This derivation assumes consistent extended residues and does not prove the conversion's alpha range or actual implementation memory behavior.

[EXECUTED] The toy bases `(3,5)`, `(5,7)`, `(3,5,7)` were checked for every x from −3Q to3Q: **933 cases**, of which **492 differ from ordinary floor**. The literal modular fast-floor formula matched `floor(x/Q)-alpha` in all cases. For base `(3,5)`, x1 has redundant CRT lift16 and fast floor−1 while ordinary floor is0. These are algebraic base-conversion toys, **not valid SEAL parameter sets, SEAL C++ runs, or decryption failures**.

[SOURCE: implementation] Breadstuffs' live `fhegg-fhe/src/bfv_mul.rs:11–18` delegates to fhe.rs 0.1.1's `Multiplicator`; SEAL is the comparison semantics named in VERDICTS, not the runtime library actually called by that wrapper. A future implementation refinement must pin whichever engine it actually claims.

## The actual fhe.rs coefficient semantics

[SOURCE: implementation] `/Users/ember/dev/breadstuffs/Cargo.toml:273–281` patches fhe0.1.1 to `vendor/fhe-dregg`. Its live wrapper `fhegg-fhe/src/bfv_mul.rs:137–141` constructs `Multiplicator::default`. The pinned vendored `src/bfv/ops/mul.rs:102–132` extends Q by `ceil((sum(moduli_bits)+60)/62)` 62-bit primes, uses identity scaling on each operand, and t/Q scaling after multiplication; `:177–194` extends four polynomials, forms three tensor components, and scales them before optional relinearization. The isolated probe calls the same engine through `Multiplicator::new` with identical public basis/factors and relinearization disabled. The vendored multiplication file is byte-identical to cached upstream fhe0.1.1; this comparison and source hashes are recorded in `engine-run.json`.

[SOURCE: implementation] The arithmetic dependency is cached `fhe-math-0.1.1`, rooted at `/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/fhe-math-0.1.1`. `src/rns/mod.rs:47–101` constructs Garner coefficients. `src/rns/scaler.rs:68–220` precomputes projections and fixed-point corrections; `:247–349` performs the word arithmetic and output reduction. `src/rq/scaler.rs:31–40,64–116` copies common limbs only for identity scaling, otherwise transforms to coefficient form, invokes the RNS scaler, and transforms the added/output limbs back. These functions were read, not merely their declarations.

[DERIVED] Write M for the scaler's input modulus product and `g_i=(M/q_i)*inverse(M/q_i mod q_i)`. Let n/d be its scale factor. The source precomputes:

```
gamma = nearest(n*M/d)
omega_i = nearest(n*g_i/d)
thetaG_i = nearest(2^s*g_i/M)
thetaF_i = ceil(2^127*(n*g_i/d - omega_i))
thetaGamma = floor(2^127*(n*M/d - gamma))
```

[DERIVED] The source's word arithmetic chooses `v=nearest(sum(r_i*thetaG_i)/2^s)` and uses the selected lift `z=sum(r_i*g_i)-v*M`. For BFV downscale, M=P includes Q as a factor, so gamma is integral and thetaGamma=0. Put `K=sum(r_i*omega_i)-v*gamma`, `C=sum(r_i*(t*g_i-Q*omega_i))`, and `T=sum(r_i*thetaF_i)`. Exact algebra gives **`t*z=Q*K+C`**. The actual scalar output before final target-modulus projection is **`Y=K+nearest(T/2^127)`**, whereas exact nearest of t*z/Q is `K+nearest(C/Q)`. This is the exact correction seam; the first patch's quotient/remainder relation does not silently prove it.

[DERIVED] At the actual six-prime instance s=126. `FheRnsScaleDecomposition.garnerScaleDecomposition` proves the generic discrepancy identity; `output_exact_iff` characterizes the missing exact-correction premise in both directions. `wordCorrection_correct`, `wordV126_correct` and `wordV127_correct` prove integer semantics of the wrapping/complement/shift/truncation branches under explicit accumulator bounds. `deployed_correction_range` and `deployed_garner_range` discharge those bounds for **every canonical six-limb residue vector**; `deployed_constructor_constants` checks the numeric Garner CRT selectors, projections and basis product. `deployed_output_exact` forces the deterministic output. `deployed_source_arithmetic_envelope` proves exact nearest≤Y≤exact nearest+1, relative to that selected lift. `deployed_witness_inhabited` checks actual canonical residues and Y172481 versus exact172480. Exact, sharp+1, missing-direction, missing-magnitude and overflow falsifiers remain in the same module.

[OPEN] These theorems prove a stated source **arithmetic** model. They do not identify Rust memory with Lean vectors, prove Shoup reduction/NTT code or a compiler correct, prove a receipt binds the source residues, or emit a digit/carry checker. The all-input scalar theorem is not an all-input theorem for the complete Rust multiply pipeline. The first27-theorem patch remains byte-identical; the second patch imports it. Both and their combined Compiler umbrella validate with their own exact axiom pins. See `formal/bfv_lift_refinement/engine_refinement/VALIDATION.md`.

[EXECUTED] The retained live probe covers four fresh seeded encrypted pairs at N16/t17/Q1098641480897, one fresh encrypted pair at N4096/t1032193/Q649033470896967801447398927572993, and six structurally accepted constructed boundary pairs at the latter parameters. The extension basis adds4611686018427322369,4611686018427289601,4611686018427215873; its product P is295 bits. All **114,944** extended coefficients match the literal source model; all **86,208** full integer convolutions match the actual unscaled extended product residues; all **86,208** three-component output coefficients match the literal downscaler. The independent integer convolution uses balanced Kronecker substitution with direct-schoolbook crosschecks for N≤64. Every observed full product stays inside P/2 and the downscaler selects that same integer product. The result is coefficient-level evidence, not a decrypted-message-only check.

[EXECUTED] All12,480 coefficients from the five fresh encrypted pairs agree with centered nearest in these runs; all12,480 differ from the first patch's unsigned-input reference. The six constructed pairs use constant a0=x, a1=0, b0=1, b1=0 through `Ciphertext::new`; these are **not claimed fresh encryption samples**. One input near Q/2 is lifted by an extra−Q. Three rounding-boundary pairs have the following c0/coefficient0 values:

| Source-selected integer product z | Exact nearest(t*z/Q) | Actual source integer Y |
|---|---:|---:|
| −106762705753993305023047615719233 | −169791 | −169790 |
| −323671011811183103592788140460737 | −514752 | −514751 |
| 108454153028594899284870262370752 | 172480 | 172481 |

[EXECUTED] Each parameter family also has65 scalar extension and90 scalar downscale boundary checks. The small family has no strict-reference disagreements; the N4096 family has33 extension and35 exact-nearest downscale disagreements. There are **zero source-model mismatches**. For one direct RNS example, x4715931063015597384263884716 scales to8 while exact nearest is7. Detailed full fixtures are retained compressed; commands, toolchain, source/fixture SHA-256 hashes and output are in `engine-run.json`, `engine-results.json`, and `ENGINE_README.md` under the experiment directory. Failed exploratory builds and the earlier successful fixture are also retained.

[REFUTED: strict coefficient reference for these structurally accepted inputs] Replacing the engine by “strictly centered input lift, then exact nearest scaling” is not universally coefficient-identical to this pinned implementation. The fixed correction's tiny directed approximation can cross an exact rounding boundary. This does not establish a fresh-ciphertext failure probability, decryption error, or insecurity, and does not refute the cited paper.

[SOURCE: paper] The local corpus PDF `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2021/204.pdf`, Kim–Polyakov–Zucca, *Revisiting Homomorphic Encryption Schemes for Finite Fields*, revision October31,2022, was inspected at Remark3.2 (printedp16/PDFp19) and §3.3 (printedpp18–19/PDFpp21–22). The source calls its scaler “inspired” by Remark3.2. The paper discusses approximate fixed-point quantities and a digit decomposition for its decryption setting; that is not a proof of this Rust implementation's exact coefficient behavior. No PDF was downloaded and no reduction claim is made from this inspection.

## Source arithmetic representation bill

[DERIVED + EXECUTED] `engine_costs.py` computes the exact independent canonical-limb range bounds and source-loop arities, recorded in `engine-costs.json`. For one downscale coefficient, the implementation uses six Garner constant products, six fixed-correction loop products (three nonzero), and18 projected modular constant products. For the full3N tensor at N4096 these are73,728;73,728 (36,864 nonzero); and221,184 respectively. Operand extension adds49,152 Garner and147,456 projected modular constant products across4N coefficients. These are source arithmetic operation counts, not emitted AIR constraint counts or runtime estimates.

| Possible witnessed intermediate | Offset width from canonical limb bounds | Radix64 digits | Naive Boolean checks over3N |
|---|---:|---:|---:|
| Nonnegative Garner fixed accumulator | 189 bits | 32 | 2,322,432 |
| Signed fixed-correction accumulator | 164 bits | 28 | 2,015,232 |
| Lift-selection index v | 63 bits | 11 | 774,144 |
| Signed rounded correction w | 37 bits | 7 | 454,656 |
| Integer projection sum S | 269 bits | 45 | 3,305,472 |

[DERIVED] These are independent range maxima, not necessarily attained simultaneously. Witness selection, constant folding and modular instead of full-integer projection can change the bill. Do not add every intermediate to the first reference certificate as a mandatory cost. Reconstruction/carries, exact endpoint comparisons, committed-residue binding, NTT/convolution checks and proof overhead are excluded. The fixed-correction error here is strictly below274877456387/2^127 in normalized rounding units; a nonzero error this small still explains the boundary witnesses. The separate compiler lane owns emission and its actual cost.

## Executed finite audit and representation bill

[EXECUTED] `python3 research/learn_infer_only/experiments/bfv_lift_refinement/audit.py` produced `results.json`: **119,301** scalar cases (Q2…39, t1…Q−1, signed z); **15,732** polynomial pairs (15,332 exhaustive N2/Q2…9 plus400 seeded cases at N1,3,4,8,16 including the 109-bit modulus); **15,332** full size2 tensor cases (N1/Q2…9); **61,328** single-field certificate mutations refused. Two differently indexed convolution implementations agreed. The seed is 20260906; Python version, platform, command, source hash and elapsed time are recorded. No wall-time result is used as a performance claim.

[DERIVED] The representation bill in `results.json.costs` uses N4096, t2^20, and the three moduli recorded in `notes/cross-limb-binding.md:57–59`, with exact product `Q=649033470896967801447398927572993` (109bits). For the unrelinearized size2×size2 tensor, the three output components have at most N,2N,N product terms per coefficient. With unsigned input lifts, `Zmax=m*N*(Q−1)^2` for multiplicity m1,2,1.

| Component | Lifted coefficient offset bits | Quotient offset bits | Remainder bits | Sum over N coefficients |
|---|---:|---:|---:|---:|
| c0 | 231 | 142 | 109 | 1,974,272 |
| c1 | 232 | 143 | 109 | 1,982,464 |
| c2 | 231 | 142 | 109 | 1,974,272 |

[DERIVED] Naive Booleanity for these three witness families is **5,931,008** bit constraints, before reconstruction/carries, comparisons to the actual range endpoints, operand-source binding, convolution verification, commitments or the proof protocol. Input coefficient Booleanity is another **1,785,856** for two size2 ciphertexts if not already established. Output-residue Booleanity is **1,339,392**, matching VERDICTS' narrower example. These counts are an explicit naive encoding baseline, **not a lower bound, a measured circuit, or an assertion that all ranges must be proved again each step**.

[DERIVED] A 109-bit coefficient takes7 radix2^16 digits, but **a single full 16-bit product exceeds BabyBear**: 65535²=4,294,836,225 >2,013,265,921. At radix2^15 it takes8 digits and a single product fits; an accumulated dot product still needs a proved carry/range schedule. Byte digits take14 per coefficient; a256-term tile has maximum16,646,400 <2^24 and <BabyBear, before any extra carries. The direct four-convolution schoolbook baseline uses67,108,864 big-integer scalar products; digit expansion yields3,288,334,336 radix2^16 products or13,153,337,344 byte products. These are deliberately unoptimized operation counts; NTT/sumcheck/other multiplication arguments may change the bill.

## Decision and next decisive tasks

[DERIVED] **Keep the integer-certificate route.** The logical refinement is inhabited, exact and falsifiable. It makes clear what a proof-bound release relation must force rather than merely naming a residue multiplication.

[OPEN] **Do not label this a closure of deployed Hole B.** There is no compiler/emitter integration, no implementation-level SEAL/fhe.rs theorem, and no cryptographic soundness bound or benchmark here. The patch is rooted into the proposed Compiler umbrella for maintainer review; the root swarm performs independent integration/adversarial review.

[DERIVED] The engine selection, literal scaler oracle and full unrelinearized coefficient comparison have now been executed. **Bind the deterministic fixed-correction formula** if exact equivalence to this engine is the target; retain the first certificate for its explicitly stated mathematical reference.

[OPEN] Next prove the Rust/vector/modular/NTT interpretation seam and emit the actual selected-lift and deterministic correction relation with no-wrap/carry bounds. The independent compiler lane owns that emission. Relinearization/noise, ciphertext provenance, private release and the absence of a master-read capability remain separate obligations. Root integration and independent adversarial review are still required before folding any verdict.
