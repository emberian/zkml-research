# Independent review of p3 folding transport

[DERIVED verdict, 2026-09-08] **Accept for its stated index/arithmetic scope.** The 15-pin patch connects the existing fixed-width reversal operations to the existing `powerTwoRoundIndex`, and the source-calibrated finite arithmetic controls are internally consistent. No blocking finding remains. This does not establish p3 acceptance-event equivalence, proximity soundness for correlated subchallenges or injected inputs, or concrete implementation/challenger security.

[SOURCE freeze] Reviewed [package README](../p3_folding_transport/README.md), [formal source/verification](../p3_folding_transport/formal/verification.json), and both manifests. Author manifest SHA256: `17b4f5a087248c521eb25e7ca8d44ee859f67f2a22dac7a54dfaca43602327f5`. Patch SHA256: `a853d61feffbe71802b46ddaf086b93a378246116abf429feef5fed870d48bca`. [INPUTS.json](INPUTS.json) records checked artifact and source hashes; [RESULTS.json](RESULTS.json) records independent review controls. The author packet was not modified.

## Formal subject, pins and useful boundaries

[SOURCE / DERIVED] [BitReverseFriTransport.lean](../p3_folding_transport/formal/src/Theory/BitReverseFriTransport.lean:13) states the projection and bounded-index contracts before proving them. `reverseIndex` is `(BitVec.ofNat bits index).reverse.toNat`, not a second reversal implementation. `reverse_high_eq_low_reverse` proves equality of bit vectors by their bits; `projection_transport` projects that equality to naturals. `bounded_extract` handles the valid-index conversion, and `query_transport` preserves both `dropped≤bits` and `index<2^bits`.

The proved equation is

`R_(bits−dropped)(index / 2^dropped) = R_bits(index) mod 2^(bits−dropped)`.

[DERIVED] Composition follows by nested power-of-two moduli; `binary_coherent_index` specializes the first drop to one bit. Natural subtraction is used within explicit bounds, including the width-zero endpoint. This is a valid identity at that endpoint, not a hidden positive-width assumption. Out-of-range machine indices are not certified by the bounded theorem.

[SOURCE / DERIVED] [P3FriQueryTransport.lean](../p3_folding_transport/formal/src/Selvage/P3FriQueryTransport.lean:16) defines `pairSeed ell q = R_(ell−1)(q/2)` in the existing `PowerTwoFriLevels ell 1`. Its statement quantifies over `m≤ell`, `j:Fin m`, and `q:Fin(2^ell)`. The proof applies `binary_coherent_index` directly; definitional reduction exposes the modulus in the existing [HalfThresholdFriCoherent.lean](/Users/ember/dev/minidregg/Selvage/HalfThresholdFriCoherent.lean:50). No alternate tower, query function, code, distance or probability definition replaces the existing subject.

[EXECUTED] Independently checked all 81 nested-manifest entries, representing 44 unique artifacts, plus all 22 declared source hashes. Both source hashes match their exact patch additions, retained source snapshots and final quiet successful Lean logs:

| Source | SHA256 | Retained check |
| --- | --- | --- |
| `Theory/BitReverseFriTransport.lean` | `f546b123f49632cbe3284baa23c3f12943529f7c2b8231e87f7ac71b2c2399cf` | `formal/logs/lean_009.json` |
| `Selvage/P3FriQueryTransport.lean` | `9cfbb720613e77e3652c7de8ddf7ebac9e39322ad36e49bf7c43ff6b09f3c176` | `formal/logs/selvage_005.json` |

[EXECUTED / SOURCE] The 15 declarations match 15 exact guarded `#print axioms` messages, including all theorem helpers. The axiom lists are three `[propext]`, nine `[propext, Quot.sound]`, and three `[propext, Classical.choice, Quot.sound]`. The selected source contains no `sorry`, `axiom`, `admit`, `native_decide`, or `unsafe` declaration/use. The archive reports exit zero with empty stdout/stderr and unchanged before/after source hashes. This review checked the records and source; it did not rerun Lean or revalidate the cached dependency closure.

[EXECUTED] Replayed the patch in a temporary directory owned by this review, against exact baseline umbrella bytes from companion commit `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`. Only `Theory.lean`, `Selvage.lean`, and the two new modules are touched. The umbrella changes are exactly the two new imports, with no prior declaration or proof-body edit. The new module bytes match the selected sources. The import lists stay within the recorded boundaries: one Mathlib import in Theory; the new Theory module and existing Selvage coherent module in Selvage. The archived boundary check passed. The author environment explicitly records cache reuse and no full closure rebuild; root's clean project integration remains the appropriate later validation.

[DERIVED coverage] The generic theorems cover all valid dimensions, drops and rounds. Concrete Lean witnesses exercise `181` at width eight/drop three, actual `ell=20,m=19` premises, and the third binary round. Wrong raw-modulo indices are refused. The premise witness includes the last valid round bound, while independent finite controls exercise every actual round, including the last. Uniform pair-seed fibres and a Rust word-width refinement are not new Lean theorems in this patch; the README correctly distinguishes them.

## Correspondence with the actual pinned source

[SOURCE] The p3 checkout is pinned to `82cfad73cd734d37a0d51953094f970c531817ec`, but the active FRI crate is the local path selected in `breadstuffs/Cargo.toml:247–250`. The inspected constructor at `circuit/src/plonky3_prover.rs:207–236` uses `TwoAdicFriPcs::new`, selecting `CpuTwoAdicFriFold`; the backend delegates to the inspected matrix implementation at `two_adic_pcs.rs:103–110`. Replaceable backends only have a stated value-equivalence contract here.

| Seam | Source read and review result |
| --- | --- |
| Reversal and storage | p3 `util/src/lib.rs:203–211` reverses machine bits at the specified width; `matrix/src/bitrev.rs:62–98` applies/cancels the row permutation. The inspected PCS LDE path at `two_adic_pcs.rs:604–609` stores bit-reversed rows. On valid indices the stated decomposition `R_L(2^a*r+s)=R_(L−a)(r)+2^(L−a)*R_a(s)` has the correct orientation. |
| Binary pair/sign | `two_adic_pcs.rs:243–249` orders fibre points by reversal. Adjacent stored entries are the natural `x,-x` pair in that order. Matrix folding at `:256–282` uses `(lo+hi)/2 + β*(lo−hi)/(2x)`, matching the existing natural half-pair `PowerTwoRootFolding.fold_pair:150` and `BabyBearFoldingTower.domain_source:56`. The referenced scalar runtime helper uses Ext6; that is only a formula/index comparison, not a carrier equivalence. |
| Query and siblings | `prover.rs:302–333` selects member `index%A`, opens row `index>>a`, and removes self without reordering siblings. `verifier.rs:422–464` reinserts self in that slot, shifts to the same row, authenticates, then folds. Both active folding wrappers return zero extra query bits. Thus the new pair seed is calibrated to the active convention; the generic extra-bit interface is not automatically covered. |
| Higher arity | `two_adic_pcs.rs:284–334` squares the challenge after each binary pass and updates twiddles as `2*t[2j]^2`. This is the coefficient fold `Σ β^r f_r(Y)`, equal to the fibre interpolation in `fold_row`. It is arithmetic with correlated challenges. |
| Input heights | `config.rs:152–178` limits each fold by the next input and terminal heights. `prover.rs:238–244` and `verifier.rs:477–479` add `β^A*g`; initial input openings use the corresponding shifted index (`prover.rs:379–384`, `verifier.rs:606–615`). Schedule/final-height/unconsumed-input checks preserve this obligation. |
| Coset and terminal | The PCS quotient vectors use `31H`, while inner FRI uses subgroup roots. Pulling back the entire quotient by `X=31Y` gives the stated inner polynomial. Normalizing the opening point also requires the factor `1/31`. At the end, `verifier.rs:311–320` deliberately uses the original reversal width and root; leading zero bits provide the exponent rescaling to the final domain. |

[DERIVED] The coset equation has the correct sign and scale: both numerator and denominator reverse sign when comparing `(f(z)−f(x))/(z−x)` with synthetic division. Variable scaling by nonzero `31` preserves degree, but this does not imply farness of maliciously claimed PCS quotient data. Similarly, truncating/reversing/IDFT-ing the final prefix recovers the intended coefficients only with the relevant degree bound; the point identity does not prove that bound.

## Pure arithmetic controls and remaining probability gap

[EXECUTED] Read the author's [check_transport.py](../p3_folding_transport/check_transport.py) and replayed an exact copy in a temporary directory under this review. Every output field matches the retained result except elapsed time; [author_replay.json](author_replay.json) retains the result. No write reached the author packet. The control triangulates row interpolation, matrix recurrence, natural half-pair folding and coefficient grouping over `F_p[U]/(U^4−11)`, using full-degree Ext4 vectors. It also covers the coset quotient scale and every query through the three-injection `128→16→4→2` example. The declared mutation refusals are actual nonzero counterexamples, not asserted universal detection for all challenges or inputs.

[EXECUTED] Separately written arithmetic in [audit.py](audit.py) uses direct basis multiplication, monomial-sum evaluation, arithmetic bit reversal and fresh root-derived twiddles. It adds:

- 4,097 small index projections and 18,943 drop-composition cases, including widths zero, zero drops and full drops.
- 58 actual 20-bit boundary queries over all 19 rounds: 1,102 checks.
- 84 full-degree Ext4 row/coefficient equalities at arities 2/4/8 with zero, minus one and a non-base challenge; 127 independently recomputed twiddle recurrences.
- All 64 queries through a different `64→8→2` mixed-height example, including both injections and sibling reconstruction: 128 round checks.

[DERIVED] These controls have useful teeth: the author's non-base challenge cases detect omitted input/twiddle/fibre reversal and repeated `β`; separate controls detect omitted next-height inputs, `β` replacing `β^A`, wrong query projection, omitted coset pullback/scale and the wrong terminal exponent. Zero-challenge coverage checks a legitimate arithmetic boundary where some mutations would naturally be invisible. Finite agreement is not universal Rust, packed-field, Montgomery, compiler or backend semantics.

[OPEN probability boundary] At arity eight the source uses `(β,β²,β⁴)` and may add `β⁸*g`. These are functions of one challenge, not four independent samples. Intermediate binary substeps are not separately committed/challenged in the frozen 19-round experiment. The new transport theorem does not change those facts. `polynomial_curve_full_ud` is a separate active theorem and receives no completion or compatibility claim from this review. Any later composition must match its actual correlated-challenge and injection hypotheses, plus initial PCS/IOP farness, row-MMCS opening semantics, terminal-word acceptance, actual parameters and challenger/Fiat–Shamir/PoW.

[SOURCE / DERIVED] The named production and IR2 rows allow maximum arity eight with log blowups three and six; their final domains therefore differ from the proposed binary rate-one-half, two-point terminal tower. Matching Ext4 and indices does not match these parameter experiments. The packet keeps this limitation explicit and makes no certificate or deployed soundness upgrade.

[EXECUTED scope] Wrote only this sibling review directory. No Lean, Rust prover, crypto protocol, network search, private/stopped-runtime inspection, companion edit, shared-ledger edit or publication. Queries: zero web, zero Scry, zero Kagi. Instruments: local source reads, SHA256 provenance checks, owned patch replay and finite Python arithmetic. This is an audit of the named frozen packet and interfaces, with no literature or repository-wide absence claim.
