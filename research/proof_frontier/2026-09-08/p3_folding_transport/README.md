# Pinned p3 folding and query transport

[DERIVED result] The pinned p3 **binary, single-input-height arithmetic** matches the frozen natural-power tower after bit reversal and a PCS coset pullback. This package proves the generic bit-reversal query identity in Lean and connects it to the existing `powerTwoRoundIndex`. Finite Ext4 calculations check the source's row/matrix folds, higher-arity challenge powers, coset quotient scaling, final evaluation point, and multi-height input injection. These are arithmetic and index results, not end-to-end p3 soundness.

[SOURCE / OPEN smallest mismatch] The named production and IR2 configurations permit arity eight. That arithmetic uses the correlated binary challenges `β, β², β⁴`; when another input height is reached it adds `β⁸` times that input word. The frozen 19-round binary soundness consumer assumes a different challenge/transition experiment. Reordering indices cannot establish equivalence of those experiments. The separate `arity_eight_soundness/` lane owns this probability obligation; no arity-eight security claim is made here.

## Exact source scope

[SOURCE] `SOURCES.json` pins 22 read-only files by absolute path and SHA-256. The p3 Cargo checkout is `/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7`, verified at commit `82cfad73cd734d37a0d51953094f970c531817ec`. The active FRI implementation for the inspected breadstuffs workspace is its local patch at `/Users/ember/dev/breadstuffs/vendor/plonky3-fri-82cfad73/src/`; `breadstuffs/Cargo.toml:246–250` selects it. This note does not substitute the unpatched git FRI crate or a newer upstream release.

[SOURCE] The audited constructor is `/Users/ember/dev/breadstuffs/circuit/src/plonky3_prover.rs:207–236`, `create_config_with_fri_full`. It selects `TwoAdicFriPcs::new`, whose vendored implementation at `two_adic_pcs.rs:114–121` chooses `CpuTwoAdicFriFold`; that backend delegates to the exact matrix routine at `:103–110`. The replaceable-backend interface at `:90–96` states a value-equality obligation; no alternative backend is certified here.

| Named source configuration | Extension | Log blowup | Maximum log arity | Final coefficient count |
|---|---|---:|---:|---:|
| `plonky3_prover.rs:108–123` PROD constants | BabyBear degree 4 | 3 | 3 | 1 |
| `descriptor_ir2.rs:7269–7294` IR2 constants | same degree 4 | 6 | 3 | 1 |
| Frozen proposed tower/sampling theorem | actual BabyBear Ext4 | rate one half | 19 separate binary rounds | degree below 1 on a two-point final domain |

[SOURCE / DERIVED] The first two rows are named inspected configurations, not a census of every runtime constructor. The proposed tower does not match these parameter rows merely because the field agrees. In particular, final domains have size `2^(log_blowup + log_final_poly_len)` in p3 (`prover.rs:197–199`, `verifier.rs:258–259`). No existing parameter, query budget or security ledger was changed by this audit.

[SOURCE] `p3/baby-bear/src/baby_bear.rs:15–29` gives modulus `2013265921` and generator `c=31`; `:42–50` gives the two-adic root table, including maximal root `440564289` and 20-bit root `195061667`. Its degree-four extension uses `W=11` at `:65–68`. `p3/field/src/extension/mod.rs:24–34` specifies `F[X]/(X^D-W)`, and `binomial_extension.rs:28–46` stores coefficients in an array. The check uses this exact abstract field presentation. It does not prove the Montgomery representation, packed multiplication, compiler or Rust implementation realizes that presentation.

## Row order, fibres and query indices

[SOURCE / DERIVED] Let `L` be the current log word length and let `R_L(q)` reverse exactly the low `L` bits of a valid index `0 ≤ q < 2^L`. p3's machine helper is `p3/util/src/lib.rs:203–211`, `reverse_bits_len`; its matrix row view applies that helper at `p3/matrix/src/bitrev.rs:62–74`, and applying the view twice cancels at `:84–98`. The inspected PCS commit paths materialize bit-reversed LDE rows (`two_adic_pcs.rs:604–609`); the stored FRI word therefore has

```
v[q] = w[R_L(q)],             w[i] = f(ω_L^i),
ω_L = 440564289^(2^(27-L)) mod p.
```

[SOURCE] The production DFT is `Radix2DitParallel` (`plonky3_prover.rs:63`), whose evaluation type and DFT/coset methods appear at `p3/dft/src/radix_2_dit_parallel.rs:146–175`. The already-patched PCS evaluation-on-domain path explicitly handles its logical versus stored row order at `two_adic_pcs.rs:638–669`. This audit consumes that fixed path and does not reopen the historical extra-bit-reversal defect.

[DERIVED] For arity `A=2^a`, set `q=A*r+s`, with `r<2^(L-a)` and `s<A`. The exact index decomposition is

```
R_L(A*r+s) = R_(L-a)(r) + 2^(L-a)*R_a(s).
```

[DERIVED] Consequently a p3 matrix row of width `A` contains the fibre points

```
x_s = ω_L^R_(L-a)(r) * ω_a^R_a(s).
```

[SOURCE / DERIVED] These are exactly `fold_row`'s subgroup start and bit-reversed fibre in `two_adic_pcs.rs:243–249`. With `a=1`, adjacent positions `2r,2r+1` become the natural indices `k,k+2^(L-1)`, where `k=R_(L-1)(r)`. Thus the first entry is at `x=ω_L^k` and the second is at `-x`, with no swapped-sign convention. The frozen tower exposes those same entries and denominator at `formal/babybear_folding_tower/src/Selvage/PowerTwoRootFolding.lean:150`, `fold_pair`.

[SOURCE / DERIVED] The prover query uses `index_in_group = current_index % A` and `group_index = current_index >> a`, opens that row, removes self while retaining sibling order, and continues at the group index (`prover.rs:302–333`). The verifier inserts the current evaluation at the same slot, authenticates the full row at the shifted index, then folds it (`verifier.rs:422–464`). The indices transport by

```
R_(L-a)(q >> a) = R_L(q) mod 2^(L-a).
```

[DERIVED] At the proposed initial size `2^20`, the formal first-pair seed is `R_19(q >> 1)`. At binary round `j` the existing natural index is

```
R_19(q >> 1) mod 2^(19-j) = R_(19-j)(q >> (j+1)).
```

[EXECUTED Lean] `formal/src/Theory/BitReverseFriTransport.lean` proves this relation generically using the existing `BitVec.reverse` and `extractLsb'` operations. `query_transport` gives the general bounded-index formula; `query_transport_composition` composes drops; `binary_coherent_index` gives the binary seed equation. `reverseEquiv` is obtained from the existing reversal involution. `formal/src/Selvage/P3FriQueryTransport.lean`, `existing_coherent_transport`, applies that equation directly to the existing `PowerTwoFriLevels` and `powerTwoRoundIndex` definitions from `/Users/ember/dev/minidregg/Selvage/HalfThresholdFriCoherent.lean:28–50`. No parallel tower, RS code or probability model is introduced.

[DERIVED / OPEN] Under an ideal uniform full-word index, each initial pair seed has exactly two preimages: the dropped low bit chooses either source member, and reversal is a permutation. The finite checker verifies the equal fibres on all small domains. The package does not prove a uniformity theorem for the actual challenger, nor a full acceptance-event equivalence: the source's initial PCS opening and authentication obligations remain present. The new Lean result is about fixed-width index operations; a Rust-machine semantics refinement is still outside it.

[SOURCE] Both active `TwoAdicFriFolding` and its backend wrapper return zero from `extra_query_index_bits` (`two_adic_pcs.rs:190–191`, `:226–227`). The generic verifier supports extra bits and removes them at `verifier.rs:286–287`. The audited active binary transport uses zero extra bits; it does not certify every strategy implementing that interface.

## Folding arithmetic and the higher-arity boundary

[SOURCE / DERIVED] The optimized binary matrix fold (`two_adic_pcs.rs:256–282`) is

```
(lo+hi)/2 + β*(lo-hi)/(2x),     x = ω_L^R_(L-1)(row).
```

[SOURCE / DERIVED] It bit-reverses the base-field inverse-root twiddles before zipping rows. `/Users/ember/dev/minidregg/prover/src/mle_kernels.rs:407–431` uses the corresponding natural-order half pairs, with the same inverse-root twiddle at `:565–572`. That scalar helper has Ext6 inputs, so matching its formula/index convention is not an Ext6/Ext4 carrier or execution equivalence. The new tower uses the actual Ext4 carrier and certified source roots; its `BabyBearFoldingTower.lean:56`, `domain_source`, fixes the root at each level.

[DERIVED] Write a polynomial as `f(X)=Σ_(r<A) X^r f_r(X^A)`. Interpolating one fibre at `β` returns the folded polynomial

```
F_β(Y) = Σ_(r<A) β^r f_r(Y).
```

[SOURCE / DERIVED] The verifier computes this by Lagrange interpolation (`two_adic_pcs.rs:230–252`). The matrix prover computes it by `a` binary passes with challenges `β, β², β⁴, …, β^(2^(a-1))` (`:284–334`). Its twiddle recurrence `t_next[j]=2*t_current[2j]^2` at `:312` gives `1/(2*x²)` from the previous `1/(2*x)`. The finite checker independently compares the matrix recurrence, natural half-pair folding, fibre Lagrange interpolation and coefficient grouping. These identities hold for the checked full-degree evaluation vectors; they do not depend on an assumed low-degree answer.

[OPEN probability boundary] For `A>2`, these binary subchallenges are correlated and the intermediate binary words are not separately challenged/committed in the same way as the frozen binary experiment. The vector `(β,β²,β⁴)` cannot be replaced by three independent uniform challenges. The pure arithmetic identity supplies no such replacement. The separate arity-eight lane needs a direct curve/proximity theorem or an appropriate dependent-challenge theorem.

## Multi-height inputs and the coset pullback

[SOURCE / DERIVED] The PCS constructs one alpha-combined quotient evaluation vector per height and sends these vectors in decreasing height order (`two_adic_pcs.rs:865–935`). `compute_log_arity_for_round` at `config.rs:152–178` chooses the minimum of the configured maximum, distance to the next input height and distance to the terminal height. The prover therefore visits each next input height. The verifier checks the schedule, final height and unconsumed inputs (`verifier.rs:158–204`, `:483–496`), rather than treating skipped input vectors as irrelevant.

[SOURCE / DERIVED] When a fold reaches a new input height, the actual update is

```
next_word = fold_A(current_word, β) + β^A * next_input_word.
```

[SOURCE] This is `prover.rs:238–244` and exactly `verifier.rs:477–479`. The new input's point is queried with the corresponding right-shifted index (`prover.rs:379–384`, `verifier.rs:606–615`). In coefficient form the update is `Σ_(r<A) β^r f_r(Y) + β^A g(Y)`, including a ninth geometric coefficient at arity eight. The source comment about maintaining independence describes its batching rationale; **`β^A` is not statistically independent of `β`**. The frozen single-word consumer does not already contain this injection transition. Omitting it would change the checked recurrence.

[SOURCE / DERIVED] The outer PCS uses the coset `cH` with `c=31`, whereas the inner fold uses unshifted subgroup roots (`two_adic_pcs.rs:626–677`, `:759–767` versus `:243`, `:270`). There is a direct arithmetic interpretation: for an outer quotient polynomial `r(X)`, let `Q(Y)=r(cY)`. The input array at row `q` is then `Q(ω_L^R_L(q))`, so unshifted inner folding applies to `Q`. Scaling the variable by a nonzero constant preserves degree. This resolves the arithmetic convention, not the initial PCS-to-FRI farness reduction for malicious claims.

[DERIVED] More explicitly, for a correctly claimed opening `f(z)` and nonzero denominator, let `F(Y)=f(cY)` and `z'=z/c`. Then

```
(f(z)-f(cY))/(z-cY) = (1/c)*(F(z')-F(Y))/(z'-Y).
```

[DERIVED] The factor `1/c` must be retained if normalized opening points are used. Equivalently, one can pull back the entire quotient polynomial `r` directly and keep the original denominator convention. For an arity-`A` fibre, the pullback formula is `Σ_(r<A)(cβ)^r f_r(c^A Y)`. The check uses a non-base-field opening point, full Ext4 coefficients and 64 coset rows; both omitting the pullback and omitting the quotient scale are refused.

## Terminal polynomial point

[SOURCE / DERIVED] The prover truncates the bit-reversed final word to the claimed coefficient count, reverses that prefix and applies an IDFT (`prover.rs:248–254`). The verifier checks coefficient count (`verifier.rs:229–234`) and evaluates by Horner at `:311–320`. It deliberately retains the **global** root and reversal width when its current index is already reduced. This is consistent: if the remaining log height is `h`, then

```
ω_L^R_L(q_final) = ω_h^R_h(q_final),     q_final < 2^h.
```

[DERIVED] The leading zero bits of `q_final` become a factor `2^(L-h)` in its reversed exponent. Using the smaller-width reversed exponent with the global root would be wrong. The checker covers all such points through initial log size 12 and refuses that incorrect variant. Interpolation from a shortened final word still relies on the intended degree bound; this arithmetic observation is not a proof of that bound or a replacement for final acceptance analysis.

## Executed controls and formal package

[EXECUTED] Run `python3 research/proof_frontier/2026-09-08/p3_folding_transport/check_transport.py`. The exact report is `RESULTS.json`; all source hashes are checked before arithmetic. It performs no Rust/Lean prover execution, hash computation for commitments, encryption, proof-of-work, network query or private-runtime inspection. File SHA-256 checks are provenance checks only. Its reference field operations are not a substitute implementation being proposed for either companion tree.

| Check | Scope executed |
|---|---:|
| Reversal involution | all 8,191 indices across log sizes 0–12 |
| Drop/group/fibre index identities | 98,305 cases across those domains |
| Equal two-element fibres of the pair seed | all 12 nontrivial small domains |
| Actual 20-bit index projections | 86,142 cases on 4,102 fixed boundary/spread queries |
| Existing 19-round coherent query path | 77,938 cases on those queries |
| Row/matrix/coefficient folding agreement | 54 Ext4 cases, 663 output rows, arities 2/4/8, challenges 0/1/non-base |
| Coset quotient pullback | 64 Ext4 rows |
| Mixed heights 128→16→4→2 | all 128 queries, 384 round checks, arities 8/4/2 with injection |
| Global versus final-root terminal points | 16,368 cases |

[EXECUTED] Deliberate mutations fail: omitted input bit reversal; omitted twiddle bit reversal; omitted within-fibre reversal; repeated `β` in higher-arity binary passes; omitted next-height input; `β` instead of `β^A`; using raw modulo instead of shifted/reversed query indices; omitted coset pullback/quotient scale; and the wrong final-root exponent convention. The field relation `U^4=11`, the certified root constants and nonzero-extension inverse controls are also checked. These finite results cover concrete formulas, not universal Rust execution or cryptographic soundness.

[EXECUTED Lean scope] The separate patch in `formal/` contains two small modules, with 15 theorem declarations and exact guarded axiom pins, including all helpers, actual dimension premise inhabitation, a positive index example and wrong-index refusals. `Theory/` imports only Mathlib. The modules are checked individually in an isolated checkout against cached dependencies; root owns full project integration. Final source/patch hashes, exact declaration census, patch replay and import-boundary results are in `formal/verification.json`. Failed proof iterations and the initial missing-cache import attempt are retained in `formal/logs/`; none is part of the final checked sources.

[OPEN remaining correspondence] The outstanding end-to-end obligations include variable-arity/dependent-challenge proximity, next-height injection/batching, initial PCS/IOP farness, mixed-matrix row authentication to symbol-opening semantics, final coefficients to transparent terminal-word semantics, exact field/machine/backend implementations, and actual challenger/Fiat–Shamir plus both proof-of-work phases. No deployed security upgrade or certificate change follows from this package. The useful completed seam is the exact index transport and a source-calibrated arithmetic account of what remains.
