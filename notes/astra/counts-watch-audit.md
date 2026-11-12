# Counts and experiment watch audit — 2026-11-06 UTC

[READ] Scope: the executable count models and experimental evidence added by zkml-research `7c75bd585a50eee0c717faf04a1c5d71e4b56e1d`, `9443850d768fd2de83e8e351e0c69c7a2161577d`, `439da79ca95432ee5f428bb6b77c6d3b8347453d`, and degg-research `15db9784e2043bb170431203f3c63d88625933e2`. This is supplementary watch coverage, not an addition to the formal-statement inventory. Source hashes and observed repository heads are in `counts/source-snapshot.json`; degg-research advanced to `6b70d64c532fd5007850d236bd7c60ea7ea21a0d` during the audit and the root was notified. This note does not claim coverage of that later commit.

[EXECUTED] Commands, exit codes and original outputs are retained in `counts/runs.json` and adjacent `.stdout.txt`/`.stderr.txt` files. Runs used Python's standard library, exact integer/Fraction controls, and the read-only AIR census. No build, network request, paid search, or companion-tree modification was performed. The AIR script's temporary directory was redirected beneath this lane's own `notes/astra/counts/air-tmp/`; its cleanup removed only its own created scratch directory.

## Coverage and verdicts

| Artifact | Audited evidence | Verdict |
|---|---|---|
| `notes/construction-search/space.py` | Full source; enumeration, named points, calibration, sensitivity; independent corrected evaluation | [EXECUTED] 76,248 points reproduced. [REFUTED: audit arithmetic] Tensor eligibility uses incompatible amortization units (K1). Its PQ flag is identically true (K2). Counts and proxy ratios are not security guarantees or measured prover times. |
| `notes/dark-learning-scripts/tradeoff_space.py`, `.out.txt`, `notes/dark-learning-tradeoff-space.md` | Full source and note; default and d=1024/L=12 runs; counterexamples | [EXECUTED] Default output byte-identical, including 784/112 and 11/10 fronts; small case gives 14/12 fronts. [REFUTED: range gate] A passing row can wrap after one legitimate update (K3). Envelope operations are absent from computation/network columns (K4). Signed-range control conflates two recipes (K5). |
| `notes/dark-learning-scripts/backward_table_virtualization.py`, `.out.txt` | Full source; full run; rational rounding and stable-evaluation controls; certified rational interval witnesses | [EXECUTED] Original output byte-identical. [REFUTED: exact-real census interpretation] The program is binary64/libm → binary32 → bf16, with cancellation (K6). The useful impossibility of output-keyed derivatives survives via independent exact-rational enclosures. |
| degg-research `experiments/mma-field-mapping/{mma_limbs.py,README.md,RESULTS.txt}` | Full source/readme/output; reproduction; counterexample and constructive encoder | [EXECUTED] Original table byte-identical. [REFUTED: general representation formula] Complete residue coverage does not justify the signed limb-count formula for this gapped digit set (K7). Actual published prime counts survive a constructive repair, which also tightens the accumulator estimate. |
| degg-research `experiments/air-census/{air_census.sh,README.md,RESULTS-2026-11-05.txt}` | Full script/readme/output; rerun; inspected actual solvency descriptor constructor | [EXECUTED] All counts reproduced, with only two equal-count lines reordered. [READ] Useful search instrument with scope limitations (K8); not an assurance percentage or literal-constructor census. |
| degg-research `research/governance-literature-notes-2026-11-05.md` | Full local note; cross-checked the count-derived claims against these scripts | [READ] The note distinguishes primary reads, extraction, snippets and incomplete reads. It remains an attribution inventory; this audit did not re-fetch papers or independently certify the mutable vendor claims. TensorZKP's published-format claims are locally reported source claims, not hardware measurements from these runs. No novelty conclusion follows from the quick-search absence entries. |

## K1. Auditing makes ineligible arithmetic tensor-eligible

[READ] `space.py:337–354` first scales all prover multiplications by audit probability `p`, then divides **unscaled** eligible work by that already scaled total. At p=0.01 this saturates `tc_share` at 1, so lookup, quotient and other noneligible multiplications receive the tensor-core discount. Lower audit probability does not change an operation's hardware eligibility.

[DERIVED] Repair: multiply the eligible numerator by the same `p`, or compute the eligible fraction before amortizing either side. The patch takes the former route.

[EXECUTED] `counts/audit_controls.py`, retained output `counts/audit-controls.stdout.txt`:

| Quantity | Original | Corrected |
|---|---:|---:|
| U1 crypto proxy, seconds | 0.00003202079721514152 | 0.00003258867909915832 |
| U1 total proxy, seconds | 0.00006341519502246437 | 0.00006398307690648117 |
| SASH proxy / U1 proxy | 675.4596824051914 | 669.4646390973758 |

[EXECUTED] Correction raises the U1 proxy by 0.8955%; the per-request row is unchanged. This is a concrete model bug, not a refutation of the large structural gain hypothesized by U1. Both columns remain proxies calibrated from assumptions, not measured runtimes.

## K2. The PQ flag is not a gate

[READ] `space.py:362` sets `pq = field != "lattice-Rq" or True`, hence every row reports true. None of the Pareto filters consumes it, so replacing it does not alter these fronts; consumers nevertheless must not read that field as a verified property.

[DERIVED] A field choice cannot certify a complete proof system's post-quantum security, particularly with a classical random-oracle compiler or an uninstantiated lattice assumption. The patch changes the output to `None` (unknown) with an explicit comment. It does not invent a parameter security assessment.

## K3. The wrap gate checks accumulated state but forgets the operand bounds used by every later matvec

[READ] `tradeoff_space.py:66–78` fixes the matvec range at symmetric 4-bit magnitudes 7,7. Lines 162–184 charge dense requantization only once per `wrap_steps()` and let all non-append update types pass `wrap_ok` unconditionally. This does not maintain the fixed operand bound between refreshes.

[EXECUTED] Counterexample in `audit_controls.py`, at the model's default d=4096:

- Start with every weight 7 and next activation 7: the row sum is `4096·7·7 = 200704`, within the centered plaintext cap `(1032193−1)/2 = 516096`.
- An allowed integer factor update `W' = W − δxᵀ` with every δ=-7 and x=7 changes each weight to 56 after **one step**.
- The next all-7 activation has row sum `4096·56·7 = 1605632 > 516096`; it wraps despite being far before the ~10,532-step state-refresh interval.
- The model's RNS-202@8192, fully dark, backprop-full, p=0.01 row reports all four gates true.

[REFUTED: gate interpretation] “112 constructions pass all gates” is an accurate report of the script, but cannot mean 112 constructions have an established no-wrap schedule. The defect applies before any debate about ciphertext noise or security parameters.

[DERIVED] Repair choices: (a) specify and charge clipping/requantization that restores **every operand range before its next use**, and prove that invariant; or (b) propagate the actual per-step ranges through each matrix product, re-tile and count the required crossings dynamically. Low-rank factors, merged bases, optimizer state and backward intermediates each need their own bound. An envelope on update magnitude alone does not keep the updated model 4-bit. An append merge does not restore ranges merely by recommitting or refreshing ciphertext noise.

[OPEN] This repair requires a concrete learning schedule. The mechanical patch deliberately does **not** turn the existing gate into a theorem or silently insert unpriced clipping. Until such a schedule exists, FHE rows carry an unresolved range invariant and the reported frontiers remain conditional model output.

## K4. Mandatory envelope work is charged to proof size but omitted from host/network work

[READ] `tradeoff_space.py:166–168` declares `env_ctct = 2·ceil(env/N)` and pays its proof cost. Line 171 omits those multiplications from `host`; the bootstrapping expression has the same omission. In MPC, lines 188–191 charge `3·env` proof felts but omit the square triples and their traffic from both host and online counts.

[DERIVED] The patch charges the operations the model already says it performs. For MPC it adds one square multiplication and one triple-preprocessing charge per `env` entry, plus that triple's modeled online communication. It does not assert that squaring these entries is a complete certificate for a product-norm bound or for `Δ(AB)`; that remains a circuit-design obligation.

[EXECUTED] At public lowrank r=16, d=4096, L=32: FHE RNS-202 needs 1,024 modeled envelope ct×ct operations, increasing modeled host work 0.9610%; MPC needs 4,194,304 square triples, increasing modeled online elements 18.1818%. In the corrected default frontier output the MPC opacity ratios change from host 39.9× / online 65.0× to **37.2× / 57.9×**. Proof ratios and the 11/10 frontier cardinalities happen to remain unchanged. These are outputs of the corrected narrow cost model, still conditional on K3 and the listed unpriced operations.

## K5. A synthetic “control” conceals two different signed ranges

[READ] `tradeoff_space.py:248` (the assertion immediately before the printed controls) inserts `+137` into `7·127` and only asserts a loose upper bound `≤504+100`. That is not a control against the referenced Rust range rule. The source rule in `breadstuffs/fhegg-fhe/src/bfv_coeff_matmul.rs:77–93` uses magnitudes `2^(w−1),2^(a−1)`, which include the most-negative signed value.

[EXECUTED] Exact arithmetic:

| Operand magnitudes | Capacity |
|---|---:|
| 8,128 (full signed 4×8-bit) | 504 |
| 7,127 (symmetric, excluding most-negative values) | 580 |
| 8,8 (full signed 4×4-bit) | 8064 |
| 7,7 (script's symmetric recipe) | 10532 |

[DERIVED] Either recipe can be useful when specified and enforced. The patch explicitly labels the symmetric recipe and replaces the `+137` assertion with the two exact, separate controls. It does not conflate 10,532 with the deployed full-signed-range capacity. `dark-learning-tradeoff-space.md:28` also retains the stale `1/q` description, while the script and later section correctly use `2B/q`; that prose should use the latter.

## K6. Reproducing the activation census does not certify its stated numerical semantics

[READ] `backward_table_virtualization.py:13–15` claims an exact real function rounded once to bf16. Lines 25–32 first round a Python float to binary32, then bf16. Its sigmoid/tanh derivative expressions also subtract rounded values near 1, and GELU forms `1+erf(x/√2)` near the negative tail.

[EXECUTED] Exact rational double-rounding falsifier: `x=1+2^-8+2^-30` is nearer bf16 code `0x3f81`, but the current function returns `0x3f80` via a binary32 midpoint. Separate exactly representable bf16 inputs demonstrate cancellation:

| Function/input | Existing evaluation | Algebraically equivalent stable evaluation (diagnostic, not certified census) |
|---|---:|---:|
| sigmoid derivative, x=40 | 0 | ≈4.2483542553e-18, bf16 `0x229d` |
| tanh derivative, x=20 | 0 | ≈1.6993417021e-17, bf16 `0x239d` |
| GELU, x=-10 | -0 | ≈-7.6198530242e-23, bf16 `0x9ab8` |

[REFUTED: provenance of counts] The quoted 148/190/412/751 counts are verified outputs of this approximation program; they are not verified counts for exact-real, single-rounding tables. The patch corrects that provenance rather than replacing one uncertified transcendental implementation with another and calling it exact.

[DERIVED] The useful replacement is stronger evidence for the **design decision**, without an unsupported full census. `counts/activation_witnesses.py` encloses exp(x) with exact rational Taylor sums plus a geometric remainder bound. It uses only integer/Fraction arithmetic to show both interval endpoints round to the same bf16 code. For positive x, the remainder after degree N is at most `next_term/(1−x/(N+2))`; subsequent positive term ratios are bounded by `x/(N+2)<1`. Monotone rational formulas transport these enclosures to σ, σ′, tanh and tanh′.

[EXECUTED] Exact-real/single-rounding witnesses:

| Activation | Inputs | Common output code | Different derivative codes |
|---|---|---|---|
| sigmoid | 7,8 | `0x3f80` (1) | `0x3a6f`, `0x39b0` |
| tanh | 4,5 | `0x3f80` (1) | `0x3ab0`, `0x393e` |

[DERIVED] These witnesses suffice to refute an output-keyed derivative function even for the true exact-real semantics. The input-keyed paired-column repair survives. No corrected exhaustive census is claimed; producing one requires certified transcendental enclosures at all inputs, including correct signed-zero/underflow/derivative conventions.

## K7. Residue coverage is not a finite-length encoding proof

[READ] `mma_limbs.py:17–25` checks every residue class then applies the contiguous-balanced-digit interval formula. The FP4 set is **gapped**, `{0,±1,±2,±3,±4,±6,±8,±12}`; it does not contain ±5.

[EXECUTED] At p=67, radix 13, the helper says two limbs suffice. Exhaustive two-digit enumeration has no representation of 65. A complete residue set permits a carry; it does not prove the chosen finite length accommodates that carry.

[DERIVED] Repair in `mma-representation.patch` (against degg-research): fix a quotient/remainder encoder using the least-absolute representative for each residue, carry a proven upper bound on the nonnegative quotient, and stop only when every possible final quotient is itself a digit. Encode the final quotient explicitly. This both produces witnesses and avoids floating-point logarithms in the count.

[EXECUTED] The corrected encoder handles all values 0..66 at p=67 with three digits. Its inductive quotient bound certifies the **actual table's** 9 limbs for M31/BabyBear/KoalaBear and 18 for Goldilocks; the terminal quotient bound is 3 or 2, respectively. Thus the actual 81/16 schoolbook ratio survives, while the generic formula is repaired.

[DERIVED] The explicit encoder uses no ±12 digit: maximum magnitude is 8. Consequently its limb-product bound is 64 instead of 144. At the same strict accumulator threshold, the conditional FP32 block bound is **262,143** rather than 116,508; the 14-bit column is **255** rather than 113. Neither number is a measured GPU guarantee: rounding mode, product exactness, subnormals, scales, initialization and accumulation schedule still need the silicon theorem's premises. The 5.06 throughput ratio is a schoolbook-operation comparison, not an architecture-independent lower bound or system-speedup promise.

## K8. AIR census is a search result, not “non-test constraints” or a literal count

[READ] The script excludes directories named tests/benches/etc., but it does not exclude inline `#[cfg(test)]` modules, comments, return types or structure declarations. For example, its two `EffectVmDescriptor2 {` hits in `solvency_leaf_adapter.rs` are the function return-type line 173 and the actual literal at 231. These are not two independently handwritten descriptors.

[EXECUTED] Current counts reproduce the committed result; the only output difference is the order of `transfer_link.rs` and `transfer_link_2out.rs` in an equal-count tie. The total is still 2,839 searched Rust files and 208 distinct matched include expressions. Both describe this filesystem corpus and these regexes, not all deployed code.

[READ] The substantive spot check survives: `solvency_to_descriptor2` at lines 173–242 explicitly constructs hash-opening, bit, range-reconstruction and PI-binding constraints in Rust. That is a useful source location for an authorship/refinement audit. Its existence alone proves neither an exploitable soundness defect nor the number of unchecked semantic boundaries.

[DERIVED] Repair the labels to “path-filtered Rust files” and “matching lines”; use deterministic secondary sorting for stable output. A semantic census must parse cfg conditions and classify emitted artifacts/refinement coverage separately. The existing README's “syntax, not semantics” disclaimer should accompany every quotation of its counts.

## Patch and validation handoff

[EXECUTED] `notes/astra/counts-model-repairs.patch` applies cleanly with `git apply --check` in zkml-research. `notes/astra/mma-representation.patch` applies cleanly with `git apply --check` in degg-research. Patches were generated from source snapshots, syntactically compiled, and executed **in memory**, leaving both source trees untouched. `counts/make_repairs.py` and `counts/make_mma_repair.py` reproduce them; patched outputs are retained beside the original outputs.

[OPEN] Mechanical patches do not discharge K3's state/operand range invariant, turn proxies into runtime measurements, establish missing cryptographic reductions, or certify a full activation table. Those limits are part of the repair, not hidden behind a green script run. Root owns commits, watch timing, and integration into the final report.
