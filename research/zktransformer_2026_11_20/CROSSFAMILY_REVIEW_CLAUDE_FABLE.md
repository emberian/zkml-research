# Cross-family review: zkTransformer audit, fix branch, formalization, pricing

**Do not file the Issue or PR as drafted.** Two critical soundness holes survive the fix branch, one honest binary regresses, and several statements in our own reports are wrong in ways upstream would catch on first read.

**Method and limits.** Nothing was compiled or executed, because the no-write rule covers `target/`. Code findings come from reading `main` @ `55344d7` and `fix/soundness-and-lookup-openings`; arithmetic was recomputed in memory. Three parallel readers covered the Lean, pricing/seam, and gadget lanes, and I spot-checked their highest-impact citations. The two critical findings need an executed PoC before going upstream; recipes are below. Line numbers are fix-branch unless marked `main:`.

---

## 1. Verdict on `fix/soundness-and-lookup-openings`

### CRITICAL

**C1. `ClampLower` output is an uncommitted, non-functional wire, so every `exp()` input is prover-chosen.** This exists on `main` and the fix does not close it. The gadget reader and I reached it independently.

- `src/basicblock/clamp.rs:43` and `src/dag/builder.rs:136` give `y` the role `Role::Output`. It has consumers, so `should_commit` (`src/dag/mod.rs:624-629`) is false and `y` is never committed. Our own count of 9 dense commitments for `structured_exp` confirms this.
- `ClampLower::verify` (`clamp.rs:62-70`) checks only `claims[0].point == claims[1].point`. No relation on evaluations is possible, since `max` is not affine.
- The Reducer's terminal check is `running_sum == reduced_claim.eval * eq_eval` (`src/basicblock/reducer.rs:99-109`), and `reduced_claim.eval` is supplied by the prover. With nothing downstream checking that value, the reducer at the ClampLower node binds nothing.
- Consequence: the three claims on `y` (from `Sub` at `builder.rs:139`, `Add` at `:151`, `ExpHelper` at `:347`) can come from three different tensors. `NonNeg(y−x)`, `NonNeg(y+C)` and `ZeroCheck` are satisfied by one, while `ExpHelper` receives an arbitrary Ỹ in its valid range.
- Impact: every Softmax, sigmoid, GELU and SiLU in every model. The same mechanism decouples the three claims on `r`, so the PoC-3 forgery (−1519) still goes through and our "Bug C fixed, zero slack" claim is false as shipped.
- PoC recipe:
  1. Take input x = −2840 and forged Ỹ = 0; recompute everything downstream of `ExpHelper` from Ỹ.
  2. At the ClampLower reducer, fake the rounds with the existing `forge_sumcheck_without_terminal_check` (`tests/test_soundness_audit.rs:90-123`).
  3. Set the reduced eval to `running_sum / eq_eval` and supply the true `x̃(z*)`.
  4. Expected result: `verify == true` with output 1024 (exp = 1.0) where the true value is 64.
- Fix: make the output `Role::Auxiliary` in both places so it is committed and opened. Add a `compile()` invariant that any node whose `verify` cannot bind its out-eval to its in-evals must have a committed output. This adds one dense commitment per `exp` call, sized like the exp input, which changes the paper's cost profile.

**C2. All four PCS verifiers take the SRS from the prover-supplied commitment and ignore the verifier key.** Also on `main`; untouched by the fix.

- `let srs = &commitment.srs;` with `_key` unused: `src/crypto/polycommit/kzh3.rs:1045-1046, 1053-1054`; `sparse_kzh3.rs:414-415, 422-423`; `kzh2.rs:1023-1024`; `sparse_kzh2.rs:213-214`.
- `KZH3Commit::fake_setup` (`kzh3.rs:918-958`, public) builds an SRS of identity points with the right dimensions. With that SRS in `commitment.srs`, every check in `kzh3_verify` (`kzh3.rs:877-892`) passes for `d_x`, `d_y`, `c_y` all identity and `f_star` a constant vector equal to any desired evaluation.
- The commitment point `c` can stay honest, so the transcript is unchanged (`to_transcript_bytes` absorbs only `c`, `kzh3.rs:406-411`).
- Result: under the same in-memory adversary our PoC 6 uses, a proof computed with weights W′ verifies against a commitment to W.
- The wire path is worse: `CanonicalDeserialize` installs `create_dummy_srs()` (`kzh3.rs:173`, degrees 1/1/1, identity points). After any round-trip, honest openings fail the length guard and length-1 forged openings pass.
- Fix: select the SRS from `key.srs_map` by the number of variables the DAG expects, reject length mismatches, and stop reading `commitment.srs`.

### MAJOR

**M1. `NonStructuredExp`: the honest binary now rejects, and the block is still unbound.**
- `run` (`src/basicblock/exp.rs:104-145`) outputs the remainder `r`, not a table lookup. For the binary's inputs 0..1023 (`src/bin/nonstructured_exp.rs:57-63`) that gives `r = x` and selector index 0 for every row.
- The new `verify` (`exp.rs:184-208`) requires `out̃(pt) = Σ aux·t = t[0] = 0`, which the honest output does not satisfy. On `main` the check was self-referential, so it "passed".
- `verify` still never produces a claim on `x`, and the selector is in neither `self.range` nor `self.two_pow`, so it has no booleanity or row-sum check.
- Our audit says "Fixed … `NonStructuredExp` prove/verify" and does not list this binary among those run.

**M2. The verifier's statement comes from the prover.**
- `Dag::verify` reads roles, shapes, scale factors, block counts and `is_permuted_with` from the `witnesses` argument (`mod.rs:1018-1020, 1358, 1417-1419`; `src/basicblock/einsum.rs:620`). The binaries pass the prover's post-run vector with data cleared.
- Flipping a role to `Output` un-commits an input or weight edge.
- Supplying surplus sparse blocks makes the new `range_block_table_vars` (`mod.rs:641-649`, `total_bits - offset` at `:647`) underflow. It panics in debug and wraps in release (no `overflow-checks` in `Cargo.toml`), adding 4 table bits per surplus block.
- Public tensors are prover-committed `Role::Constant` edges. That includes our new `r_min`/`r_max` scalars (`builder.rs:364-377`), the clamp constant, 1/6, 1/2, 1, masks, and the token one-hot selectors (`src/dag/oneshot.rs:20, 44-45, 97-98`).
- The "public shift-constraint check" is an `assert_eq!` on the prover's own variables (`src/bin/oneshot_gpt2.rs:288-296`).
- So the new remainder bound is parameterised by two scalars the prover commits.

**M3. Fixing the lookup verifier exposes honest-prover failures we did not test.** We ran only `scale_factor_log: 10`, power-of-two shapes, `SEQ_LEN ≤ 2` and random weights.
- Causal mask against the clamp: the mask is `−1000·2^s` (`src/dag/llama.rs:231`) and the clamp needs `y − x < 2^20` (`builder.rs:139-141`). At s=10 an honest proof fails once a future-position score is about 33.7 below the row max; the repo's own comment (`llama.rs:226-230`) reports real GPT-2 scores of ±223. At the paper's s=15 it cannot pass for any masked entry unless `table_size_log ≥ 25`.
- RMS tolerance on padded rows: for non-power-of-two `SEQ_LEN`, a padded row gives `positive_3 = 0 − SF + 512 < 0` (`llama.rs:367-373`). We masked argmax (`oneshot.rs:107-111`) but not this.
- On `main` both were hidden because out-of-range indices clamp to 0 (`src/basicblock/range.rs:43-49`) and the range proof was not checked.

**M4. The PR says "resolves six soundness issues" while known slack remains.** Besides C1 and C2:
- `ScaleDown` quotients are unbounded mod p.
- `ScaleUp` allows ±2^(Δ−1), although `y = 2^Δ·x` is a free linear check (`src/basicblock/scale.rs:134-145, 178-186`).
- The RMS tolerance is a fixed 512 regardless of scale (`llama.rs:339`); the in-code comment itself says ±25%.
- The Softmax and sigmoid advice is unconstrained, and its per-entry shift can cancel the causal mask.

**M5. The 5.14×–9.05× proof-size and 6×–21× verifier figures are an upper bound of our unbatched implementation, not the cost of soundness.**
- All blocks in a booleanity group are opened at the same point (`mod.rs:1702`, `:1524`), and all same-width blocks of a node share `inp_point ‖ r_tbl` (`:1660`, `:1487`).
- The commitment type is additively homomorphic (`src/crypto/polycommit/mod.rs:397-398`), and `batch_open` is `todo!()` (`kzh3.rs:1062-1069`).
- Random-linear-combination batching would need roughly two table openings per range node plus one per booleanity group. For nanoGPT's 216 sparse edges that is on the order of 450 rather than 1,652 (my estimate, not measured).

### MINOR

| # | Finding | Location |
|---|---|---|
| m1 | `verify_and_extract` evaluates `proof.f_star` before the new length guards; `evaluate_at_point` asserts `point.len() == self.n`, so a malformed `f_star.n` panics instead of returning `false` | `kzh3.rs:1057`, `sparse_kzh3.rs:426`, `src/util/poly.rs:788` |
| m2 | `Reducer` squeezes `reducer_alpha` without absorbing its claims; binding exists only because `Dag` absorbed them earlier. Standalone callers are unbound | `reducer.rs:26, 65`; `mod.rs:762, 847, 1074, 1180` |
| m3 | `verify_range` trusts `node_proofs[n]` for `ScaleDown`/`ScaleUp`/`ExpHelper` without confirming the node was visited. An unvisited node's point is unabsorbed and could cancel another block's error in the batched table sumcheck. Unreachable for DAGs the honest prover can prove (`prove_range` unwraps at `:1576`), so hardening only | `mod.rs:1364-1383` |
| m4 | Silent config fallback: a mistyped path now loads `./config.yaml` | `src/lib.rs:13-25` |
| m5 | `1u32 << (sparse_id * TABLE_COMMIT_LOG)` wraps for ranges of 33 bits or more; rescale factors are cast `as u32` | `mod.rs:1442, 1421, 1429` |
| m6 | `KZH2Commitment::to_transcript_bytes` was added, but KZH2 has no `verify_and_extract`; the default returns eval 0, so KZH2 cannot be used with `Dag::verify` | `src/crypto/polycommit/mod.rs:427-429` |
| m7 | Negative tests assert only `!verified`, so they can pass for an unrelated reason. No cases for fan-out reducer forgery, non-power-of-two shapes, s=15, or real weights | `tests/test_soundness_audit.rs` |
| m8 | The argmax mask adds a dense `S_pad·V_pad` constant for non-power-of-two vocab (2^21 at V=50257, S=32); our benchmarks used V=256 and exclude it | `oneshot.rs:107-111` |

**Nits.**
- `TwoPow` assumes one block: the prover asserts it (`mod.rs:1873`), the verifier only requires `sparse_id == 0`.
- The transcript is seeded with `b"zkml"` alone; no DAG digest, config or SRS.
- `Einsum` appends eq even when no free index repeats (`einsum.rs:548`), costing one extra evaluation per round.
- The node loop terminates only because node ids are topologically ordered (`mod.rs:1087-1098`).
- Upstream tests were consolidated (−267 lines in `test_basicblock_add.rs`, −180 in `test_fix_variables.rs`); say so in the PR.

### What holds

- **Challenge order** is identical in `prove_range`/`verify_range` and `prove_two_pow`/`verify_two_pow`: middle claims absorbed, then α, β, γ, then table groups in `BTreeMap` order with evaluations absorbed, then booleanity groups with a fresh eq point each (`mod.rs:1398-1408` and `1614-1624`).
- **Folding weights** are distinct monomials: β^i·γ^s for the table check and β^(2i)·γ^(2s) for booleanity. I found no cross-block cancellation, given visited nodes.
- **Row-sum via α** is correct in both lookups.
- **Booleanity** covers every block in `self.range`, and every `TwoPow` selector whether or not `self.range` is empty (`mod.rs:1803-1811`).
- **Variable ordering** is consistent: low bit folded first (`src/crypto/sumcheck/linear_prover.rs:128-129`), dimension 0 in the low bits (`src/basicblock/add.rs:11-19`), sparse index = input | table << d (`mod.rs:1591-1592`), KZH split z/y/x from low to high (`kzh3.rs:443-459`).
- **Committed-edge claims** are bound by ordered equality (`mod.rs:1225-1240`).
- **Remainder interval** is exact given consistent tensors: r ∈ [−354, 355] at s=10 and [−11356, 11356] at s=15, with a unique (k, r) for every provable q (enumerated by the gadget reader).

---

## 2. Previously overlooked findings in zkTransformer (code and paper)

1. **`ClampLower` unbound output** (C1). The most serious item; a one-word role change plus a commitment fixes it.

2. **SRS taken from the commitment** (C2). Our audit's "KZH3/SparseKZH3 … sound" row needs this caveat.

3. **The artifact is not zero-knowledge.**
   - The code says so: `// Non-ZK KZH3 Commitment` (`kzh3.rs:119`). Commitments are deterministic, and no file in `src/` draws prover randomness for blinding.
   - Each opening sends `f_star = f(r_x, r_y, ·)` in the clear (`kzh3.rs:116, 761-764`), which is 2^⌊n/3⌋ exact linear functionals of the tensor.
   - Sumcheck rounds are unmasked, and every `Claim.eval` on weights and activations is in the proof.
   - Derived: an n-variable weight tensor is recoverable by linear algebra after about 2^(n−⌊n/3⌋) openings at generic points, roughly 65k proofs for a 16M-entry matrix and far fewer for small tensors.
   - The paper is explicit that the built system is a SNARK. `zkTransformer.txt:580-582` requires zero-knowledge in the security model, `:586-590` says it "can be achieved", and `:1153-1160` says "to obtain a SNARK. To turn zkTransformer into a zkSNARK, the blinding techniques … are directly applicable".
   - This is a labelling and benchmark-scope point, not a bug. The README has no such sentence, and all reported numbers exclude blinding.

4. **Statement binding differs from the paper.**
   - `zkTransformer.txt:564-565` says the proof maps "a public sequence of input token IDs to a public sequence of output token IDs"; `:597` says the selector is "built from the public input token IDs"; `:633` says its one-hotness "is enforced by the gadget in Shout". The code has no check on the selector at all (M2).
   - `:663` says the RoPE permutation is evaluated "without a commitment"; the code commits a dense matrix (`llama.rs:204-207`).

5. **The paper says lookup openings are included; the artifact produces none.** `zkTransformer.txt:736-738` attributes proof size partly to "end-to-end commitments and openings to lookup auxiliaries that prior systems omit". On `main`, `edge_proofs` is filled at `main:src/dag/mod.rs:854`, before the lookups run at `:857-858`, and the idempotence guard at `main:…:659` skips blocks after the first. This quote is the strongest evidence that both are accidents. Use it.

6. **The non-structured exp baseline does not compute exp** (M1), which matters for any ablation that uses it.

7. **`Einsum` runs only equations whose operands have identical residual variable sets.** It uses `LinearSumcheckProver` (`einsum.rs:552`), which asserts equal sizes (`linear_prover.rs:45-52`). The paper's own example `bsdhv,btdh->bsth` would panic unless `v` has dimension 1. `GeneralLinearSumcheckProver` is not referenced by any block.

8. **Normalisation advice is loose.** Beyond the sign flip we noted: tolerance fixed at 512 (±50% on z at s=10), quotients and `r` not integrality-checked, and padded rows fail (M3).

9. **`ppl_repro` evaluates a different function from the circuit**, though its README calls it "circuit-faithful: K=4 cubic Taylor".

   | Aspect | `ppl_repro` | Circuit |
   |---|---|---|
   | k range | `K_BITS = 5` (`ppl_repro/gpt2_quant.py:80`) | `K_BITS = 4` (`exp.rs:16`) |
   | Taylor | quartic, float (`gpt2_quant.py:104`) | cubic, Q15 constants, four rescales |
   | ln 2 | unrounded float | integer L |
   | GELU | tanh form | `x·σ(1.702x)` |
   | Scale | s = 15 | `config.yaml` s = 10 |

   Its docstring admits the gap ("vs circuit's current K_BITS=4 cubic"). The README's own table shows LLaMA-2-7B on WikiText-2 going 5.18 → 6.21 (+19.8%), above the paper's 0.5 threshold.

10. **Honest-path causality leak at s=15.** Masked tokens clamp to −14·ln 2 and each keeps weight 2^−14; `gpt2.rs:138-140` does not re-mask after `exp`. At s=10 the floor rounds to zero.

11. **RoPE sign.** `llama.rs:291-316` rotates by −θ, where the paper's Appendix I and the reference implementation use +θ (gadget reader, verified by computation).

12. **Smaller items.**
    - `split_input` silently truncates over-long points (`kzh3.rs:449-459`).
    - The SRS is generated in-process with `thread_rng`, and the "verifier key" is the full prover SRS (`src/bin/nanogpt.rs:288-289`).
    - Challenges reduce a 256-bit value mod r (`poly.rs:71-77`). That gives statistical distance about 0.039 from uniform and a maximum point probability of 1.134/r. It is harmless, but it is not the "~2^−253 bias" we wrote.

---

## 3. Review of our research and formal claims

### `UPSTREAM_AUDIT.md`: errors to fix before anything is quoted upstream

| Where | Problem |
|---|---|
| Header | The paper's title is "zkTransformer: Scalable Zero-Knowledge Proofs for LLM Inference via Einsum Arithmetization and Structured Exponentiation Lookups". The extracted text and README name no venue or arXiv ID. Verify "CCS 2026" and the arXiv number independently. |
| §2.2 snippet; §2.6 F5; §4.1 | `should_open` does not exist on either branch, and the quoted block is not the code at `main:854`. The real line is `claims.iter().enumerate().for_each(…)`; opening selection on `main` is `irreducable_edge_ids` (`main:1008`). |
| §0.4, §4.2 | "Reproduces Table 4 to the byte and millisecond … verifier 0.138s (Table 4: 0.13s)". Table 4 reports verifier time **0.06 s** (`zkTransformer.txt:756`), on a 32-core Xeon. Only the byte count is a reproduction. |
| §0.1, §7.1 | Einsum is credited with an "unequal-variable-count … reduction (`GeneralLinearSumcheckProver`)". It never instantiates it (finding 7). |
| §1 Reducer row; §2.5 | "Absorbed claims before `r_beta`". There is no `r_beta`, and `Reducer` absorbs nothing (m2). |
| §1 | "Fixed … `NonStructuredExp`" (M1); "zero boundary slack … pins r" (C1); "`DivConst` & `Reciprocal` builder constraints sound" (`reciprocal()` is dead code, and its tolerance is ±50% at s=10). |
| §3.1 | "7 passed on main" came from an inverted variant. The committed suite asserts `!verified` and fails on `main`, as a regression suite should. Say that. |
| §5.3 | The 2-ULP floor exists only at s=15. |
| §7.1 | `@bingjyuechen, @liliatang, @ddkang` are unverified handles, and GitHub notifies whoever owns them. |

### Lemma 3.2 and the Lean (`FORMAL_EINSUMCHECK.md`)

**Our critique is unfair as tagged.**
- The lemma (`zkTransformer.txt:369-376`) bounds the Sumcheck that reduces a claim Z̃(r)=c to operand claims. That is how Theorem 3.1 (`:396-398`) and §5.3 use it.
- Under that reading the "omitted outer Schwartz–Zippel term" belongs to the DAG composition, charged once at the output. Our `einsumcheck_soundness` proves a different, standalone committed-Z statement.
- The lemma is **true and loose for every equation the artifact can run**, because one operand always carries every summed variable.
- It is imprecise in one respect: it uses v = the largest operand's variable count where the round count ρ belongs. That undercounts only when no operand carries all summed indices. The Lean reader simulated an exact cheating prover for `bp,bq->b` over F₁₁ and got 819/1331 = 0.615 against the paper's 6/11 = 0.545. zkTransformer uses no such shape.

**Neither Lean "tooth" refutes the formula.**
- `einsum_forged_accepts_end_to_end` runs the honest prover at a point where the claimed evaluation is true.
- On that instance both the paper's bound and ours exceed 1.
- `lemma32_v_not_upper_bound_on_rounds` is `decide` on numerals and references no acceptance event.

**Math error in our text** (`FORMAL_EINSUMCHECK.md:30`): "at μS = κ = 0, Lemma 3.2's sumcheck bound is 0". The paper's formula there is 3·max(μL, μR)/|F|; the zero is our own inner term.

**Other points.**
- The GQA theorems are definitional arithmetic (`omega`, `rfl`) and are not connected to the protocol theorems.
- Knowledge soundness, half of the lemma, is not formalised.
- The recorded `[EXECUTED]` lines cannot have been printed by `build_and_verify.sh`.
- The zkGPT relation is Eq. (4) in eprint 2025/1184, not Eq. (8).

**Confirmed.** Both files elaborate with no `sorry`, all 43 axiom pins pass, the patch matches the files, and `einsumcheck_soundness` is non-vacuous over adaptive degree-3 provers.

**Recommended tag:** `[IMPRECISE: Lemma 3.2 round parameter; holds for all shipped Einsums]`.

### `EXP_AND_GQA_PRICING.md`

- **`table_size_log: 20` is misread** (line 98). It is the `NonNegative` range width (`builder.rs:88-92`), not an exp table. The cited "Table 2" is the GPT-2 per-token table; the ablation is Table 6.
- **The headline winner is a configuration the report itself refutes.** On BabyBear, 0-rescale `Rank1ProdExp` is either too imprecise (18.19% error at 10-bit tables) or overflows a single field element. With the usable 1-rescale variant the crossovers roughly halve (16,192 → 8,032 at b=15). "0/25" survives; the 2.15–3.67× range and the m* values do not.
- **"Every field backend"** is asserted for one comparison only. The BN254 conversion constants are unsourced, yet the grid is tagged `[EXECUTED]`.
- **"20.14% Softmax denominator error"** reproduces, but it is the maximum of 200 synthetic trials (mean 2.6%), uses our normalisation rather than upstream's, and exists only at s=15.
- **GQA "saved committed KV cells"** is measured against a baseline that commits a repeated tensor, which no prover would do. Upstream `llama.rs:403-405` has no GQA at all. The defensible numbers are rounds 12→9 and sumcheck cost ≈8×.
- **"Matches 24-layer gpt-oss-20b, 32/32"** does not discriminate: the refuted (8,8) variant also scores 32/32.
- **Confirmed.** The script regenerates its saved grid with 0 mismatches, and the `Rank1ProdExp` error figures reproduce.

### `SEAM_AND_PRIOR_ART.md`

- **StructuredExp is misdescribed** (lines 128-137). The paper has symmetric r, degree 3 ("here we use degree 𝑑 = 3", `zkTransformer.txt:487`) and four multiplications, not r ∈ [0, L), degree 5, five multiplications.
- **"Zamir's Theorem 1" is misstated** (line 165). The theorem concerns an adversarially constructed, functionally equivalent model, not steering an honest commitment. "Steganographic" and "argmax" are ours. This propagates into `UPSTREAM_AUDIT.md` §5.1 and §6.
- **The (3, 3, 2) round-degree claim is correct** by operand incidence for order j→k→b, and (2, 3, 3) reversed. The comparison at line 346 is wrong: upstream would not "charge degree 4"; it would panic on unequal residuals (finding 7).
- **MXFP4 bit reduction mixes baselines.** 29 bits is the spec window, while 9 bits uses the measured maximum. Like-for-like the reduction is 2.46–3.06×, not 5.49–6.82×. The einsum does not enforce that weights lie in the MXFP4 value set or that scales are powers of two.
- **Our own spec is misquoted with line citations**: the exp table has 2,840 entries, not 4,097, and the quoted einsum strings and division form do not match `layer.py`.
- **`r` belongs in F₁** for `tre,tkb,ejkb,ejk->trj` (line 307).
- **Smaller items.** "HyperKZG" does not appear in the paper; line 270 says "exactly 5" contractions and lists six; lines 356-361 still contain drafting text.

---

## 4. Checklist before pushing upstream

**Blockers**
- [ ] Execute PoCs for C1 and C2 on both branches. If confirmed, lead the Issue with them and fix both in the PR (`Role::Auxiliary` for ClampLower plus the compile-time invariant; SRS from the verifier key).
- [ ] Run `nonstructured_exp` on the fix branch. Either repair the block (output = table value, bind x, one-hot checks) or revert that hunk and label the block an unsound baseline.
- [ ] Run honest end-to-end at s=15, at `SEQ_LEN=3`, and with real GPT-2 weights. Raise `table_size_log` or redesign the mask so M3 does not make the PR look like a regression.
- [ ] Remove every reference to `should_open` and the invented snippet. Correct the paper title, the Table 4 verifier time, and the `GeneralLinearSumcheckProver` credit.

**Code**
- [ ] Derive roles, shapes, scale factors, block counts and permutation flags from `Dag`. Assert `num_blocks == ceil(bits / TABLE_COMMIT_LOG)` and use `checked_sub`.
- [ ] Have the verifier evaluate public scalars and the token selector directly instead of trusting commitments.
- [ ] Guard `f_star.n` and length before `evaluate_at_point`.
- [ ] Absorb claims inside `Reducer`.
- [ ] Track visited nodes and require every non-sink range node to be visited.
- [ ] Make `ScaleUp` an exact linear check and drop its lookup.
- [ ] Batch same-point sparse openings, or state plainly that the reported overhead is unbatched.
- [ ] Remove the silent config fallback; use the environment variable only.

**Tests**
- [ ] Add negative tests for C1, C2, a role flip, surplus blocks, and a malformed `f_star`.
- [ ] Make each negative test assert which check rejected.
- [ ] Keep the upstream test rewrites in a separate commit.

**Issue and PR text**
- [ ] Drop the bare @-mentions.
- [ ] Split into: (a) lookup arguments unverified and unopened, quoting `zkTransformer.txt:736-738`; (b) ClampLower; (c) the SRS source; (d) design notes on advice constraints, statement binding and ZK status.
- [ ] Replace "resolves six soundness issues" with an explicit list of what remains open (M4).
- [ ] Present 5–9× as "with per-claim openings".
- [ ] Move Lemma 3.2 to a clearly labelled precision note. Suggested text:

> **Precision note on Lemma 3.2 (paper only; no code impact).** We read Lemma 3.2 as bounding the Sumcheck that reduces an evaluation claim Z̃(r)=c to operand claims, and under that reading it holds for every Einsum in the repo. One suggestion: the proof instantiates the per-round bound with v = the largest operand's variable count, whereas the relevant quantity is the number of Sumcheck rounds ρ = Σ log₂ D_u over summed and repeated-free indices. ρ ≤ v whenever one operand carries every summed index, which is true for Eq. (10) and every equation in `src/dag/*.rs`, so the stated bound is valid there and conservative. It undercounts only for contractions where no operand carries all summed indices (e.g. `bp,bq->b`), which zkTransformer does not use. Writing the bound as (m+1)·ρ/|F| makes it exact, and it may help to say this is the per-block term of an end-to-end bound.

**Our own notes**
- [ ] Retag the Lemma 3.2 result and fix the μS=κ=0 sentence.
- [ ] Correct the Zamir statement in all three files.
- [ ] Redo the pricing headline with 1-rescale.
- [ ] Fix the `table_size_log` paragraph and the MXFP4 baseline.

Since these findings change reported benchmark numbers, consider emailing the authors a day or two before filing publicly.
