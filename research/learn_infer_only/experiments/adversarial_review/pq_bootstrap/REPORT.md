# Independent review of the conditional quantum-advice bootstrap

[DERIVED / independent review, 2026-09-07] **Accepted under the explicitly stated B/P/G/X interfaces, including the pointwise-correctness supplement.** I found no blocking mathematical error in the reviewed bootstrap. The one-key encoding and shared-key tree reductions use one continuing quantum advice state and polynomial classical wrappers. The all-input correctness argument pays for replacing complete pseudorandom encoding tapes before using fresh-coin correctness. This is a review of an author-derived conditional proof, not a machine-checked cryptographic theorem or an instantiated post-quantum construction.

[EXECUTED / identity and preservation] Reviewer: `/root/entropy_composition`; author: `/root/pq_composition`. The exact targets are [BOOTSTRAP_LIFT.md](../../pq_composition/qio_instantiation/bootstrap_lift/BOOTSTRAP_LIFT.md), SHA256 `ec9f721f2402d31a49a9fd4ee14f978b4cf7474429600710347dc555fe0d9792`, and [POINTWISE_CORRECTNESS.md](../../pq_composition/qio_instantiation/bootstrap_lift/POINTWISE_CORRECTNESS.md), SHA256 `c63e299a31a33617888814d5b4f371cf0f1e25541b4ebaa061e9bc84340d81f2`. Both were read in full. The source PDFs, extracts, targets and controls have matching before/after hashes in [results.json](results.json). Author files and companion trees were not edited; there were no commits, downloads or metered queries.

## 1. What the source actually supplies

[SOURCE / full definitions, construction and relevant proof passages read] The local primary sources are:

| Source | Inspected locations | Role and limit |
|---|---|---|
| [2016/006](https://eprint.iacr.org/2016/006), PDF SHA256 `aef02e2f8ea90f0dc21893fbe925c84fbee6039b0df38a9daba598948f74297e` | Definitions 3–6, pp.5–6; Definitions 7–8 and logarithmic-input remark, pp.7–8; Theorem 6 construction and hybrids, pp.9–11 | Static one-key Boolean FE, compactness, and the indexed-encryption xiO transformation. Its printed definitions are classical/nonuniform, with perfect correctness. They do not themselves establish the target's quantum-advice games or its separately stated short-public-key parameterization. |
| [2015/720](https://eprint.iacr.org/2015/720), PDF SHA256 `00542fa45b6ee70bb9fba31cfdb80116913384c30396111909b2c09a70170d16` | Child-coin hybrid, §4.1 pp.22–23; PRG/runtime discussion, §5 p.25; Definitions 20–25, pp.28–30; Theorems 11–13, pp.30–36; circuit consequence, Theorem 15 p.37 | RE with a short public encoding key and potentially long CRS; joint simulation of public key, CRS and encoding; composition; FE-to-RE pad hybrids; and independent setup per tree level. The detailed one-key bit-indexed encoding and explicit quantitative quantum lift are derived additions in the target. |

[EXECUTED / access] These PDFs were read from `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2016/006.pdf` and `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/720.pdf`. The commands were `pdftotext -layout <absolute PDF path> <owned extracts path>`, followed by text inspection. Both extraction commands exited 0. Extract hashes are respectively `bb35f26eab10391b9090ad1813dd463266d3f1b8bfa16c90f1f65cf9cee03576` and `4a5a32b76235b51f94f1db8cbc5025f7d2c390627b6f319b8bd435ed98e26713`. The LWE/base-FE chain is being independently reviewed by another lane; this review does not incorporate an unreviewed base-instantiation conclusion.

## 2. One key is enough for the bit-indexed encoding

[DERIVED / accepted, target lines 54–71] For a fixed pad `c`, program/input and output position, the real message and simulated message yield the same Boolean result. The function `F_U,c` and both messages can be fixed before the current B setup. The pad, program, output and seed may first be sampled or computed from independent public parameters. Reordering these independent choices before current setup does not change their distribution.

[DERIVED] In one ciphertext-position hybrid, the reduction receives `(pk,sk_F,ct_i)`. It uses public encryption to produce every other position under that supplied `pk`, retaining the one supplied `sk_F`. The other positions may contain different messages, but no additional function key or encryption oracle is needed. The entire joint ciphertext vector has the intended distribution. This is ordinary single-challenge public-key hybrid reasoning under the stated one-key game, with all additional encryption work charged.

[DERIVED] Both pad switches occur while the encoded branch is still the real branch. Therefore their reductions do not need the seed behind a PRG challenge pad. After the second pad switch the real and simulated FE messages are exactly compatible. The resulting `2 eps_G + l eps_B` bound is valid as an absolute acceptance gap. The primitive-to-RE accounting is also correct:

```text
eps_W <= (2s+2) eps_X + 2s eps_P + s eps_B
eps_R <= (l_H+s) eps_B + (2s+2) eps_X + 2s eps_P + 5 eps_G.
```

[DERIVED] The raw xiO circuit equivalences are exact independently of FE or xiO correctness. Consequently a decryption error is not an additional privacy bad event in these switches. Public lengths, index bounds and padding must remain common between both sides, as required by the target's normalized construction.

## 3. Composition and the common runtime bound

[SOURCE / DERIVED, target lines 73–100] Theorem 11 of 2015/720 explicitly uses the required simulation order: simulate the outside encoding, replace the inside encoding's PRG tape, then simulate the inside encoding. The target preserves that order. The simulator returns the public key and CRS along with the encoding, so it can replace their joint distribution as required by the tree proof. It receives the output and public metadata, not the original program or its hidden seed.

[DERIVED] Once the outer encoding is simulated, the seed `zeta` has disappeared from the exposed real-program representation. The middle reduction computes the inner encoding from its supplied PRG challenge string and invokes the outer simulator. There is no request to reconstruct a real outer program containing an unknown seed. The correctness argument separately uses a marginal failure predicate, which also needs only the challenge tape.

[DERIVED / accepted, target lines 102–125] The tagged node-program representation closes the size recursion under the stated short-key premise. Each payload contains the original circuit once, one prefix/seed, at most `n` future short public keys, and binary bounds. It does not contain expanded descendant source code or future CRS values. Thus, before fixing `T`, its width is `M0+O(log T)` with `M0` polynomial in the original parameters. The outer succinct encoding handles the short description of a program whose execution can take polynomial time in `T`; it need not execute that entire inner computation while constructing its own encoding.

[DERIVED] Logarithmic payload and PRG overhead can be absorbed into a smaller positive exponent: for any fixed logarithmic degree and positive margin, `(log T)^d` is bounded by a constant times a positive power of `T`. The explicit near-linear-in-output PRG hypothesis and sublinear encoding time then give one bound `A T^(1-beta')+B0`, with `A,B0` independent of `T`. Taking `T >= (2A)^(1/beta')` and `T >= 2B0`, together with the leaf bound and fixed encoding constants, is a polynomial choice and gives runtime at most `T`. Setup and evaluation can take other fixed polynomials in this common `T`; they do not recursively raise its degree at each depth.

[DERIVED / scope] This conclusion depends on the *stated* public-key width, succinct encryption, bounded classical algorithms and PRG efficiency. An encryption-time succinctness statement alone does not imply the short-key premise. XiO is used for classical circuits, whose deterministic evaluation is bounded by their circuit size; replacing that type by an arbitrary unbounded program would require a separate evaluation cap. The source's additional unbounded-input/Turing-machine transformations are outside the reviewed conclusion.

## 4. The shared-next-key induction is a joint reduction

[DERIVED / accepted, target lines 127–150] The induction exposes the challenged node together with all current and later public keys and CRS values. After the child seed/tape tuple is replaced by independent uniform blocks, a child reduction receives the one next-level setup and can generate the sibling under its supplied public key. The sibling uses fresh independent seed/tape blocks and the same exposed later package. It does not need the setup secret, another CRS, another function key, or independent next-level keys.

[DERIVED] In distribution notation, the allowed operation is a public channel

```text
(pk, crs, child, later) ->
(pk, crs, child, Enc(pk, sibling_program(later); fresh_tape), later).
```

[DERIVED] The parent simulator and any ancestral wrappers are subsequent public processing. They invoke the continuing distinguisher once. Replacing the sibling's key with an independent key would change this joint distribution; the target does not do that. The explicit child-coin replacement is essential because the induction's fresh child seed/tape premise would otherwise be missing.

[DERIVED] With uniform envelopes at the enlarged resources, the leaf contributes `2 eps_R` and an internal node contributes `2 eps_R+2 eps_G+2 a_(i+1)`. Hence the reviewed exact bound is

```text
Delta_IO <= (2^(n+2)-2) eps_R + (2^(n+1)-2) eps_G.
```

[DERIVED / quantum and resource scope] All wrappers here sample/process classical values and run the final quantum distinguisher once. No reduction needs to clone, rewind or measure its advice to choose a hybrid. Mathematical fixing of an independent classical package permits an arbitrary residual density operator in the stipulated advice class; no algorithm must prepare a conditioned state. Triangle inequalities use separate experiments, not multiple executions on the same physical advice specimen. A path may require different hardwired classical constants or an output complement; these fit the charged nonuniform description/gate budget. The proof therefore preserves `q` in its explicitly chosen classical-code initialization model. It does not establish an exact unchanged-`q` claim in every alternative uniform-machine model.

[DERIVED] A single primitive reduction follows one child challenge per level and generates the other child publicly. Its overhead is at most the target's polynomial one-level bound times the path length. The exponential number of terms appears in the probability bound, not in one reduction's running time. The primitive envelope must cover the final adversary *plus* these wrappers; a security-error exponent alone does not supply a running-time guarantee. The target already requires security against the needed circuits at their actual budgets, and its sufficient-parameter discussion is accepted in that sense.

## 5. Fresh pointwise errors propagate to all-input correctness

[DERIVED / accepted, main lines 152–174 and supplement lines 7–87] A fixed latent-tree prefix supplies a seed and a **complete** current encoding tape. The path hybrid compares their joint marginal to an independent uniform pair at cost `d eps_G,tree-corr`. It discards ancestor data. Separate uniform marginals would be insufficient, and the distribution conditioned on a known ancestor seed is not this experiment.

[DERIVED] The node-failure test samples the current/future level packages independently, constructs the fixed-prefix raw program, computes its bounded output, and compares actual decoding against that output. All operations are polynomial under the common bound. The raw node program contains future keys only, so it is independent of its current setup. This is enough to average the fresh-object correctness bound. The reduction does not enumerate the exponentially many latent nodes or compute the event that any node in the whole tree fails.

[DERIVED / supplement] Uniform pointwise fresh B correctness is sufficient. For each fixed output index, the PRF point-value game supplies a value `V`; the reduction can ignore its punctured-key component, sample the B setup/key independently, and test Boolean decryption failure using `V` as the encryption tape. This gives `delta_B+eps_P,corr` for the actual marginal indexed ciphertext. Union over the `s` positions and add X's all-input fresh-object error. For the outer succinct encoding, each of its `l_H` messages has a fixed function/message independent of the current outer setup and fresh encryption coins, giving `l_H delta_B` by a union bound. Shared-key failures need not be independent.

[DERIVED] The inner PRG-tape replacement is paid separately. Thus the fresh composed-object error is bounded by

```text
delta_R,fresh <= delta_X + (l_H+s) delta_B
                         + s eps_P,corr + eps_G,composition-corr.
```

[DERIVED] This is used only *after* the fixed-prefix joint marginal replacement has made the current complete encoding tape fresh. That replacement covers the outer succinct encoder's coins too. The supplement correctly avoids claiming that pointwise-correct B makes the outer encoding correct on every PRG-derived tape.

[DERIVED] Every latent node decoding to its raw output implies correct evaluation on all inputs. The converse is unnecessary: a bad internal decoding might still happen to leave some or all final outputs correct. A union bound over the latent nodes gives the reviewed sufficient error bound, with `M=2^(n+1)-1` and `S=sum d*2^d`:

```text
eta_IO <= M [delta_X + (l_H+s) delta_B + s eps_P,corr
                    + eps_G,composition-corr] + S eps_G,tree-corr.

If l_H,s <= B and the PRG envelopes share an upper bound:
eta_IO <= M [delta_X + 2B delta_B + B eps_P,corr]
          + (n*2^(n+1)+1) eps_G,corr.
```

[DERIVED] No all-message union over `2^|m|` was used. Current-program independence is doing real work: arbitrary post-setup selection of a bad message would not follow from the premise. The all-node union is valid under arbitrary correlations among node failures and reused level setups. The `n=0` case also has the expected coefficients: one fresh object, no tree expansion, two RE privacy simulations.

## 6. Executed controls and remaining boundary

[EXECUTED] The independent command

```text
python3 research/learn_infer_only/experiments/adversarial_review/pq_bootstrap/review.py > research/learn_infer_only/experiments/adversarial_review/pq_bootstrap/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/pq_bootstrap/stderr.txt
```

[EXECUTED] exited 0 with empty stderr. [review.py](review.py), [results.json](results.json) and [stdout.txt](stdout.txt) preserve:

- 1,252 indexed-message compatibility pairs and 2,504 exact laws for assembling the remaining ciphertext positions around one supplied challenge.
- A 64-point shared-key child/sibling law and 16 public-postprocessing checks. The deliberate independent-sibling-key substitution has total-variation distance `3/4` from the intended toy law.
- 510 fixed-prefix joint seed/tape laws. One test channel is a deliberately insecure deterministic expander; the other is a randomized near-uniform channel testing the same hybrid algebra with a smaller statistical gap. The latter is explicitly **not a PRG construction**. Separate uniform seed/tape marginals can still have joint distance `1/2`; conditioning on a known seed changes the toy distance to `3/4`.
- 270 shared-setup error-union cases. With three positions and pointwise error `1/8`, coincident failures give union `1/8` and disjoint failures give `3/8`; neither requires the independence formula `169/512`. A post-setup choice of the synthetic bad index gives error one, explicitly outside the fixed-message premise.
- 7,936 independent privacy/correctness coefficient checks.

[EXECUTED / author replay distinguished] Byte-identical owned copies of the author's two control scripts also reproduced their recorded JSON exactly, including 145,636 compatibility cases, 225 recurrence cases, 25 all-node coefficient cases, 4,096 composition cases, 32,906 toy latent-tree masks, 1,056 fixed-point examples and 17,408 supplement coefficient cases. These executions wrote only into this review directory. No test failed during this review; failed-premise controls are intentional passing assertions. Neither the independent controls nor the replay is evidence that a cryptographic primitive meets its assumed game.

[OPEN / unchanged conclusion] The first construction obligation remains the instantiated base suite, including the short public key under one coherent parameterization, the charged quantum-advice security envelopes, PRG/PRF efficiency and explicit correctness rates. Merely negligible pointwise error does not imply the exponentially weighted final error is negligible. The supplement resolves the *type* of base correctness premise; it does not supply a quantitative lattice instantiation or correctness amplification. The accepted conditional bridge does not establish LWE-only post-quantum iO, QROM security, private ingress, a compact resident implementation or a credential-lifecycle theorem. No source or finite control in this review removes those obligations.

[DERIVED / next bounded check] Once the base-source lane freezes its result, substitute its actual width-dependent public-key/runtime bounds and explicit `delta_B`, `eps_B`, `eps_P`, `eps_G` rates into this theorem's common-bound construction and equations (4), (6), (C5). If its public key grows with the recursive program width, retain that dependence in the fixed-point inequality rather than reusing `p0(kappa)`. This is the precise next integration point; no change to the two reviewed proof targets is required for their present conditional scope.
