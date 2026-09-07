# Independent review of the public-environment bootstrap

[DERIVED / independent review, 2026-09-07] **Accepted as a conditional construction.** The revised public environment, bottom-up setup and regenerated simulator packages remove the literal future-key-in-plaintext recursion. The effective key may be polynomial in message width and logarithmic function size; it need not be bounded by a polynomial in kappa alone. The exact dependency projection proves this effective-key bound from the stated compact encryption-circuit premise. No blocking proof error was found in the frozen target.

[DERIVED / normalization made explicit] The proof must choose its common output padding from the sublinear child-ciphertext upper bound. Padding every raw node to T bits while omitting those T writes would not justify the displayed sublinear work inequality. The required choice is available from the proof's own bounds and is detailed in §4 below; the author confirmed this interpretation. The frozen target's output-binding premise also incorporates the gate-only counterexample identified before freezing.

[EXECUTED / identity and exact target] Reviewer: `/root/entropy_composition`; author: `/root/he_closure_costs`. The reviewed [PUBLIC_ENVIRONMENT.md](../../pq_composition/base_fe_audit/public_environment/PUBLIC_ENVIRONMENT.md) has SHA256 `0293ce75968387ca33b49691274ffb91777f78a31f724dd6a71f76ca2d012ca8`. Its author artifact manifest has SHA256 `c5528234217b96c373a6425874b6a16867505275931c36574cb754c696de00d1`. The final target was read in full. [results.json](results.json) records unchanged before/after hashes for all 22 reviewed inputs: the 14 inherited frozen/source inputs, seven author artifacts and their manifest. No author, shared-ledger or companion writes, commits, network queries or downloads were made.

## 1. The changed interface is coherent

[SOURCE / inherited primary coverage] The underlying indexed-FE, RE composition and tree constructions were inspected in [2016/006](https://eprint.iacr.org/2016/006), Theorem 6 pp.9–11, and [2015/720](https://eprint.iacr.org/2015/720), Definitions 20–25 and Theorems 11–13 pp.28–36. The raw key layout was inspected in [2012/733](https://eprint.iacr.org/2012/733), §3.1 and Appendix B pp.23–24,47–49, and [2013/337](https://eprint.iacr.org/2013/337), §6.1 pp.16–17. Their exact local PDF/text hashes were rechecked against the inherited manifest. The new public-environment construction is the author's derivation, not a theorem attributed to those papers. This review also reuses the separately frozen [bootstrap review](../pq_bootstrap/REPORT.md) and [base-FE review](../base_fe/REPORT.md).

[DERIVED / accepted] For fixed public E, the interpreter `V_E` is an ordinary bounded classical function. The environment is included in the function that receives a B key, and the encrypted payload contains only the circuit/prefix/seed/tag/bounds. A real-to-simulated comparison retains E and any entire later public package Z. It may therefore expose E; no environment-hiding premise is being used. The actual E contains next-level encoding keys and fixed templates, not the private challenge circuit C. Equal-size challenge circuits select the same public bounds and interpreter family.

[DERIVED] The static B timing is preserved. The inner indexed function is fixed after E and its pad are chosen but before its own fresh B setup. The outer indexed function is fixed after the inner encoding key is known but before the fresh outer B setup. Neither function contains its own current B public key. That current key remains explicitly inside the circuit given to xiO, with its full effective length charged. This distinction prevents the environment change from silently granting an oracle to xiO or smuggling current setup into the static function-selection phase.

[DERIVED] B.Setup is required to depend on public bounds, not the selected function. Function-key issuance is allowed to process a long specialized circuit. Its work and CRS size are charged to setup/key generation. They are not silently included in a short payload or omitted from the overall polynomial construction cost.

## 2. Composition and shared-key induction preserve correlations

[DERIVED / accepted] The composed encoder needs only the outer encoding key. It encrypts `(m,zeta)` with the succinct outer encoding and does not execute `H_J` or the weak encoder while doing so. The outer function key computes `R_W.Enc(ek_W,m;G(zeta))` during evaluation. This is the same useful separation of encoding work and evaluation work as the source composition, with the inner public key moved into the outer function's public environment.

[DERIVED] The simulation order is valid:

1. Simulate the outer tuple conditional on its already sampled inner environment and package.
2. Replace the inner PRG tape after the real outer program/payload has disappeared from the view.
3. Replace the inner public-key/CRS/ciphertext tuple by its simulation, then create a new outer simulated setup specialized to the **supplied new inner key**.

[DERIVED] The final step is a classical randomized channel of the whole supplied inner tuple. It knows the new inner encoding key and inner ciphertext, so it can form the new J and call `Sim_S(J,ct_W)`. It does not need m, zeta, a hidden seed or inner setup secrets. The old outer CRS is not retained across a change of inner key. The joint auxiliary inner CRS and key can remain visible throughout; they are independent of fresh outer setup before applying the outer fixed-environment game.

[DERIVED] The same reasoning applies to a child switch. The induction retains current and later packages. A reduction receives the child key, CRS, ciphertext and later package; generates the sibling under that **same child key** with fresh independent seed/tape; rebuilds the parent E from the supplied child key; and runs the parent simulator anew. Ancestor simulators repeat this as public postprocessing. No old parent CRS hardwired to a different child key is carried through the switch.

[DERIVED] The unchanged per-encoding and tree privacy bounds are therefore justified at the expanded resource envelopes:

```text
eps_R <= (l_H+s) eps_B + (2s+2) eps_X + 2s eps_P + 5 eps_G,

a_n <= 2 eps_R,
a_i <= 2 eps_R + 2 eps_G + 2 a_(i+1),

Delta_IO <= (2^(n+2)-2) eps_R + (2^(n+1)-2) eps_G.
```

[DERIVED / quantum scope] Every wrapper uses classical values and one final invocation of the continuing quantum distinguisher. Independent setup/environment samples can be fixed mathematically within the uniform game envelope; no reduction prepares a conditional density operator, clones advice, or measures it to choose a hybrid. The advice and all classical descriptions/workspace remain charged as in the accepted nonuniform model. There are exponentially many hybrid terms but only one continuing child challenge per level in any selected reduction. Public sibling generation and regenerated ancestor setups add polynomial work, not a full-tree simulation.

## 3. Dependency projection is exact under its stated model

[DERIVED / accepted] For a fixed fan-in-two encryption circuit with g gates and o output bindings, retain every distinct public-key input position appearing on a gate input or directly on an output. At most `2g+o` such positions exist. Renaming these inputs and supplying the retained bits preserves each gate value by induction in topological order, and preserves every output, for all key/message/tape assignments. Dead gates may retain unnecessary bits; minimality is not required.

[DERIVED] The frozen version correctly requires `g+o+|r|=poly(kappa,N,log S)`. Without the output term, a zero-gate circuit can output the whole arbitrarily large key. Without a bounded random tape/bit-operation model, evaluating the remapped encryption circuit would not by itself provide the claimed compact encoder interface. The template must be uniformly constructible from public bounds; key-bit positions must not be selected by secretly inspecting the eventual key value.

[DERIVED] Setup can construct the template and extract its needed key positions using `poly(kappa,N,S)` work. After remapping, original huge-key indices are unnecessary in the encoder. The compact serialized template and retained bits have the claimed polynomial width. Encryption evaluates that small circuit; KeyGen and the stipulated decryption interface are unchanged. A transformed-scheme reduction projects its supplied original public key and exposes the resulting view. Ciphertexts are exactly equal, so this step adds no correctness error or probability-gap multiplier; its setup/projection overhead is still charged.

[DERIVED / machine-model limit] A fixed clocked sequential Turing-machine encoder with a separate key input tape initially positioned at its first cell can inspect only a bounded prefix in t steps. Keeping reachable cells/end markers and explicitly unrolling the bounded configurations yields a polynomial-in-t Boolean circuit. This supplies the premise for standard bit-computation compactness. A unit-cost arbitrary RAM lookup can select among many key bits depending on a message; a small lookup-time bound alone does not supply a small fixed Boolean circuit. The target expressly retains that distinction. The lemma does not remove secret key-generation authority or compress every possible public-key representation.

## 4. One common polynomial bound closes

[DERIVED / accepted] In the revised layout, payload width has no K term: `N <= a(U+log(T+2))`, where `U=kappa+|C|+n+1`. The outer payload excludes the inner key as well as future keys. The specialized node/outer functions may contain effective keys as constants and execute the weak encoder, including the xiO obfuscation algorithm, but have an ordinary bound polynomial in U, T and K.

[DERIVED] The S feedback has only logarithmic dependence through K and encryption work. More explicitly, after substituting the compact encoder/key bounds, an upper bound on specialized function size has the form

```text
F_size <= A (U+T)^d [1+log S]^e
```

[DERIVED] for fixed constants. Choose `S=(c(U+T))^r` with `r>d` plus enough fixed margin to absorb the logarithm. Since `log S=r log(c(U+T))`, increasing c once covers the remaining fixed constants and all small inputs. This yields a single polynomial S and `K,g=poly(U,log T)`. No actual sampled key bits enter the parameter choice. Full original B setup keys and issued CRS values may have polynomial dependence on S; they are not executed or embedded anew inside the short payload.

[DERIVED] The xiO input circuit explicitly includes the compact current B key and encoder, so its size is `poly(U,log T)`. Its ciphertext bound, and then the outer repetition bound, give a uniform estimate

```text
ct_R, Enc_R_work, Enc_R_tape <= Q(U,log T) T^(1-alpha)
```

[DERIVED] after increasing a fixed polynomial Q, valid over all admitted output bounds `l<=T`. For concrete padding, choose l large enough for twice this ciphertext upper bound and the leaf output, using the uniform estimate, and choose T so this selected l is at most T. This is a legal common bound because the estimate was uniform in all `l<=T`; it is not an equation requiring the actual ciphertext width to be known before its own setup. The selected padding width is itself sublinear up to the polynomial/logarithmic factor. Charging its writes preserves the claimed node-work form. It would be incorrect instead to force every node to write T padding bits and omit that work. The author confirmed the former normalization in review coordination.

[DERIVED] Near-linear-output PRG work and two child encodings then fit

```text
node_work <= A U^a (1+log(T+2))^b T^(1-alpha) + B U^d.
```

[DERIVED] For a fixed positive alpha, absorb the logarithmic factor into a constant times `T^(alpha/2)`. Choosing `T=(c0 U)^D` with sufficiently large fixed c0,D covers this inequality, leaf work and the selected output width. Thus N, K, S, full setup work and CRS size are polynomial in U across all levels. No bound is raised to a fresh exponent per level. For the inherited logarithmic-input xiO contract, use the same admitted polynomial circuit families/public security-parameter enlargement as in the frozen bootstrap so `log T=O(log kappa)`.

[DERIVED / relation to the obstruction] The earlier literal bound `|pk_GKP(N)|>=4N` remains correct for its explicit representation. It does not obstruct this layout because a parent plaintext no longer contains that key. Here `K>N` is allowed; K contributes to the specialized function/CRS and the current small encoder circuit, not to the next payload's own width. This removes the representation loop under the compact encoder premise. It does not show that raw GKP already satisfies that premise for the required specialized arbitrary function.

## 5. The fresh-error and all-input bounds still apply

[DERIVED / accepted] Current setup remains fresh after fixing the **later** package. Child seeds and complete encoding tapes are derived from the independent root seed, so a fixed-prefix seed/tape marginal can be replaced by a fresh independent pair before invoking current fresh correctness. No ancestor CRS or ancestor seed is conditioned on. Such an ancestor package depends on current keys and could change their distribution; the proof does not give that correlated material away for free in its fresh-current-setup argument.

[DERIVED] The inner R_W failure predicate ignores the correlated outer package and uses the inner marginal. For the outer failure bound, the inner key is fixed first and the outer setup/tape are then fresh. Thus the same pointwise B-correctness averaging and error union work despite inner/outer specialization. The marginal PRG replacement covers the **complete** composed encoding tape, including outer succinct-encoder coins. Exact public-key projection introduces no additional failure event.

[DERIVED] With `M=2^(n+1)-1` and `S_depth=sum_(d=0)^n d*2^d`, the inherited bound is

```text
eta_IO <= M [delta_X + (l_H+s) delta_B + s eps_P,corr
                    + eps_G,composition-corr]
          + S_depth eps_G,tree-corr.
```

[DERIVED] Taking `l_H,s<=B_max` and a common PRG envelope gives

```text
eta_IO <= M [delta_X + 2 B_max delta_B + B_max eps_P,corr]
          + (n*2^(n+1)+1) eps_G,corr.
```

[DERIVED] The latent all-node union is unchanged and requires no independence among node failures or reused level keys. It concerns simultaneous correctness over every input of the bounded circuit. The source's unspecified negligible rates do not by themselves make this exponentially weighted bound negligible.

## 6. Executed evidence and remaining obligation

[EXECUTED] The independent command

```text
python3 research/learn_infer_only/experiments/adversarial_review/public_environment/review.py > research/learn_infer_only/experiments/adversarial_review/public_environment/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/public_environment/stderr.txt
```

[EXECUTED] exited 0 with empty stderr. [review.py](review.py), [results.json](results.json) and [stdout.txt](stdout.txt) preserve:

- 10,240 exact projection equalities over 40 ordinary Boolean circuits, including 8,528 nonzero-output cases and five zero-gate passthrough controls.
- Two finite dependency-reassembly models with 256 records each. Retaining a stale environment gives disjoint consistency support; rebuilding it from the supplied key gives the intended relation. A separate dependency example changes an event from marginal probability `1/4` to conditional probability one after exposing a parent record, illustrating the forbidden conditioning step without implementing encryption.
- 561 setup-order constraints over depths 0 through 32.
- Twelve exact integer models simultaneously satisfying declared key, specialized-function, output-padding and node-work bounds with the same fixed polynomials `T=(2U)^256` and `S=(2(U+T))^8`, while `K>N`. These are deliberately loose declared model bounds, not measured primitive costs.
- 6,400 unchanged privacy/correctness coefficient checks.

[EXECUTED / author replay distinguished] A byte-identical owned copy of the author's ordinary-circuit script reproduced its JSON exactly, including 32,768 projection checks and eight after-log-absorption examples. It wrote only in the review directory. All 22 input hashes were then rechecked unchanged. No test failed. These finite controls do not verify FE privacy, the asymptotic theorem or an implementation of the source compiler.

[OPEN / preserved scope] Raw GKP has costs depending on prescribed depth. The specialized outer function executes `R_W.Enc`, including X's obfuscation algorithm; its depth is not bounded by `poly(U,log T)` simply because its encrypted payload is short. Using only a generic polynomial-in-T depth bound can destroy the sublinear saving when substituted into GKP encryption and the current-key-containing xiO circuit. A compact P/poly base implementation or a proved shallow specialization still has to resolve that issue, together with the Boolean/multi-output source interface and concrete QA/statistical/correctness rates. The public-environment proof supplies neither a LWE-only construction nor a resident credential-lifecycle theorem.

[DERIVED / decision] The public-environment successor supplies a valid conditional replacement for the stronger short-key bootstrap premise in the stated bit/circuit model. The next construction target is now the actual compact encryption/depth interface and quantitative base rates, rather than the literal future-key payload equation. Preserve that distinction when folding this review.
