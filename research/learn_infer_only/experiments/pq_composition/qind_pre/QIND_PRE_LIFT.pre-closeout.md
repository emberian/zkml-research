# A conditional quantum lift of the pre-public-key randomized-FE game

[DERIVED theorem; 2026-09-06] The normalized 2013/729 construction satisfies the **classical-API quantum `IND_pre` game defined below**, conditional on the explicit quantum primitive games in this note. Every reduction uses one running adversary and one retained quantum state. The proof does not use quantum rewinding, state duplication, weak extraction, or an iO-to-NIWI/PRF construction. It allows nonzero **uniform all-input** obfuscator correctness error and gives an explicit loss ledger.

[DERIVED limitation] This is our conditional game/proof, not a PQ-FE theorem sourced to the paper, a primitive instantiation, a kernel-checked result, or a lift of its entire adaptive-key SIM game. In particular, the quantum auxiliary-input iO hypothesis below has not been instantiated by 2025/2215. The initial source audit [PQ_COMPOSITION.md](../../../PQ_COMPOSITION.md) remains unchanged.

## 1. Classical APIs, one quantum state, and compatibility

[DERIVED definition] Fix public polynomial bounds before the experiment: security parameter `lambda`, state width, circuit/function widths, randomness/output widths, padding size `S`, key count bound `qK`, decryption-query bound `qD`, and adversary time/space bounds. Every function is a classical deterministic circuit `f(x;r)` with explicit random-coin input. All parsers and algorithms are total; malformed encodings reject. Decryption uses a fixed public default if the underlying PKE returns failure, identically in every hybrid. Honest PKE decryption never uses that default under the hypothesis below.

[DERIVED advice convention] The adversary is a nonuniform polynomial-size quantum circuit family, optionally initialized with **one copy** of an arbitrary polynomial-qubit advice state `sigma_lambda`. The state and classical circuit advice may depend on the public family and lambda but are independent of all subsequently sampled current-instance setup and challenge coins. No efficient preparation of the advice state is assumed. All quantum work registers, including retained reference registers available to the adversary, are collected into `R`. Separate security experiments start from their own specified initial state; no reduction is allowed a second copy during its run.

[DERIVED game `QIND_pre^cl(b)`] The following order is binding:

```text
A1(sigma_lambda) -> classical L=(x0,x1,F,Z), retained quantum R1
    where F=(f1,...,fk), k<=qK; x0,x1 have the fixed state width.

Independently sample (MPK,MSK) <- Setup(lambda).
Issue one fresh function key for each entry of F.
A2 receives MPK, all those classical keys, L, and R1.
    It may make <=qD classical (CT,g) decryption queries.
    For each query the challenger generates a FRESH KeyGen(g,MSK),
    evaluates it on CT, returns the classical result, and discards that key.
A2 finishes with retained quantum R2.
CT* <- Enc(MPK,x_b).
A3 receives CT*, R2 and its retained classical data, then outputs a bit.
    There are no further external decryption or key queries.
```

[DERIVED access rule] A classical API request is measured/dephased in the computational basis; its classical reply is delivered to the continuing adversary. The issued key code is public. The adversary may execute, copy or reversibly implement that code, including local superpositions. This theorem does not offer coherent access to the challenger's secret decryption/key-generation service. Each service decryption uses a new function key; it is not a persistent-key decryption oracle.

[DERIVED compatibility] From the *same* `A1` sampler define the two classical-quantum ensembles

```text
V_b = (L, R1, Y_b),
Y_b = (f_j(x_b; u_j))_{j=1..k}, with fresh independent uniform u_j.
```

[DERIVED] Require `V_0` and `V_1` to be quantum computationally indistinguishable for the resource bounds used below. Write `Delta_comp(T')` for their maximum output-probability gap against the required quantum postprocessors. Including the classical `x0,x1,F` in `L` is intentional: an adversary can retain copies of its classical choices, and reductions must preserve that view. `Z,R1` include the **complete exposed future-key package** and any permitted quantum state. No future key is silently removed from compatibility.

[DERIVED nonvacuity] Let `x0=(0,0)`, `x1=(0,1)`, `F=(first_coordinate,constant_ACK)`, and let `R1` contain any identical advice state in both experiments, even a two-qubit Bell state. The two `V_b` are identical, the plaintexts are distinct, and the first-coordinate function is nonconstant on the message space. This inhabits compatibility; it does not instantiate the cryptographic assumptions.

[SOURCE: game read] The timing, preissued keys and pre-challenge-only decryption oracle follow 2013/729 Definition 2.4 p.8. Its original states/adversaries are classical. Appendix C p.25, footnote 8, identifies independence of the **current** `(MPK,MSK)` from the prechosen functions as necessary. The quantum registers, advice convention and resource bounds above are our additions.

## 2. Exact primitive hypotheses

[DERIVED convention] Primitive advantages use the probability gap `|Pr[D=1|b=0]-Pr[D=1|b=1]|`, not the half-sized guessing advantage. Every computational hypothesis quantifies over quantum adversaries with the same one-copy advice convention, classical challenge objects, and retained quantum work state. Keys/coins drawn by a primitive challenger are fresh and independent of prior advice. All public algorithms are efficient classical circuits. The bounds below are evaluated at the reduction's actual time, space, circuit and query resources; none means “classically secure but apparently PQ.”

| Hypothesis | Exact requirement used |
|---|---|
| [DERIVED `QIO`] | A two-stage sampler outputs classical equal-size circuits `(C0,C1)` and one retained quantum register `R`. The challenger obfuscates `C_b`; a quantum continuation receives it and `R`. Let `E` be the mathematical predicate `C0 == C1` on **all inputs**. Require the qualified gap `abs(Pr[D=1 and E | b=0] - Pr[D=1 and E | b=1]) <= epsilon_IO`. The referee may evaluate `E` inefficiently; the adversary cannot. This explicitly permits bad-pair accounting: total gap is at most `epsilon_IO + Pr[not E]`. No primitive theorem establishing this quantum auxiliary-input form is imported. |
| [DERIVED `IO-CORR`] | For every allowed raw circuit `C`, with fresh obfuscation coins, `Pr[exists x: Eval(Obf(C),x) != C(x)] <= eta_IO`. Evaluation is deterministic once the returned classical circuit is fixed. The bound is uniform over circuits of the permitted size, so it also holds conditionally when an adaptive classical query chooses the next circuit. Perfect correctness is the special case `eta_IO=0`. |
| [DERIVED `QPPRF`] | A quantum sampler chooses a classical point `t` and retains `R` **before** the fresh PRF key `K`. The challenge is `(Puncture(K,{t}),v)`, where `v` is either `PRF(K,t)` or a uniform string; its gap is at most `epsilon_PPRF`. Puncturing preserves evaluation exactly at every other point. Discarding the punctured key gives the fresh-key, single-point PRF game also used below. Coherent PRF-oracle queries are unnecessary. |
| [DERIVED `QCOM`] | Perfect binding for every pair of distinct messages and all commitment coins; computational hiding gap at most `epsilon_COM` for a quantum two-stage chosen-message adversary retaining `R`. The construction here uses the noninteractive perfectly binding version, not the paper's optional two-round variant. |
| [DERIVED `QWI + NIWI-SOUND`] | NIWI has perfect completeness. After receiving its classical CRS, a quantum sampler may supply a classical statement with two valid witnesses and retain `R`; distinguishing the proof of either witness has gap at most `epsilon_WI`. This adaptive-auxiliary game is an explicit sufficient hypothesis; its minimality is not claimed. In addition, over CRS generation, probability that **any false bounded statement has any accepted bounded proof** is at most `nu_NIWI`. This global bad-CRS form is the statistical soundness needed for all-input circuit equivalence. |
| [DERIVED `QPKE`] | Perfect correctness for all honest keys/messages/encryption coins and total deterministic decryption. Adaptive chosen-classical-message IND-CPA against a quantum two-stage adversary with retained state has gap at most `epsilon_PKE`. The reduction needs one challenge ciphertext under one public key. |
| [DERIVED `QSUF`] | Perfect OTS verification correctness and quantum strong unforgeability with **at most one classical signing query**, allowing zero queries. Probability of outputting a new valid `(message,signature)` pair under the challenge verification key is at most `epsilon_SUF`. The bound covers the first qualifying event among adaptively observed classical queries. The privacy proof does not use this hypothesis when `qD=0`. |

[DERIVED scope of `QIO`] The qualified game is stronger and more explicit than merely quoting a fixed-circuit classical iO definition. It is the precise hypothesis used to handle statistically bad NIWI reference strings without an efficient test for circuit equivalence. Alternatively, a uniform worst-case auxiliary-state iO bound for every equivalent pair and every allowed residual state **conditional on that pair**, independent only of fresh obfuscation coins, implies the qualified bound by averaging over the sampler's classical output and its conditional residual state. This alternative does not require efficient preparation of each conditional state; its arbitrary-quantum-advice quantifier covers those states. That stronger bound is also an assumption here, not a sourced instantiation.

[DERIVED resource envelope] Let `T_A` include the adversary's use of every exposed future object. A reduction below runs `A1,A2,A3` once, plus at most polynomial honest work `W(lambda,S,qK,qD)` for setup, encryption, proof generation, key generation and query handling. Its time is at most `T'=T_A+W`, and its retained space is the adversary's state plus the corresponding honest workspace. All obfuscated programs have a common explicit padding bound `S`; they contain `f`, keys and fixed data, **never the adversary's circuit**. Primitive epsilons in the compact bound are suprema at that envelope; using separate per-transition envelopes gives a finer sum. No numerical security claim is made.

## 3. Normalized construction and the eleven hybrids

[SOURCE / DERIVED normalization] The local source hash is `58bb2eb72bc8e5c3eaf3193fefd6c72754ff428265231fb459b0de6c8db32e30`. A visual read of Figure 1 p.13 confirms its step 2 literally rejects “If Verify(...)”; this is not a text-extraction loss. Observation A.2 p.19 instead explicitly rejects when `Verify=0`, and its proof uses that meaning. This derived construction uses the latter intended predicate: **reject invalid signatures**. It does not claim the contradictory printed pseudocode is executable as written.

[DERIVED raw programs] Put `t=(c1,c2,vk)`. The ordinary key program `G_f^a` validates the signature and NIWI, decrypts `c_a` with `SK_a`, computes `PRF(K,t)`, and returns `f(x;PRF(K,t))`, for `a` in `{1,2}`. The simulated program `S_f^a` validates first, returns the hardcoded `Y_f` when `t=t*`, and otherwise decrypts `c_a`, evaluates the punctured PRF at `t`, and applies `f`. It contains only `(t*,Y_f)`, not the unused challenge proof/signature. All programs use the same parsing/default convention and padding.

[DERIVED timing normalization] The original real key has no challenge ciphertext. In every simulated key, only `t*` is needed for its comparison. Therefore the challenge proof may be formed as needed but the challenge **signature is sampled only immediately before release to A3**. Removing unused proof/signature literals in our choice of raw hybrid circuit changes no raw function, costs no additional real-world change, and makes the signing reduction below implementable. Before that release the permitted oracle must not reject `CT*` merely because it happens to equal a future challenge: there is no such exclusion in `IND_pre`.

[DERIVED hybrids] Fix a world index `b`, run `A1` once, and use `x=x_b` from its classical output. Do not condition on, or re-prepare, its retained quantum state. Sample challenge PKE components and `vk*` early, since none are released before A3; this is an order change of independent randomness. Use the source's `H0,...,H11` pattern, specialized to the above preissued-key game. `I_x=H11` is generated from ideal vector `Y=(f_j(x;u_j))_j`.

| Transition | Change and reduction | Loss for one world |
|---|---|---|
| [DERIVED `H0 -> H1`] | Replace each exposed `Obf(G_f^1)` by `Obf(S_f^1)`, with `Y_f=f(x;PRF(K,t*))`. At the special tag, perfect PKE correctness gives `Dec_1(c1*)=x`; elsewhere puncturing is exact. Validation agrees on every input, so the raw circuits are exactly equivalent. One `QIO` challenge per issued key; retain the original quantum state. | `qK * epsilon_IO` |
| [DERIVED `H1 -> H2`] | For each exposed key, replace its special-point PRF value by independent uniform coins, and compute `Y_f` from them. The punctured key and target are exactly the `QPPRF` challenge; target selection precedes that fresh key. Other keys and the full future package are reproduced around it. | `qK * epsilon_PPRF` |
| [DERIVED `H2 -> H3`] | Change setup commitment from `Com(0^len)` to `Com(t*)`. All PKE keys are known to the reduction; challenge proofs still use the real encryption witness, so a commitment opening is not needed to simulate either side. This is a one-challenge `QCOM` reduction. | `epsilon_COM` |
| [DERIVED `H3 -> H4`] | Switch the challenge NIWI from the real encryption witness to the opening of `Com(t*)`. Both witnesses are known and valid; pass the returned proof through the remainder of the experiment, signing it at release. `QWI` permits the retained quantum state and all correlated classical data. | `epsilon_WI` |
| [DERIVED `H4 -> H5`] | Replace `c2* = Enc(PK2,x)` by `Enc(PK2,0)`. Embed the `QPKE` challenge as `c2*`; build `Com(t*)` and its NIWI via the known trapdoor opening. Exposed simulated keys and oracle replies use `SK1`, so the reduction never needs the challenge secret `SK2`. | `epsilon_PKE` |
| [DERIVED `H5 -> H6`] | Switch each exposed simulated key from `S_f^1` to `S_f^2`. On a sound CRS, validity implies either both ciphertexts encrypt the same message or `t=t*`; perfect commitment binding proves the latter alternative unique. The special branch outputs the same `Y_f`; every other branch has equal plaintext. Use `QIO` with bad-pair probability at most `nu_NIWI` per switch. | `qK * (epsilon_IO + nu_NIWI)` |
| [DERIVED `H6 -> H7`] | Change each fresh-key oracle computation from `G_g^1` to `G_g^2`. Except on a bad CRS or accepted special-tag query, raw outputs coincide. Each side's fresh obfuscator may err, costing at most `2*qD*eta_IO`. A valid special-tag query before challenge release is an OTS forgery under `vk*` **before any signing query**; see below. | `d*(epsilon_SUF + nu_NIWI) + 2*qD*eta_IO` |
| [DERIVED `H7 -> H8`] | Change `c1*` to an encryption of zero. Embed the `QPKE` challenge under `PK1`; both the exposed simulated keys and decryption oracle now use known `SK2`. Trapdoor NIWI handles the challenge statement. | `epsilon_PKE` |
| [DERIVED `H8 -> H9`] | Switch the fresh-key decryption oracle back to `G_g^1`. The same sound-CRS/special-tag argument and uniform correctness coupling apply. | `d*(epsilon_SUF + nu_NIWI) + 2*qD*eta_IO` |
| [DERIVED `H9 -> H10`] | Switch every exposed key back from `S_f^2` to `S_f^1`. Both special ciphertext components now encrypt zero, but special-key outputs remain the same ideal `Y_f`. The soundness/binding argument again supplies all-input raw-circuit equivalence. | `qK * (epsilon_IO + nu_NIWI)` |
| [DERIVED `H10 -> H11`] | In each decryption query, replace evaluation of the fresh obfuscated `G_g^1` by its exact raw circuit, costing `eta_IO`. Then replace its fresh-key single-point PRF value by uniform coins using `QPPRF` with the punctured key discarded. Return `g(Dec_1(c1);u)` after the identical validity check. Each target may be adaptive, but is chosen before that query's fresh key. | `qD * (eta_IO + epsilon_PPRF)` |

[DERIVED] Here `d=1` if `qD>0`, otherwise `d=0`. When `qD=0`, transitions 6->7, 8->9 and 10->11 are identical experiments and incur zero loss. No signature unforgeability or obfuscator-correctness assumption is used by the remaining privacy hybrids. Correct evaluation of the **delivered** key programs is a separate functional claim below.

[SOURCE: proof correspondence] Source locations are §5.1-§5.2 pp.14-17; Claim A.4 and Lemma A.5 p.20; Lemmas A.6-A.8 p.21; Lemma A.9/Claims A.11-A.12 pp.21-23; Lemmas A.13-A.17 pp.23-24. The source labels A.13/A.15 “statistical” while invoking computational signature unforgeability. Our ledger charges the computational signature advantage explicitly and makes no statistical claim for that leg.

[DERIVED special-tag argument] Consider the first classical oracle query with `t=t*` and a valid signature. The reduction receives `vk*` from its OTS challenger, samples every other secret itself, and can generate every ordinary/simulated key because none needs the OTS signing secret. Until this event, it has made **zero** signing queries: no challenge signature appears in any exposed program or public message. The query contains a valid signature on `c1*||c2*||pi`. Output that pair as a forgery and stop. If the event never occurs, request the single signature on the actual challenge proof at release and finish the experiment. This is a valid at-most-one-query quantum forgery reduction, and its event bound covers all `qD` queries without a further `qD` factor. Extending the game to post-challenge decryption would need the explicit `CT != CT*` rule and the strong-forgery case; that extension is not claimed here.

[DERIVED quantum-state argument] Every primitive reduction consists of a quantum prefix, one classical primitive challenge, and a quantum continuation. It may pass newly generated public data to the adversary and monitor its measured API requests, but never reads, copies, rewinds, re-prepares or postselects the retained register. Selecting a hybrid index fixes a different reduction; it does not run one physical adversary eleven times. Thus arbitrary retained quantum state is allowed precisely where the hypotheses quantify it.

[DERIVED bad-event argument] Until the first bad CRS, special-tag event or incorrect internal obfuscation evaluation, coupled classical histories are equal and the same channels act on the adversary's register. Decomposing final states into their common good-history contribution and remaining bad histories bounds every final measurement's probability gap by the bad-history probability. This is a mathematical comparison of experiments, not a simulator that duplicates a quantum state. Uniform soundness/correctness and the union bound supply the displayed probabilities.

## 4. Resulting theorem and what correctness means

[DERIVED one-world bound] At the resource envelope above, put

```text
B(qK,qD) = 3*qK*epsilon_IO
         + (qK+qD)*epsilon_PPRF
         + epsilon_COM + epsilon_WI + 2*epsilon_PKE
         + 2*d*epsilon_SUF
         + (2*qK+2*d)*nu_NIWI
         + 5*qD*eta_IO .
```

[DERIVED proof] Add the eleven row bounds by the triangle inequality. This gives `gap(Real_x,I_x) <= B`. On each raw-circuit switch, the `QIO` qualified advantage contributes `epsilon_IO` and its exceptional probability contributes at most `nu_NIWI`; no efficient soundness/equivalence test is assumed. On oracle switches, a direct coupling contributes one global bad-CRS bound, one signature-event bound and both sides' fresh-object correctness bounds. This conservative sum does not claim optimal constants.

[DERIVED quantum `IND_pre` theorem] Let all primitive epsilons, `nu_NIWI` and `eta_IO` be negligible for the polynomial resources used, and let `V_0,V_1` satisfy compatibility. Then for every admissible quantum adversary in the stated game,

```text
gap(QIND_pre^cl(0), QIND_pre^cl(1))
    <= B_0(qK,qD) + Delta_comp(T_A+W_ideal) + B_1(qK,qD).
```

[DERIVED proof of the middle step] There is a *single* quantum postprocessor `J` that receives `(L,R1,Y)`, independently samples the current PKE keys/NIWI CRS and a challenge encryption of zero, commits to its challenge tag, builds the simulated keys from `Y`, and runs the adversary through the ideal oracle above. It never uses which plaintext index generated `Y`. Therefore `I_b=J(V_b)`. A distinguisher for `I_0,I_1` composed with `J` would distinguish `V_0,V_1` with exactly the same gap while consuming its input state once. Sampling and retaining current `(MPK,MSK)` inside `J` is permitted because its fresh coins are independent of `V_b`; future packages remain in `L,R1`. This proves the middle bound and the displayed theorem. With a common envelope, replace `B_0+B_1` by `2B`.

[DERIVED advantage convention] If the adversary guesses a uniform hidden bit, its usual advantage above one half is half the displayed probability gap. The bound is resource-indexed: recursive applications must propagate the compatibility postprocessor's runtime and description sizes, not treat `Delta_comp` as a security constant at the original adversary runtime. Horizon analysis belongs to the private-construction lane.

[DERIVED functional correctness] For `M` obfuscations honestly generated with fresh coins during a bounded execution, including issued keys and internal service keys, the uniform all-input premise gives

```text
Pr[at least one generated object disagrees with its raw program on some input]
    <= sum_{j=1..M} eta_IO(lambda,S_j).
```

[DERIVED] Independence between object choices is unnecessary: condition on the history selecting the next raw circuit, apply the uniform fresh-coin bound, and sum. A good issued key remains correct on every subsequent input, including every fork using that key, so evaluations of the same good object do not multiply this bound. For this game's execution, `M<=qK+qD`; additional honest public objects generated by a larger protocol require their own count. The privacy proof uses a different `5*qD*eta_IO` hybrid ledger because it compares multiple analytical oracle implementations.

[DERIVED boundary] Good-object correctness means agreement with `f(Dec(c1);PRF(K,t))`, including deterministic reuse of coins for identical tag/key calls. It does not claim fresh independent randomness for repeated evaluations of the same ciphertext/key, malicious-encryptor randomness robustness, authenticated ingress, recipient binding, finality or receipt security. Statistical soundness is used to justify program switches; honest ciphertext evaluation already has a real NIWI witness and perfect PKE correctness.

[OPEN instantiation] The theorem is conditional on the enumerated primitive games, including quantum auxiliary-state iO and quantum WI, perfect PKE/commitment/puncturing facts, and the chosen advice convention. The earlier audit did not establish these jointly from 2025/2215 or from LWE. This tranche therefore closes a **conditional reduction argument**, not the primitive-instantiation or whole-resident PQ claim.

## 5. Executed premise controls and resumption

[EXECUTED] `python3 research/learn_infer_only/experiments/pq_composition/qind_pre/functional_checks.py > research/learn_infer_only/experiments/pq_composition/qind_pre/functional_checks.stdout.txt` passed. Results are in [functional_checks.json](functional_checks.json). The finite model deliberately stores plaintext in its mock ciphertext and implements no cryptography. It checks 128 simulated-key all-input equivalence cases, exhibits unequal outputs after removing NIWI truth, and exhibits disagreement of the two unhooked oracle programs on the special tag. These are premise checks and falsifiers, not cryptographic evidence.

[EXECUTED] The same script verifies 289 `(qK,qD)` coefficient sums against the eleven-row ledger. A separate 16-input control has pointwise error `1/16` for every fixed input but all-input failure probability 1: each returned program exposes its one bad location. Reading that location lets an adaptive code holder find an error with probability 1. This explains why a merely pointwise average correctness statement is insufficient for the uniform object guarantee above.

[EXECUTED visual provenance] `pdftoppm -f 13 -l 13 -scale-to 1800 -singlefile -png /Users/ember/dev/gh/forks/IACR-eprint-mirror/2013/729.pdf research/learn_infer_only/experiments/pq_composition/qind_pre/renders/2013-729-p13` returned exit 0 with empty output; the PNG was inspected with `view_image`. The raw source hash is pinned above and in the parent source manifest. No PDF was downloaded. This tranche used zero SQL/schema/Kagi/web queries and installed no software.

[OPEN next] Independently review the qualified `QIO` and `QWI` games, the pre-release signature timing, and the resource-indexed compatibility postprocessor. Then seek a theorem instantiating that exact primitive suite or explicitly restrict the advice model. Keep the new theorem distinct from sourced PQ FE and from the remaining QROM/ingress/continuity work.
