# Does 2025/2215 instantiate the accepted quantum-advice interface?

[DERIVED decision; 2026-09-07] **The main aviO-to-xiO reduction lifts to one-copy quantum advice under explicit quantum-advice versions of its classical primitive games. A complete source-audited instantiation of full quantum-advice iO from the advertised LWE-and-aviO assumptions is not established by this tranche.** The remaining obligation is the advice/resource contract through the cited xiO bootstrap and its base primitives. It is not a need for quantum-valued aviO `KeySamp`, nor an obstacle caused by the qualified equivalence event.

[SOURCE / scope] Six directly relevant local PDFs were read at the locations below and pinned in [audit.json](audit.json). The question is the exact interface in the [accepted QIO lemma](../qio_interface/QIO_INTERFACE.md), not whether the paper claims post-quantum security: it expressly does. This note separates that source claim from the stronger model and reductions actually audited here. It does not refute the paper's theorem or claim a literature-wide absence.

## Required endpoint and premise interpretation

[DERIVED endpoint] The endpoint is worst-case security for every polynomially bounded sequence of equivalent, equally padded **classical** circuit pairs, against a nonuniform quantum circuit family with one arbitrary polynomial quantum advice state independent of fresh obfuscation coins. Fix circuit, runtime, workspace and advice bounds before taking the uniform advantage envelope. The public output is classical code, so a quantum adversary may compute reversibly with it. No coherent secret service or random oracle is introduced.

[SOURCE: statement/game read] [2025/2215](https://eprint.iacr.org/2025/2215), Theorem 2 p.3, claims standard-model iO from subexponentially secure LWE and average-case iO, with a PQ extension when both assumptions are PQ. Its accompanying explanation says the reduction is straight-line with one adversary invocation. Definition 3 p.10 nevertheless prints a PPT adversary, and Definition 6 p.16 does not give an explicit nonuniform-quantum-advice or quantitative subexponential convention. These omissions require a stated interpretation; the occurrence of “PPT” alone is not a proof that the claimed extension fails.

| Contract for the main transform | Exact interpretation used here |
|---|---|
| [HYPOTHESIS `AVI_QA`] | Definition 6's **classical** keyed-circuit, `KeySamp`, `Sim`, auxiliary-data and precondition-to-postcondition interface holds against distinguishers with one arbitrary independent quantum advice state. Fixed outer circuit descriptions and row indices may be classical nonuniform parameters, or explicit public classical inputs to uniform sampler/simulator algorithms. No quantum output from `KeySamp` or `Sim` is required. |
| [HYPOTHESIS `SMS_QA`] | Definition 1 p.9's encoding-key hiding game holds against that advice model, uniformly over the selected classical messages/circuits and resource bounds. Vector correctness has uniform error `delta_SMS`. Definition 2 p.10 supplies statistical equivocation with distance `nu_eq`. |
| [HYPOTHESIS efficiency/correctness] | Use Definition 6's required `|C|*poly(lambda)` aviO size directly, and the perfect aviO correctness assumed by Lemma 4. The optional Appendix B efficiency compiler is not silently imported; using it would require its PRF/blind-garbling games to be audited too. |

[DERIVED advice interpretation] For a fixed outer pair `C0,C1`, its advice `rho` is independent of the fresh SMS/aviO coins. Thus the precondition can remain a distribution of classical strings tested by a quantum distinguisher carrying `rho`. The accepted worst-case interface lemma later handles a sampled FE pair and its correlated residual state. Demanding a quantum-valued aviO key sampler at this point would reintroduce the error corrected by that lemma.

[OPEN classical parameter convention] The proof hardwires arbitrary outer circuit descriptions into `G_k`, the keyed circuit family and its simulator. If “PPT KeySamp/Sim” is interpreted as uniform algorithms taking only `1^lambda` with no such public/nonuniform circuit parameters, that closure must be stated separately. This is a classical parameter issue already present in the worst-case proof, not an extra quantum-state sampling requirement.

## What the main construction actually does

[SOURCE: construction read] Section 6.1 p.17 writes the circuit truth table as `ell` rows of `m` bits, with `ell=m=sqrt(N)`. The output contains `hk,y,r` and one `(ek_i, aviO(D_i))` per row. The classical circuit `D_i(j)` computes `Dec_j(td_i,h) XOR C(i,j)`; evaluation combines this with the public SMS encoding bit. Section 6.3 p.18 explicitly restricts the proof to `N=poly(lambda)`, sufficient for the cited bootstrap.

[DERIVED core theorem] Assume the three main-transform contracts above, at the resources described below. For any fixed equivalent pair and independent advice, the following precondition proof and postcondition reduction are valid quantum experiments.

| Source step, pp.19–20 | Audited operation and loss |
|---|---|
| [DERIVED] `P0 -> P1` | Replace the row's decomposable decryption outputs by its public SMS encoding outputs. Under vector correctness the classical views differ with probability at most `delta_SMS`; adjoining the same independent advice preserves the statistical bound. |
| [DERIVED] `P1 -> P2`, Claim 4 | Challenge SMS on the fixed classical inputs `Z,G_k`, generate `y,r` and the row using the received key, then call the quantum distinguisher once. Loss `epsilon_SMS` at its actual augmented resources. |
| [DERIVED] `P2 -> P3` | A second vector-correctness replacement costs at most `delta_SMS`. |
| [DERIVED] `P3 -> P4`, Claim 5 | Use alternate hash setup and equivocation. Uniform statistical distance costs at most `nu_eq`, also after adjoining advice and applying the classical remainder of the experiment. |
| [DERIVED] Final reorder, printed as a second `P4` | Draw the uniform row first, then derive `y` using the generated decryption row. The resulting classical joint distribution is identical. This is an equality of distributions, not a procedure conditioning, measuring or preparing quantum advice. |

[DERIVED precondition bound] Consequently, for this classical sampler/simulator pair,

```text
Delta_pre <= 2*delta_SMS + epsilon_SMS + nu_eq.
```

[DERIVED] Here `delta_SMS` denotes the complete-vector correctness error in Definition 1. A merely per-coordinate bound would instead require the corresponding row-length union factors. All terms are uniform over the admitted fixed classical parameters.

[DERIVED postcondition] `D_k` and its replacement differ only by `C0(k,j)` versus `C1(k,j)`, hence are exactly equivalent on every `j`. Invoke `AVI_QA`, then generate all other rows from the classical auxiliary tuple `(y,r,hk,ek_k)` and fresh coins. The reduction retains the original advice and invokes the final adversary once. Thus, **once the aviO precondition promise applies**, the xiO gap is at most

```text
Delta_xiO <= sum_{k=1..ell} epsilon_aviO,k
          <= ell * epsilon_aviO  = sqrt(N) * epsilon_aviO.
```

[DERIVED promise boundary] Definition 6 is a precondition-implies-postcondition assumption. It does not supply a numerical function translating an arbitrary precondition gap into a postcondition gap. The displayed precondition error is therefore an eligibility check for the aviO assumption, not an extra term that can automatically be added to the final xiO bound. A subexponential application must specify which precondition advantage/time guarantees qualify for the asserted subexponential postcondition guarantee.

[DERIVED resources] A precondition distinguisher gains the work of generating a row, at most `m` decomposable decryptions and the corresponding SMS calls. A postcondition distinguisher gains at most `ell-1` other aviO calls and the public setup work. These are `poly(lambda,N,|C|)` for the stated `N=poly(lambda)` regime. Runtime is `T_A+W`, the original advice is used once, and work registers grow by the honest computation's workspace. Classical descriptions/row indices are included in the nonuniform description budget. No circuit contains or evaluates the distinguishing adversary.

[SOURCE normalization] Claim 5 p.20 prints `(ek_k,td_k) <- Enc(hk,G_k)` although the required typed algorithm throughout §6 is `KeyGen`. The audited reduction uses `KeyGen`. The duplicated `P4` label is distinguished above as the final reorder. Neither local pseudocode issue is treated as a theorem-level refutation.

## The full-iO bootstrap is a separate chain

[SOURCE / DERIVED audit] The table records the exact dependency edges read. “One continuing adversary” describes the inspected wrappers; it does not assert that every underlying LWE construction has already been proved secure in the required quantum-advice game.

| Dependency and source access | What is established or remains required |
|---|---|
| [SOURCE] 2025/2215 Lemma 1 / Corollary 1 p.11 -> [2016/006](https://eprint.iacr.org/2016/006), Theorem 7 p.11 | The full-iO step passes through succinct FE, weakly sublinear compact FE and [2015/720](https://eprint.iacr.org/2015/720). The 2016 preliminaries pp.4–7 explicitly use classical `nuPPT` and circuit adversaries. A quantum-advice reading of Theorem 7 is not literally supplied by those definitions. |
| [DERIVED] 2016/006 Theorem 6, complete construction/hybrids pp.9–11 | Given quantum-advice-secure static single-key succinct FE, puncturable PRF and xiO, the displayed transformation carries advice unchanged. For `s` padded output positions it uses two xiO switches, two punctured-PRF switches and one FE challenge per position, plus two boundary xiO switches: a conservative bound is `(2s+2)*eps_xiO + 2s*eps_PPRF + s*eps_sFE`, at `T+poly(lambda,|m|,s)` resources. The function/message pair is fixed before current FE setup. This is a conditional lift of the written transformation, not a derivation of its inputs from LWE. |
| [SOURCE / DERIVED] 2015/720 Theorem 12 pp.32–34 and Theorem 11 pp.30–31 | FE-to-RE generates a classical simulated encoding using FE and a PRG; composition invokes classical `Sim1,Sim2`. Theorem 12 explicitly charges polynomial simulation work and a factor-four security loss. The same wrappers accept one continuing quantum distinguisher under quantum-advice FE/PRG/RE games. No adversary state is passed to a simulator for duplication. |
| [SOURCE / OPEN] 2015/720 Theorem 13, construction/proof sketch pp.35–36, and Theorem 15 p.37 | Circuit iO uses a tree of classical encoding-generating programs and independent public setups by level. The proof needs joint security with the exposed later public-key package. Its child-output switch also needs pseudorandom child coins replaced by independent coins, as made explicit in §4.1 pp.22–23. The sketch is compatible with one-copy advice, but a complete quantum-advice quantitative restatement of this bridge is not claimed here. |
| [SOURCE / OPEN] 2016/006 Theorems 3–4 p.6; [2012/733](https://eprint.iacr.org/2012/733), Theorem 3.1 / Corollary 3.2 pp.20–22 and Lemmas 3.9–3.11 pp.26–29 | The initial succinct FE depends on FHE, one-time garbling and ABE. The explicit FE reductions forward state through FHE/garbling/ABE challenges and finally call the distinguisher. This establishes the relevant game interfaces to strengthen. It does not by itself prove the underlying LWE-based ABE, FHE and garbling constructions against quantum advice at the needed subexponential parameters. |
| [SOURCE / OPEN] [2014/917](https://eprint.iacr.org/2014/917), §4 / Theorem 3 pp.12–14 | The depth bootstrap uses shallow weak PRFs, symmetric encryption with pseudorandom ciphertexts and shallow randomized encodings. The printed direct theorem is private-key; it states that an essentially identical public-key transformation applies. These primitive games and the required public-key specialization remain obligations in a full quantum-advice instantiation. |

[DERIVED first remaining full-instantiation premise] After accepting `AVI_QA` and `SMS_QA`, the main xiO interface is discharged. To conclude the requested full iO from **LWE plus aviO alone**, the next concrete missing premise is a quantum-advice/subexponential version of **2016/006 Theorem 7 with its cited base-succinct-FE and FE-to-iO dependencies**, including their public-key game, advice, resource and correctness conventions. This audit identifies the wrappers and their primitive inputs; it does not replace that obligation by assuming all those primitives and then calling the result “from LWE.”

## Subexponential resources and uniform correctness

[SOURCE: parameter definitions read] 2016/006 Definitions 3 and 7 pp.6–7 use a common constant `kappa>0` with adversary size at most `2^(lambda^kappa)` and gap at most `2^(-lambda^kappa)`. The strengthened application must state the allowed quantum workspace/advice alongside that size. 2015/720 §2 pp.7–8 and Theorem 12 pp.33–34 retain explicit size budgets and subtract polynomial honest-work overhead. An unspecified negligible quantum gap is not this quantitative premise.

[DERIVED parameter compatibility] Polynomially many rows and polynomial reduction overhead preserve stretched-exponential security after shrinking a common exponent if needed. The full-iO tree and all-input correctness incur exponential-in-input-length losses. If such a bridge costs at most `2^(a*eta)*poly(lambda,|C|)` for a fixed `a`, choosing `eta=lambda^gamma` with `gamma` strictly below every relevant security/correctness exponent makes those losses dominated. This is an algebraic sufficient condition, not an extracted concrete parameter set or a completed proof of every inherited resource bound. Ordinary worst-case polynomial quantum advice remains permitted; any stronger advice-size convention must be stated rather than hidden inside “subexponential.”

[SOURCE correctness] 2025/2215 Definition 3 p.10 is an **all-input** correctness event. Lemma 4 p.18 proves xiO error at most `N*delta_SMS` assuming perfect aviO correctness. Lemma 1 / Remark 1 p.11 give the full-iO propagation factor `2^eta*poly(eta)`, by a union bound over inputs and xiO uses. Theorem 3 p.10 and Corollary 1 p.11 use `delta_SMS <= 2^(-lambda^a)`, `0<a<1/2`, and choose an input exponent below `a`. The formulas were visually checked against the local PDF.

[DERIVED error-tolerant accounting] If the underlying aviO instead has uniform fresh-object all-input error `delta_aviO`, a conservative extension of the main construction's bound is

```text
delta_xiO <= N*delta_SMS + ell*delta_aviO,
delta_iO  <= 2^eta * poly(eta) * delta_xiO
```

[DERIVED / OPEN] The second line uses the cited bootstrap's otherwise-correct primitive hypotheses. Any additional base-FE/RE correctness errors require their own propagation. Perfect aviO sets its contribution to zero. Merely negligible `delta_aviO` need not keep this **bound** negligible after the exponential factor; this observation is not a counterexample to the actual scheme's correctness. The final object guarantee must remain uniform over allowed circuits and all inputs, not just over a fixed query. It can then feed the already reviewed FE correctness union bound.

## Bounded conclusion and evidence

[DERIVED supported implication] With the explicit classical-parameter `AVI_QA` promise, `SMS_QA`, statistical equivocation, and the stated efficiency/correctness contracts, §6 produces worst-case quantum-advice xiO on logarithmic-input classical circuits, with the displayed resource-indexed gap and all-input error. This is a proved conditional lifting of the inspected main algorithm.

[OPEN full advertised-instantiation interface] The paper's PQ standard-model claim is stronger than the conditional xiO prefix audited here. To mark it as a source-audited instantiation of our accepted QIO interface, its PQ assumptions and inherited bootstrap still need the exact quantum-advice/subexponential interpretation above. No quantum-valued key sampler, weak extractor, QROM assumption, or new LWE-only iO construction is proposed. The remainder is a named theorem-premise audit, not evidence that such an instantiation is impossible.

[EXECUTED] `python3 research/learn_infer_only/experiments/pq_composition/qio_instantiation/audit.py > research/learn_infer_only/experiments/pq_composition/qio_instantiation/audit.stdout.txt` exited 0. The [script](audit.py), [manifest](audit.json) and [stdout](audit.stdout.txt) retain twelve successful extraction/metadata commands and all six hashes. Sixty-four arithmetic checks verify the conditional Theorem 6 coefficient sum; they do not verify cryptographic security. [ACCESS.md](ACCESS.md) records exact source access and the two metadata searches. Zero SQL/schema/Kagi queries, zero PDF downloads, no installs, no shared-file/companion/frozen-proof changes and no commits.
