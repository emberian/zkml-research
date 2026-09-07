# Completion of the conditional QIND_pre review

[DERIVED status; 2026-09-07 UTC] **The conditional lemma passed bounded independent source/proof review: no blocking error was found in its eleven hybrid transitions under its explicit primitive hypotheses.** This completes review of a derived reduction, not a source-backed primitive instantiation. The first remaining instantiation gap is the exact quantum auxiliary-state `QIO` game; the remainder of the named suite also remains uninstantiated by this audit. No PQ-from-LWE or whole-resident PQ conclusion follows.

## Reviewed bytes and responsibility

| Role / artifact | Attributed status |
|---|---|
| [REPORTED] Derivation author and completion recorder | `/root/pq_composition`. The checks and explanations in this completion note are author-side work, not independent review. |
| [REPORTED] Independent source/proof reviewer | `/root/restricted_private_step`, a separate agent that read the source and reviewed the frozen argument. Its direct final message confirms no blocking error across all eleven transitions, subject to the stated hypotheses and API scope. This is role attribution, not a cryptographic signature or external peer review. |
| [EXECUTED] Frozen reviewed artifact | [QIND_PRE_LIFT.pre-closeout.md](QIND_PRE_LIFT.pre-closeout.md), SHA256 `78b5140be6fd2b2cd7d15706eabad4ee2da476b437ef310f1feb77ec5d3dbd66`. |
| [EXECUTED] Current display artifact | [QIND_PRE_LIFT.md](QIND_PRE_LIFT.md), SHA256 `e36e7a17bfd1660d6ac41b6050b9217adc3e441a8fb86288d7a2ab35b2242d10`. It consists of one later `[OPEN closeout]` status paragraph followed by the exact reviewed bytes. Neither file was changed during this completion tranche. |
| [REPORTED] Reviewer report location | The reviewer confirmed it will not create a separate `REPORT.md` because its next assignment is practical E2E work. This note records its direct final conclusion; it does not claim that an absent report exists. |

[REPORTED independent final conclusion] The reviewer confirmed: the qualified `QIO` assumption is a deliberately stronger sufficient hypothesis and must remain explicit; joint `V_b` includes the complete correlated future package and residual quantum state; the postprocessor `J` runs once without cloning, conditioning or re-preparing that state; delayed signing and minimal simulated programs make a prechallenge valid special-tag request a zero-signing-query forgery, including a request equal to the eventual challenge; and the `5*qD*eta_IO` and `(2*qK+2*d)*nu_NIWI` coefficients are consistent with the stated game. It identified one nonblocking conservatism: the `H8 -> H9` signature term is unnecessary because both special ciphertext components already encrypt zero, but retaining it keeps the bound valid. It did not establish the primitive suite, full quantum SIM, coherent decryption or implemented PQ FE.

## Exact accepted conditional statement

[DERIVED] Retain the game and hypotheses of the frozen note without amendment. The adversary has one arbitrary polynomial-qubit advice state, independent of fresh current setup/challenge coins, and retains its quantum workspace throughout. Messages and functions are chosen before current setup. Function keys are preissued. There are at most `qD` measured classical decryption requests before the challenge, each served using a **fresh** function key; no external key/decryption requests occur after challenge release. Public classical key code may be copied and evaluated locally, including reversibly in superposition. Coherent access to the secret service is outside this theorem.

[DERIVED] For `d = 1[qD > 0]`, the exact retained one-world bound is

```text
B(qK,qD) = 3*qK*epsilon_IO
         + (qK+qD)*epsilon_PPRF
         + epsilon_COM + epsilon_WI + 2*epsilon_PKE
         + 2*d*epsilon_SUF
         + (2*qK+2*d)*nu_NIWI
         + 5*qD*eta_IO.

gap(QIND_pre^cl(0), QIND_pre^cl(1))
    <= B_0(qK,qD) + Delta_comp(T_A + W_ideal) + B_1(qK,qD).
```

[DERIVED] `gap` is an output-probability difference. Usual guessing advantage above one half is half this bound. Each primitive error is evaluated at the actual reduction's circuit, time, space and query resources, bounded in the frozen note by the corresponding polynomial honest-work envelope. With common resources, `B_0+B_1 <= 2B`. This is an asymptotic conditional bound, with no numerical security parameters supplied.

[DERIVED zero-oracle specialization] For the private ladder's `qD=0` specialization, transitions `H6 -> H7`, `H8 -> H9` and `H10 -> H11` are identical experiments. The one-world privacy bound becomes

```text
B(qK,0) = 3*qK*epsilon_IO + qK*epsilon_PPRF
        + epsilon_COM + epsilon_WI + 2*epsilon_PKE
        + 2*qK*nu_NIWI.
```

[DERIVED] No signature-unforgeability or obfuscation-correctness error is charged by these remaining privacy hybrids. Correct functionality of delivered keys is still a separate claim. This single-instance review does not prove the resource accounting of a growing-horizon ladder.

## Assumptions still requiring an instantiation

[DERIVED audit scope] “Uninstantiated here” below means this source audit and conditional proof have not supplied a theorem establishing that exact interface. It is not an absence claim about the literature. All computational games retain quantum state and use the frozen note's one-copy advice convention.

| Named premise | Required fact and unresolved instantiation |
|---|---|
| [OPEN] `QIO` | The sampler outputs equal-size classical circuits and a retained register before the challenge bit. With `E` denoting all-input equivalence, the **qualified** distinguishing gap on `E` is at most `epsilon_IO`. The full gap is then at most `epsilon_IO + Pr[not E]`. An alternative worst-case formulation must cover arbitrary residual states conditional on the circuit pair, independent only of fresh obfuscation coins, uniformly over all permitted pairs/states. No source-backed theorem establishing this precise interface was supplied. |
| [OPEN] `IO-CORR` | Fresh obfuscation of every permitted raw circuit has uniform probability at most `eta_IO` of disagreeing on **any** input. A pointwise statement is insufficient for the delivered-object guarantee. The derived proof accommodates this error; it does not instantiate the full `QIO + IO-CORR` pair. |
| [OPEN] `QPPRF` | Quantum punctured-point indistinguishability with a classical target chosen before the fresh key, retained state, and exact off-point evaluation. The fresh-key one-point PRF step discards the punctured key. No iO/OWF-to-PPRF quantum reduction was imported. |
| [OPEN] `QCOM` | Quantum chosen-message hiding, together with perfect binding for all messages and coins. No jointly compatible concrete commitment family was established here. |
| [OPEN] `QWI + NIWI-SOUND` | Quantum witness indistinguishability for adaptively chosen post-CRS classical statements/two valid witnesses and retained state; perfect completeness; and a global bad-CRS probability `nu_NIWI` that any bounded false statement has any accepted bounded proof. Ordinary computational soundness alone does not establish the all-input equivalence premise. No iO-to-NIWI quantum construction was imported. |
| [OPEN] `QPKE` | Quantum adaptive chosen-classical-message IND-CPA with one challenge, retained state, and perfect correctness for all honest key/message/encryption-coin choices. No simultaneous implementation satisfying the complete suite was supplied. |
| [OPEN] `QSUF` | Quantum strong one-time unforgeability with at most one classical signing request, including zero requests, and perfect verification correctness. Its unforgeability premise is used only when `qD>0`; the derived signing schedule is not an instantiation of a signature scheme. |

[SOURCE: theorem/definition/reduction read in initial audit] The inspected local version of 2025/2215, Theorem 2 p.3, gives its standard-model PQ iO claim conditional on PQ subexponential **LWE and average-case iO**. Definition 6 p.16 and Lemma 5 pp.18–20 use the stated classical auxiliary data interface; Definition 3 p.10, Lemma 4 p.18 and Corollary 1 p.11 track nonzero all-input correctness error. That theorem does not by itself discharge the qualified quantum-auxiliary game above or the entire downstream suite. The pinned version and exact access record remain in [source_manifest.json](../source_manifest.json) and [ACCESS_LOG.md](../ACCESS_LOG.md).

[SOURCE: original construction/game/reduction read] 2013/729 Definition 2.4 p.8 is the classical source game; §4 pp.12–14 gives the primitive construction; §5.2 pp.15–17 and Appendix A pp.19–24 give the eleven-hybrid proof; Appendix C p.25 footnote 8 records the current-key independence requirement. The quantum game and error-tolerant proof are our derivation, not a theorem attributed to those pages. The normalization rejects **invalid** signatures, following Observation A.2 p.19; Figure 1 p.13 prints the contradictory predicate, as visually checked in the earlier tranche.

## Three premises that cannot be weakened silently

[DERIVED all-input correctness] For `M` honestly generated obfuscations with fresh coins, the proved object guarantee is `Pr[exists generated object wrong on some input] <= sum_j eta_IO(lambda,S_j)`. Adaptive choices of raw circuits are covered by the uniform conditional bound; independence between choices is unnecessary. Here `M <= qK+qD`. Repeated evaluation or forks of a good object do not create new correctness events. This actual-execution count is distinct from the analytical `5*qD*eta_IO` privacy-hybrid sum. A fixed-input correctness probability cannot replace it when a holder can inspect the code and select a bad input.

[DERIVED joint compatibility] The required ensembles are `V_b=(L,R1,Y_b)`, with the same one-time `A1` prefix, `L` containing both chosen messages, functions and the full exposed future-key package, and `R1` its retained quantum state. Fresh independent ideal coins generate `Y_b`. The middle reduction applies one common postprocessor `J` to this entire joint input, samples the **current** setup independently inside `J`, and consumes its state once. Separate indistinguishability of output and auxiliary marginals is insufficient. The future package may be correlated with the prefix, but current setup randomness must retain the independence required by the game.

[DERIVED delayed-signing OTS] A simulated program contains `(t*,Y_f)` and necessary keys/public data, without an unused challenge-signature literal. The signature is requested only immediately before challenge release. The first valid classical prechallenge query at `t*` therefore supplies a valid pair after zero signing queries, even if it equals the eventual challenge. The reduction outputs that pair and stops; otherwise it requests the one allowed signature at release. This first-event argument covers all requests without an additional `qD` factor. Eager signing would invalidate the zero-query explanation for the exact future challenge. Postchallenge service requests require a different game and are not covered.

## Saved evidence and completion boundary

[REPORTED / EXECUTED provenance] The independent reviewer saved [controls.py](../../adversarial_review/qind_pre/controls.py), [results.json](../../adversarial_review/qind_pre/results.json) and [stdout.txt](../../adversarial_review/qind_pre/stdout.txt), pinned to `78b5140...`. They record 3,125 exact rational qualification cases, a challenge-dependent-qualification falsifier, an exact joint quantum-auxiliary marginal counterexample, a symbolic delayed-signing control, and a common-substate bad-history control. These finite premise controls are not a cryptographic theorem checker or a quantum FE implementation.

[EXECUTED author-side verification] The command below exited 0. [review_completion_check.json](review_completion_check.json) and [review_completion_check.stdout.txt](review_completion_check.stdout.txt) retain its output. It checked both note hashes and the byte-identical body, the reviewer script/results/stdout and primary PDF provenance, and replayed the four pure control functions with results identical to the saved results. It did not invoke the reviewer's file-writing `main`, alter its artifacts, or count this replay as another independent review.

```sh
python3 research/learn_infer_only/experiments/pq_composition/qind_pre/review_completion_check.py > research/learn_infer_only/experiments/pq_composition/qind_pre/review_completion_check.stdout.txt
```

[EXECUTED accounting] This completion tranche used zero SQL, schema, web or Kagi queries and zero network PDF downloads. It edited only this completion note and its targeted verification script/results. Frozen proof files, reviewer files, shared ledgers, companion trees and commits were left untouched.

[DERIVED completion boundary] Record the eleven-hybrid conditional lemma as independently reviewed with no blocking error found. The next theorem obligation for a sourced PQ instantiation is the exact primitive suite above, starting with quantum auxiliary-state iO. Neither finite horizon nor this review discharges that obligation. Full quantum SIM, coherent secret APIs, two-input ingress, authenticated release, whole-resident composition and QROM receipt security remain outside this result.

[SOURCE: repository game read] The assumption ledger in [SECURITY_GAME.md](../../../SECURITY_GAME.md) scopes the existing receipt proof to uniform-field classical ROM. This completion note makes no change to that separate statement.
