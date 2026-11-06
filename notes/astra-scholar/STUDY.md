# Astra scholar — study and working judgments

2026-11-06. [READ] Research snapshot: `1fdf80cd3006baba5e41661e2b59f7382a4bac8f` on `dev`. These are research claims, not a shipped custody system. `docs/VERDICTS.md` is unchanged; corrections here are proposals to its maintainer.

[READ] I read README, then the scheme decision in full (including the unusually ordered §§9/8), the complete C1–C23 program, foundations critique, tradeoff space, Codex synthesis, Astra response, and cross-limb-binding. I then read the harness README, `e2s_proof.py`, `cosnark.py`, `he_matvec.py`, `step_counts.py`, `cert_b61.py`, the FS and encoding falsifiers, recorded results and original experiment logs; followed by the prior Astra statement/experiment audits and watch log. Supporting reads include `bfv_ref.py` and `spdz.py`. Read scope distinguishes source code, saved execution reports, conditional theorems, and proposed constructions.

[READ] I read `Selvage/AuditSampling.lean` in the companion checkout and the complete `AuditDisplacement.lean` at commit `6841009788e86849eabf7f4a025c518ec4400f3b` via `git show`. The latter file is absent from the current working checkout and local `main`; a local all-ref path log finds the displacement branch. I did not modify/fetch/switch the companion tree or infer that the user's remote-main statement is false. Finally I read the dated dark-learning §9 of VERDICTS, including its encoding and FS corrections.

[READ] The theorem actually available is conditional: `AuditSampling.lean:585` `Round.sequential_bound`, and committed `AuditDisplacement.lean:106` `Round.displacement_bound`. Both require per-history detection; the latter also caps actual and honest updates, covers semantic corruptions, and counts the alarming round. It bounds injected displacement, not final model distance, confidentiality, or the welfare of a computation. A real protocol still owes the premises and a whole-run computational failure budget.

## What survives the study

[INFERRED] Computing and proving inside custody is the right architectural direction when no host should hold readable weights. The cheap plaintext algebra belongs where its witness lives. Keeping the BFV keys with custodians avoids exporting the model's reusable evaluation object. Neither fact alone realizes a private protocol: all public transcripts, auxiliary keys, aborts, and preprocessing must be covered.

[READ] The exact integer learner and separate adversarial verifiers are substantial progress over candidate count formulas. The previous FS attack was correctly actionable: free quotient witnesses must be fixed before the evaluation point. Hashing the witness in a transparent reference checker is useful evidence of order; a ZK implementation instead hashes hiding commitments and proves their openings consistently.

## What I doubt, and will try to break

1. [READ/INFERRED] `HEMatvec` sends **secret-key** `encrypt_exact` ciphertexts, whereas its priced two-equation `u,e0,e1` proof describes **public-key** encryption. The six-gigabit figure does not identify a matching proof system, hiding mechanism, knowledge reduction, or exact-scaling relation. The proof must cover a fixed valid key, all limbs, plaintext layout, bounded error, and complete context; knowledge of bounded coins is not proof of honest randomness.
2. [INFERRED] Flooding the first ciphertext component by forty bits over one noise estimate cannot simply be called forty-bit circuit privacy. The second component is observable to the key owner; the whole ring and all block sums/returns matter. A phase smudging bound and a simulation of the entire ciphertext are different obligations.
3. [READ/INFERRED] Dealer output size is not dealer generation cost. Matrix and outer correlations, powers of one mask, and correlated truncation bits cost different protocols. Calling the remaining idealization “the same object in both forks” does not make its unequal quantities cancel.
4. [READ/INFERRED] The Freivalds code hashes a suffix of the authentication transcript, and the chain checks weight roots. Neither interface yet describes a durable, context-bound state machine. I will distinguish an algebraically valid edge from authorization, replay protection, and atomic acceptance.
5. [READ/INFERRED] The collaborative proof is presently a linear-algebra spine with non-ZK openings. Its source already says so. Its arithmetic counts cannot establish the fully private full-step verdict; the live Claude successor owns gates, ZK, and custody handover, so this run will not duplicate them.

## Work partition and evidence rules

[READ] Four scholars own disjoint files: ZKPoPK, circuit privacy, preprocessing, and independent rederivation/attacks. I integrate and write the welfare statement/report. Only `notes/astra-scholar/` and new `scholar_` harness files are written. Changes to other lanes are supplied as patches. Parent alone serializes named-file commits and pushes to `origin/dev`.

[MEASURED] Initial Mac available space was 283 GiB, above the 30 GiB threshold (`df -h /System/Volumes/Data`). No large computation ran during study. N=8192 batches, if necessary, use hbox under `swarm-build`, an 8–12 GB cap, PID files, and the 30 GB root-free-space gate. No external search was used for this study deliverable; literature reads belong to their subsequent bricks.

[OPEN] A deployable ZKPoPK and a whole-transcript confidentiality proof are not promised by passing a witness-checking harness. Where a proposed brick is unsound, the output will include its falsifier, a useful replacement, and a precise unfinished interface.
