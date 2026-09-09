# Teaching arithmetic for the live nonlinear learner

[DERIVED] The complete teaching update reuses the existing compiler-generated four-prime paired-MAC circuit and native witness plans. No new AIR, emitter, or witness executor is needed. `BfvTeachingUpdate.updateSound` proves that every accepted, correctly bound full update forces `next = acc + fresh - old` componentwise modulo each actual prime. `learnThenInferSound` substitutes that forced model into the completed generic Infer contract.

[SOURCE] The native operation is `acc += fresh`, followed by optional `acc -= old`, in `research/learn_infer_only/experiments/end_to_end/nonlinear_successor_2026_09_08/crypto/src/main.rs:55`. Issuance has already encrypted the example into its chosen lane. Teaching itself does not multiply a lane mask. The live lane selected one teaching per class and no expiry; the theorem also supports explicit subtraction. No-expiry old is the literal zero coefficient tensor, not an independent encryption of zero.

[DERIVED] At each prime and NTT index the shared 97-column MAC tuple uses the following sixteen words, each encoded with six radix512 digits after rowID:

| Role | Words |
|---|---|
| Shared D | fresh0, fresh1, old0, old1 |
| First output K | 1, 0, q−1, 0 |
| Second output K | 0, 1, 0, q−1 |
| Addends | acc0, acc1 |
| Outputs | next0, next1 |

[DERIVED] The existing source still constrains every word's canonical range. The public binding fixes all constants and operand roles. `signedReduction` proves the positive-modulus identity turning multiplication by q−1 into signed subtraction; it is not a finite runtime comparison. `operandSound` applies it to both MAC outputs. `updateRow_sound` consumes the existing `BfvKeyswitchRow` accepted source theorem, and `updateSound` quantifies over all four primes and every one of 8192 NTT positions. Eight 4096-row chunks therefore cover all 65,536 output residues of a two-component update. `ARTIFACT_REUSE.json` gives the exact existing template/plan/executor paths and hashes.

[DERIVED] `historySound` proves induction over any finite sequence of accepted ciphertext updates. `learnThenInferSound` needs neither saved input hashes nor an old-data specialization: the completed Infer theorem already quantifies over the caller-selected model, query and public evaluation key. This statement is about the bound ciphertext arithmetic. Authorization, lane choice, issuance validity and FIFO selection are additional live-service bindings.

[DERIVED] `BfvTeachingExhibits.nonzeroUpdateInhabited` is a genuinely accepting source witness at q37, including nonzero old ciphertext words and nonzero quotient digits. Inputs acc=(7,8), fresh=(2,3), old=(5,7) force out=(4,4). `omittedExpiryRefused` rules out the still-canonical out=(9,11) for every auxiliary assignment. This small kernel witness is distinct from full-parameter execution; no giant actual trace is kernel-reduced.

[EXECUTED] Both new Compiler modules pass their final isolated checks with fourteen exact axiom guards. Commands, source hashes and failed elaboration attempts remain in `results/`. One simplifier loop was corrected with the already proved modular identity; no cap escalation or broad build followed. Frozen predecessors and companion trees were unchanged. This lane generated no ciphertexts, opened no keys and ran no live proof campaign; the live service/runtime lane owns fresh execution evidence.

[OPEN] Public ciphertext decoding/canonical serialization, query/SIMD encoding, evaluation-key seed expansion, NTT callbacks, proof-backend soundness and the request/row binding controller remain the inherited TCB. The theorem does not establish hidden plaintext contents, FHE noise/security, lane membership, prior journal history, teacher authorization or learning utility. Those are not inferred from an accepting modular equation.
