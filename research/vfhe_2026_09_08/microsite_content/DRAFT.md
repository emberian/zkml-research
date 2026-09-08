# Keep learning. Keep a secret.

*Editorial draft · 8 September 2026. Status labels and links are source cues for the site editor. The current global verdict remains [VERDICTS](https://github.com/emberian/zkml-research/blob/dev/docs/VERDICTS.md); newer experiments below have their own stated scope.*

## The machine is yours. Must its memory be?

[HYPOTHESIS — research ambition] Imagine a machine running on someone else's computer. You teach it something. It changes. Later, you ask a question, and what it learned changes its answer.

The host supplies the processor, stores the memory and carries the messages. The ambition is that none of those jobs grants a universal reader of the machine's learned state.

It must still learn. It must still answer. Its secrets cannot simply be made safe by making them useless.

This research is building toward that arrangement. Four requirements have to meet in the same machine: encrypted learning, verifiable computation, restricted release and continuity.

## First, make it keep going

[EXECUTED] The latest completed nonlinear experiment ran **384 Learn operations and 96 Infer operations** over two histories. Every one of the 480 operations had a matching independent replay on complete ciphertext bytes. After the public run closed, an authorized reader checked 484 initial states, learned states and answers against the integer reference. All matched.

The runtime executed Learn and Infer programs emitted from Lean definitions. That connects the experiment to a specified computation, while the interpreter and encryption implementation remain additional dependencies.

This is a completed continuing encrypted workload. It is not yet the private machine above: the fixture was reused, the run adds no new utility estimate, and a full decryption key survives. Matching a reference answer also does not mean correctly classifying a real-world example. [Executed report](https://github.com/emberian/zkml-research/blob/dev/research/learn_infer_only/experiments/end_to_end/private_ema/emitted_long_run/REPORT.md).

## A hidden computation can still be the wrong computation

[DERIVED] Encryption and integrity answer different questions. Hiding a state does not establish that the host applied the requested update to it. Verifiable FHE aims to attach checkable evidence to the encrypted computation: these inputs, this operation, this output.

Even correct arithmetic can leave the wrong statement proved. Large ciphertext values are often represented by several smaller modular pieces. Each piece can check perfectly while pieces come from different source ciphertexts. The missing claim is that **all the pieces belong to the same input**. This provenance failure has an explicit counterexample in the research record. [Current verdict, §7 item 5](https://github.com/emberian/zkml-research/blob/dev/docs/VERDICTS.md#7-genuinely-open).

[OPEN] The constructive task is to make the proof follow the actual encryption operation, including shared inputs and any rounding it performs. Friendly arithmetic alone does not supply that connection.

## An answer is a smaller power than a reader

[DERIVED] A full decryption key can read retained ciphertexts. An answer capability should reveal only the answer it authorizes. Putting the full key behind an approval gate still releases a full reader when the gate opens.

[EXECUTED] One completed construction derives its public setup from a public seed and recipient-owned keys, without computing a scalar master. It ran 33 Learn operations, four Infer operations and an exact expiry; all four recipient scores matched the reference. But surviving recipient credentials still cover the entire fixed query span. That is a narrower construction step, not arbitrary learn/infer-only privacy. [Public-seed experiment](https://github.com/emberian/zkml-research/blob/dev/research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/public_seed/adapter/REPORT.md).

[DERIVED] Release also has a time dimension. A host can keep yesterday's ciphertext. It can copy a state and try two futures. A proof that each update was computed correctly does not, by itself, select the history entitled to produce today's answer.

[EXECUTED] A separate durable-journal experiment completed 40 Learn operations, four Infer operations and eight exact expiries, with 44 independent arithmetic replays. It resumed after reopening and preserved its accepted history across retries. Its journal supplies software ordering and deduplication; it does not revoke surviving cryptographic readers. [Journal experiment](https://github.com/emberian/zkml-research/blob/dev/research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/journal/README.md).

## Build the next conjunction

[OPEN — work in progress] Today's wider construction cycle is attempting concrete joins:

- An eight-intent teach/query learner, so encrypted updates can be judged by what the learner does on held-out examples.
- A generated BFV operation and its proof, with compiler support for the integer arithmetic the operation actually uses.
- A bounded transcript-based release construction and an executable ring-based restricted-output scheme.
- Arity-eight proof composition and faster sumcheck computation, to connect the mathematical argument to the work a prover actually performs.

These are active attempts, not completed results. [Current construction queue](https://github.com/emberian/zkml-research/blob/dev/research/vfhe_2026_09_08/STATUS.md).

[OPEN] No present result combines useful private nonlinear learning, exact history-bound release, resistance to a malicious host and absence of an equivalent full reader. Post-quantum and implementation security remain separate obligations; no numerical security level follows from these experiments.

The destination is concrete: a machine changes through teaching, speaks through authorized answers, and keeps doing both without handing its host the power to read everything it has learned.
