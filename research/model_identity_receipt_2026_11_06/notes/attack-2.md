# Cross-model attack 2 (gpt-6-astra via codex exec, read-only, 2026-11-06)

Target: Receipt.lean version 2 (commit c02ffb55). Verbatim final answer; GROUNDING.md section 7 says what changed.

**V2’s conditional decomposition is sound; the remaining gaps are between its predicates and actual execution.** `hollow_refused` now matches its narrow docstring: wrong-ID rejection and conditional non-equivocation, not effort resistance.

[EXECUTED] Tests below used synthetic receipts through stdin, explicitly trusted test keys, and no actual FlashProve proof.

1. **High — deployment semantics remain unbound.** [DERIVED/EXECUTED] [`World`](lean/Mir/Receipt.lean:216) never connects `conv`, `satisfies`, or `fpAccept` to the deployment’s configuration. [`edgeFieldsOf`](lean/Mir/Receipt.lean:169) signs endpoints and free-text rules, not deployment components. Changing `flashprove-config`, recomputing deployment, and re-signing **only the evaluation** passed strict verification with unchanged recomputer signatures. The builder’s configuration digest is merely [`KL.bin`](receipt/make_receipt.py:53), omitting `policy.txt` and `layout.txt`; runtime semantics are absent.
   
   **Fix:** bind complete configuration and conversion parameters into both edges; parameterize the proof relation by that configuration; name the evaluated runtime/backend. A llama.cpp GGUF evaluation can currently be labelled as the integer deployment and accepted—even with a benchmark explicitly saying “llama.cpp.” That demonstrates missing semantic validation, not forgery. Equal GGUF bytes do not establish equal integer/float behavior.

2. **High — `CommitRun` still assumes committer correctness rather than describing a run.** [DERIVED] [`CommitRun`](lean/Mir/Receipt.lean:255) expands to `∃ g, files g = f ∧ committed cid (conv g)`. There is no executable, randomness, configuration, trace, or output relation. Public-seed reproduction establishes that specified inputs and implementation reproduce `cid`; deriving this semantic premise additionally requires correct conversion/encoding. FlashProve explicitly [does not prove correctness of `cp_commit` or binding for the programs](/Users/ember/src/FlashProve/docs/protocol.md:121).
   
   **Fix:** separate operational run evidence, committer refinement, and binding/extraction. Hiding does not invalidate this decomposition. A hidden-seed commitment needs its own witnessed/attested run or a proof linking its hidden opening to the roots; reproducing the public-seed commitment establishes nothing about another ID. Also, [GROUNDING](GROUNDING.md:55) conflates secret randomness with private weights: a secret seed does **not** make publicly computable `wsums` secret.

3. **High — explicit proof rejection returns success.** [EXECUTED] [`Main.check`](lean/Main.lean:92) maps both `--fp-verdict no` and absence to `false`; [line 124](lean/Main.lean:124) returns zero and prints “No proof verdict given.” `yes` is simply a caller-supplied Boolean, with no proof/request/configuration linkage.
   
   **Fix:** distinguish missing/accepted/rejected; reject `no` and malformed values. Separate receipt-check success from proof acceptance. An integrated command must consume the actual verifier result tied to the exact request, coverage, configuration, and ID.

4. **Medium — the builder signs unsupported conversion claims by default.** [DERIVED] [`build`](receipt/make_receipt.py:37) merely warns when streamed file hashes disagree with the published list, then uses the published file digest alongside the stream’s roots. `--require-match` fixes only that comparison: it does not check expected `wsums` or `m["eres"]`, while the edge asserts `e_res 10`.
   
   **Fix:** fail closed on file-list, sums, and conversion-parameter mismatches before signing; require an explicit synthetic-fixture mode for demonstrations.

5. **Medium — the failure disjunction remains quantitatively vacuous.** [DERIVED] [`FpSoundUpTo`](lean/Mir/Receipt.lean:235) permits `bad := fun _ => True`; neither identity theorem bounds that event. Strict mode replaces two semantic premises with [`HonestRecomputer`](lean/Mir/Receipt.lean:260), a universal semantic premise about every accepted signature. It does not eliminate trust.
   
   **Fix:** state the implementation-refinement assumption and a concrete security game/error bound separately. Describe strict mode as authenticated recomputer attestation. The Lean deductions themselves are valid.

6. **Medium — `FilesCollision` is not yet a SHA-256 collision witness.** [DERIVED] [`FilesCollision`](lean/Mir/Receipt.lean:242) only witnesses noninjectivity of arbitrary `World.files`. Unequal abstract `G` values need not have distinct serialized bytes. Nested file hashes also require distinguishing an inner collision from an outer manifest collision.
   
   **Fix:** instantiate canonical, complete named file collections and prove reduction to distinct byte strings colliding at a specified hash layer. V2 moved the earlier abstraction gap from sums to files.

7. **Medium, conditional on key enrollment — universal signatures are accepted for the identity key.** [EXECUTED] [`ed25519Verify`](lean/Mir/Crypto/Ed25519.lean:121) accepts `A = R = identity, S = 0` for every message. Trusting that key allowed arbitrary strict receipts without any private key. This does **not** bypass an ordinary honestly generated trusted key.
   
   **Fix:** reject identity/small-order public keys during trust enrollment and verification. [`EncodingInjective`](lean/Mir/Receipt.lean:95) is neither encoding injectivity nor a standard signature-forgery game; rename it and state the intended security assumption precisely.

8. **Low — evaluator attribution is unsigned.** [EXECUTED] Changing `eval.evaluator` to another lab’s name preserves acceptance; [`evalFields`](lean/Mir/Receipt.lean:183) omits it, while the CLI displays it beside its trust verdict.
   
   **Fix:** derive attribution from the client’s trusted-key registry, or include it in signed fields.
