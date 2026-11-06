# Cross-model attack 1 (gpt-6-astra via codex exec, read-only, 2026-11-06)

Target: Receipt.lean version 1. Verbatim final answer below. Every defect was addressed in version 2 (the head of lean/Mir/Receipt.lean says how); receipt/falsify.py now runs the executed attacks as falsifiers.

**`identity_sound` is a conditional binding lemma, not a soundness theorem for `verify`. `CommitEdge` assumes the crucial binding; strict mode does not establish it.**

[EXECUTED] Against the existing `lean/.lake/build/bin/mir-verify`, six malformed fixtures returned `ACCEPT` under `--strict`. I supplied fresh evaluator signatures under an explicitly trusted test key and `--fp-verdict yes`; these demonstrate missing checks, not signature forgery or acceptance of an actual FlashProve proof.

Ranked defects:

1. **Critical — `CommitEdge` assumes the missing commitment binding.**  
   [DERIVED] [Receipt.lean:215](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:215) universally quantifies over *every* weight set committed under the ID. An honest `cp_commit` run checking its input hashes does not establish that universal statement. Publishing adjacent digests in `expected.txt` does not either.  
   [SOURCE] FlashProve explicitly says the ID excludes `wsums.txt` and the verifier never sees it: [weight_sums/README.md:186](/Users/ember/src/FlashProve/weight_sums/README.md:186). It also disclaims a binding proof for the actual programs: [protocol.md:121](/Users/ember/src/FlashProve/docs/protocol.md:121).  
   **Fix:** separate “this audited run committed these integers” from commitment binding/extraction, then derive `CommitEdge` with explicit failure events. Public-seed reproduction supplies run evidence; hidden masks require an attestation or a proof linking the hidden committed witness to the digest. Hiding itself neither proves nor disproves that link.

2. **Critical — strict verification accepts invented evidence, including no evidence.**  
   [EXECUTED] [`edgesStrict`:147](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:147) accepts `.checked "because I said so"`; an empty edge list passes vacuously. Five naming nodes, **no edges**, and an arbitrary nonhex `integers.digest` passed strict verification. Neither `StreamTranscript` nor `CommitEdge` is checked or derived.  
   **Fix:** require specific E1–E3 relations and validated evidence for each. Make “checked” a result produced by verifier-side computation, not receipt-supplied text. Bind the integers node to the validated transcript.

3. **High — dependency edges become model equivalences; the default deployment transfer is unsound.**  
   [EXECUTED] [`exactStep`:112](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:112) treats every `lossy=false` edge as bidirectional functional equivalence. The builder marks `integers → deployment` and several hash/configuration dependencies that way: [make_receipt.py:61](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/receipt/make_receipt.py:61). On its generated graph, evaluations naming **`deployment`, `wsums`, and `fp-release` all passed**; `meta-bf16` failed. A checksum or prover release is not an executable model.  
   The deployment digest at line 52 hashes a constant label, not component digests. The whole-graph signature protects component edits, but no check binds an actual deployment to those components.  
   **Fix:** distinguish `DerivedFrom`, `CommitsTo`, `ComponentOf`, and proved `SameFunction` edges. Only the last permits evaluation transfer. Identify deployments by their complete component/configuration manifest and validate the evaluated execution against it.

4. **High — “same integers” does not specify the evaluated function across conversions.**  
   [DERIVED] [`World.conv`:186](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:186) hides all conversion parameters; `produced` supplies the entire behavioral interpretation externally. bf16 bytes, Q4_K_XL GGUF bytes, and FlashProve’s rounded integer serialization are three different objects. Equal committed tensors also do not alone fix scales, tokenizer, prompting, adapters, or decoding policy.  
   [SOURCE] §11 explicitly says no proof checks the conversion and makes `e_res` an input: [model.md:344](/Users/ember/src/FlashProve/docs/model.md:344), [model.md:451](/Users/ember/src/FlashProve/docs/model.md:451).  
   **Fix:** parameterize conversion and execution by a pinned configuration. Sign the evaluated executable model/deployment identity. Treat both quantization steps as non-transferable absent a separate equivalence result; evaluate the final integer implementation.

5. **High — recomputer signatures authenticate names, not their referents.**  
   [EXECUTED] [`edgeFields`:108](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:108) signs only source ID, destination ID, rule, and lossy flag. I changed an endpoint digest, retained the recomputer signature, freshly signed the evaluation, and passed strict verification. Evaluator trust has silently substituted for recomputer approval.  
   **Fix:** sign endpoint kinds and content digests, conversion parameters, evidence digest, and a versioned relation type. Use content-addressed endpoints.

6. **High — node lookup permits identity aliasing and nonexistent objects.**  
   [EXECUTED] [`nodeOfKind`:101](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:101), [`wellFormed`:128](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:128), and [`evalOnCommitted`:141](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:141) accepted:
   - A first `integers` node aliasing a bf16 node, shadowing another integers node.
   - Duplicate IDs giving bf16 and integers zero-hop “equivalence.”
   - An absent evaluation node connected through another absent node.

   **Fix:** unique IDs; exactly one required node per role; valid typed digests; existing endpoints and evaluation node; lookup by validated references. Reject malformed graphs before signing as well as verification.

7. **High — `FpSound` is substantially stronger than the cited FlashProve result.**  
   [DERIVED] [`FpSound`:204](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:204) assumes unconditional, zero-error soundness for arbitrary `fpAccept`. FlashProve distinguishes its Lean verifier from `cp_verify`, requires exact-match conditions, and has cryptographic error bounds: [protocol.md:51](/Users/ember/src/FlashProve/docs/protocol.md:51). A proof also establishes a relation about outputs, not that the provider causally computed them using those weights.  
   **Fix:** state the precise verifier, configuration, request coverage, policy, and failure bound. Rename `produced` to a semantic relation such as `SatisfiesIntegerModel`; explicitly retain the implementation-refinement assumption.

8. **Medium — `SumsCollision` is not necessarily a SHA-256 collision witness.**  
   [DERIVED] [`SumsCollision`:219](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:219) merely finds unequal abstract `W` values with equal arbitrary `World.wsums`. It supplies no distinct hash-input bytes. Different tensors could collide at an **inner tensor hash**, yielding identical sums-file bytes; omitted metadata could also identify different `W` values without any hash collision. `wsums.txt` records element counts, not tensor dimensions.  
   **Fix:** define the exact weight domain and injective serialization, including layout metadata; return concrete distinct byte strings colliding at a named hash layer. Localize the witness to the extracted and streamed models rather than a global existential collision.

9. **Medium — the hollow theorems prove much less than their framing suggests.**  
   [DERIVED] [`hollow_refused`:254](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:254) is simply rejection of unequal strings by an explicit equality conjunct. [`hollow_needs_collision`:264](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:264) follows directly from the assumed common sums digest and defines “hollow” as different roots. It neither characterizes reduced effort nor needs verification. The roots are an equality discriminator here, not a commitment opening.  
   **Fix:** rename these `wrong_cid_rejected` and `different_roots_imply_sums_collision`; reserve a hollow-resistance claim for a defined adversary/security game with independently established binding premises.

10. **Medium — `reachExact` has an avoidable resource attack.**  
    [DERIVED] [`reachExact`:116](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:116) filters against the previous `seen` list but does not deduplicate new discoveries. Parallel edges along successive layers multiply duplicate entries. It runs before signature verification. Its node-count fuel also stops corresponding to graph size when nonexistent endpoints are allowed.  
    **Fix:** validate endpoints, bound receipt size, and use adjacency maps plus a visited set.

**Graph encoding qualification:** [DERIVED] I do **not** find an accepted tab/newline injection: `textOk` blocks those delimiters. `graphText` deliberately omits recomputer signatures, so it is not injective over the complete `Graph` structure. [`other_graph_changes_fields`:298](/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/lean/Mir/Receipt.lean:298) assumes different serialized text rather than proving structural injectivity. Define the signed graph projection explicitly and prove its encoding injective on well-formed inputs.
