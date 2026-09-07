# Worst-case quantum-advice iO implies the qualified interface

[DERIVED result; 2026-09-07] **Yes.** Worst-case iO for equivalent classical circuit pairs against nonuniform quantum adversaries with arbitrary polynomial quantum advice implies the qualified `QIO` premise of the [reviewed lift](../qind_pre/REVIEW_COMPLETION.md). The implication uses averaging, with no equivalence test, no inverse-probability loss and no physical conditioning or copying of a state. A primary source explicitly uses the needed worst-case/advice convention. This removes a bespoke interface obligation; it does not instantiate iO or reduce its underlying hardness assumptions.

## Precise convention and resources

[DERIVED definition] Fix polynomial resource bounds **before** taking any supremum. Let `m` bound each padded classical circuit description, `w` the complete retained classical prefix output, `q` the retained quantum register, and `t,u` the continuation's gate and workspace bounds in a fixed finite gate-set model. Include every accessible quantum reference register in `q`. Quantum advice is one arbitrary `q`-qubit density operator, with no efficient preparation requirement, independent of fresh obfuscation coins. Classical nonuniform circuit descriptions are allowed. This advice budget covers the **residual** state, which can exceed the prefix's initial advice length.

[DERIVED worst-case envelope] Write `eps_wc(lambda;m,t,u,q)` for the supremum of the output-probability gap over all permitted equivalent equal-size pairs, all distinguishers within those fixed resources, and all such advice states. A fixed-pair distinguisher receives only the freshly obfuscated circuit; other classical constants can be hardwired. “Secure” means this envelope is negligible for each fixed polynomial envelope. It does not mean a supremum over every polynomial degree at once.

[DERIVED pure-advice convention] A definition allowing arbitrary pure advice suffices without increasing `q`: for a fixed pair and distinguisher the acceptance difference is linear in the density operator. Decomposing a mixed state into pure states bounds its absolute gap by the largest pure-state gap. This is a mathematical argument, not an algorithm preparing the decomposition or a purification.

## Averaging proof

[DERIVED prefix model] A sampler runs once, before the challenge bit and fresh obfuscation coins. Its complete classical output is `W=(C0,C1,Z)` of length at most `w`; its residual state is `R`. Write its classical-quantum output as

```text
omega_WR = sum_a |a><a| tensor tau_a,
p_a = Tr(tau_a),     sum_a p_a = 1.
```

[DERIVED] The subnormalized operators `tau_a` are identical in the two challenge worlds. Let `E(a)` mean that the two circuits encoded by `a` agree on every input. The finite-circuit predicate is decidable by exhaustive evaluation; this argument supplies and requires no efficient decision procedure.

[DERIVED lemma] Put

```text
eps* = eps_wc(lambda; m, t+w, u+w, q).
```

[DERIVED proof] For each classical `a`, specialize the continuation by hardwiring `a`. Initializing its classical constants takes at most `w` X gates and `w` additional wires, with corresponding `O(w*log(u+w+1))` gate-description bits. The obfuscation size and number of challenges do not change. For `p_a>0` the mathematical state `tau_a/p_a` is admissible independent advice. On every `E(a)=1` block, the specialized continuation's gap is at most `eps*`. Therefore, by linearity and the triangle inequality,

```text
|Pr[D=1 and E | b=0] - Pr[D=1 and E | b=1]|
  = |sum_{a:E(a)} p_a * delta_a|
 <= sum_{a:E(a)} p_a * |delta_a|
 <= Pr[E] * eps*
 <= eps*.
```

[DERIVED] Zero-mass blocks contribute zero. The bad blocks have common total probability `beta=Pr[not E]`, so the total unqualified gap is at most `Pr[E]*eps* + beta <= eps*+beta`. There is no factor `1/Pr[E]`, even for a rare good event. This is the exact qualified-interface bound needed by the existing hybrid ledger; substitute the resource-indexed `eps*` for `epsilon_IO`.

[DERIVED advice boundary] The proof does **not** turn the running sampler's input advice into a selected residual state. It invokes a worst-case guarantee that already quantifies over that residual state. In a contradiction formulation, choosing a fixed pair and one corresponding advice state produces a different allowed nonuniform adversary. This is explicit nonuniform reasoning, not a uniform black-box reduction given only the original advice. No extra copy is obtained, and no experiment is efficiently conditioned on `E`. If the target primitive only allows efficiently preparable states or caps advice at the prefix's smaller initial length, the stated implication has not been established at those narrower resources.

## From the usual sequence definition to a uniform envelope

[DERIVED quantifier lemma] Suppose the definition says: for **every polynomially bounded sequence** of equivalent circuit pairs and every nonuniform QPT adversary family with arbitrary polynomial quantum advice, the gap is negligible; the negligible function may initially depend on that family. This implies negligible `eps_wc` for each fixed polynomial resource envelope. Otherwise, an infinite set of parameters has inverse-polynomial envelope gap. At each such parameter choose a witnessing pair, bounded distinguisher and advice state with at least half the supremum gap; use an identical pair and trivial adversary elsewhere. These choices form one permitted nonuniform polynomial-size family with nonnegligible gap, a contradiction. No efficient algorithm selecting the witnesses is needed or claimed. Pure-state witnesses suffice by linearity.

[DERIVED] Thus a source need not literally print one common epsilon over all pairs/states if it has the full sequence and nonuniform-advice quantifiers. Merely quantifying over fixed labels is weaker: `a(lambda,k)=1[lambda=k]` is eventually zero for every fixed `k`, while `sup_k a(lambda,k)=1` always. The arbitrary sequence `k=lambda` detects this defect. This is a quantifier countermodel, not an obfuscator construction.

## What an efficient-pair-sampler promise does and does not give

| Formulation | Consequence |
|---|---|
| [DERIVED] Worst-case sequences plus arbitrary quantum advice | The proof above applies directly. Sampled-pair correlations are represented by the mathematical conditional residual states already covered by the assumption. |
| [DERIVED] Security for samplers promised always to output equivalent pairs, where nonuniform samplers may have arbitrary polynomial quantum advice | This also contains the constant-pair sampler for every pair sequence and advice state, with an explicit extra budget for emitting/hardwiring its classical constants. It therefore supplies the worst-case premise at that resource overhead. A sampler formulation is not automatically weaker. |
| [OPEN interface] Only uniform efficient pair samplers, or only classical/efficiently preparable correlated auxiliary data | The constant arbitrary sequence/state argument may be unavailable. No implication is claimed here. Rejection-sampling until equivalence holds is not a permitted repair: no efficient equivalence test or efficient conditional-state preparation has been supplied. |
| [REFUTED: one-experiment inference] An unqualified gap bound for one sampler that sometimes produces nonequivalent pairs | It does not alone yield the same qualified bound. Two equally likely blocks with acceptance probabilities `(0,1)` in world 0 and `(1,0)` in world 1 have total gap zero; qualifying on the first block gives gap `1/2`. This countermodel does not separate complete iO definitions. |

[DERIVED] Conversely, qualified `QIO` for all nonuniform samplers with the stated advice resources implies the corresponding worst-case guarantee by choosing a constant equivalent pair and its advice, so `Pr[E]=1`. The two interfaces are equivalent up to the explicitly budgeted constant preparation. The qualified event is not an additional cryptographic hardness assumption under this convention.

## Primary-source definition and the remaining 2025/2215 gap

[SOURCE: definition and surrounding conventions read, visually confirmed] The pinned local [2023/265](https://eprint.iacr.org/2023/265) is titled *Software with Certified Deletion*. Section 4.1 p.19 defines nonuniform QPT using a polynomial-time unitary and a nonuniform quantum advice state. Definition 4.3 p.20 quantifies iO security over every sequence of functionally equivalent circuits and every QPT adversary sequence. Restricting it to our equally padded circuit pairs is sufficient. It states an asymptotic definition, not a concrete advantage bound or an iO construction. These are the local version's title and numbering; indexed older copies use a different title/numbering.

[SOURCE / DERIVED boundary] The same PDF's Definition 4.6 and following paragraph p.21 explicitly keep differing-input sampler auxiliary data classical and distinguish it from quantum advice independent of the sampled pair. That distributional diO qualification should not be conflated with Definition 4.3's fixed-sequence iO quantifiers. This lane imports no extraction argument or advice-copy construction from pp.21–22.

[SOURCE: theorem/game/reduction read] In [2025/2215](https://eprint.iacr.org/2025/2215), Definition 3 p.10 states worst-case equivalent-pair iO with PPT adversaries. Theorem 2 p.3 claims a post-quantum extension from post-quantum subexponential LWE **and** average-case iO, explaining its straight-line single-adversary invocation. Definition 6 p.16 gives classical `KeySamp`, `Sim` and auxiliary data. The pinned text does not explicitly define its “post-quantum” adversaries to include arbitrary nonuniform quantum advice at the needed resource bounds.

[DERIVED / OPEN precise remaining interface] If that theorem's output security is established in the 2023/265 worst-case quantum-advice convention, this lemma supplies qualified `QIO` immediately. For a fixed outer circuit pair, the advice is independent of fresh internal challenge/setup randomness; sampled FE-pair correlation alone does **not** force a quantum-valued aviO `KeySamp`. What remains to establish is the required advice/resource security of the LWE and aviO assumptions and its inherited transformations. This note neither re-audits those transformations nor promotes an unstated interpretation to a sourced theorem. No aviO construction, LWE-only iO claim or full primitive-suite instantiation follows.

[DERIVED stopping result] A conventional primary-source definition now supports the exact interface lemma. No separate qualified-QIO assumption is needed **beyond** worst-case iO with the explicitly allowed quantum advice. No underlying hardness or instantiation obstacle has been discharged. The earlier conditional FE lemma, correctness losses and other primitive obligations remain as recorded; shared notes were not edited.

## Reproduction and access

[EXECUTED] [audit.py](audit.py) exited 0 using the command below; [audit.json](audit.json) and [audit.stdout.txt](audit.stdout.txt) retain all extraction commands/output, hashes, locator pages and finite controls. It checked 10,000 scalar averaging cases and the two scoped quantifier/cancellation controls. These are finite premise checks, not a proof checker or cryptographic implementation. Local extracts and renders are ignored.

```sh
python3 research/learn_infer_only/experiments/pq_composition/qio_interface/audit.py > research/learn_infer_only/experiments/pq_composition/qio_interface/audit.stdout.txt
```

[EXECUTED source pins] The local PDF SHA256 values are `18dce0afa750386cdf530c6ce4f4cc6aa6be29703e9782ee1e152e527e0afeb9` for 2023/265 and `5ffbaabd34120b58c46b3c6763d6e665be7a535118566c709ad007ea0fa99866` for 2025/2215. Exact access and web accounting are in [ACCESS.md](ACCESS.md). This tranche used zero SQL/schema/Kagi queries, three web searches, one HTML open and zero network PDF downloads. No companion, shared-ledger or frozen-proof changes; no commits.
