# Independent bounded review of the qualified-QIO interface

[DERIVED review verdict; 2026-09-07] **Accepted as a conditional interface lemma;
no blocking error found.** The frozen note proves that worst-case iO for all
polynomially bounded equivalent-pair sequences, against nonuniform quantum
adversaries with arbitrary polynomial quantum advice, implies the stated
qualified `QIO` bound. The required negligible envelope is uniform over each
fixed polynomial resource class. No efficient equivalence test, conditional-state
preparation, rewinding, advice copy, or inverse-good-probability loss is needed.
This is independent source/proof review, not a Lean-checked theorem or primitive
instantiation.

[EXECUTED reviewed bytes] Target:
`experiments/pq_composition/qio_interface/QIO_INTERFACE.md`, SHA256
`2cc1d2dc58d8cde8e6a3c3badba602357f9de2d11e008b6d421177eea3dd01d3`.
The file was read but never edited. `review.py`, `results.json`, and `stdout.txt`
record independent local PDF extraction, source and script hashes, and exact
finite controls. The reviewer is `/root/entropy_composition`, distinct from the
derivation author. No shared ledger, companion, commit, or other lane artifact
was changed by this review.

## The exact implication

[DERIVED] Fix the circuit, continuation, addressed-wire, and retained-advice
bounds before maximizing advantage. For each classical prefix outcome `a`, let
`tau_a` be its common subnormalized retained quantum state. All accessible
reference registers must be included. Fresh obfuscation coins and the challenge
bit are independent of this prefix. The two continuations, after fixing `a`,
induce measurement effects `F_0,a` and `F_1,a` on that same retained register.
Put `H_a = F_0,a - F_1,a`.

[DERIVED independent proof check] On an equivalent-circuit block, the worst-case
pure-advice guarantee bounds the expectation of `H_a` on every unit vector in
absolute value by `eps*`. Thus

```
-eps* I <= H_a <= eps* I,
|Tr(H_a tau_a)| <= eps* Tr(tau_a).
```

Summing only the good blocks and applying the triangle inequality gives

```
|Pr[D=1 and E | b=0] - Pr[D=1 and E | b=1]|
 <= Pr[E] * eps*.
```

This operator formulation does not even need to normalize `tau_a`; zero-mass
blocks contribute zero directly. It confirms the note's normalized-state proof
for mixed states and arbitrary quantum coherences. The bad blocks have common
mass `beta`, so their contribution to the unqualified gap is at most `beta`,
not `2*beta`. The retained bound `Pr[E]*eps* + beta` is correct.

[DERIVED signs and rare paths] Block gaps may have unrelated signs. The absolute
value is taken before each local upper bound; no efficient sign selector or
coherent selection of a favorable branch is used. In the sequence-contradiction
argument the source also measures absolute gaps, so signs changing with the
security parameter do not spoil nonnegligibility. The argument remains valid
when the good event has exponentially small or zero probability. It is a
mathematical comparison of experiments, not a physical postselection algorithm.

## Quantifiers and source check

[SOURCE: definition and surrounding convention read] The independently extracted
local **2023/265**, titled *Software with Certified Deletion*, has the following
relevant content:

| Local PDF location | What was checked |
|---|---|
| Section 4.1, p.19 | Nonuniform QPT is described using a polynomial-time implementable unitary and a nonuniform pure quantum advice state. |
| Definition 4.3, p.20 | Security quantifies over all sequences of functionally equivalent circuits and all QPT adversary sequences, with absolute probability gap negligible. |
| Definition 4.6 and following paragraph, p.21 | The different, distributional differing-input definition uses classical sampled auxiliary data; additional quantum advice depends on the circuit family rather than its sampled pair. |
| p.22 and footnote 11 | The separate differing-input argument discusses multiple nonuniform advice copies; no such extraction or copying step is needed or imported by the reviewed lemma. |

[EXECUTED] Local PDF SHA256:
`18dce0afa750386cdf530c6ce4f4cc6aa6be29703e9782ee1e152e527e0afeb9`.
Text was extracted with `pdftotext -layout` from the local mirror. The review
read the actual definition and convention, not an abstract or search snippet.

[DERIVED quantifier audit] If the fixed-resource supremum were nonnegligible,
choose an inverse-polynomial witness on an infinite set of parameters, achieving
at least half that supremum. Outside that set choose an identical pair and a
trivial distinguisher. The fixed resource bounds make the resulting circuit and
advice family polynomially bounded. Its advice may depend on the selected pair
sequence but not on fresh obfuscation coins. This is a permitted nonuniform
family, contradicting the source's all-sequences guarantee. No uniform procedure
for finding witnesses is required. The order of the quantifiers is doing real
work; per-fixed-label negligibility would not suffice. Taking a supremum over
all polynomial degrees simultaneously would also be invalid, and the note does
not do so.

[DERIVED mixed-advice audit] Pure advice suffices at the same quantum dimension
for the note's fixed distinguisher model: expectation is linear, so a mixed
state's absolute gap cannot exceed the maximum pure-state gap. Purifying a
conditional state would unnecessarily enlarge the register; that is not the
argument used. A smaller initial-prefix advice bound cannot replace the bound
on the complete residual register. Efficiently preparable-only advice is also
a different, narrower assumption.

## Concrete resource qualification

[DERIVED nonblocking qualification] The exact envelope substitution
`eps_wc(lambda; m, t+w, u+w, q)` is valid in the note's expressly chosen model
where the continuation is a nonuniform bounded quantum circuit, `u` bounds all
addressable wires relevant to gate descriptions, and computational-basis
constant initialization uses a primitive X gate. If the fixed gate set does
not contain X directly, use the corresponding constant-factor preparation cost.
If `u` excludes input/advice wires, include those in the wire-address budget.
These are model conventions, not extra cryptographic assumptions.

[SOURCE / DERIVED qualification] The short p.19 source convention does not give
this concrete four-parameter cost model. If its polynomial-time unitary is read
as a **uniform** interpreter instead of an arbitrary nonuniform circuit family,
put the selected classical continuation description and fixed prefix constants
in computational-basis advice and interpret them uniformly. This incurs
polynomial additional advice and simulation resources. Therefore the source
still implies negligible envelopes for each fixed polynomial class, but this
alternative source-to-model conversion must not be represented as preserving
the exact `q` or the exact `t+w` numerical budget. The reviewed note explicitly
supplies its nonuniform-circuit convention and does not claim a source-proved
concrete numerical epsilon, so this is not a blocking defect.

## Is an assumption removed?

[DERIVED bounded answer] **The bespoke qualification requirement is removed as
an additional independent property, conditional on this worst-case
quantum-advice iO convention.** The averaging implication is substantive: a
sampler can have rare nonequivalent outputs and pair-correlated residual states
without requiring an efficient test for equivalence. Conversely, a qualified
game covering nonuniform constant-pair samplers and the same advice resources
contains the worst-case game with `Pr[E]=1`, up to explicit constant-output
preparation. The interfaces are therefore equivalent at the stated polynomial
resources.

[DERIVED limit] This does **not** remove the assumption that the required iO is
secure against arbitrary polynomial quantum advice. Naming a source definition
is not an existence theorem. It would be incorrect to replace ordinary
classical iO, uniform-QPT-only iO, or efficiently-preparable-advice iO by this
worst-case arbitrary-advice property without a separate implication.

[SOURCE: remaining theorem boundary read] The local **2025/2215**, SHA256
`5ffbaabd34120b58c46b3c6763d6e665be7a535118566c709ad007ea0fa99866`,
Theorem 2 p.3 invokes subexponential LWE **and average-case iO** and describes a
straight-line, one-adversary-call post-quantum extension. Definition 3 p.10 is
written for PPT adversaries; Definition 6 p.16 uses classical `KeySamp`, `Sim`,
and auxiliary data. These inspected locations do not explicitly establish the
required arbitrary-quantum-advice resource convention. No transformation in
that construction was re-audited or promoted to such a theorem here. The
reviewed note correctly leaves that obligation, the remaining primitive suite,
and all whole-resident/PQ-from-LWE claims open.

[DERIVED sampler boundary] A promise that an efficient sampler always outputs
equivalent pairs is not automatically weaker if nonuniform polynomial quantum
advice and constant pair sequences are allowed. In contrast, security for one
particular sampler which sometimes emits nonequivalent pairs cannot by itself
supply the same qualified bound: cancellation can hide a bad qualified gap.
The note separates these cases correctly. Outer FE-pair correlation alone does
not establish that an internal average-case-iO sampler must output quantum
auxiliary data; determining that requires the actual transformation and its
advice handling, still outside this review.

## Executed controls and stopping result

[EXECUTED] The command below exited 0. The independent script checked:

- 12,005 exact rational-complex density-matrix mixtures, including noncommuting
  X/Y coherences, against acceptance linearity and the pure-state extremal bound.
- 600 qualified classical-quantum block cases with both gap signs, good masks,
  mixed states, zero-mass blocks, and a good event of probability `2^-32`.
- An unqualified-cancellation control: total gap 0 but qualified gap 1/2.
- A fresh-coin-independence falsifier: a challenge marginal can be identical
  while a retained register correlated with its fresh random mask distinguishes
  the two worlds perfectly.
- The scoped moving-sequence quantifier control and both local source hashes.

These are finite premise controls, not an implementation or automated proof of
iO security, asymptotic negligibility, or the source's constructions.

```sh
python3 research/learn_infer_only/experiments/adversarial_review/qio_interface/review.py > research/learn_infer_only/experiments/adversarial_review/qio_interface/stdout.txt
```

[EXECUTED access] Zero web, Scry, Kagi, SQL/schema queries, installs, or network
PDF downloads. All output is confined to
`experiments/adversarial_review/qio_interface/`.

[DERIVED stopping result] Record the qualified-QIO interface lemma as
independently reviewed and accepted under its explicit worst-case quantum-advice
and polynomial-resource convention, with the concrete model qualification
above. The next necessary source obligation is the actual iO construction's
advice/resource security and its inherited assumptions; this review establishes
no primitive-suite instantiation and launches no further work.
