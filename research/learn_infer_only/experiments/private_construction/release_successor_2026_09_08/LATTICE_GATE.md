# A direct lattice gate candidate, with its missing security step exposed

[SOURCE / DERIVED, 2026-09-09] Abram–Malavolta–Roy, **How to Authenticate a
Non-Deterministic Computation** ([2026/741](https://eprint.iacr.org/2026/741)),
gives a concrete, different route to obfuscating our small release function.
Its general obfuscator is explicitly **heuristic**. The proved shift-hiding
primitive and the proved compressed-sampler application do not establish the
resident's confidentiality. This is a useful new construction target, not a
reason to start another purportedly private demo.

## The actual algorithm, and why it is relevant

[SOURCE construction] Section4.2, printed pp34–37, constructs a laconic
shift-hiding PRF from decomposed LWE. Its interface satisfies

```
K       <- Setup(lambda, constraint_length)
K_beta  <- Shift(K, beta)
ShiftEval(K_beta, a) = Eval(K, a) + f(a, beta).
```

[SOURCE theorem scope] Lemma11 gives correctness simultaneously for all inputs,
except a negligible setup probability. Lemma12 makes a shifted key
indistinguishable from the specified random distribution for each **fixed**
constraint beta. It does not expose the original K to the distinguisher.
Decomposed LWE is the separately stated assumption in Definition1, printed p19;
the paper does not reduce this assumption to ordinary LWE here.

[SOURCE construction] Section4.4, printed p38, chooses
`f(a,beta_K) = C(a) - Eval(K,a)` and publishes `Shift(K,beta_K)`.
Evaluation therefore returns C(a). The laconic property makes the circuit
dependency well-defined: evaluation complexity depends on the constraint's
depth rather than its full size. The paper explicitly says the proof of
Lemma12 fails when beta depends on K, and leaves the general obfuscator's
security open. The same limitation appears in the technical overview, p12.

[HYPOTHESIS concrete use] C could be the existing fixed, context-bound release
program: verify the authorized genesis/program/parent/output/recipient statement,
then decrypt only its designated output ciphertext and deliver the authorized
message. Its actual accepted-proof predicate, recipient delivery and random-coin
rules must remain part of C. An ordinary exported `Dec` is not the proposed C.
This separates the large homomorphic learner from the smaller protected release
computation, but does not assume the latter is cheap: proof verification itself
has a circuit cost.

[DERIVED credential lifecycle] Setup/compiler plaintexts include K, beta_K,
the unprotected release circuit and all its embedded decryption/randomness
secrets. Those must be erased with their copies. The surviving host gets the
shifted key, its public evaluation machinery, public encryption material and
all resident ciphertexts/proofs. Security of that exposed bitstring is exactly
the unresolved obfuscation obligation; erasure alone does not discharge it.
No claim that iO supplies a universal virtual black box is made.

## Retaining the unshifted key gives a concrete reader

[SOURCE algorithms] Section4.2, p35, has
`K = (pk, crs, z, M0, s, t)` and
`K_beta = (pk, crs, z, ec, t)`, where `ec=LFE.Encode(crs,s,beta)`.
Section4.1, p33, explicitly parses s as a GSW secret key. The encoding ec contains
the flattened GSW ciphertexts encrypting every bit of beta, together with the
homomorphic authentication encodings.

[DERIVED: this construction, exposed K] A host holding both K and K_beta can
recover beta by ordinary GSW decryption of those included ciphertexts. Thus
publishing K to cancel the PRF mask is not a safe alternative to solving the
K-dependent shift. If beta contains a release secret or an unprotected circuit
description containing one, that secret is exposed. This follows from the
source's algorithms and encryption correctness; no attack program or keys were
generated, and it is not a break of Lemma12's experiment.

## What the proved preimage-sampling result actually covers

[SOURCE inspected] The overview pp12–14 describes a two-shift construction
whose output is a short preimage satisfying `M*w = Q*h`. It extracts a trapdoor
for M from auxiliary data using a hardwired tau. The formal application is the
compressed sampler of Section5: Definition2 pp44–45 and Theorem5 pp45–48.
The attacker supplies tau before setup; its later `(Y,aux)` must yield
`T=Extract(tau,Y,aux)` with `|T|_infinity <= 1` and
`Y*T = I_(m*c*s) tensor G`. The challenge concerns a compressed LWE sample
and its particular derandomization. We inspected the game and the first five
hybrids, not every algebraic step in the remaining reduction.

[SOURCE explicit scope] Section2.2, printed p18, says it does not separately
use the preimage sampler's intuitive distribution-hiding property: security
appears inside the more complex Section5.2 argument.

[DERIVED] Theorem5 is consequently not a general theorem that an arbitrary
hidden decryption trapdoor can be put in a publicly executable program with an
arbitrary proof gate. In particular, the admissibility extractor and matrix
equations above must be instantiated. A future use of this narrower primitive
needs to connect its precise public short-preimage functionality to restricted
resident release; replacing `Extract` with `decrypt the model` is unjustified.
No such connection is established by this source read.

## Costs and the proof-system lead

[SOURCE asymptotic contract] Section4.2 p34 requires

```
q/p >= (m*n*t*sigma*sqrt(lambda))^O(d*delta)
       * 2^O(delta) * d^O(delta) * 2^omega(log lambda),
```

where delta is the depth of the circuit computing the LFE hash of the shift
function. Section4.1 expands each constraint bit into a GSW ciphertext and
then authenticates the flattened ciphertext entries. These are substantial
objects; the inspected construction supplies no selected concrete parameter set
or runtime benchmark. No practical security-bit or speed estimate is inferred
from the word “laconic.”

[SOURCE separate lead] Ma–Dai–Shi, **Quasi-Linear Indistinguishability
Obfuscation via Mathematical Proofs of Equivalence and Applications**
([2025/307](https://eprint.iacr.org/2025/307)), Theorems1.1–1.2, printed pp1–2,
offers quasi-linear dependence on circuit size plus equivalence-proof size.
It still assumes subexponentially secure small-circuit iO and one-way functions,
along with the stated LWE hardness. Its MIFE theorem requires succinct
Extended-Frege proofs of the relevant function equivalences for every indicated
partial input substitution. Only the abstract/introduction/theorems were read.

[DERIVED] Our Lean arithmetic soundness proofs are not automatically those
Extended-Frege equivalence certificates. This lead makes a possible efficiency
bridge precise, but neither supplies an iO implementation nor removes the
resident's all-input compatibility obligation. There is no justified compiler
integration to launch from the currently inspected result alone.

[OPEN decision] Keep the direct shifted-key release circuit as an explicit
heuristic candidate, and the special sampler as a narrower mathematical lead.
To advance either, supply a security argument for the actual exposed release
capability or a defensible concrete cryptanalysis/parameter experiment. The
current result changes our source map and isolates a specific missing step;
it does not change the running learner's full-reader limitation.

[SOURCE provenance] Both PDFs were read from the local IACR mirror, using
`pdftotext -layout`, with selected sections inspected as stated above. PDF/text
hashes and discovery-query accounting are in `SOURCES.json`. No PDF download,
cryptographic run, estimator or companion-tree mutation occurred.
