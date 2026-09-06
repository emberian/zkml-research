# Learn-and-infer-only protected state: research note

Date: 2026-09-05

## Scope

The target is a computation whose internal state is not exportable using any
surviving general decryption credential. This is stronger than ordinary FHE with
a trusted decryptor, and stronger than splitting a general decryption key among
custodians who could collectively reconstruct it.

This packet contains an interface-leakage experiment and a literature/design
note. It contains **no FE implementation, no encryption, no neural model, no
hardware benchmark, and no completed security proof**. The literature leads
below do not by themselves constitute a complete practical post-quantum system.

## 1. Functionality to protect

Let S contain the model's private weights/adapters, optimizer, recurrent state,
episodic memory, RNG seed, and policy state. Fix an allowed transition function:

    Step(S, learn(x)) = (Learn(S, x), no_public_output)
    Step(S, infer(q)) = (S', Answer(S, q))

The cryptographic implementation carries an encoded S, not a public S. Learning
changes the data in S; choosing the transition function in advance does not mean
freezing its learned weights. Arbitrary operator-supplied machine code is NOT
an allowed learning command: such an interpreter would permit a dump-state
program. The input schema, authorized learning rule, output form, randomness,
and numerical semantics must be part of the definition.

Security should identify precisely which secrets/histories must remain
indistinguishable, which outputs are intentionally revealed, and which setup and
corruption assumptions apply. A full ideal-oracle simulation claim is stronger
than a standard indistinguishability claim; these are not interchangeable.

## 2. Literature leads [READ]

### Streaming functional encryption

Guan, Korb, Sahai, *Streaming Functional Encryption*, CRYPTO 2023,
ePrint 2022/1599. Streaming FE processes encrypted inputs while retaining encoded
state and releasing specified output values.

Bhushan, Korb, Sahai, *Dynamic Bounded-Collusion Streaming Functional Encryption
from Minimal Assumptions*, CRYPTO 2025, ePrint 2024/1213, DOI
10.1007/978-3-032-01881-6_5. The bound concerns distinct function keys, not stream
steps. Its public-key result uses identity-based encryption; its secret-key
result uses one-way functions. Function-selective timing and secret stream
encoding state remain part of its model. These are not performance or complete
post-quantum deployment results.

### Multi-input functional encryption

Goldwasser et al., *Multi-input Functional Encryption*, EUROCRYPT 2014, DOI
10.1007/978-3-642-55220-5_32. General constructions use indistinguishability
obfuscation; the paper distinguishes feasible indistinguishability security from
stronger simulation requirements and their limitations.

### Removing a central key authority

Datta, Pal, Yamada, *Registered FE beyond Predicates: (Attribute-Based) Linear
Functions and more*, ePrint 2023/457. Registered FE removes a secret-keeping
central authority. Its general-function route uses iO; this is not a theorem for
masterless streaming neural learning.

Pal, Schaedlich, Tairi, *Registered Functional Encryption for Pseudorandom
Functionalities from Lattices and Applications*, ePrint 2025/967. The restriction
to pseudorandom functionalities matters. It is not a general neural-output
construction. The assumptions include evasive LWE, not just an unqualified
appeal to ordinary LWE.

### Obfuscation and setup boundaries

Barak et al., *On the (Im)possibility of Obfuscating Programs*, JACM 2012:
general virtual-black-box software obfuscation is impossible in its model. This
does not rule out useful restricted function families, other security notions,
or constructions using additional setup/hardware assumptions.

Branco, Jain, Srinivasan, *Obfuscating Pseudorandom Functions is Post-Quantum
Complete*, ePrint 2025/2215, revised 2026: a relevant frontier result, not a
ready post-quantum compiler for protected learners.

## 3. Bounded-history construction sketch [DERIVED / NOT INSTANTIATED]

For a fixed time budget T, define a circuit H_T that accepts an initial state and
T command slots, executes the specified transition rule, and returns only its
permitted inference outputs. Prefixes are padded with no-ops. A multi-input-FE
instantiation with the appropriate public-input/key-exposure security would
supply one function key for H_T and separate encryption interfaces for the input
slots. Issue that restricted key, encrypt the initial state, then erase all
unrestricted setup and recovery credentials.

This is an in-principle design route, not a completed reduction to a named
parameterized scheme. One must check admissible output leakage, chosen-input
security, adaptivity, setup erasure, and the exact function class. Its costs can
grow with the entire history and allowed time budget. Re-running H_T to obtain a
prefix is functionally correct but can be extremely expensive. The script checks
this functional equivalence only.

Streaming FE is attractive because it instead maintains encoded state across
steps. However, its remaining encoder credentials must satisfy the stronger
post-setup compromise target; that does not follow from its ordinary security
game.

## 4. A concrete live-credential caveat [READ + DERIVED]

Korb's 2026 dissertation, Chapter 3, printed pp. 94-95 (PDF pp. 106-107), sets
`Enc.ST = (FPFE.msk, FE.ct)`. Stream ciphertext i is an FPFE function key H_i.
Given `FPFE.msk`, choose known inner streaming keys and encrypt them as an FPFE
input. Evaluating H_i then returns x_i encrypted under those chosen inner keys;
an inner projection key reveals its bits. This is a derived recovery route, not
a break of the paper's game: the encoder state is assumed secret. Erasing only
the outer MSK is insufficient. This check concerns that specific Chapter 3
bootstrap, not every streaming-FE construction.

Source identifier: Alexis Lei Wan Korb, *Streaming Functional Encryption*, UCLA
PhD dissertation, 2026, eScholarship qt8j13s3tb.

## 5. Interface experiment [CHECKED]

Run:

    python interface_audit.py

No dependencies beyond Python 3.10+ standard library. Results are rewritten to
`results.json` next to the script. All tests were executed in this session.

The hidden state s is an unsigned byte. `infer()` returns its highest bit.
`learn(a)` adds a modulo 256 without returning an observation.

- Inference alone leaves two equivalence classes of 128 possible states each.
- Allowing only learn(128) preserves those two classes under every finite trace.
- Allowing learn(1) makes every state behaviorally distinguishable eventually.
  Partition refinement converges to 256 singleton classes.
- Allowing arbitrary learn(a) permits an adaptive attack that reconstructs the
  initial state using exactly eight inference observations. All 256 possible
  initial states were tested.
- 2,048 algebraic checks verify that unrestricted evaluation can route any state
  bit into a highest-bit release function.
- 990 prefix checks compare online execution with the no-op-padded fixed-horizon
  replay circuit.

These are attacks/correctness checks against ideal mathematical interfaces, not
against encryption or a real learned model. Their relevance is that even
perfect cryptography cannot hide a secret that the allowed interface reveals.

## 6. Two statement-level proof targets

### A. Trace noninterference from a preserved relation [DERIVED]

Let R relate states that should remain observationally indistinguishable. Assume
that for every related pair (s,t) and every authorized command a:

1. the public outputs of Step(s,a) and Step(t,a) are equal;
2. their next states are again related by R.

Then every finite authorized command sequence yields equal output traces from
related initial states. Proof: induction on the sequence. It also covers
adaptive command strategies because identical past outputs induce identical
next commands when the strategy's coins are coupled.

Witness: relation 'same highest bit' for learn(128) and highest-bit inference.
Falsifier for dropping preservation: the same initial relation with learn(1).
Cryptographic implementation security is an ADDITIONAL theorem.

### B. Unrestricted evaluation defeats an unbound nonconstant release [DERIVED]

Suppose a caller can homomorphically evaluate arbitrary H on encrypted S and
submit the result to a release interface O. If known states z0,z1 satisfy
O(z0) != O(z1), then a caller can recover any efficiently computable predicate
b(S) by submitting H_b(S)=z_{b(S)} and distinguishing the two outputs.

For bit predicates this recovers the state one bit at a time. Therefore the
release must bind the exact authorized transition/output provenance. Merely
publishing a restricted output function next to unrestricted FHE evaluation is
not a security proof.

## 7. Required distinctions

- No retained unrestricted decryption credential is not absolute secrecy from
  permitted outputs.
- Deleting a named master-key file is not deleting all equivalent capabilities.
- A malicious initializer can keep a copy; ordinary software cannot prove that
  it forgot a secret. An erasure/setup assumption must be explicit.
- Known initial state plus known deterministic updates and inputs enables
  plaintext replay even if every stored representation is encrypted.
- Encoded states remain copyable in ordinary classical software. Preventing
  replay/fork quota bypass needs an independent continuity resource. That
  resource need not possess a decryption key.
- No-master-read confidentiality does not imply availability or protection from
  harmful authorized inputs.
- A successful FE/SFE component does not automatically provide active integrity,
  timing/access-pattern privacy, or end-to-end post-quantum security.

## 8. The next cryptographic acceptance test

After setup and claimed erasure, give an adversary every surviving software
artifact: function keys, input-encoding state, caches, ciphertext history, and
all operator-visible execution state. It may choose permitted observations and
queries and clone any copyable state. Specify precisely which hidden histories
must remain indistinguishable under this exposure and which externally
maintained resources, if any, enforce a unique continuation.

A candidate passes only with a theorem under this exposure model, not just an
API that omits `decrypt`. The bounded-history and streaming designs above have
not yet been instantiated or proved to pass this full test.
