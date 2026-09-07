# Conditional privacy of the designated-span protocol transcript

[DERIVED, implementation contract] This argument connects the reviewed
designated-span primitive to a public journal and a recipient that verifies
before accepting an output. It is a conditional transcript argument. The
implementation is still being built; no statement here establishes that its
actual bytes, process access or timing meet every premise.

## Exact experiment and exposed roles

[DERIVED definition] Fix the group family, dimension, public rows Y, recipient
assignment, window capacity and route policy before secret setup. Fix a recipient
coalition J as a subset of these row/recipient slots before setup; a later
concrete identity may be a public function of its generated key and context.
The host may know every journal, issuer and command authentication secret.
Generate these dedicated keys with fresh coins independent of the entire
designated setup and its private coins, including every recipient scalar;
use independent authentication-operation coins thereafter. Adaptive messages
may depend on already exposed authentication keys, so no unconditional
independence of those keys from all later messages is asserted. It may know
recipient scalars for J and all their setup messages. It does not receive the
initializer's master/copies, its retained projection scalars k_i outside J,
private delivery/pending copies of those scalars, any other master-correlated
auxiliary secret outside the specified K_J view, fresh input randomizers,
noncoalition recipient scalars or the private issuer's input history. Honest
private setup and erasure are explicit assumptions. No extra possession proof
or prior-use transcript under a noncoalition a_i is silently included.

[DERIVED definition] The adversary chooses at most T adaptive pairs of bounded
input vectors (x0,x1) with identical declared public metadata. A single hidden
bit selects the issued side, freshly encrypted each time. Every pair must
satisfy Y_J x0=Y_J x1 modulo q; a failing pair gives the same fixed public
rejection and final output in both worlds. Publicly known input encryptions
may also be generated directly. T counts all challenge issuances visible to
the host, including unfinalized, retained, expired and forked inputs, not only
the currently installed window or the final accepted history.

[DERIVED initial state] The public history starts with empty queues and the
known zero state ciphertext (the group identity). Every other exposed object
is computed from the setup, challenged issuances and independent role coins.
Any private initial state ciphertext must instead be included as an admissible
challenge issuance with its own declared metadata and charged count; arbitrary
private initialization is not supplied by this public postprocessing argument.

[DERIVED definition] The view includes complete public context and tokens,
all issued ciphertexts and input authorizations, public query choices,
canonical journal requests, receipts, ciphertexts, snapshots and public
acceptance/retry results. It includes any efficient computations using J's
credentials. A noncoalition recipient's private answer and decoding trace
are not in this view. The intended public acknowledgment is issued after
durable acceptance of an encrypted output and **before** private decoding.
Every later public retry, status, error, delivery count and persistence effect
must also be independent of the private drain's value, success and progress.
A separate private answer database must not silently influence those public
branches. This condition covers the complete public transcript, not just its
first acknowledgment.
Any later recipient feedback must either be generated from already allowed
leakage or added explicitly to the experiment.

[DERIVED modeling boundary] Runtime timing, memory access, process inspection,
secret-dependent setup/issuance diagnostics and physical side channels are
excluded. Shared-account execution is not evidence that this boundary exists
against the computer's operator. Public lengths and metadata are included;
paired inputs must have the same public encoding shape. A real private text
encoder requires a separate proof that its observation-generation process and
public metadata meet this vector-issuance experiment.

## Reduction by public postprocessing

[DERIVED] Start from the ordinary fixed-key IPFE experiment for rows Y_J.
Use the exact setup simulator in [the reviewed lemma](review/REVIEW.md): choose
uniform tau_i, derive A_i=product(h_j^y_ij)/g^tau_i, and reveal
a_i=k_i-tau_i for i in J. This reproduces the entire designated package and
coalition setup messages exactly without the master. Independent role
authentication keys and public context bindings are then generated locally.

[DERIVED] Forward each valid input pair to the IPFE challenger. The returned
ciphertext has exactly the distribution of the real issued object. Its
canonical wrapper and the issuer's signature can be computed from public
metadata and these bytes. Every subsequent insertion, exact-original expiry,
fixed-row transform, public validation, journal signature and local retry is
an efficient operation on this visible history and independently sampled role
coins. Simulating it needs neither an input plaintext nor the encryption
master. Shared aggregate randomness and histories that reuse a retained
ciphertext are already covered by deterministic public postprocessing of the
freshly randomized issuance history.

[DERIVED] The simulator can execute any coalition recipient algorithm using
its exactly simulated scalars. For noncoalition recipients, it simulates only
public acceptance and persistence, which by premise do not depend on private
decoding or its result. This is why merely hiding decoder stdout while delaying
a public acknowledgment until a variable-time decoder finishes would not
justify the stated public-view premise.

[DERIVED conditional bound] Let k_J=d-rank(Y_J) and let M be the least power
of two at least max(1,T*k_J). Under the scalar-sampling and classical DDH
resource conventions of the reviewed general fixed-span lemma, the complete
protocol output-probability gap satisfies

```
Delta_protocol <= 2*M*epsilon_DDH.
```

[DERIVED] The extra simulator work includes the actual public context,
authorization, journal and verification operations; its cost must be charged
to epsilon_DDH's adversary envelope. No signature-security or hash-collision
term is needed merely for this privacy postprocessing argument: the simulator
can give those independent role secrets to the adversary and run the literal
public algorithms, including their failures. Claims of authenticated integrity,
canonical identity or continuity have separate assumptions and correctness
obligations. This argument does not prove them.

[DERIVED] For J empty, there is no projection compatibility restriction. For
all recipients together, every individual input must agree on all fixed rows.
The bound is zero when the game admits only identical inputs. A fixed 2048-bit
group execution supplies no numerical security level or post-quantum claim.
The reviewed capped-sampling correction must be applied if using its strict
bounded-time convention instead of exact expected-time uniform sampling.

## Meaning of the no-master claim

[DERIVED] The listed surviving recipient scalars recover only their fixed
projection-key span. The initializer's unrestricted scalar master is absent
only under honest erasure of all copies. An issuer coalition that already knows
the complete deterministic input history and initial state can reconstruct
that state by replay; cryptography does not erase prior knowledge. This
transcript experiment therefore protects private issuance from the host and
specified recipients, not from an omniscient coalition of all input sources.

[DERIVED] Actual keys reveal more than one selected aggregate answer: they
permit each retained input's full coalition projection span, arbitrary public
linear combinations and counterfactual continuations. A plaintext behavioral
implementation can maintain the ordered queues of these projected records.
The hidden common kernel cannot affect any of the fixed linear answers.
Neither ambient rank deficiency nor encryption of a public fixture proves a
private useful mental state on the actual text encoder's image.

[OPEN implementation correspondence] Check the completed CLI and integration
against this view: honest setup/delivery, no exported master, independent input
coins, complete context pinning, recipient-only credentials, public acceptance
before private decode, public log fields, and independent integer results.
The normal functional suite can establish concrete data flow and arithmetic.
It does not establish cryptographic hardness, physical erasure, side-channel
exclusion or enforcement of the recipient's local software policy against that
recipient.
