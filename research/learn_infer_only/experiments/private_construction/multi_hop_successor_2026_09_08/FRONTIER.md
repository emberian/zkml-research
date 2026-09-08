# Multi-Hop FE and an exposed continuation capability

[DERIVED result, 2026-09-08] The new Multi-Hop FE lead cannot yet replace the
verified T-slot Replay compiler on inspected evidence: its full construction
and game were not found in the bounded source search. The useful next interface
is precise: a **parent-specific continuation capability**, issued before a fresh
observation, that can specialize only the fixed Learn/Infer Step after that
observation's ciphertext exists and that produces another restricted capability.
All such capabilities must be covered jointly by security. This note specifies
that design, a nontrivial continuing privacy family, and a narrow impossibility
for deriving its public specialization using only previously issued hop keys.
It does not claim an implementation of the missing capability.

## 1. What the primary source actually says

[SOURCE abstract only] Jiaxin Guan's publication entry for Datta–Guan–Korb–Sahai,
“Multi-Hop Functional Encryption,” TCC2026, describes computation DAGs with
intermediate releases and forwardable encrypted state. It announces simulation
security from standard FE for circuits, while retaining a central key issuer.
Its advertised game orders hop-key queries after the incoming ciphertexts/keys
are fixed. The entry has abstract and bibliography controls but no paper link.
https://www.guan.io/publications/

[SOURCE access limits] Korb's inspected publication page gives no MHFE entry;
Sahai's homepage points to publication indexes. The official TCC2026 page fetch
failed. Six targeted web searches and one OpenAlex/Scry SQL did not locate a
full paper. A `pdftotext -f 1 -l 2` scan of every1855 existing2026 mirror PDF,
with whitespace normalization and the title regex in `search_local.py`, found
zero matches and zero extraction errors. This covers those front pages, not
other years, unmirrored uploads or unindexed private manuscripts. No PDF was
downloaded. `sources/local_search.json` and `SOURCES.json` retain exact scope.

[OPEN] No actual MHFE Setup/KeyGen/Forward signature, issued-key contents,
public-writer credential, compactness guarantee, corruption experiment or
reduction is available for inspection here. A security-game timing condition
alone does not show that KeyGen syntactically takes ciphertext bytes, nor that
keys are reusable on different incoming tuples. Neither is assumed below.

## 2. The new closed-state design to ask the primitive to realize

[HYPOTHESIS interface, not attributed to the paper] Let Step be one fixed bounded
circuit whose state/output pair is

```
Step(s, Learn(i,y)) = (mistake_update(s,i,y), ACK)
Step(s, Infer(q))   = (s, class(s,q)).
```

Use the exact mistake-driven two-coordinate update from the Replay successor:
class(s,q)=1[s[q]≥0]; add label y∈{-1,+1} to coordinate i only on a mistaken
classification. Invalid canonical commands yield FAIL and no authorized child.
Private Learn addresses/labels and public Infer queries are issued using one
public command-encryption interface. No arbitrary function descriptor is an
argument to the following public algorithms.

```
Initialize(lambda, s0, Step):
    run the actual scheme's setup, obtaining pp, input EK, state issuer and MSK
    C0 = issue the initial encrypted state
    D0 = restrict the issuer to this exact parent C0 and the fixed Step
    publish (pp, input EK, C0, D0)
    erase MSK, raw state issuer, initialization plaintexts/coins and copies

Issue(EK, cmd; r):
    return X = EncInput(EK, canonical(cmd); r)

Specialize(Dv, X; u):
    return a hop key K[v,X] restricted to parent Cv, input X and Step

Run(K[v,X], Cv, X):
    return (released y, next encrypted state Cw, next continuation capability Dw)

Resident state = (Cv,Dv).
```

[HYPOTHESIS crucial distinction] Dv is issued before X exists; K[v,X] is created
only after X exists. Thus ordinary **hop-key timing** can remain topological.
Security must additionally cover the earlier exposed Dv, which can generate many
such hop keys locally. Treating Dv merely as an ideal key oracle removes the main
exposed-software question. Its complete bitstring and white-box use are part of
the adversary's view. A root master key embedded in an ordinary script is not an
instantiation. A source-proved restricted cryptographic credential might be.

[HYPOTHESIS parent binding] Dv cannot specialize another parent, select identity
or a coordinate-reader circuit, create an unrelated state origin, or change the
policy. Dw is bound to the precise Run output and the same policy. The necessary
cryptographic origin/binding property must hold for adversarial use of all old
Dv, K[v,X], Cw and input EK, not only for an honest API caller. Copying a capability
and creating many allowed children is permitted. There is no linear-resource,
single-history, quota or rollback claim.

[DERIVED resource target] A real replacement for Replay needs explicit bounds
on |Cv|+|Dv| and per-hop work polynomial in lambda and the fixed state/command
width, independent of the accumulated transcript length (or with a stated
polylogarithmic index overhead). Returning an opaque string containing the entire
prior program/history does not meet this target. The abstract's forwardability
claim is not taken as this compactness theorem. Public archives may grow with
use, but honest continuation should need only the current pair and new input.

[HYPOTHESIS complete surviving credential list]

| Surviving item | Intended power that must be proved |
|---|---|
| Public pp and input EK | Issue arbitrary commands; no new state origins or functions. |
| Current and all old Cv | Forwardable state ciphertexts; public metadata/ancestry. |
| Current and all old Dv | Specialize the fixed Step for any fresh command ciphertext, only at that parent. |
| Every generated K[v,X] | Run the fixed node, obtain its permitted output and child pair. |
| Raw state issuer/MSK, setup/compiler trapdoors and unobfuscated copies | Erased, never part of the surviving view. |
| Issuer input/coins | Known to that issuer; erasure or explicit corruption leakage is required. |

[DERIVED] If the actual central credential can still issue an identity-output
node on a live state, correctness alone makes it a full reader. A wrapper that
chooses to request only Step does not restrict the retained credential. This is
a test to apply to the eventual source algorithms, not a conclusion about their
unavailable key formats.

## 3. An exact extra security obligation

[HYPOTHESIS joint exposed-capability game] A uniform PPT adversary receives the
entire Initialize output, including D0, and may make adaptive paired command
ciphertext requests under a common challenge bit. It can run Specialize/Run
locally, inspect every resulting bitstring, retain archives, fork, submit public
commands and postprocess arbitrarily. Every delegate and hop key is exposed.
The hidden-state/command pairs must give the same released values on the allowed
forked graph; public lengths/context and explicit corruption leakage agree.

The required theorem is IND for this **joint view**, or a stronger simulator
producing that whole view from the allowed Step outputs. An ideal simulator must
produce actual exposed credential bytes under its stated simulated setup; it
cannot silently give the real host a private online key-generation service.
Any source reduction must explain how these bytes and future local specialization
are generated without the challenged master or plaintext state. A proof only
about the distribution of keys returned by honest calls does not do that.

[DERIVED conditional resident theorem] If a concrete scheme implements section2,
its correctness and origin binding hold for the stated admissible graph, and
its joint exposed-capability game is secure, then the above resident implements
an encrypted closed Step transition. Correctness is induction on graph ancestry;
all cryptographic operations and artifacts are exactly the game's operations
and view, so an IND distinguisher for the resident is a same-advantage game
adversary, with no additional per-hop hybrid. For a Q-step correctness bound,
use the actual primitive's adaptive correctness/binding guarantee; a Q·delta
union bound is justified only when the primitive supplies that per-step bound.

[DERIVED scope] This is a conditional interface theorem, not an instantiation
from standard FE or from the author abstract. It isolates a smaller concrete
construction target than general reusable obfuscation: one fixed policy, one
honestly initialized origin, public fresh command issuance, and descendant-only
self-delegation. The next source read can check each item directly.

## 4. Why legal topological hop-key replies alone are insufficient

[DERIVED new scoped obstruction] Consider the following **explicit input-bound
hop interface**, not a claim about the unavailable MHFE syntax. A descriptor d
contains canonical incoming object identities and the node function. A master
can issue k←HopKey(msk,d); Run accepts k only for that descriptor. The ordinary
security game issues keys after d's incoming objects are fixed. Suppose a correct
secure scheme exists for this interface.

Wrap it with an independent EUF-CMA signature scheme:

```
Setup+:        (pp,msk) ← Setup; (vk,ssk) ← Sig.KeyGen
HopKey+(d):    k ← HopKey(msk,d)
               sigma ← Sig.Sign(ssk, encode(d,k))
               return (d,k,sigma)
Run+((d,k,sigma),d',inputs):
               require d=d' and Sig.Verify(vk,encode(d,k),sigma)
               return Run(k,d,inputs)
```

[DERIVED preservation] Signature correctness preserves honest correctness.
For a topological security experiment whose exposed keys are produced by the
issuing oracle, a reduction samples the signature keys independently and signs
whatever real/simulated base keys it receives. It can likewise verify/strip
wrappers in later public operations. All additional fields are efficient
postprocessing of the base view and independent signature coins. Thus the
wrapper retains the underlying per-node security under this explicit interface.
This argument does not assert preservation of any additional, uninspected
paper feature such as applying one key to arbitrary future incoming tuples.

[DERIVED oracle-only preprocessing theorem] Let an offline PPT compiler receive
pp+ and at most M legal HopKey+ replies, but **not msk or ssk**. It exports any
polynomial-length public string rho, including all its working state. Afterward
it has no issuing-oracle access. A fresh valid descriptor d* is sampled with
conditional min-entropy at least h given the complete preprocessing transcript.
An arbitrary local online algorithm gets rho and the new incoming objects and
tries to return an accepted HopKey+ for d*. Then

```
Pr[accepted newly synthesized hop key]
    ≤ Adv_EUF-CMA(B) + min(1, M·2^(-h)).
```

The signature reduction B has at most M signing queries and runs the compiler,
input sampler and online algorithm plus the base scheme simulation. The input
sampler must be PPT and simulatable using that base setup and public history;
no unknown signing-secret-dependent advice is allowed.

[DERIVED proof] Let D be the at-most-M descriptors queried offline. Conditioned
on each preprocessing transcript, the chance d*∈D is at most M·2^-h. If d*∉D,
an accepted wrapper contains a valid signature on encode(d*,k*), a message never
submitted to the signing oracle, regardless of k*. B generates the base setup
locally, uses its signing oracle to answer preprocessing queries, then outputs
that new message/signature. Therefore acceptance outside D is an EUF-CMA forgery.
Average over the transcript and add the two events. No assumption that encryption
coins are injective is used to invent h. An independently sampled nonce included
injectively in d* is one explicit way to meet the entropy premise.

[DERIVED numerical illustration only] If an honest future descriptor has128
fresh uniform nonce bits and the table holds M=2^20 descriptors, the prebound-hit
term is exactly2^-108. This is table coverage arithmetic, not a security-level
claim or an attack estimate. Signature security supplies the separate term.

[DERIVED precise boundary] This rules out a generic **key-oracle-only offline
specializer preserving this wrapped interface**, unless forging is feasible or
preprocessing covers the future descriptors. It does not rule out using msk/ssk
during setup to cryptographically compile a restricted rho and then erase them;
that is exactly the white-box joint-view construction still needed. Nor does it
rule out a different ciphertext format, another primitive, online trusted
issuance, weak freshness, or reusable unbound keys under a separately proved game.
The unavailable paper might contain relevant structure beyond its abstract.

[DERIVED consequence for the lead] Replacing the central issuer by a polynomial
library of already issued keys or by a purported simulator that only asks legal
past key queries is not a generic consequence of the announced topological game.
A genuine pre-input delegate Dv may solve the problem, but its exposure must be
part of the construction/reduction. This obstruction concerns source-theorem
transport, not a cryptographic break or a field-wide impossibility.

## 5. A continuing nontrivial privacy family for the proposed interface

[DERIVED semantic witness, no cryptography assumed] The earlier Replay witness
used a fixed T margin. For a continuing polynomial-time game, choose lambda-bit
signed weight encodings with W=2^(lambda-1)-1 and initial second weight
A=2^(lambda-2), lambda≥3. Let the first coordinate start at zero. The same
mistake-driven update preserves [-W,W] forever, so state/command widths stay fixed
as the learner continues; arithmetic does not need a growing observation tape.

Permit protected command pairs to differ only between Learn(1,-1) and Learn(1,+1),
or be identical. Every branch containing at most Q Learn operations satisfies
w1≥A-Q. For any fixed polynomial Q(lambda), eventually Q(lambda)<A. All released
second-coordinate classifications then agree, first-coordinate trajectories
agree, and Learn releases ACK. This remains true for every allowed fork and
adversarial common command substitution within the Q-operation game.

[DERIVED nonvacuity] A private negative observation changes A to A-1; a positive
one leaves A. The difference is part of the evolving model, not ignored padding.
A subsequent sequence of A negative observations separates their classes, but
requires exponentially many operations in lambda. Coordinate0 can learn and
change its classification repeatedly during a polynomial run. Thus a joint
capability theorem would protect a semantically active observation bit under
all surviving credential exposure, without a horizon T fixed in setup. This
witness establishes a nonempty privacy game, not practical learning utility or
privacy for every data pair. The ideal necessarily reveals authorized outputs.

[DERIVED] A full reader of the second weight would distinguish the protected bit
immediately in this family, whereas the allowed polynomial Step interface cannot.
Consequently the conditional privacy property is stronger than merely omitting
a filename called master key. It remains conditional on the missing joint
capability theorem and the runtime/resource properties in section2.

## 6. Outcome and next decisive source facts

[DERIVED decision] Keep the existing T-slot Replay result as the inspected
positive. The MHFE lead supports a sharply identified research target, not a
replacement construction yet. The public parent-specific delegate is the new
closure design; its joint security and compact generation are open. The
oracle-only preprocessing obstruction explains why a generic call-oracle
argument is insufficient and leaves setup-time cryptographic compilation open.

[OPEN when the full paper is available] Inspect the exact forwarding object and
whether it already contains a restricted delegatable key; whether a public input
issuer retains a master/read-equivalent credential; whether all such forward
objects and future hop keys are exposed in the SIM game; whether incoming-object
fixing is a game condition or literal key binding; and whether size/work remain
bounded through polynomial depth. No further broad survey or review layer is
needed before those algorithms can be read.
