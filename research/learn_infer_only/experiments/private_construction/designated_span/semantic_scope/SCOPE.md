# The privacy functionality of the fixed-span learner

[DERIVED conclusion] The achieved mathematical target is **host-private
additive state with recipient-private projected answers, and privacy of
each issued input modulo the surviving recipients' full projection span**.
It is stronger than keeping a universal reader key in a trusted service:
after the stated honest erasure, the listed surviving scalars need not
determine the raw vector master. It is weaker than a cryptographic
Learn/Infer-only interface against every surviving credential holder.
Those holders can read their complete projection space on each retained
input, without waiting for the selected aggregate release.

[SOURCE boundary] The parent [contract](../CONTRACT.md), lines 53–76 and
104–113, states the fixed-span and continuity scope. The designated backend's
[specification](../crypto/README.md), lines 118–132, distinguishes that
mathematical privacy from implementation proof. The frozen
[construction review](../review/REVIEW.md), sections 3–5, supplies the
credential view-equivalence and conditional adaptive-message game; the
[general fixed-span note](../../fixed_span/scaling/GENERAL_FIXED_SPAN.md),
lines 92–145, supplies its quantitative reduction. Exact snapshots and
read scopes are in `sources.json`.
Integration/execution status remains owned by the parent; a contract or
backend specification is not evidence that its complete protocol has been
proved secure. This is written mathematics only. No construction, disclosure,
routing or runtime experiment is run here.

## 1. An ideal selected-release functionality

[DERIVED definition] Fix a route set, FIFO capacity `W`, public rows `Y`,
recipient assignment and the public admission/finality policy. Each route
has a private ordered queue `Q=(x_1,...,x_n)`, `n<=W`, and aggregate
`S=sum_j x_j`. Hold public history metadata equal when comparing two worlds.
An ideal selected-release service would implement:

| Command | Private transition | Intended information delivered |
|---|---|---|
| `Learn(route,id,x)` from an admitted issuer | Append `x`; expire the oldest record if needed | Public acknowledgment and declared metadata, including any public count/expired identifier |
| `Infer(route,i,recipient)` with valid authorization | No plaintext state change | Only `<y_i,S>` to its designated recipient, or the specified narrower answer if that is the contract |
| Authenticated checkpoint/continuation | Preserve this state and its admitted history | Only declared public continuity metadata |

[DERIVED] The exact public leakage must list identifiers, route, row,
recipient, lengths, counters and any other disclosed metadata. A later
public score, sign, decoding-success flag or value-dependent timing is
additional information; it is not hidden by placing the key file elsewhere.
The intended interface is indexed by the **actual authorized history**, not
by every computation someone could perform on a saved ciphertext.

[DERIVED] An ideal confidentiality refinement of this service would protect
two histories whenever their public metadata and actually delivered
recipient outputs agree for the observed/corrupted parties. A claim that
the real view is simulatable from that leakage is stronger than merely
matching the service on honest inputs or validating its signed history.

## 2. What the surviving DDH credentials actually authorize

[SOURCE/DERIVED] In the reviewed designated package, `tau_i+a_i=<s,y_i>`.
For a fixed coalition `J`, possession of its recipient scalars and the
public tokens is exactly equivalent to possession of all ordinary IPFE
projection-key scalars for `Y_J`. The equivalence includes correlated public
keys, redundant rows and arbitrary efficient uses of the available material.

[DERIVED] Thus a faithful leakage profile for this **primitive layer** is

```
L_J(history) = declared public metadata
              + (g^(Y_J*x_t)) for every issued input t
              + any separately disclosed endpoint information.
```

The vector notation means one group element per independent projection;
all span combinations are available. It includes retained inputs later
expired from the live queue and all snapshots derived from them. Where an
honest integer interval permits efficient unambiguous decoding, the
corresponding integer projections are available too. The decoder's interval
does not narrow the algebraic credential to a sign or to one chosen call.

[DERIVED] The established DDH theorem is an adaptive-message **IND** statement
for equal `L_J` projection histories, under its private setup/issuance and
sampling assumptions. Naming `L_J` characterizes that equivalence relation;
it does not by itself establish a complete real/ideal or UC simulation theorem
for the journal, signatures, source attestations, receiver and corruption
schedule. The separate adaptive-recipient result has an explicit
subset-guess loss and a precisely stated admissibility game.

| Observer | Mathematical privacy profile |
|---|---|
| Host, with no recipient secret and no private-answer feedback | Full input IND hiding; no projection-equality restriction |
| Host plus fixed recipient coalition `J` | Input IND hiding modulo `ker(Y_J)`, independently for every issued input |
| All listed surviving recipient credentials plus host | The full fixed row span on every input; a proper raw-state kernel remains only when rank and input-domain nonvacuity conditions hold |
| An honest receiver service following its finality checks | Actual selected outputs follow that service's policy; this is not a restriction on someone possessing the same raw recipient scalars |

[DERIVED separation witness] Consider two otherwise identical histories
consisting only of an acknowledged `Learn(x)` from an empty queue, with no
Infer yet. If `Y_J*x != Y_J*x'`, their intended selected-release leakage can
be identical while their primitive projection leakage differs. Therefore
the raw-credential package cannot be said to realize acknowledgment-only
Learn confidentiality against `J` from the **completed selected trace**.
This is a specification-level separation, not a runtime extraction test.

[DERIVED] Cryptographic history/recipient binding and this leakage question
are different obligations. An honest receiver may refuse an unfinalized
object, while its scalar credential still permits the fixed projection
outside that receiver program. The former is meaningful protocol enforcement
under the receiver's stated trust; it does not erase the latter capability.

## 3. The exact behavioral quotient: aggregate versus FIFO state

[DERIVED definition] Two private states are behaviorally equivalent for an
observer if every permitted finite continuation using the same future inputs
and commands yields the same observable answers. For adaptive command
selection, equal earlier answers force the same later command choices, so
a relation preserved by each transition gives equal adaptive traces. Public
metadata and admission state are held equal separately.

[DERIVED aggregate lemma] For a state vector with only additive updates
`S<-S+u` and fixed linear observations `Y*S`, the equivalence is exactly

```
S ~ S'  iff  Y*(S-S')=0.
```

Necessity follows from an immediate differing row observation. Sufficiency
follows because equal additions preserve the difference, and every selected
row annihilates it. A plaintext machine storing `Y*S` has exactly the same
permitted behavior. A direction in `ker(Y)` cannot affect a future answer
under these transitions.

[DERIVED FIFO lemma] For an ordered bounded FIFO, the quotient is generally
**not just the current projected aggregate**. Assuming zero inputs are
admissible and the observer can obtain the relevant row observations during
a sufficiently long continuation, equal-length queues satisfy

```
(x_1,...,x_n) ~ (x'_1,...,x'_n)
    iff  Y*x_j = Y*x'_j for every ordered slot j.
```

Sufficiency is immediate: the ordered projected queues remain identical
under equal appends, FIFO expiry and observations. For necessity, fill any
unused slots with zero inputs, then append zeros until the old entries have
expired in order. Let `P_j` be the observed projected aggregate after the
first `j` original records have expired, including `P_0` before that starts.
Then `P_(j-1)-P_j=Y*x_j`. Equality of all permitted continuation answers
therefore forces equality in every slot. This is a symbolic quotient proof;
no such continuation is run in this tranche.

[DERIVED] Consequently a plaintext queue of projected records, together with
the public FIFO metadata, realizes the fixed learner's complete observable
behavior. Two queues whose projections cancel in the current sum can still
be distinguished by later legitimate expiry. A recordwise kernel difference
is the part that remains forever behaviorally irrelevant.

[DERIVED scope] The necessity argument assumes the continuation and readouts
it names are actually permitted. A finite query quota, restricted issuer
admission, inaccessible recipient outputs or a shorter horizon can produce a
coarser observational equivalence. Their resources must be included in the
ideal machine. Algebraic raw-key access does not acquire those restrictions
merely because a separate live service has them.

## 4. Interface learnability and cryptographic privilege are distinct

[DERIVED] Learning ordered projected records from genuinely permitted
aggregate observations during a permitted continuation is **ideal-interface
learnability**. Even an ideal cryptographic implementation would communicate
those answers. This does not refute a property saying the running code
provides no additional inspection privilege.

[DERIVED] Obtaining every projection immediately from an input ciphertext,
or after that input is gone from the only authorized live history, is an
additional **credential capability** relative to the actual selected trace.
It may coincide with information obtainable under a more permissive,
unbounded or copyable interface. That coincidence does not establish
simulation from the narrower completed trace. Both the observer and the
allowed continuation resources have to be fixed before comparing claims.

[DERIVED] The phrase “hidden state affects future behavior” also has two
meanings. A direction hidden from **the answers seen so far** can affect a
later permitted answer. A direction in the kernel of **every possible
future behavior** cannot do so, by the definition of behavioral equivalence.
A useful protected learner need not have a large forever-unobservable kernel;
it can have behaviorally identifiable state while restricting access to the
permitted computations. Cryptography cannot erase information the ideal
interface itself reveals.

[DERIVED] The present linear package exposes the whole plaintext behavioral
quotient to the full credential coalition, record by record. Its remaining
encrypted kernel does not contribute to the fixed learner's behavior. Thus
absence of a raw vector-master scalar is not yet absence of an export of
all **behaviorally relevant** state. This is why raw ambient dimension minus
matrix rank is an incomplete measure of progress toward machinic mental
autarky. It remains a real host-confidentiality and restricted raw-state
privacy result under the stated assumptions.

## 5. Narrow next step and remaining target

[DERIVED proposal] `LINEAR_CONTINUATION.md` gives one positive next
functionality: a finite public family of invertible linear state transitions,
implemented in a moving public encryption frame. Previously unobserved state
can affect a later permitted answer. The exact observable span is computed
to closure, and a proper closure avoids issuing a raw master/read-all key.
It uses the existing DDH equations and independent mask basis; it does not
require publishing a scalar correction vector.

[DERIVED limit] That next step still preissues the entire closure's projection
capability to the intended recipient bundle. It advances protected state
continuation, but it does not by itself enforce selected-trace-only disclosure
against the bundle holder. The stronger next cryptographic obligation is a
restricted transition/release capability whose surviving implementation
communicates only the selected authorized outcome. A local decoder check
around a scalar that already opens richer projections is insufficient.

[OPEN] Post-quantum assumptions, nonlinear private updates, receiver-independent
release enforcement, actual encoder-image nonvacuity, private-ingress
provenance and public-output learnability remain separate targets. This note
neither resumes a stopped runtime investigation nor proposes an unbounded
survey. It specifies the precise positive and the next algebraic seam.
