# HIO: a bounded private-continuation construction and the missing joint extension

[DERIVED, 2026-09-08] Bhushan–Koppula–Prabhakaran's HIO gives a concrete way to
extend an obfuscated computation without repeated full nesting. Its proved
interface composes on the **output**; its input-side and DAG extensions are
sketched. Neither the core game nor the hierarchical-MIFE application gives
out the retained parent and child together. Thus the paper does not, as stated,
instantiate our exposed resident continuation interface. There is nevertheless
a meaningful positive construction: an issuer who knows only its own command
and an authentic public parent can privately specialize a bounded continuation
using ordinary iO. This removes the persistent encryption master from input
issuance. It has a joint-view proof for the explicit bounded game below, but no
useful repeated-size guarantee. A joint-secure, input-side version of HIO is the
specific remaining construction target, rather than another bilinear writer.

## 1. What the inspected source proves

[SOURCE: algorithms and game] The inspected version is *Homomorphic
Indistinguishability Obfuscation and Its Applications*, eprint2023/925 (ITCS2024).
Section4, printed pp10–11, defines

```
Obfuscate(lambda, C) -> O
Eval(O, x) -> C(x)
Compose(O, Cprime) -> Oprime       // represents Cprime composed with C
```

Its security experiment compares two equal-depth, equally padded chains whose
**final functions agree on every input**. It returns only the final obfuscated
chain. It does not return earlier obfuscations, compilation randomness, or
secret keys sampled during composition. The fresh-obfuscation remark on p11
also compares standalone distributions, not distributions jointly with a parent.
The size guarantee is polynomial in the security parameter and the entire list
of component-circuit sizes; it is not independent of history length.

[SOURCE: construction] Section5.1, pp12–13, represents the result by a list
`(Dhat_0,...,Dhat_k)`. Evaluation runs the list in order; after a nonempty chain
it removes an input tag from the last output. Each `Compose` creates fresh ACE
setup material and unrestricted encryption/decryption keys `(EK,DK)`, replaces
the old last node by an iO wrapper which encrypts its output, and appends an iO
wrapper which decrypts that boundary and evaluates `Cprime`. Thus one hop uses
one ACE setup, two key derivations and two iO invocations. Interior components
have two iO layers rather than nesting the whole old chain at each hop.
Evaluation still traverses every component. The p13 efficiency discussion gives
`O(sum_i |C_i|)+poly(lambda)` using its referenced iO implementation theorem;
this is an asymptotic source claim, not a measured implementation cost.

[SOURCE: reduction] Theorem3 and its proof, pp13–19 and AppendixB pp32–34,
use input-by-input hybrids. For an `n`-bit input domain there are `2^n` outer
steps, each with order `k` iO and ACE switches. The assumed subexponential
security is doing real work. In explicit advantage notation the source argument
has the form

```
epsilon_HIO <= O((k+1) 2^n) (epsilon_iO + epsilon_ACE-CD + epsilon_ACE-CT),
```

[DERIVED resource reading] Each epsilon here must be evaluated at the actual
padded circuits and reduction resources. If a primitive bound were
`2^(-kappa^c)`, the internal parameter would have to make `kappa^c` dominate
`n + log2(k+1)` and the desired slack. “Subexponential” does not erase the
`2^n` cost at a fixed parameter. The paper does not supply finite security bits,
practical iO costs, or a quantum-adversary instantiation for this application.

[SOURCE: extensions] Section7, p29, explicitly discusses prepending on the
input side, merging obfuscated chains, and a composition DAG. It supplies a
DAG construction outline: carry the original input; encrypt each child-root
output under a fresh ACE pair; decrypt at the parent; reject disagreement about
the original input. The proof is outlined using the same input-by-input
hybrids. It does **not** give a full input-prepending algorithm or a retained
ancestor/multiple-output security experiment. The stated DAG comparison has
equal topology and equivalent final functions. Calling the paper exclusively
an output-composition proposal would overlook this substantive extension;
calling the joint extension proved would overstate what was inspected.

## 2. H-MIFE changes delegation, not fresh writer custody

[SOURCE: complete algorithms] Section6.1, pp19–22, Figure13, starts with
secret-key function-hiding MIFE:

```
Setup -> msk
KeyGen(msk,f) -> HIO.Obfuscate(D_skf), where skf=MiFE.KeyGen(msk,f)
D_skf(ct_1,...,ct_n) = MiFE.Dec(skf,ct_1,...,ct_n)
Delegate(parent,g) -> HIO.Compose(parent, padded(g))
Enc(msk,x,i) -> MiFE.Enc(msk,x,i)
Dec(key,tuple) -> HIO.Eval(key,tuple)
```

[DERIVED custody] Delegation needs no MIFE master: a holder can narrow an
existing output through `g` after the master has been erased. This is a genuine
capability improvement. However, fresh ciphertext issuance in these algorithms
still takes `msk`, which can generate an identity/full-output key when the
function family includes it. No separate constrained writer credential is
constructed here. Deleting `msk` permits delegation over previously issued
ciphertexts but removes this issuance algorithm. Delegation retains the same
original `n` ciphertext slots; it does not introduce a fresh slot or renew arity.

[SOURCE: security and loss] The p20 game selects all paired message tuples
before setup, then requests one pair of function chains and receives only the
last key. Admissibility includes all cross-slot mixes of queried messages.
Theorem4 uses two HIO switches around one function-hiding-MIFE switch, giving
`2 epsilon_HIO + epsilon_FH-MIFE` at the reduction resources. The key circuits
are padded to the maximum decryption-circuit size for the composed functions.
This is not a game for exposed `msk`, multiple retained delegates, or continuing
private issuance under a restricted writer.

[DERIVED instantiation obligation] The proof on p22 invokes exact functional
equivalence of the two decryption chains. Applying it to a chosen FE backend
requires that equality on the whole input domain of the obfuscated circuits,
including malformed ciphertext strings, or a sound restricted-domain wrapper.
Honest-ciphertext correctness alone is insufficient to discharge that premise.
No concrete backend is being endorsed here.

[DERIVED output limitation] If `f(s0,x)=f(s1,x)` for all permitted inputs,
then `g(f(s0,x))=g(f(s1,x))` for every postprocessing `g`. Pure delegation
cannot recover hidden state omitted by the parent's output. Making that output
the entire plaintext state instead gives every retained parent holder a state
reader; making it ACK leaves no state from which an arbitrary new transition
can be computed. The continuation-function construction below changes the
parent's interface rather than attempting to evade this identity.

## 3. A concrete bounded construction using ordinary iO

[DERIVED algorithms] Fix one deterministic, bounded Step circuit, public policy,
canonical command encoding and horizon `T`. Define `R_s^H(h)` to return only
the released trace of running Step from state `s` on at most `H` commands.
Its input is a fixed-width encoded tape with a length field and canonical
padding; invalid encodings return FAIL. Initial setup publishes
`O0 = iO(R_s0^T)`, then retires the plaintext initial state/program and its
compilation records according to the state-origin trust assumption.

An issuer receiving **an authentic parent** `O_v` at depth `t<T` and knowing
its own private command `cmd` runs:

```
Issue(O_v, cmd):
    y = the first release in Eval(O_v, [cmd])
    Q_cmd(h):
        reject invalid residual tapes or residual length > T-t-1
        trace = Eval(O_v, canonical_prepend(cmd, h))
        return trace with its first release removed
    O_w = iO(pad_to_public_depth_bound(Q_cmd))
    return (y, O_w)
```

[DERIVED correctness] For an authentic parent representing `R_s^(T-t)`,
the new program represents `R_s'^(T-t-1)`, where
`Step(s,cmd)=(s',y)`. Removing the first release is necessary: otherwise
successive children accumulate old releases instead of implementing the
declared residual interface. The issuer never learns `s` from this algorithm
and never needs a secret encryption or key-generation credential. Its compile
input consists of its own command and the public parent's bytes.

[DERIVED meaningful behavior] The hidden state participates in each future
Step, rather than being an unused complement of a fixed projection. A holder
may evaluate all permitted continuations and fork from every old program.
Those future trace functions are the authorized capabilities; no single-history,
quota, destructive expiry, or rollback restriction is cryptographically
enforced. The horizon decreases with every specialization. Increasing tape
length at the next hop is not an operation of this fixed-domain construction.

[DERIVED private-input requirement] Publishing an obfuscated standalone
`P_cmd(h)=cmd::h` does not hide `cmd`: its evaluation reveals that command.
The issuer must privately specialize the parent and publish only the residual
program and authorized release. Its own observation can be known to that
issuer, but a game protecting that observation from the host cannot also expose
its plaintext or compilation record to the host. There is no reusable writer
secret whose copies can later produce coordinate probes.

### An explicit joint-view theorem for the bounded version

[DERIVED one-step theorem] Fix the same public authentic parent bytes `O` in
both worlds. Suppose commands `cmd0,cmd1` give the same immediate release and
the two padded residual circuits `Q0,Q1` agree on **every** encoded input,
including the specified invalid-input behavior. Ordinary auxiliary-input iO
gives indistinguishability of `(O,y,iO(Q0))` and `(O,y,iO(Q1))`. The retained
parent is auxiliary information and the challenge is the child obfuscation.
This is already stronger than applying the HIO final-only game incorrectly.

[DERIVED finite-forest theorem] More generally, fix a finite named issuance
forest of `N` nodes including roots, with maximum depth at most `T`. Each
nonroot node is privately issued from the named, honestly generated parent;
all published parent/child bytes are retained. Consider two executions with
the same public topology, depth-dependent padding and immediate releases.
Require each pair of canonical residual replay circuits at corresponding
nodes to be functionally equivalent on its entire remaining-tape domain.
Assume ordinary iO with auxiliary information at the largest actual circuit
and total experiment resources. Then the joint public transcripts are
indistinguishable, with a conservative loss at most `3N epsilon_iO`.

[DERIVED proof] In world0, replace each recursively wrapped nonroot program,
in issuance order, by an independent iO of its canonical residual replay
circuit, padded to the same public size. Exact correctness of every parent
makes these circuit pairs functionally equivalent, regardless of earlier
replacements. Previous outputs are auxiliary information; later issuance is
postprocessing of the challenge. This takes at most `N` iO switches. With
all nodes canonical, switch the `N` equivalent node circuits to world1; then
reverse the canonicalization in world1 using at most `N` more switches.
This proof covers every retained node, rather than asking for final-function
equivalence alone. It is an ordinary-iO construction, not a theorem attributed
to Section7. Its premise is full functional equivalence, not merely equality
of releases observed on the executed path.

[DERIVED scope] Arbitrary polynomial host computations, local forks and
evaluations **after receiving this view** are covered by postprocessing.
The stated theorem uses a fixed finite issuance forest. It does not silently
extend to a private issuer accepting arbitrary adversarial parent programs,
or to adaptive issuance with an unstated admissibility/corruption experiment.
For a protected private-issuance node the theorem excludes its private
obfuscation coins and unobfuscated command wrapper. Public-command descendants
can instead be generated with coins known to the host as postprocessing of an
already protected ancestor. No state-revealing setup artifact may survive.

### A nonvacuous family satisfying the residual-equivalence premise

[DERIVED, transported from `CONSTRUCTION.md` Section3] Use its two-coordinate
mistake-driven learner with `W=T+2` and state `(w0,w1)` in `[-W,W]^2`.
The predicted label is `+1` at a nonnegative weight and `-1` otherwise.
`Learn(i,y)` adds `y` to `w_i` only on a mistaken prediction and releases ACK;
`Infer(i)` returns the classification bit. NOP and invalid-command behavior
are fixed identically. Compare initial states `(a,T+1)` and `(a,T+2)` for
the same legal first weight `a`. Corresponding private issuance commands may
be identical, or may pair `Learn(1,-1)` with `Learn(1,+1)` in either order.
This permits distinct initial states and fresh private labels, rather than
merely two encodings of the same state and history.

[DERIVED all-residual-tapes proof] At every corresponding depth-`t` node,
the first weights agree: differing command pairs touch only coordinate1,
and all other commands agree. Each command lowers the second weight by at
most one, so both second weights are at least `T+1-t`. For **any** common
remaining tape of length `ell <= T-t`, and at every prefix of that tape,
the second weight is at least `T+1-t-ell >= 1`. Thus every second-coordinate
Infer returns one, while the two first-coordinate trajectories and answers
remain equal. Learn/NOP releases and invalid-input rejection also agree.
Consequently the canonical residual circuits are equivalent on their entire
remaining domains at every retained node of the named forest. Counting Infer
and NOP against this continuation horizon only strengthens the update bound;
it does not grant `T` additional updates after a prefix.

[DERIVED activity and limit] The first coordinate can still learn and change
answers: for `a=0` and `T>=2`, a negative Learn at coordinate0 moves its weight
to `-1`, changing the answer of a subsequent Infer. A private negative label
at coordinate1 also changes that hidden weight, whereas a private positive
label leaves it unchanged. Nevertheless, **the paired hidden differences never
affect an authorized answer anywhere within the full horizon**, including all
remaining continuations from retained prefixes. This is exactly why iO's
functional-equivalence premise holds, not a claim that iO hides different
authorized answers. For the initial pair `(a,T+1)` versus `(a,T+2)`, extending
past the contract with `T+2` consecutive negative coordinate1 updates yields
second weights `-1` versus `0` and different classifications. Such an extension
is unavailable to the bounded program and is not protected by this scheme.
No new experiment or enumeration is needed for this transported inequality.

## 4. Lifecycle and the two real limits

[DERIVED credential inventory]

| Actor/artifact | Continuing authority and required boundary |
|---|---|
| Initial state owner | Knows `s0`; creates the root. Raw state, unobfuscated root and recoverable copies are excluded from later host exposure. |
| Private issuer | Knows only its own command, public parent and fresh compiler coins. No state key or persistent writer key is necessary. Its own protected command/compile records are not supplied to the host. |
| Public host | Retains every obfuscation, release, policy, topology and algorithm. May fork and evaluate every permitted residual tape. |
| Recipient/evaluator | Needs only the appropriate residual program; there is no universal decryption master. Its authority is the full bounded continuation function. |
| Parent authenticator | Must ensure the private issuer receives the intended authentic descendant. This authenticates a public object; it need not read state. Acceptance of arbitrary privately formed descendants needs an additional provenance construction. |

[DERIVED input-binding obstruction] An attacker can substitute a purported
parent which returns its input tape as the released trace. A private issuer
would then wrap a program revealing `cmd` upon evaluation. iO does not make
an adversarial program a valid state origin. An authentic registered parent
chain therefore matters before **each** private issuance, not only at setup.
One can assume an authenticated honest issuance registry for the bounded
theorem; realizing acceptance of arbitrary hostile descendants without a
trusted registry requires an explicit proof/certification mechanism. Hiding a
command while proving correct specialization is an additional requirement,
not supplied by the simple wrapper or by the source's final-only game.

[DERIVED size barrier] Let `L_t` be the obfuscated program size and let
`P_iO(kappa,s)` bound iO output size. The direct wrapper has a recurrence of
the form `L_(t+1) <= P_iO(kappa, poly(L_t,T,|Step|))`. A generic polynomial
bound does not imply polynomial dependence on `t`: iterating a bound `s^a`
gives an upper envelope growing as `L_0^(a^t)`. Even a constant multiplicative
overhead can compound exponentially. These are limits of the available
guarantee, not a measured lower bound on every iO. The finite-forest theorem
applies only while actual circuit/experiment sizes lie inside the assumed
security resources. There is no practical iO backend here and no execution.

## 5. Why the source's final-only theorem is not the missing lemma

[DERIVED countermodel to an implication, not a source attack] Take any secure
core HIO and augment each object with an independent public random PRF key
`r`. Evaluation strips this auxiliary data. Composition strips the parent's
auxiliary fields before invoking core composition, samples the child's fresh
`r'`, and appends a tag equal to the private new circuit description masked
with a PRF stream under the **parent's** `r`. Retain only the new tag. Circuit
lengths are padded as in the original game. In a standalone final challenge
the old `r` is absent and independent of the core chain, so PRF security makes
the tag pseudorandom; correctness, efficiency and final-only HIO security are
preserved. With both parent and child, the parent exposes `r` and the private
new circuit is recoverable. The current fresh `r'` does not help protect it.

[DERIVED implication] Thus final-only HIO security does not logically imply
privacy of a private specialization jointly with the retained parent, even
when parent functions and final functions agree. This construction says
nothing adverse about the actual ACE-based implementation. It prevents using
the wrong abstract theorem as its proof.

[OPEN concrete next lemma] Give the Section7 input-prepending operation in
full, with canonical domain/invalid-input rules, then prove security for an
exposed forest retaining every ancestor and child, under the corresponding
whole residual-function equivalence and explicit issuance/authentication
schedule. Account for all ACE keys, shared chain components and compilation
coins in that joint view. A final DAG whose output is a tuple of node values
is not automatically the same distribution as publicly retaining all original
unwrapped node encodings. Establish polynomial total size and the precise
input-domain security loss for this joint construction. The source's flat
composition machinery gives a specific route to try, but this note does not
claim to have proved that extension.

[DERIVED decision/status] This is a positive conditional public-issuance
advance over the prior fixed-slot secret-key Replay interface: the direct
bounded wrapper needs no continuing encryption master and handles private
commands using only an authentic public parent. It is not the compact,
arbitrarily continuing resident targeted in
`../multi_hop_successor_2026_09_08/FRONTIER.md`. The critical path is the joint
input-side HIO construction and origin binding, together with its real size
bound—not an H-MIFE writer rename, a weaker two-input demo, or a claim that
plain iO recursion is practical. No PQ or concrete-security claim follows.

## Source record and next handoff

[SOURCE] Primary source: https://eprint.iacr.org/2023/925, local mirror only:
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2023/925.pdf`.
PDF SHA256: `f1a689cef440625a0b05a88fd544d6ef1f256d03c7894644d8270923db6b9b0f`.
Inspected full definitions/algorithms/proofs: Sections3.1–3.3,4,5,6.1,7 and
AppendixB at the printed pages cited above.

[EXECUTED source extraction] `pdftotext -layout` produced
`sources/2023-925.txt`, SHA256
`8609e43f898df47f45f57a4b4538c9ded337f7f72fd302e9fd18e42fc2347326`.
This task used zero web queries, zero Scry SQL calls, zero PDF downloads and
zero cryptographic/estimator/runtime experiments. Earlier lane and parent
query counts are separate. Local source inspection used `rg` and text reads;
the zero external-query counts do not mean zero local source searches.
Existing frontier notes were read for comparison;
original implementations, companions, shared ledgers and `SOURCES.json`
were not changed.

[OPEN next] Root can choose whether the explicitly bounded authenticated
ordinary-iO construction merits further theory, or whether to work directly
on joint input-side HIO. No independent-review queue or implementation launch
is required to receive this source-grounded result.
