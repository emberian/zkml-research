# A tagged encrypted-witness backend for public HIO provenance

[DERIVED, 2026-09-09] The custom online simulation/extraction interface in
`HIO_PROVENANCE.md` can be constructed from established primitives: perfectly
correct IND-CCA2 public-key encryption and an adaptive, unbounded
simulation-sound NIZK for NP with its standard simulated-CRS interface. The
certificate encrypts the exact edge statement together with its command and
compiler coins. Online extraction is ordinary decryption plus public checks.
The exact statement tag resolves challenge-ciphertext reuse in the CCA
reduction, including adaptive extraction feedback. This is a derived generic
backend and security argument, not a cryptographic implementation or a new
size bound for iO.

## 1. Source match and the precise choice of primitives

[SOURCE: nearby construction] Dodis–Haralambiev–López-Alt–Wichs,
eprint2010/154, Section4.4 Theorem4.5, printed p11, constructs true-simulation
extractability from labeled CCA encryption of a witness function and NIZK.
Definition3.1 pp8–9 and AppendixA.4 pp21–22 give its game and reduction.
The simulation-query game supplies a valid witness and tests one final
extraction. Section4.5 also identifies the CPA-encryption plus simulation-sound
NIZK route to any-simulation extractability. These are close established
constructions, but they are not taken as an automatic theorem about our
unknown-witness queries and online feedback. The explicit tagged compiler
and feedback argument below discharge those differences.

[DERIVED source-game distinction] That ordinary-NIZK variant's extraction
proof changes simulated ciphertexts back into encryptions of the witnesses
supplied with its simulation queries. An iO challenge does not supply its
compiler coins. The construction below instead uses simulation soundness to
prove fresh extraction directly after arbitrary simulated inner proofs; it
never needs to recover the unknown witnesses of earlier simulated edges.

[SOURCE: selected proof primitive] De Santis–Di Crescenzo–Ostrovsky–Persiano–
Sahai, *Robust Non-interactive Zero Knowledge*, CRYPTO2001, Definition2 p572
and Definition6 pp575–576 specify adaptive multiple-proof ZK and unbounded
simulation soundness. Section3.2 pp578–579 gives an explicit simulator whose
trapdoor branch works for arbitrary statements. Theorem2 p579 supplies this
proof system from an adaptive single-theorem NIZK proof for the related NP
language and one-way functions. Its verifier checks the statement embedded
in the proof; a simulated proof cannot be reused verbatim for a different
statement. The simulation-soundness proof is on pp580–584. This is a
classical source theorem, not a QPT claim.
[Author-hosted primary paper](https://web.cs.ucla.edu/~sahai/work/web/2001%20Publications/Crypto_DeSantis2001.pdf).

[DERIVED primitive contract] Let `E=(KeyGen,Enc,Dec)` be IND-CCA2 secure
for all polynomially bounded message lengths used below, with deterministic
decryption and perfect correctness for every admitted encryption coin string
and honest key. Let `Pi=(Setup,Prove,Verify,SimSetup,SimProve)` be the selected
NIZK for the inner NP relation defined below. Its properties are:

* adaptive multi-theorem ZK, comparing real setup/proofs to simulated
  setup/proofs on true statements;
* accepting simulation of arbitrary statements under the simulated CRS;
* unbounded simulation soundness after those arbitrary simulations;
* explicit statement binding of proof bytes, as in the selected source.

[DERIVED assumption scope] These are standard primitives, rather than a
bespoke extraction oracle. The source's NIZK proof, PRF, commitment and
one-time-signature construction is one established way to instantiate the
proof component. The encryption component remains any perfectly correct
IND-CCA2 scheme for the declared lengths. No concrete library or finite
parameter set is selected, and no claim that the primitive set is PQ follows.
Average-case decryption correctness alone would leave a gap: an adversary
could certify encryption coins on which decryption fails. A replacement using
such a scheme needs a verifiable good-coins restriction or a separate bound
against adversarially chosen admitted coins.

## 2. Full certificate algorithms

[DERIVED notation] Specialize the exact edge relation from `HIO_PROVENANCE.md`
to one pinned setup. Write `G0` for its state origin, iO suite, policy and
resource bounds; the final genesis is `G=(G0,pk,crs)`. Check equality with
this full pinned `G` before proof verification. Within this fixed context,
encode the variable edge statement as `x=(G0,d,parent,child,y)` and write
its relation as `R(x,w)`. The full original edge statement is uniquely
determined by `(pp,x)`: this drops no variable context and uses no hash.
Its witness
`w=(cmd,r_iO)` satisfies

```
child = iO(padded(Q_parent,cmd); r_iO)
y = first_release(Eval(parent,[cmd])).
```

[DERIVED serialization] Use a canonical, injective, publicly bounded encoding
of the **entire** context-relative statement, including all its fields. Pad the statement
and witness to the public bounds for that depth. No hash substitutes for the
statement in this theorem. Define equal-length message encodings

```
M1(x,w) = encode(1, x, padded(w))
M0(x)   = encode(0, x, all_zero_witness_field).
```

The fixed-context factoring above avoids putting the proof CRS inside the
message whose length determines that same proof setup. Choose `G0`, the
depth-dependent program/witness bounds and encryption parameters first;
then instantiate the proof system for the resulting bounded inner relation.
The public context check enforces the final genesis exactly. All experiments
below use one pinned setup; cross-setup replacement is rejected before this
relation is used.

The leading flag ensures a simulated payload is never a valid witness
payload, even if the zero string happens to be a valid witness. The statement
tag is present in both payloads. This does not create a circular encryption
relation: `x` contains the state-origin context and edge, but not this
certificate's ciphertext/proof or the proof CRS. The witness contains no
PKE secret key.

[DERIVED inner NP relation] The proof statement is `z=(pk,x,C)`, and

```
R_in(z; w,rho) = 1 iff
    all encodings, suites and public resource bounds are valid;
    R(x,w) = 1;
    C = E.Enc(pk,M1(x,w);rho).
```

This is an NP relation over bounded computations, not a universal circuit
equivalence test. Public-key generation is honest at setup and its exact key
is pinned. All relation checks use that key.

[DERIVED setup and honest proving]

```
RealSetup():
    (pk,sk) = E.KeyGen(lambda)
    crs = Pi.Setup(lambda, declared relation/resource bounds)
    publish pp=(pk,crs,suite,bounds), bind pp into the pinned genesis
    retain no sk or proof-forging/extraction setup material

ProveEdge(pp,x,w):
    require R(x,w)=1
    sample encryption coins rho
    C = E.Enc(pk,M1(x,w);rho)
    pi = Pi.Prove(crs,(pk,x,C),(w,rho))
    return cert=(C,pi)

VerifyEdge(pp,x,cert):
    parse cert=(C,pi), rejecting bad encodings or public bounds
    return Pi.Verify(crs,(pk,x,C),pi)
```

[DERIVED simulation]

```
SimSetup():
    (pk,sk) = E.KeyGen(lambda)
    (crs,tau) = Pi.SimSetup(lambda, declared relation/resource bounds)
    return pp=(pk,crs,suite,bounds), simulation key tau,
           extraction key sk

SimEdge(pp,tau,x):
    C = E.Enc(pk,M0(x); fresh coins)
    pi = Pi.SimProve(tau,(pk,x,C))
    return cert=(C,pi)
```

[DERIVED two statement levels] In the direct iO hybrid, `x` is a true edge
statement: some compiler coins exist, although the reduction does not know
them. Nevertheless `(pk,x,C)` is a **false inner statement** when `C`
encrypts `M0(x)`. The selected NIZK simulator handles this under its simulated
CRS. Ordinary ZK alone does not promise this behavior. Indeed `SimEdge` also
works for false outer statements; this stronger property is available if a
later proof uses canonical-child substitution. No accepting false proof is
required under a real, independently fixed CRS.

[DERIVED online extraction] Maintain a monotonically growing set `S` of exact
outer statements for which the simulation/proving oracle issued certificates.
Record membership before exposing a response. The extraction interface is

```
ExtractFresh(pp,sk,S,x,cert):
    if VerifyEdge(pp,x,cert)=0: return REJECT
    if x in S: return KNOWN_STATEMENT
    m = E.Dec(sk,cert.C)
    parse m=(flag,xprime,w), or return FAILURE
    if flag!=1 or xprime!=x or R(x,w)!=1: return FAILURE
    return w
```

[DERIVED replay semantics] `KNOWN_STATEMENT` means the resident reduction
uses its recorded child semantics; it is not witness disclosure. Changing
proof bytes or ciphertexts for the same `x` does not change the certified
public child. Changing any edge field changes `x` and requires extraction.
This matches the statement-new extraction interface needed by provenance.
The deployment has no extraction service: real issuers verify public ancestry.
The set and secret decryption key above are reduction state only.

## 3. Online extraction after arbitrary simulation and feedback

[DERIVED theorem] In any polynomially bounded adaptive interaction with
`SimEdge` and `ExtractFresh`, the probability of a fresh accepting certificate
returning `FAILURE` is at most the simulation-soundness error of `Pi` at the
full interaction resources. Queries to `SimEdge` may be false outer statements
and may depend on previous extracted witnesses. No eventual rewinding or
custom online-extractor assumption is used.

[DERIVED proof] A simulation-soundness adversary generates `(pk,sk)` itself,
receives the challenge simulated CRS, and uses the source simulation oracle
to answer every inner proof query `(pk,x,C)`. It knows `sk`, so it answers
every extraction query immediately and performs all public witness checks.
Thus later simulation queries may depend arbitrarily on this feedback.

At the first fresh accepting extraction failure, output its inner statement
and proof. If that inner statement were true, some `(w,rho)` would satisfy
`C=Enc(pk,M1(x,w);rho)` and `R(x,w)=1`. Perfect correctness would make the
decryption check return a valid witness, contradicting failure. Hence the
inner statement is false. Since `x` was never a simulated outer statement,
`(pk,x,C)` is a new inner statement. The source's explicit statement check
also prevents a byte-identical previously simulated proof from verifying
this different statement, satisfying its proof-fresh formulation of
simulation soundness. This is a valid source-game forgery.

[DERIVED loss and feedback] The reduction detects the first failure in
polynomial time using `sk` and the NP verifier. It does not guess which of
the submitted edges fails, so there is no separate factor for the number
of extraction requests. That number instead enters the reduction's runtime
and oracle-query bounds. The reduction's privately generated encryption key
is ordinary auxiliary state independent of the proof CRS; giving feedback
computed with it is behavior of one efficient adversary in the existing
simulation-soundness game. The NIZK simulation trapdoor is never given to that
adversary.

## 4. Zero knowledge with adaptive extraction feedback

[DERIVED experiment] The proving oracle initially receives valid `(x,w)`
queries and returns real certificates; its simulated counterpart receives
the same queries but discards `w`. The surrounding environment may adapt its
future queries using `ExtractFresh` outputs. The set `S` excludes all issued
outer statements in both experiments. This is the standard witness-carrying
ZK comparison. Once simulation is established, the executable `SimEdge`
itself needs no witness, which is what the later iO challenge requires.

[DERIVED first hybrid] Replace the real proof CRS and all honest inner
proofs by the simulated CRS and simulated inner proofs, leaving every
`C=Enc(pk,M1(x,w))` unchanged. All those inner statements are true. An
adaptive multi-theorem ZK reduction generates the encryption keys itself
and therefore answers extraction feedback exactly. Its loss is one
`epsilon_MT-ZK` at the entire interaction resources.

[DERIVED ciphertext hybrids] With all proofs now simulated, replace the
issued ciphertexts one at a time, in issuance order, from `M1(x,w)` to
`M0(x)`. For the challenge index, a CCA reduction receives `pk`, samples
the simulated proof CRS and its trapdoor, and submits the two equal-length
payloads as its challenge messages. It simulates the inner proof for the
returned challenge ciphertext `Cstar`, then records `xstar` in `S` before
returning any response. Earlier and later encryption/proof calls are
performed normally in the prescribed hybrid. The number of issued proofs
may be adaptive; use a fixed public upper bound and inactive positions after
termination.

[DERIVED exact decryption-oracle handling] For an extraction request:

1. Verify and handle `x in S` without decryption, as above.
2. If `C != Cstar`, query the CCA decryption oracle and run the same public
   parsing/tag/relation checks.
3. If `C = Cstar` and the request is fresh, then `x != xstar`, because
   `xstar` is already in `S`. Under either challenge bit, decryption of
   `Cstar` contains the exact tag `xstar` (and possibly the dummy flag).
   Therefore the real extraction algorithm returns `FAILURE` on this
   fresh `x`. The reduction returns `FAILURE` directly, without the
   prohibited CCA decryption query.

[DERIVED consequence] This handling is exact; it does not assume the
adversary cannot reuse challenge ciphertexts and needs no extra bad-event
bound for such reuse. It continues to work if the adversary uses extraction
responses to choose later simulation queries. If an accepting proof accompanies
the reuse, extraction failure is still handled identically in both worlds;
the separate simulation-soundness theorem bounds that event where the resident
proof needs to abort. Reusing the challenge ciphertext at its original outer
statement simply invokes the known-statement table.

[DERIVED backend bounds] Write all advantages as distinguishing probability
gaps; converting a guessing advantage over one half requires the usual
factor of two. For at most `q_s` issued proofs and the declared extraction
budget `q_e`, the resulting primitive satisfies

```
epsilon_backend-ZK <= epsilon_MT-ZK(Pi) + q_s * epsilon_CCA(E)
epsilon_backend-extract <= epsilon_SS(Pi).
```

Each epsilon uses the full adaptive runtime, statement sizes and query limits
of its reduction. Completeness and any separately admitted bad-key/correctness
events must be added if the selected primitive definitions allow them. In
particular an average honest-encryption failure rate cannot simply be used
for adversarially certified coins.

## 5. Application to the retained resident forest

[DERIVED instantiated provenance theorem] Substitute these algorithms for
the custom interface in `HIO_PROVENANCE.md`, keeping its exact edge relation,
full ancestry checks, private-issuer boundary, all-coins iO correctness and
paired residual invariant. The direct parent-preserving hybrid remains valid.
With `N` its root/protected-output switch bound, a conservative inherited
ledger is

```
Adv_forest <= N * epsilon_iO
              + 2 * epsilon_MT-ZK(Pi)
              + 2 * q_s * epsilon_CCA(E)
              + 2 * (N+1) * epsilon_SS(Pi).
```

All terms are evaluated at the maximum resources across these hybrids. This
is a symbolic security reduction, not a claimed numerical security level.
The fixed horizon and concrete margin witness are unchanged. The same
backend even supplies accepting simulation and fresh-edge extraction after
false **outer** certificates under simulated setup, if canonicalization is
used instead; the direct proof does not need that stronger outer simulation.

[DERIVED surviving credentials] The published setup contains only the PKE
public key, proof CRS, suite/bounds and pinned genesis. The PKE secret key is
generated during honest setup and retired before protected issuance. If
retained, it would decrypt protected commands and compiler coins from the
certificates, so it is not a permitted continuing audit or recovery key.
The real proof setup likewise retains no simulation capability. Initial-state
retirement remains exactly the existing assumption. Private issuers hold only
their own command and fresh local coins; public actors hold certificates and
ancestry. There is no online registry, resident-state master, or deployed
witness extractor.

[DERIVED setup chronology] Genesis pinning authenticates the descriptor
produced by the setup ceremony. Security compares that entire setup
distribution with the simulated one; it does not simulate under an externally
fixed arbitrary CRS while preserving its bits. PKE and proof parameters are
fixed before any protected issuer is given a command. A private issuer checks
the complete rooted path before receiving its protected observation.

[DERIVED cost] One certificate adds one encryption of a payload containing
the full edge and its compiler witness, plus one simulation-sound NP proof.
Its honest prover must prove both the encryption computation and the bounded
iO compilation/evaluation relation. Online reduction extraction uses one
decryption and one public `R` check per fresh accepted edge. The CCA reduction
uses at most the declared extraction budget in decryption queries per
ciphertext hybrid. No succinct proof, compressed ancestry, practical iO
compiler, or polynomial-in-hops iO-size bound is supplied here. Certificates
do not repair the ACE boundary leak in `HIO_CONTINUATION.md`.

[DERIVED status] The online simulation/extraction interface is now reduced
to explicitly stated established primitives with a concrete tagged compiler.
What remains for implementation is selecting and costing those primitive
backends at the actual large NP relation, together with the existing iO
size problem. The argument is classical and conditional; it is not a
certified PQ or concrete-SHAKE result. No crypto demo or validation grid was
run, and the prior completed notes were not changed.

## Source and query record

[SOURCE] Local eprint paper:
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2010/154.pdf`, SHA256
`e1aeb4789d4a1c26d23a4a242b2273b73779c9c8ee27206a69c22747163bc42a`.
The targeted `pdftotext -layout` extraction is
`/tmp/hio-dhlw-2010-154.txt`, SHA256
`f5775c6f4bbb3fa7fc73216146bf048e14187d4a59bc8ea23190946f1b15a5a1`.
Inspected Sections3,4.4,4.5 and AppendixA.4, including their definitions,
algorithms and proof, rather than only the abstract.

[SOURCE] The CRYPTO2001 primary paper was read through the author-hosted PDF
linked above: Definitions2/6, Section3.2, Theorem2 and its proof through p584.
No eprint PDF was fetched. Its precise source claims are confined to Section1
of this note; the new tags, feedback experiment and reductions are ours.

[EXECUTED source-work record] Six targeted web search queries; eight page-open
requests, of which two IACR archive URL variants failed and six author-PDF
opens/positioned reads succeeded; zero Scry queries. One local mirror PDF
extraction; one author-hosted PDF read through the web tool; zero eprint
downloads. Local `rg`/text reads and source hashes only. No private artifacts,
cryptographic runs, estimators, new tests or source-ledger edits.
