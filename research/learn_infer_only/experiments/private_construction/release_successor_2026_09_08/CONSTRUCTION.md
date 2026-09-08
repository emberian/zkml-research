# A one-time encrypted anchor and reusable transcript release key

[DERIVED positive conditional construction, 2026-09-08] Fix a polynomial horizon
T and a bounded deterministic nonlinear learner. One MIFE instance, T public
observation slots, one public selector slot, and one **nonpublic one-time anchor
slot** suffice for reusable restricted release after honest master erasure.
Learn appends an independently encrypted observation; Infer replays the learner
inside the fixed function key. The protected state is the encrypted transcript.
There is no encrypted FE output, FHE secret-key capsule, state-key refresh, or
FE-level recursive next-state hybrid. The fixed key supports every prefix up to
T, including arbitrary public observation replacements and archived forks.

[SOURCE/DERIVED] The deterministic specialization of 2025/330 Definition4.4,
Construction2 and Theorem6.1 supplies the needed adaptive exposed-key game under
its exact subexponential assumptions. We prove its compatibility premise below,
including a fresh observation that changes evolving hidden weights. This is a
classical source-conditional FE construction, not an iO implementation, a SIM
claim, a PQ result, or selected-history cryptographic release.

## 1. Exact functionality and construction

[DERIVED general contract] Let S be a finite canonical state domain, X a finite
canonical observation domain, and Q a fixed public query domain. Fix total
circuits U:S×X→S and R:S×Q→Y and genesis state s. A no-op observation is allowed.
Set n=T+2. Position0 is the anchor, positions1..T are observations, and position
T+1 is a selector (t,q), 0≤t≤T. All slots use the source's common bit width;
position-specific parsing rejects noncanonical padding and invalid ranges with
one common output REJECT. Y and REJECT have a fixed canonical output encoding.
No receipt signature, parent commitment or verification-key literal occurs.

```
Replay_T(anchor, observation[1..T], selector; ignored_coins):
    parse every field; on any failure return REJECT
    (t,q) = selector
    s = anchor
    for j = 1..t: s = U(s, observation[j])
    return R(s,q)
```

[DERIVED] This is a deterministic member of the source randomized circuit class:
its output is independent of the functional coins. A polynomial T and polynomial
S/U/R encoding sizes yield a polynomial circuit. Parsing **all** observation
slots, even those beyond t, keeps invalid-input behavior fixed and explicit.

```
Initialize(lambda,T,s):
    set every dimension and source primitive parameter before Setup
    (EK[0..T+1],MSK) = MIFE.Setup(...)
    K = MIFE.KeyGen(MSK,Replay_T)
    anchor = MIFE.Enc(EK[0],encode(s))
    nop[j] = MIFE.Enc(EK[j],encode(NOP)) for j=1..T
    publish EK[1..T+1], K, anchor, nop[1..T], public contract
    erase MSK, EK[0], all raw internal secret keys/coins, s and its copies
    return resident=(anchor,nop[1..T],used=0)

Learn(resident, privately issued observation ciphertext c at slot used+1):
    replace that slot's NOP by c, increase used, return new resident and ACK

Infer(resident,q,t=used):
    csel = MIFE.Enc(EK[T+1],encode(t,q))
    return MIFE.Dec(K,anchor,observations[1..T],csel)
```

[DERIVED closure] Every successive resident has exactly the same ciphertext-slot
interface. Its anchor bytes never change. Fresh issuers use public EK[j] and need
no master, no prior plaintext model, no protected-state encoder, and no other
issuer's secret. The host can append, retain snapshots, select any prefix, replace
public observation ciphertexts, and evaluate repeatedly with the same K. No new
key issuance occurs after setup. Public `used` is convenience metadata; the
cryptographic function itself only enforces t≤T. The host can inspect future NOPs,
fill future slots early and reorder/reuse observations via fresh encryption of
known inputs. These are allowed by the stated leakage, not prevented by a wrapper.
The construction supports T private observations, not an unbounded epoch renewal.

[DERIVED credential lifecycle] Every surviving software credential is exposed:

| Credential/object | Survives? | Authority in this construction |
|---|---|---|
| MSK and raw PKE decryption keys, authentication PRF keys, function PRF key and obfuscator/setup secret copies | No | Setup has full read/key-issuance power; erasure is an honest-initialization assumption. |
| EK[0], including its authenticated input-issuance obfuscation | No | Can make replacement anchors if retained. No such capability is required by Learn. |
| EK[1..T], EK[T+1] | Yes, public | Arbitrary observations/selectors in the corresponding slots. |
| K=SK_Replay | Yes, public | Releases the fixed replay output on every supported ciphertext combination. |
| Anchor, all observation ciphertexts, all old snapshots/selectors | Yes, public | All archive mixtures and public replacement evaluations. |
| New issuer input and encryption coins | Ephemeral issuer data | Own-input knowledge is unavoidable; erase or explicitly leak them on later issuer corruption. |

[DERIVED] K contains an obfuscated program with decryption/authentication material
in Construction2. Its restriction is a **source FE security claim**, not a claim
that the bytes do not contain keys or that Python hides them. No signing authority,
trusted online reader or persistent secret writer is added. An initializer observed
while holding MSK/s or retaining EK[0] is outside this honest-erasure theorem.

## 2. Exact exposed-credential security statement

[DERIVED game] The environment chooses the fixed public contract and submits an
initial pair s0,s1. It receives the public deployment in world b. It may adaptively
request any polynomial number of paired observation encryptions at any public
slot, use the public EKs itself, keep every snapshot, combine archived ciphertexts,
evaluate K on arbitrary strings, and compute arbitrary PPT postprocessing. Expose
all surviving credentials at initialization. No identity/projection key or EK[0]
is requested. The challenge interface hides input encryption coins; additional
issuer-state leakage must be explicitly supplied and compatible with the pair.

Let C[i,j]^b denote the plaintexts submitted in slot i by challenge row j.
The **robust compatibility** condition is: for every subset U⊆{1,..,T+1}, every
common replacement x'_i in each i∈U, and every independent challenge-row choice
j_i in every un-replaced slot, the two evaluations of Replay_T are equal. The
anchor slot is never in U. Multiple available anchor ciphertexts, if modeled,
are still covered by the independent row choice. This is exact equality of
full output encodings, including rejection; it is not equality only along the
honest chronological trajectory.

[DERIVED theorem] Assume Construction2 satisfies 2025/330 Definition4.4 with its
Theorem6.1 parameters for the actual n,input/function/output widths and running
time. For any uniform PPT environment whose adaptive challenge pairs satisfy
robust compatibility pointwise, the two complete deployed views are IND-secure.
The reduction has the same guessing advantage as the resident game and uses one
MIFE instance and one function-key query, with no horizon/tree hybrid loss.
For an absolute probability-difference convention, convert both sides consistently
(the source guessing advantage is half that difference for the corresponding
oriented guesser). This is a computational indistinguishability theorem, not a
black-box simulator for all authorized outputs.

[DERIVED proof]

1. The reduction obtains exactly EK[1..T+1] via OGetEK, requests SK_Replay once,
   and uses OEncLR on the anchor pair plus common NOP/selector fillers. Keep the
   anchor component and make all other public NOP ciphertexts honestly. The
   initial package has exactly the deployed distribution.
2. For a later single-slot LR observation request, submit one full source LR row.
   Fill the anchor with the original (s0,s1), fill other observation positions
   with common NOP, and the selector with common (0,q0). Return only the requested
   component; discard the others. Extra source rows contain only duplicate anchor
   pairs and publicly encryptable common fillers. Therefore their Cartesian
   combinations add no case beyond the robust-compatibility premise already stated.
3. Every public encryption, ciphertext archive, selector and local K evaluation is
   available to the source adversary without MSK. Preserve the same environment
   state and fresh local coins. The reduction never constructs an encryption of
   an unknown secret key or manufactures a next-layer issued key.
4. Replay_T ignores its functional coins, and equal outputs give identical
   distributions even with every auxiliary plaintext in Definition4.3. Thus its
   source epsilon is **zero**, which meets Theorem6.1's positive exponentially
   small threshold. Adaptive timing is already in Definition4.4's oracles.
5. The final bit and complete observed view have the exact real distribution.
   Source security yields the claimed indistinguishability.

[DERIVED correctness] Inductively, appending c_j=Enc(EK[j],x_j) represents the
extended plaintext history and changes no earlier ciphertext. Source correctness
applied to the tuple and Replay_T gives R(U^t(s,x[1..t]),q). For Qv evaluations,
use the source correctness error at the actual dimensions and a union bound
Qv·delta_corr where that pointwise/source guarantee applies. No numerical rate
or adversarial ciphertext correctness is invented. Exact ideal execution is
checked separately below. Malicious-host origin/finality correctness is not claimed.

## 3. A nontrivial fresh-observation privacy family

[DERIVED nonlinear learner] For any T≥1 let W=T+2, S={-W,..,W}², and let an
observation be NOP or (i,y), i∈{0,1}, y∈{-1,+1}. Prediction is 1[w_i≥0]. Learn
adds y to w_i only when that prediction disagrees with y; otherwise it leaves
w_i unchanged. It touches only the privately encoded address i. This preserves
S and is nonlinear in the state: the same negative observation maps weights
-1,0,1 to -1,-1,0. Infer returns a classification bit in either coordinate.
This is a concrete mistake-driven learner, not a utility benchmark.

[DERIVED fresh-input witness] Start at s=(a,T+1), for any fixed legal a. Allow
challenge pairs in any observation slot to be either identical observations or
(1,-1) versus (1,+1), in either order. One may also compare initial states
(a,T+1) and (a,T+2). For **all** public replacements, archive-row mixtures and
selectors t≤T:

* First-coordinate trajectories agree: every nonidentical challenge pair targets
  only coordinate1; identical and replacement records affect coordinate0 equally.
* Each coordinate1 update decreases its weight by at most one. Hence in both
  worlds w1(t)≥T+1-t≥1. Every released coordinate1 classification is one.
* Every invalid plaintext field rejects identically; the fixed anchor encoding
  is valid in both worlds. Selector choices are public and arbitrary within range.

Therefore the robust equality condition holds for arbitrarily many adaptive
ciphertext queries from this family, including simultaneous hidden labels in
multiple slots. This is a proved family for every polynomial T, not an inference
from the finite enumeration. It permits genuinely fresh private observations
chosen after setup under the oracle convention in section2.

[DERIVED semantic activity] A first private negative label changes w1 from T+1
to T, while a private positive label leaves it at T+1; the hidden observation
therefore changes the evolving model. For T=4, the pair followed by five negative
observations yields weights -1 and0 and different classes at step6, outside the
four-observation contract. The label is not ignored padding. Within the contract
its prediction cannot differ; the theorem cannot hide an authorized answer.
Coordinate0 can change classifications repeatedly in the same deployment, so
this is neither a constant-output function nor a dead learning transition.

[DERIVED load-bearing erased capability] If arbitrary replacement anchors were
allowed, (w0,w1)=(0,0) followed by the same private ± label would immediately
produce different coordinate1 predictions. The source condition would then fail.
Erasing EK[0] removes precisely that exposure; subsequent learning never needs it.
This finite function witness does not execute a disclosure or routing experiment.

## 4. Symbolic executable and exact checks

[EXECUTED] `prototype.py` supplies canonical bit encodings, the fixed replay
function, immutable reusable resident states, public per-slot encryption calls,
snapshot/fork reuse, and an explicitly **ideal** MIFE oracle. Its plaintext table
is visible to Python introspection; it is not a deployed security boundary or a
cryptographic implementation. The source-conditional theorem above, not the
oracle table, supplies the cryptographic claim. The executable does validate the
state interface and the mathematical premise on finite domains.

[EXECUTED command]

```
python3 -I -B research/learn_infer_only/experiments/private_construction/release_successor_2026_09_08/prototype.py
```

[EXECUTED] `RESULTS.json` and `prototype.log` record:

* 1,056,250 comparisons against an independently written direct learner, covering
  every valid initial pair at T=4, all 5^4 observation vectors, and every selector.
* 5,000 fresh-label comparisons: every challenged position, every valid public
  replacement in all other slots, every prefix and both queries.
* 6,250 initial-state pair comparisons and 1,250 plaintext parsing controls.
* Two 32-Learn symbolic worlds, 66 Infer evaluations each including archive/fork
  reuse, identical release traces and different terminal states (0,21)/(0,22).
  Coordinate0 changes its released classification ten times in the selected run.
* Nonlinear-step, outside-horizon and replacement-anchor finite witnesses.

[DERIVED scope] The finite controls are not a substitute for all-bitstring
compatibility. Section3 proves the invariant and handles invalid encodings; the
controls instantiate it. No encryption, obfuscation, cryptanalytic attack,
malformed-ciphertext experiment or stopped task was run.

## 5. Cost and what this construction changes

[DERIVED counts] For T=32, n=34; 33 public EKs and one restricted function key
survive. A resident stores 33 ciphertexts; an Infer adds one selector ciphertext.
The prototype's common input width is14 bits. In source Construction2, setup
creates 2n=68 PKE key pairs, n=34 authentication PRF keys and n=34 input-issuance
obfuscations; one additional obfuscation implements K. The anchor issuance
obfuscation is erased, leaving34 obfuscated objects (33 public issuers plus K).
Raw keys/coins are erased in addition to the explicitly exposed objects.

[DERIVED symbolic costs] Let s be the actual PKE ciphertext width and tau the
authentication-tag width. One source ciphertext is 2s+tau bits, before serialization
metadata. Current resident size is (T+1)(2s+tau); public material is
(T+1)(2|pk|+|iO(E)|)+|iO(G)| plus fixed metadata. A Learn uses two PKE encryptions
and one E evaluation. An Infer uses another such encryption, then T+2 underlying
PKE decryptions, T+2 authentication-PRF evaluations and associated injective-OWF
checks, one functional-PRF evaluation, and at most T learner updates inside G.
These are algorithmic counts, not timings or instantiated parameter sizes.
The immutable Python vector update also copies O(T) handles.

[SOURCE parameter scope] Theorem6.1 requires CPA-secure PKE, subexponential iO,
puncturable PRFs and an injective OWF with §6.1's precise enlarged parameters.
Its output-compatibility threshold is 2^(-2ns-lambda_iO); exact equality meets it.
The printed iO weak-extractability gap is 2^(-3ns-lambda_iO). No classical/PQ
bits, practical iO implementation, or numerical parameter choice is supplied.
Finite nonrecursive circuit sizing removes the earlier next-ciphertext-width
recurrence, but these strong primitive assumptions remain substantive.

[DERIVED comparison] Unlike the independent-key FE ladder, this has one instance
and one function key, with no branching-tree or depth-by-depth encrypted-output
proof; T may be polynomial at setup. Unlike a plaintext quotient table, private
observations may arrive after deployment and no complete future-response tree
is precomputed. The cost is replaying the whole bounded history inside FE and
retaining its ciphertexts. The public transcript interface still enables all
source-compatible archive mixtures and forks. It does not enforce one selected
receipt history, quotas, expiry, oblivious timing, designated private delivery,
or continuation beyond T. Those are separate functionality changes.

## 6. Source orientation and next step

[SOURCE inspected] Local 2025/330 (Datta–Guan–Korb–Sahai, TCC2025 full version):
Def4.2 pp.21–22, Def4.3 p.22, Def4.4 p.23, Construction2 pp.48–49, §6.1 p.48,
Theorem6.1 p.50 and its opening adaptive query hybrids. Local 2013/727 Def2–3
pp.10–11 checked the exact public-replacement/Cartesian-product obligation.
Existing capsule and terminal-joint notes were read before constructing this
successor; their original files remain unchanged. `SOURCES.json` records access.

[SOURCE discovery only] Guan's current primary publication page announces
“Multi-Hop Functional Encryption” (TCC2026), with forwardable encrypted state,
controlled intermediate release, a central key issuer and topologically ordered
hop-key queries. No full paper link is present in the inspected entry. That
abstract is relevant future work, not an inspected construction or a replacement
for this proof. In particular, its announced key-issuance role is not erased by
an inference here. https://www.guan.io/publications/

[OPEN next constructive target] Instantiate or obtain a costed implementation of
this deterministic bounded MIFE family, or derive a stronger compact-state
primitive from an inspectable source. A cryptographic selected-history guard
must come with a new proof, not a signature check grafted onto this theorem.
The current positive is bounded adaptive private ingress plus reusable nonlinear
restricted release under complete surviving-credential exposure and the exact
robust leakage relation. No new review layers or shared ledgers were created.
