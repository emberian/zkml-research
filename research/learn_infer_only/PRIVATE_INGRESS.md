# Private observation ingress: the two-input seam

[DERIVED reviewed successor, 2026-09-07] The exact parent-bound candidate now has
a sharper source-application obstruction. With an observation encryption key
exposed, the source's arbitrary-replacement test can submit one valid left-parent
packet against both challenged states: the observable guard accepts one and
rejects the other, giving gap1. No state-slot key or forged proof is needed for
that compatibility finding. It rejects the natural FE hybrid, not private ingress
as a field. See [provenance review](experiments/private_ingress/provenance_review/REVIEW.md).

[DERIVED correction] That review also corrects the augmented provenance
candidate's fixed-ciphertext event: fresh coins *inside the encrypted payload*
must be guessed too, giving the lower bound `2^(-rho-lambda_next)`. The earlier
`2^(-lambda_next)` bound does not apply to that augmented payload. A stated
fixed-width premise still yields an equal-parameter epsilon obstruction.
The simpler original deterministic-payload candidate below is separately scoped.
The reviewed candidate additionally needs an internal check of its supplied
history witness before extending it. Proposed dual-mode repairs remain open.

[DERIVED further parameter correction] The source's `s` counts the current
underlying PKE input ciphertext. It does not bound function description,
randomness, output or next-ciphertext width. [PARAMETER_CLOSURE.md](experiments/private_ingress/provenance_review/PARAMETER_CLOSURE.md)
therefore withdraws an all-parameter circuit-size objection: fixed-H polynomial
enlargement can evade the particular support lower bounds. A short effective
random seed remains an obstruction, including deterministic PRG stretching.
The source's lambda/ellR shorthand and the derived width-complete reading are
stated separately. Independent review is in progress; none of these sizing
controls establishes a quantitative joint future-package compatibility bound.

[DERIVED same-parent repair boundary] [DUAL_MODE.md](experiments/private_ingress/provenance_review/DUAL_MODE.md)
shows how an equivocal hiding commitment can keep one current parent valid on
both challenge projections. That repairs the named opening guard in that mode.
It does not establish the joint future-output hybrid, honest history extension
or tiny source epsilon. The source-backed commitment equations and mode ordering
are explicit; this is not a completed private-ingress construction.

[DERIVED decision; 2026-09-06] The inspected randomized-MIFE construction has
the required **two-input syntax with independent writer keys**, and its public
encryption interface needs no online raw master secret. That is a real
construction-level improvement over the streaming-FE writer. It does not yet
establish private ingress for the bounded resident. The first source theorem
premise fails for the natural equal-parameter encrypted-output transition; and
public state issuance can itself turn the restricted transition into a reader
of every fresh observation. Independent layers alone fix neither fact.

[DERIVED scope] This note owns only fresh private ingress into a fixed H=2
ladder. It does not replace the public-command result in
`experiments/private_construction/FINITE_LADDER.md`, audit a growing horizon, or
claim a post-quantum result. Honest setup and precisely listed erasures are
assumptions. No cryptographic primitive was implemented. No shared ledger,
companion tree, or `docs/VERDICTS.md` was edited.

## 1. The actual primitive, rather than an added argument to single-input FE

[SOURCE: algorithms/game/theorem statements read]
Datta–Guan–Korb–Sahai,
[(Multi-Input) FE for Randomized Functionalities, Revisited](https://eprint.iacr.org/2025/330),
Definition 4.2 printed pp.21–22 and Construction 2 pp.48–49, give:

```text
Setup -> EK[1], ..., EK[n], MSK
Enc(EK[j], x[j]) -> ct[j]
KeyGen(MSK, f) -> SK[f]
Dec(SK[f], ct[1], ..., ct[n]) -> f(x[1], ..., x[n]; derived_coins)
```

[SOURCE] In Construction 2 each slot j has two independently generated PKE
key pairs and an authentication PRF key. Its issued encryption key is
`EK[j]=(pk[j,0],pk[j,1],iO(E[j]))`. Public E[j] checks two proposed PKE
encryptions against the supplied plaintext/coins and returns their PRF tag.
The function key is `iO(G[f,{sk[j,0],Kauth[j]}_j,Kf])`: G authenticates each
slot, decrypts its first component, derives function coins by a PRF on the
entire ciphertext tuple, then evaluates f. Two PKE coin strings of length
lambda are sampled for each honestly issued input. These are separate
per-slot encryption keys under one MIFE setup, not independently set up
single-input FE schemes that are assumed to combine.

[DERIVED candidate syntax] Let each transition layer i have state slot S and
observation slot X. With deterministic bounded circuits `Step_i(s,x)=(T_i(s,x),a_i(s,x))`,
define

```text
F_i(s,x;r) = (Enc(EK[i+1,S], T_i(s,x);r), a_i(s,x)), i=0,1.
```

[DERIVED] The terminal instance is single-input with an issued restricted key
for g. Set up the terminal instance first, then layer 1 and layer 0; every F_i
can contain its already generated next-state encryption key. A sensor issues
`Enc(EK[i,X],x)` after deployment, without knowing the protected state or any
master. Evaluation of F_i consumes a state ciphertext and that independently
issued observation ciphertext and returns reusable next-layer state. It need
not expose the observation to a plaintext state holder. With one function at
each layer this uses five slot encryption-key objects and three issued function
keys; this is an object count, not a byte/time cost.

[DERIVED limit] This is only a syntactic H=2 candidate. There is no third
transition key and no indefinite closure claim. The source's fixed tuple/key
evaluation is deterministic even though its ideal function is randomized;
representation coins are not a claim of fresh developmental entropy per replay.

## 2. The mixed-input game exposes exactly where probing is permitted

[SOURCE: full game read] Definition 4.3 pp.22–23 defines compatibility using
I, the set of slot encryption keys exposed to the adversary. For **every**
subset U of I, it allows arbitrary replacement plaintexts in U. Every remaining
slot independently selects a challenge-query index. It compares the resulting
function-output distributions for the two challenge worlds. The compatibility
distinguisher receives f's description, U, those replacement values, and the
left-world unreplaced inputs as advice. Definition 4.4 p.23 lets the adversary
adaptively request encryption keys, left/right ciphertext tuples and function
keys, and conditions its win on cumulative compatibility.

[DERIVED exact n=2 reading] With both EKS and EKX exposed, all of these tests
belong to the game for every issued F and every relevant j,k:

| U | Compared inputs |
|---|---|
| empty | `(s0[j],x0[k])` versus `(s1[j],x1[k])` |
| state only | `(s*,x0[k])` versus `(s*,x1[k])` for every s* |
| observation only | `(s0[j],x*)` versus `(s1[j],x*)` for every x* |
| both | `(s*,x*)` in both worlds |

[DERIVED] Equality on the matched honest histories j=k does not discharge the
first row. Equality on all stored pairs does not discharge the middle rows.
Different issuers, different streams and saved snapshots do not remove these
combinations from exposed software. The actual function must reject a forbidden
combination, or the ideal interface must permit its information. A plaintext
origin/epoch label alone does not authenticate a state when its encryption key
lets the host issue that label on any chosen state.

[SOURCE: precursor game read] The four-author precursor
[Multi-Input Functional Encryption, 2013/727](https://eprint.iacr.org/2013/727)
already gives this reason in §2.2.1 printed pp.10–11, Definition 2. Its separate
public and secret encryption-key cases make the distinction explicit. This is
not a new attack against a MIFE theorem; the source excludes these challenge
pairs for the correct reason.

## 3. Executed fresh-observation reader and controls

[EXECUTED] Run:

```sh
python3 research/learn_infer_only/experiments/private_ingress/ingress_audit.py
```

[EXECUTED] `experiments/private_ingress/ingress_audit.stdout.txt` and
`results.json` retain results, command, Python/platform and source hash. Handles
are entries in a Python registry. They are **not encryption**. Their slot checks
are model rules, not evidence that actual malformed or cross-layer ciphertexts
are cryptographically refused.

[EXECUTED falsifier] The first model uses a fixed genesis s=0, one private
Learn `s <- s+x mod256` returning ACK, followed by state-preserving Infer and a
terminal key returning `high_bit(s)`. The sensor issues x after setup. Inputs
x=0 and x=1 produce identical complete fixed-root traces `[ACK,0,0]` and
distinct protected next states. There is no output of a plaintext next state.
The model's second transition omits its unused dummy observation argument;
it is the n=2 function that ignores that slot, not a second private Learn.

[DERIVED attack] If EKS at the Learn layer is exposed, the host encrypts a
chosen offset d as a replacement state and applies the same Learn key to the
honest private observation ciphertext. The future keys reveal

```text
probe(d,x) = high_bit((d+x) mod256).
```

[DERIVED] Binary search on x uses eight such probes. On a current interval
`[lo,hi]`, take `m=ceil((lo+hi)/2)` and `d=(128-m) mod256`; within that interval
the probe distinguishes x below m from x at least m. The initial interval is
all bytes. Every probe starts a fresh encrypted branch and uses the complete
future package already exposed to the host. In particular d=127 separates
the otherwise honest-trace-equivalent observations 0 and 1.

[EXECUTED] All 256 bytes are recovered, with eight probes each. The recorded
model spends 16 transition-key evaluations and eight terminal evaluations per
recovery. The terminal evaluations duplicate the Infer bit as a consistency
control; eight terminal reads are not a necessary additional attack cost when
Infer already releases it. Raw setup masters are absent from the modeled
attack. Removing precisely public state issuance blocks the chosen-state call
while the honest Learn/Infer path still works. This control proves only that
this capability path was removed, not that hidden issuance is cryptographically
realized by the candidate.

[EXECUTED separate cross-query falsifier] Even if no encryption key is exposed,
an XOR function with two stored inputs per slot yields output matrices
`[[0,1],[1,0]]` and `[[0,0],[0,0]]` in the two worlds. Their honest diagonals
agree; a mixed stored pair distinguishes. This is the U=empty obligation,
separate from chosen-state issuance.

[EXECUTED semantic positive] Private ingress is not universally ruled out by
the mixed-input condition. A second finite machine has state/observation
`(visible bit, hidden Z4)` and updates
`(v,h),(u,k) -> (v XOR u, 3h+k mod4)`, with terminal read v. The run checks
100 mixed/replaced input cases, 800 continuations with identical next inputs,
and all 1,024 combinations of state-related and observation-related pairs.
Visible-coordinate equivalence is preserved. A fresh observation changes
hidden next state 0 to 1, then to 3 at the next step; visible observations can
change the permitted answer. Update order can change the retained hidden
state. The hidden coordinate never affects this interface's outward answer;
no claim of learned utility follows. These are nonvacuous semantic obligations
that a suitable cryptographic composition could realize, not such a composition.

## 4. Why publishing only the observation key is not yet a proof

[DERIVED] MIFE syntax does not require all encryption keys to be published.
The initial state can be encrypted during setup and its EKS erased. If the
only exposed slot key were EKX, the game would use I={observation}; its
arbitrary-state replacement row would disappear. Therefore “all slots must be
public because Enc is public-key encryption” is an incorrect inference.

[OPEN exact continuation seam] For subsequent state, F_i contains
`EK[i+1,S]`. Omitting that key as a separate deployment file does not prove it
stays hidden in an exposed function key. Ordinary message-hiding FE does not
supply function hiding. In the **inspected 2025/330 compatibility test**, the
distinguisher receives the description of F_i, including its embedded next
state encryption key. Thus the compatibility argument itself has that writer
capability even if a concrete host is not separately handed it.

[DERIVED reduction boundary] The natural backward reduction for the future
layer also needs EK[i+1,S] to build the preceding transition circuit whose
output is a valid next-state ciphertext. Requesting it from the future MIFE
challenger puts that slot into I. Without requesting it, this reduction cannot
construct that circuit by the source's algorithms. Supplying an ordinary
encryption oracle to an obfuscated circuit is not one of those algorithms.
Consequently the existing exposed-future-package induction does not justify
I={observation} merely by withholding a standalone EKS file.

[DERIVED scope] This is a missing hidden-constant/composition theorem, not
evidence that every obfuscation actually reveals EKS. A construction proving
the required restricted issuance through protected program constants might
repair it. It must include *all preceding issued transition keys*, not only
the future package without its issuer. Even perfect hiding of EKS does not
remove known states reachable by authorized observations on forked histories;
those and cross-issued observations remain part of the stated ideal interface.

[OPEN authentication seam] A concrete parent/genesis/provenance-bound input
adapter might forbid unwanted pairings. The source's E/G authentication
establishes consistency with a slot encryption interface; it does not certify
resident genesis, current parent, intended sensor or authorized recipient.
Since public EKX is public issuance, a signature on an observation or an
equivalent restriction would require an additional construction/game. Signing
authority need not be a reader, but no such adapter was instantiated here.

## 5. The encrypted-output compatibility premise still fails first

[SOURCE: parameters/theorem read] For Construction 2, §6.1 p.48 and Theorem
6.1 p.50 require compatibility epsilon

```text
epsilon_i = 2^(-2*n*s_i-lambda_iO_i),
lambda_iO_i = lambda_i,
n=2 here, hence epsilon_i = 2^(-4*s_i-lambda_i).
```

[SOURCE] The PKE correctness definition is perfect (Definition 3.8 p.18),
and Construction 2's PKE coins each have length lambda. The theorem uses
subexponential iO and enlarged puncturable-PRF/injective-OWF parameters. The
PQ dependency audit belongs to `PQ_COMPOSITION.md`.

[DERIVED first failed premise] Consider one mixed input tuple for which the
two possible next plaintext states u0 and u1 are distinct but all permitted
outward answers agree. F_i's description includes the independent next EK.
The compatibility distinguisher can compute the public first-component
ciphertext `c*=PKE.Enc(pk[next,0],u0;0^lambda_next)` and test equality against
the first component of F_i's encrypted output. Under u0 its probability is at
least `2^(-lambda_next)`; perfect correctness makes it zero under u1.

[DERIVED] At equal parameters `lambda_next=lambda_i`, this gap is larger
than `2^(-4*s_i-lambda_i)` for every positive s_i. Independent output keys do
not alter this calculation. The source compatibility condition therefore
fails before one can use Theorem 6.1 for this private transition. This repeats
the mathematical test from `RFE_RECURRENCE.md` **only to pin its actual n=2
MIFE application**; the new ingress-specific findings are the mixed-input
capability/game audit and hidden state-issuance boundary above.

[EXECUTED / DERIVED limit] The script checks 4,096 positive integer
lambda_i/s_i pairs by exponents, not by constructing ciphertexts. The
necessary condition to evade this particular test is
`lambda_next >= 4*s_i+lambda_i`. It is not sufficient: collisions can enlarge
the event, and every efficient output test with the entire exposed future
package must meet the bound. Unequal, enlarged future parameters are therefore
an **unclosed quantitative route**, not refuted by the equal-parameter test.
Ordinary negligible IND-CPA security alone supplies no such specific
exponentially small bound. The observed gap is normally negligible and is not
an efficient cryptographic break of the actual rMIFE deployment.

[DERIVED] A marginal CPA claim for the next ciphertext is also insufficient.
Its future function keys are exposed and correlated with that ciphertext key;
all their joint information belongs in the compatibility proof. The public
single-input ladder handled this through its pre-setup joint computational
condition. Replacing its primitive by rMIFE requires an actual rMIFE theorem
with the corresponding condition; the word “randomized” does not provide it.

## 6. The older rMIFE outline does not supply the missing theorem

[SOURCE: full relevant section read] The local four-author 2013/727 §7,
printed pp.25–27 (PDF pp.26–28), defines dishonest-sender security and combines
it with dishonest-receiver simulation security in Definitions 26–27. It
explicitly leaves IND details unstated. Its concrete randomized modification
is given for the diO scheme: add a one-time signature, use a private PRF over
the ciphertext tuple, and evaluate f on decrypted inputs with those coins.
It says the iO construction can be modified similarly and contains a brief
informal security paragraph referring to single-input rFE. It does not state
the pre-public-key joint computational-output rMIFE game used by the desired
backward induction, or a reduction for that exact game.

[SOURCE clarification] This local PDF is the four-author precursor, not the
merged nine-author EUROCRYPT proceedings text. 2025/330 §1 pp.5–6 describes
the older construction's missing formal treatment. We record what was actually
seen in the precursor: there **is** a short informal proof paragraph. We do
not strengthen “no audited theorem for this game” to “no proof sketch exists.”

[SOURCE / DERIVED] Single-input 2013/729 Definition 2.4 p.8 supplies the
computational joint condition `(st1,{f(x0)}) ≈ (st1,{f(x1)})` before its public
key. Its Remark 2.5 lifts single-input challenge count. Neither changes arity
or proves public-slot replacement/cross-input compatibility. The presence of
a randomized-MIFE outline elsewhere is not a theorem connecting these two
claims. General SIM/VBB impossibility statements are not needed for this
decision and are not used to rule out the bounded resident.

## 7. Exposure and malicious-issuer scope

| Claim label / actor or artifact | Exact scope in this audit |
|---|---|
| [SOURCE / DERIVED] Public slot EK | Issues that slot without an online raw master; its exposed coalition also gets every function evaluation enabled by arbitrary replacement in that slot. |
| [SOURCE / DERIVED] Issued F0/F1/terminal keys | All remain exposed. Internally the obfuscations contain raw decryption/authentication material. Protection depends on an applicable source theorem; erasing the master file is not itself a proof. |
| [SOURCE / DERIVED] Setup erasures | Erase both PKE secret keys in every slot, all raw slot PRFs, function PRF keys, unobfuscated E/G code and key-generation copies, plus initializer plaintext/coins. Either retained PKE component secret decrypts every ciphertext in that slot. |
| [DERIVED] Honest fresh sensor | Knows its own observation/issuance coins. Uses the issued observation EK after setup and need not know other observations or state. Privacy from its own retained plaintext is excluded. Later corruption needs the corresponding plaintext/coin erasure or declared leakage. |
| [SOURCE / DERIVED] Host plus corrupted input issuers | The source decryptor game exposes requested EKs and function keys, permits arbitrary PPT processing, and challenges honestly encrypted unknown inputs subject to compatibility. Issuer collusion does not erase replacement or mixed-query obligations. |
| [SOURCE / DERIVED] Malicious input encodings | The decryptor theorem concerns confidentiality of honest challenges. Its arbitrary host computations do not establish resident authorization, honest sensor provenance, or correctness of all attacker-issued state. |
| [SOURCE / DERIVED] Malicious-encryptor randomness | Definition 4.5 pp.24–25 / Theorem 6.9 p.67 store randomized function keys privately in `KeyReg`; challenged decryptions reuse those stored keys and cache tuple outputs. Separate KeyGen calls expose independently generated keys, even for the same function. This does not give a same-issued-key fully exposed randomness oracle ideal or unbiased delivery after local branch selection. |
| [DERIVED] Malicious initializer/master issuer | Retained setup coins/raw masters can read slots and issue projection keys. Honest erasure tier A excludes them. The inspected games do not validate a malicious genesis or force the intended transition policy; tier B is unproved. |
| [DERIVED] Reader/recipient collusion | Every allowed terminal answer must already be in the ideal leakage. No hidden external recipient credential is invoked to rescue next-state ciphertext privacy. |

[DERIVED] The source permits requesting many function keys, but compatibility
can exclude a challenge after an identity/projection key is requested. It does
not enforce a resident's “only these keys may ever be issued” policy. In the
candidate, the master is erased after the finite intended key set is issued;
compromise before that erasure is a different game.

## Status and next decisive work

[DERIVED status] **Syntax retained; private-ingress theorem not established.**
The source's writer EK is an actual encryption capability rather than the
streaming-FE read-all master. Yet its union with exposed transition/future keys
can read fresh observations for the executed additive interface. A restricted
state-issuance design and a suitable joint output theorem are both necessary
to extend that interface to the intended fixed-root resident.

[OPEN next] Choose one of two precise proof obligations before expanding H:
(a) a pre-setup computational-output rMIFE theorem supporting exposed-slot
replacement, all mixed ciphertexts and full future/issuer auxiliary material;
or (b) a quantitative unequal-parameter application of Construction 2 that
actually bounds those joint distributions by its epsilon. For the restricted
EKX-only variant, additionally prove that embedded future EKS remains a
restricted writer capability under all prior-key exposure, or provide a
concrete authenticated transition/input mechanism enforcing the smaller
pairing interface. No broad new survey is recommended by this result.

[EXECUTED source/accounting] Four local-mirror PDFs were extracted; three were
read at the specific levels above, and 2013/774 received only a targeted
deterministic-syntax scan. `experiments/private_ingress/source_manifest.json`
pins absolute paths, SHA-256, locations, access level and exact extraction
commands. Full texts are ignored scratch. This lane used **zero Scry SQL,
zero schema, zero Kagi, two web search queries, zero PDF downloads**. Web
search identified the precursor metadata; every load-bearing game/algorithm
claim above was checked in the local primary PDF. No literature-wide absence
claim is made.

[DERIVED/EXECUTED draft successor] [PROVENANCE.md](experiments/private_ingress/provenance/PROVENANCE.md) investigates an internal public-proof guard and exact observation-parent binding. Its ideal controls reject false/cross-parent paths and exhibit ancestry-only and unrestricted-certifier failures. The actual joint commitment/proof/FE privacy hybrid is still missing. Five local source/extract pairs were pinned during final collection; independent review was interrupted. No encryption or ZK implementation is supplied.
