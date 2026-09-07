# Dual-mode feasibility addendum

[DERIVED decision; 2026-09-07] A dual-mode commitment is a concrete repair for
the **opening-check mismatch** in the frozen review. The initial CRS switch
can include all generated FE programs and keys by ordinary closure under PPT
computation. Neither step needs function hiding. Groth–Sahai supplies actual
commitment algebra and proof-mode theorems supporting these local steps.

[DERIVED limit] This does not yet give the H=2 private-ingress construction.
The equal-parameter randomized-output epsilon obstruction remains. Moreover,
when a current parent is equivocal, the source game's public-state-slot
replacements may contain valid alternative histories opened to that same
parent. The required joint output condition with the future terminal key can
then fail. The latter counterexample is specific to a hybrid that hides the
**current** parent while switching a differing fresh observation; a different
per-epoch mode order could avoid that example and still needs proof.

[DERIVED preservation] `REVIEW.md` and the eight artifacts pinned by
`review_hashes.json` were frozen before this followup and remain unchanged.
This addendum revises the feasibility of one missing step, not the scoped
refutation of the saved ordinary rMIFE application.

## 1. An actual equivocal commitment

[SOURCE: algorithm read] Groth–Sahai,
[Efficient Non-interactive Proof Systems for Bilinear Groups](https://eprint.iacr.org/2007/155),
local version dated April 7, 2016, §9 printed/PDF pp.24–25, constructs two
computationally indistinguishable commitment-key modes under DDH. For a
prime-order group with additive notation, let `u1=(P,alpha*P)` and choose t.
The binding key has `u2=t*u1`; the hiding key has
`u2=t*u1-(0,P)`. The scalar commitment, defined with `u=u2+(0,P)`, is

```text
Com_sigma(x;r) = x*u + r*u1,        x,r in Z_p.
binding mode:   u=t*u1+(0,P).
hiding mode:    u=t*u1.
```

[SOURCE] The scalar commitment is perfectly binding in binding mode and
perfectly hiding in hiding mode. The paper uses the two group-specific
commitment keys together in its SXDH instantiation. These are concrete
algorithms, not an assumed ideal equivocation API.

[DERIVED exact opening transformation] In hiding mode,
`Com(x;r)=(r+t*x)*u1`. Given the retained setup scalar t, set
`r'=r+t*(x-x') mod p`. Then `Com(x;r)=Com(x';r')` exactly. Uniform r gives
uniform r' for every fixed x,x', so both marginals are honest hiding-mode
commitments/openings. A vector of bounded state components can use this
coordinatewise. This is a derived equivocation algorithm from the source's
scalar formula; it is stronger than merely saying the commitment is hiding.

[DERIVED finite-circuit detail] The algebra uses uniform field coefficients.
An actual rMIFE F has a finite bit-coin tape. A bounded sampler must therefore
be specified: for example, reducing a sufficiently long uniform bit string
modulo p gives a quantified statistical error from uniform. That error is
part of the composition budget, particularly for the tiny source epsilon.
The algebra test below samples uniformly from the small field and does not
instantiate that cryptographic sampler.

[EXECUTED] `dual_mode_audit.py` uses p=257 and explicit integer exponents;
DDH is easy in this toy representation. It verifies all 66,049 scalar/opening
pairs: the binding map has 66,049 distinct outputs, every hiding-mode message
has the same 257-element uniform support, and the opening translation is a
permutation of the randomness space. This proves finite algebra identities,
not commitment or CRS security.

## 2. Why the first CRS hybrid can include the key programs

[DERIVED local reduction] Let `Build_b(sigma;omega)` be the entire honest
world-b initialization and bounded exposed view. It generates commitments,
true history witnesses and proofs using the public sigma, defines F from
public sigma/genesis/policy literals, generates independent FE instances,
issues all keys, erases designated raw secrets and runs the host. All of
these are PPT computations for fixed H=2. `Build_b` receives no commitment
equivocation trapdoor and need not use one. If an adversary distinguishes

```text
(sigma_bind, Build_b(sigma_bind;omega))
from
(sigma_hide, Build_b(sigma_hide;omega)),
```

[DERIVED] the CRS-mode adversary given sigma runs this same Build_b and
forwards the resulting view. This distinguishes the source CRS distributions
with the same advantage. It may know FE masters internally because it creates
those instances; only the prescribed erased view goes to the target host.
Every exposed prior/future key, function description, proof and snapshot can
be included. Correlations created by this common PPT process are preserved.

[DERIVED conditions] This hop relies on honest initialization being an
efficient function of the public challenged CRS and available plaintext
witnesses. It does not cover a generator that needs the challenge CRS's secret
trapdoor, an externally supplied correlated trapdoor, or an inconsistent
genesis registry. Every public copy of genesis/parameters must be generated
consistently in the simulated experiment. Malicious setup with retained
trapdoors remains outside the tier-A erasure claim.

[DERIVED function-description distinction] F can differ between the binding
and hiding CRS experiments because the entire program/key generation is the
above postprocessing. There is no need to invoke iO on two nonequivalent
genesis guards for this hop. At the later **FE message switch**, however,
one common sigma, genesis, F and current setup must be fixed. CRS closure is
not a substitute for that FE challenge's compatibility requirement.

[DERIVED trapdoor timing] Define the hiding-mode game by sampling
`(sigma,t)` with the source setup and ignoring t in Build_b. The next game
may use that already sampled t to couple two openings. This does not require
recovering or sampling a matching trapdoor from an arbitrary given sigma.
The CRS distinguisher for the first hop only needs sigma; it reproduces the
same marginal view without t. No trapdoor is inserted into the real F.

[DERIVED dynamic-parent timing] A descendant C_i that is generated by an
earlier private evaluation cannot simply be hardcoded into a preissued F_i
before it exists. Keep the saved packet layout: C_i enters through the
observation/state boundary, while genesis and per-epoch parameters are fixed
at setup. A **common C_i in a proof coupling** need not be a literal fixed
in the real initialization. Any variant requiring the literal must exhibit
an acyclic setup schedule that actually produces it in time.

## 3. Same-parent guard compatibility really improves

[DERIVED guard projection] Suppose two challenged states have valid
histories and openings to the same C under the hiding-mode CRS. For any one
replacement observation z, its public proof/authorization/epoch checks are
identical in the two evaluations. If its parent differs from C, both opening
checks fail. If its parent equals C, both succeed. Thus the opening/history
guard's success bit agrees for **every** replacement observation, including
malformed ones. This removes the exact U={O} witness from REVIEW §3.

[DERIVED] If two challenged observation packets have the same C and each
passes its own observation-only checks, the guard result also agrees for
every replacement state: it asks the same opening/history predicate against
C in either world. This statement uses the saved authorization predicate,
whose arguments are `(G,policy,epoch,C,x,auth)`; adding a hidden-state-dependent
authorization predicate would require rechecking it. Guard equality alone
does not say that Step's outputs are compatible.

[EXECUTED positive control] The algebra model verifies 132,098 observation
replacement cases across the entire toy parent domain and 131,584 state
replacement cases in the two modes. The guard projections agree. Therefore
the addendum does not recycle the original accept/reject counterexample after
the common-parent premise has repaired it.

[SOURCE: proof games and theorem read] Groth–Sahai Definitions 4–5, pp.9–10,
separate CRS indistinguishability from perfect witness indistinguishability
or perfect proof simulation on the simulated CRS. Definition 5 even permits
the proof distinguisher to know the simulation trapdoor. Theorem 18 and §11.1,
pp.34–36, give the composable NIZK result for the specified quadratic-equation
languages; not every pairing-product target is covered without the paper's
additional rewrite. These statements concern the proof distribution, not
privacy of a correlated FE state ciphertext.

[DERIVED possible relation route] A bounded Boolean verifier for the full
history relation can be expressed as scalar quadratic equations: constrain
every bit by `b(b-1)=0`, AND by `z=xy`, NOT by `z=1-x`, and fix the output
wire to accept. This is a theoretical route to the scalar quadratic language
used by the source. It requires the complete verifier circuit, canonical
encodings and all witness wires; none is implemented in this tranche.
The source proof theorem must be applied to the actual resulting language,
not to an uncompiled “authorizedStep” label.

[DERIVED joint-proof boundary] For a shared statement C with two **true**
histories under the hiding commitment CRS, a suitable proof-mode theorem can
hide which history was used. This need not invoke false provenance. It still
does not equate the distributions of the encrypted histories consumed by F.
Proof simulation/extraction trapdoors stay outside the real exposure set;
the presence of a simulator in a proof is not a deployed reader credential.

## 4. The larger replacement-state domain can defeat the next lemma

[DERIVED scoped counterexample] Consider the permitted first Learn relation
where every byte can have a true authorized one-step history from genesis 0.
The real current parent commits to state 0. A fresh final observation has
value x=0 or x=1 and is bound to that same parent. Its Learn returns ACK and
an encrypted next state `0+x mod256`; the issued terminal key reads only its
high bit. Both intended paths produce terminal answer 0. The source-game
state slot is public, so a replacement plaintext must be considered.

[DERIVED] In binding mode, an opening to the exact parent cannot certify
state 127. In hiding mode, equivocation provides an opening to 127, and the
first-Learn history with observation 127 is a **true** alternative descent
history under this mode. Replacing the state by that plaintext, while keeping
the challenged fresh observation x, yields next states 127 and 128, whose
terminal answers are 0 and 1. No false proof is required. The substitution
includes its valid opening/history; it is allowed by the source's universal
plaintext-replacement quantifier even if a real host cannot derive it without
the hidden trapdoor.

[DERIVED exact scope] This separates the **joint laws with the exposed future
terminal key**. If F itself releases only ACK and an encrypted next state,
the terminal-key distinguisher is not silently inserted into Definition 4.3's
explicit advice tuple. It defeats the stronger joint-future-output lemma
needed by a ladder proof with that key exposed. If an allowed F directly
returns this restricted high-bit answer, the same example is already an
ordinary function-output incompatibility. These are distinct claims.

[EXECUTED] The toy relation uses a permissive first-observation policy and
explicit true histories. At the common parent, binding mode accepts one byte
state, 0; hiding mode accepts all 256 byte states. Values 127 and 255 separate
fresh x=0 from x=1 through the terminal key. All guards accept in these
separating cases. A policy that immutably pins an already-issued first-input
record may rule out these alternative histories; that additional relation
must be checked instead of assuming this example still applies.

[DERIVED no target attack claimed] The real host receives no equivocation
trapdoor. The valid replacement above is part of the source compatibility
domain and the failed reduction lemma. It does not contradict the legitimate
real-to-hiding CRS hop, whose host remains computationally bounded and is
not handed the new opening. A hiding-mode game may contain mathematically
valid witnesses that its actual adversary cannot find.

[OPEN mode-order scope] This counterexample applies when a differing fresh
observation is switched while its **current-parent** commitment is hiding.
Keeping that parent binding and hiding only a subsequent commitment could
avoid this particular witness. H=2 proof work would then need one complete
mode/key/message schedule for all private input switches, with consistent
parent packets and no timing cycles. There is no conclusion here that all
per-epoch mode schedules fail. This alternative does not change the next
section's actual-source epsilon problem.

## 5. The source rMIFE application is still unavailable

[SOURCE / DERIVED] The locally pinned 2025/330 Theorem 6.1, p.50, still
requires `epsilon_i=2^(-4*s_i-lambda_i)` for n=2. When F's two next-state
payloads differ, its first next-PKE ciphertext has the fixed-output event
analyzed in REVIEW §5. Dual-mode commitment/proof setup does not hide that
ciphertext from the compatibility distinguisher or remove the next state's
plaintext component.

[DERIVED] With a fixed commitment-opening width across adjacent layers and
equal PKE parameters, the corrected event exceeds epsilon. In the GS scalar
setting, uniform next opening r has a specified-value probability 1/p; using
that value and fixed first-PKE coins gives gap at least
`(1/p)*2^(-lambda_next)`. The stored field-opening width is at most the
current input/ciphertext width. Increasing the sampler's raw coin tape while
still storing one reduced field element does not by itself erase this event.
Unequal, sufficiently enlarged next parameters could avoid this particular
comparison, but an actual quantitative joint-compatibility bound is still
required. Merely knowing a future FE advantage is negligible does not prove
it is below the specified exponentially small epsilon.

[DERIVED complete attempted order] The following separates the justified
steps from the unavailable one:

| Step | Status |
|---|---|
| Real binding CRS, one honest world and all generated keys | Defined honest endpoint |
| Switch to hiding CRS with the same honest-generation algorithms | Conditional on the source CRS theorem; valid PPT postprocessing reduction |
| Retain hidden t in that game and couple two state openings to common C | Exact algebra with honest uniform-opening marginals |
| Hide the proof witness for a common true statement in the appropriate proof mode | Available source proof notion; complete relation/circuit mapping still required |
| Switch encrypted state/observation plaintexts with one common F and full exposed future package | Not established: epsilon fails at equal parameters; some current-parent hiding schedules also fail the joint replacement-state condition |
| Restore honest world-1 openings/proofs and the binding CRS | Only reachable after the unsupported switch; no completed end-to-end hybrid |

[DERIVED state-slot withholding] Withholding the state-slot EK would remove
U={S} from the nominal source I. The saved independent-layer reduction still
has to generate earlier function/key artifacts that contain this future EK
as an encryption literal. Requesting it from the challenged future rMIFE
instance places S in I. A theorem constructing those correlated prior
artifacts without revealing/requesting that EK would be additional work.
Dual-mode commitments do not supply function hiding or that key-generation
interface. This is a proof/exposure obligation, not a claim that ordinary
public-key syntax requires publishing every slot's EK to the host.

[DERIVED credential check] In this scalar commitment, two distinct scalar
openings to the same C reveal t via
`t=(r-r')/(x'-x) mod p`. The toy verifies this identity. Thus a proof that
hands both openings to a real coalition would also hand it equivocation
power in this instantiation. The proposed reduction keeps these private
challenge witnesses and trapdoors internal. An unrestricted state-signing
key or false-proof trapdoor remains a separate authority; neither is renamed
to the public prover key here.

## Status and source accounting

[DERIVED status] The dual-mode route is plausible at the commitment/CRS
and proof-witness level, and fixes one previously explicit gap. It has not
passed the actual source rMIFE encrypted-output game. Keep the completed
negative review, its narrower initial-private-input/public-learning positive,
and this qualified local repair as separate claims.

[OPEN next] Before a new construction claim, provide the full per-epoch
hybrid schedule and a quantitative randomized-MIFE theorem covering its
actual mixed-input functions with every future/prior key exposed. If the
next-parameter growth is used, prove its compatibility bound; if state-slot
issuance is restricted, realize the prior-function package without quietly
requesting the excluded EK. The local algebra is no substitute for either.

[EXECUTED] The command, Python version, code hash and complete finite results
are retained in `dual_mode_results.json` and `dual_mode_audit.stdout.txt`.
`dual_mode_sources.json` pins the local GS PDF/extract SHA-256 and exact read
locations, and rechecks the frozen review hashes. The toy implements no
encryption, NIZK, authenticated issuer, or hardness assumption.

[EXECUTED accounting] This followup used two web search queries, one HTML
open of the GS eprint landing page, zero Scry SQL/schema or Kagi queries and
zero PDF downloads. One new local PDF was extracted; 2009/599 was only
observed to exist and was not read or used as evidence. The four-source
negative review's counts remain frozen and unchanged.
