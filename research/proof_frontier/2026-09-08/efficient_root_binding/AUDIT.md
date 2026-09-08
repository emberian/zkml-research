# Efficient binding after arbitrary-root resolution

[DERIVED outcome, 2026-09-08] The frozen root-resolution theorem remains
correct, but **its semantic BadRoots probability cannot be replaced by a
computational collision advantage**. This fails even for the exact two-leaf
BinaryMerkle interface in an ideal random oracle: an efficiently generated
honest root has conflicting accepted paths with probability approaching
`1−e^-2`, although no efficient party need find them. The efficient positive
route is a different game: freeze a word extracted from the hash-query log at
each commitment, then charge later accepted openings that disagree with it.
Below is a concrete classical-ROM reduction and its finite loss. It needs new
word/farness and source adapters; it does not price the frozen BadRoots event.

## 1. Frozen input and actual interface

[SOURCE] Read the author [README](../formal/full_ud_commitment_timing/README.md),
all five source modules, and the independent
[root-resolution review](../../../learn_infer_only/experiments/adversarial_review/full_ud_root_resolution/REPORT.md).
The frozen patch is `449608f151061051d3c2567d86d6b505c86ecf03906f990ffb7a5238995e4756`.
`OpeningResolution.word` uses `Classical.choose` over all accepted values and
paths. `DoubleOpening` existentially quantifies two such paths. `BadRoots`
ranges over roots emitted on the actual challenge prefix. The exported
BabyBear head is `Pr[raw accepts] ≤ 2^-55 + Pr[BadRoots]`, with the existing
19-round tower, 3603 coherent queries and initial resolved-word farness.
The author and reviewer already keep the binding term unpriced.

[SOURCE] `/Users/ember/dev/minidregg/Selvage/BinaryMerkle.lean:80–160`
recomputes a leaf hash and an ordered binary path with exact length checking.
Sibling digests are arbitrary members of `Digest`; the verifier does not
require them to have leaf/subtree preimages. Lines 257–275 prove that two
supplied unequal accepted values at one index imply a leaf-or-node collision.
This deterministic argument needs no honest-root-image premise.

[SOURCE] The active FRI verifier, pinned in the frozen source evidence,
calls `mmcs.verify_batch` with a reconstructed evaluation row at
`breadstuffs/vendor/plonky3-fri-82cfad73/src/verifier.rs:442–457`.
The matching local p3 commit `82cfad7` has
`merkle-tree/src/mmcs.rs:1049–1194`: it hashes the supplied rows, checks the
path length from the shape/arity schedule, incorporates supplied sibling
digests into compression inputs, may inject other-height row hashes, and
compares with a cap entry. The public verification interface contains no
prover hash-query log, state snapshot, rewind operation or complete word.
These are source reads, not a proved binary-to-MMCS adapter or execution test.

## 2. A quantitative counterexample to pricing semantic existence

[DERIVED construction] Let the digest set have cardinality `N≥2`. Let
`L:{v0,v1}→D` and `H:D²→D` be independent uniformly sampled functions, with
`v0≠v1`. This is the classical random-oracle model with typed leaf/node
domains. Run the honest depth-one commitment on `(v0,v0)`:

    a = L(v0);  rt = H(a,a).

The observed transcript contains just the valid index-zero opening
`(v0,[a])`. Thus its observed conflict event is identically false. Ambiguity
at index zero holds exactly when there exists `s∈D` with
`H(L(v1),s)=rt`; then `(v1,[s])` is also accepted by the exact verifier.
Ambiguity at index one analogously uses `H(s,L(v1))=rt`. Literal
DoubleOpening is the union over both indices.

[DERIVED probability] With probability `1/N`, `L(v1)=a`, already giving
the alternative opening. Otherwise the `N` inputs `(L(v1),s)` are distinct
from `(a,a)`, and their outputs are independent of `rt`. Consequently

    Pr[index-zero ambiguity] = 1 − (1−1/N)^(N+1).

The row/column union for both indices has `2N−1` distinct inputs, disjoint
from `(a,a)` when the leaf digests differ. Hence the exact root event is

    Pr[DoubleOpening(rt)] = 1 − (1−1/N)^(2N),

which tends to `1−e^-2`. This is a selected honest root, with no malformed
path or adversarial root search. Extra values in the leaf alphabet can only
increase the semantic event. An arbitrary sibling digest need not correspond
to a complete alternative honest tree; the source interface deliberately
accepts paths without that extra condition.

[DERIVED separation] Any classical oracle algorithm making at most `Q`
queries and outputting a candidate collision has collision success at most
`binom(Q+2,2)/N`: append at most two queries for its proposed collision
inputs, then apply the ordinary adaptive birthday union bound. This holds
for either typed hash collision event, even charging a larger union over all
responses. For polynomial `Q` and `N=2^λ` this is negligible while the
semantic event above is constant. Thus no polynomial-resource reduction can
generally infer a small semantic BadRoots probability from ordinary CR.
The counterexample already works classically; no QROM lower bound is needed.

[DERIVED scope] This refutes the proposed **event identification**, not
Merkle computational binding, the frozen theorem, or every possible CR-based
interactive compiler. For each fixed oracle, BadRoots is a predicate of the
selected root; the displayed probability averages over the oracle setup.
An efficient transcript may use only one opening even on bad oracle setups.

[EXECUTED finite witness] `finite_controls.py` exhausts all 64 two-value,
two-digest function tables and all 177,147 two-value, three-digest tables.
The exact root-event probabilities are `15/16` and `665/729`, respectively;
the narrower fixed-index-zero probabilities are `7/8` and `65/81`.
observed conflicting pairs are zero in every supplied transcript. These are
tiny total-function tables, not cryptographic hash evaluations or attacks.

[DERIVED revision precision] The initial draft labeled the fixed-index
formula as the full root event. This revision distinguishes them and verifies
both counts; the corrected root probability strengthens the same barrier.

## 3. The lossless efficient game the opening interface does support

[DERIVED game] Setup supplies the hash-suite description/key. A bounded
adversary, with all hash-dependent preprocessing included in its resource
budget, outputs an adaptive transcript of at most `U` records
`(scheme/shape,root,index,value,path)`. The game verifies each record. It
wins if two accepted records have the same scheme/shape, root and index but
unequal values. A dictionary can retain the first accepted record for each
key and return the first observed conflict.

[DERIVED reduction] Given that pair, compute both leaf digests. If they
are equal, output a leaf collision. Otherwise reconstruct both paths. Since
the terminal roots agree, some first meeting of their unequal intermediate
digests uses unequal ordered child pairs with equal parent hash. Output that
node collision. The pair-to-collision postprocessing takes at most
`2(k+1)` hash evaluations and `O(k)` digest storage for depth `k`.
Processing the whole transcript takes at most `U(k+1)` verification hash calls
plus dictionary work; no exhaustive path search or rewinding is used.

[DERIVED theorem] Against the joint leaf-or-node collision game,

    Pr[observed conflicting openings] ≤ Adv_suite_collision(B),

with no success loss and no multiplier for the number of roots, levels or
opened positions. If separately stated leaf and node assumptions are used,
the two corresponding advantages add. The source Lean implication is the
deterministic mathematical core; an efficient output datatype/algorithm and
resource theorem remain unformalized. The actual MMCS needs the fixed-shape
cap/row/compression adapter before this exact binary cost is assigned to it.

[DERIVED limit] This game is too weak to substitute into the current
root-resolution proof: its second canonical path may never appear in any
transcript. A table filled after final queries also lets a purported word
depend on those queries, violating the prefix timing needed by ideal FRI.

## 4. A concrete prefix-time classical-ROM alternative

[DERIVED model] Use independent typed uniform random functions for the leaf
and ordered-node hashes, with common digest set `D`, `|D|=N`. Equivalently
use one random function on an injectively encoded tagged query domain.
Leaf serialization must identify semantic values injectively. All parties
use one consistent lazy cache. The adversary has classical state and queries;
its code, coins and initial auxiliary input are independent of that oracle,
or all oracle-dependent preprocessing is included in the logged game.
No root-dependent unlogged advice is allowed under the empty-cache bound.

[DERIVED timing] A classical prover emits at most `R` raw Merkle roots.
At each emission, before the next independent verifier fold challenge,
record the root, the shape/index interpretation and the complete cumulative
hash-query log. Copying the log reference is proof-side bookkeeping and does
not alter the prover's private state. It is immutable thereafter. The final
polynomial/evaluation word is frozen before query sampling and is transparent,
so it needs no additional Merkle extraction checkpoint.

[DERIVED extractor E] At checkpoint `(rt,k,log)`, reconstruct along an index:
look up the first logged node query with answer `rt`; choose the child for
the prescribed address bit and recurse for exactly `k` levels. At the leaf,
look up the first logged leaf query with that digest and return its value.
Return a fixed public default if any lookup is absent. The whole word is
the resulting deterministic function of checkpoint and index. It need not
hash back to the original root. Under the ideal identity commitment it is a
valid ideal word/root pair, exactly as in the frozen semantic construction.

[DERIVED bad trace] Include honest verification queries in a bound `q` on
all distinct hash inputs. Flag either of the following when a fresh response
is sampled: it equals a previous response; or it equals a previously declared
root or a digest component of a node input seen no later than this query.
The latter includes the current input, ruling out self-reference. At fresh
query `t`, at most `(t−1)+2t+R=3t−1+R` outputs are forbidden. Therefore

    δ_trace ≤ min(1, ((3q²+q)/2 + Rq)/N).

This is deliberately conservative. It covers cross-type response collisions,
all emitted roots and all child components, whether or not eventually used.
No number of openings is hidden: `q≤q_prover+S(k_max+1)` suffices for `S`
unpruned binary opening verifications, with all preprocessing also charged.

[DERIVED invariant/proof] Suppose the trace is unflagged. If a later accepted
path's final query were absent at the root checkpoint, its later response
would hit the earlier declared root. Thus the final query was already logged.
Uniqueness of responses pins its ordered children. If the next path query
were absent at the checkpoint, its response would hit an earlier child
component. Induct down the path, including the leaf query. Every query on
the accepted path was in the checkpoint, and every selected lookup is unique.
Hence its value equals `E(checkpoint,index)`. This proves the implication
for **every opening actually verified in that execution**, including ones
chosen after future challenges or the full final query batch. It does not
quantify over unqueried alternative paths in the complete random function.

[DERIVED cost] A naive finite-log implementation takes `O(qk)` comparisons
per extracted coordinate; a persistent response index gives `k+1` lookups.
Enumerating a length-`L` word necessarily writes `L` values and takes
`O(L(k+1))` indexed lookups. An implicit word oracle suffices for the
mathematical ideal-verifier reduction. A claim of polynomial total extraction
must specify that `L` is polynomial in the permitted input/prover-size bound,
or explicitly retain this oracle representation. No exponential enumeration
of continuations or digest preimages is being hidden.

[DERIVED conditional soundness] Replace the semantic resolver by these
checkpoint words and replace existential raw opening acceptance by acceptance
of the actual supplied proof. Reuse the frozen deterministic round equations
and transparent terminal argument. On an unflagged trace, actual raw
acceptance implies ideal adaptive acceptance for the extracted words. Let
`Far_E` mean that the initial extracted word satisfies the same initial
farness premise, and retain the same tower/gap/sampling premises. Then

    Pr[actual raw accepts ∧ Far_E] ≤ ε_ideal + δ_trace.

If `Far_E` always holds for the invalid inputs under study, drop it on the
left; otherwise add `Pr[not Far_E]` to bound unconditional acceptance.
Here `ε_ideal` is the existing ideal bound, conditionally `2^-55` for the
frozen BabyBear instantiation. This is a new scoped mathematical reduction,
not a new proved Lean theorem or a deployed security number.

[DERIVED timing justification] Fix the sampled full random function and
the prover's independent random tape, without conditioning on the good-trace
event. Each checkpoint word then depends only on the challenge prefix, so
the ideal theorem applies pointwise whenever its initial word is far.
Average afterward and add the bad-trace probability. Conditioning future
challenges on successful extraction instead would be unjustified. The event
`Far_E` is fixed before the first challenge. No assertion equates it with
farness of the frozen `Classical.choose` word; they can differ on roots with
semantic double openings.

[DERIVED totality] Aborted prover branches may be extended with fixed default
roots/words to define a total prefix strategy; the actual verifier rejects
those branches. This extension uses no future challenge or query information.

[EXECUTED finite control] The script checks 22,016 accepted toy openings
over all two-digest oracle tables and prefix traces of length at most two.
All 10,880 checkpoint-word mismatches flag the defined trace event. It also
checks the exact union-bound numerator on 1,071 integer `(q,R)` pairs.
This is a finite falsifier search for the derivation, not a general proof.

[EXECUTED nonvacuity] An explicit unflagged five-entry checkpoint log
resolves the F5 word `(1,4,4,1)` on domain `(1,2,3,4)`. Its distance to all
25 affine codewords is at least `1/2`, so initial extracted-word farness at
radius `2/5` is inhabited. A transparent constant terminal word fixed before
queries accepts five of the ten one-query challenge/index executions. This
exhibits farness and actual accepting openings together, without claiming
all premises of the 19-round BabyBear head.

## 5. Primary-source correspondence and exact limits

[SOURCE] Ben-Sasson–Chiesa–Spooner, *Interactive Oracle Proofs*, local
ePrint [2016/116](https://eprint.iacr.org/2016/116), §3.1 pp.14–15,
specifies Valiant's extractor from the oracle query graph. It excludes equal
responses and forward references to future query responses, then fills
missing leaves with zero. Lemma 3.2 states a `(m²+1)2^-λ` failure term in
its own query/output game. This supports the log-and-timing mechanism; its
exact bit-leaf encoding, root-query index and output conditions are not a
drop-in instantiation of this repository's row/MMCS verifier. Our bound above
charges actual verifier calls explicitly and does not borrow its constant.

[SOURCE] Block et al., *Fiat-Shamir Security of FRI and Related SNARKs*,
local ePrint [2023/1071](https://eprint.iacr.org/2023/1071), §3.4 pp.24–25,
uses the random oracle itself for the Merkle tree and for the BCS transform.
Theorem 3.15 consumes round-by-round soundness/knowledge premises and gives
an explicit classical BCS term plus separate quantum asymptotic statements.
It is a compiler theorem in that oracle model, not a conversion of semantic
collision existence into standard computational collision resistance.

[SOURCE] The local VCVio snapshot `ffd0ca1` implements the stronger practical
proof interface already: `MerkleTree/Extractor.lean:40–89` is first-response
log lookup; `MultiExtractability/Sequential.lean:34–68` threads abstract
private state and records a checkpoint after each root; `Stateful.lean:51–132`
fixes configuration-tagged immutable snapshots. `Game.lean` uses a shared
cache for commitment, opening and honest verification, and permits the
opening adversary to see the final private and extractor states.

[SOURCE] Its `StrongBound.lean:697–717`, theorem
`anyCheckpointDisagreement_binomial_bound_of_prefixQueryBound`, bounds the
stronger checkpoint disagreement event by

    [binom(q_adv,2) + nodeBudget*(q_adv+verifierOverhead)] / |Y|,

with explicit global adversarial-query, verifier-query, per-configuration
node and checkpoint-count hypotheses. It addresses accepted openings and
snapshot evolution; it does not bound all mathematical alternative paths.
We inspected source rather than rerunning its Lean build. The homogeneous
internal-node model recovers digest-valued leaves: the repository's extra
`leaf : Value→Digest` layer still needs a typed leaf extractor or a separate
leaf preimage/binding adapter. Row arity, cap roots and serialization remain
additional adapters, so this theorem is not silently imported here.

## 6. Rewinding and auxiliary-state barriers

[DERIVED reset game] One can define a classical reset interface that freezes
the prover state immediately after a root, restores it twice, and supplies
independent future verifier challenges under the same hash oracle. For a
fixed requested index, let `p_v` be the probability that one continuation
returns an accepted opening with value `v`. Two independent continuations
yield conflicting openings with probability

    (sum_v p_v)^2 − sum_v p_v^2.

An extractor then uses §3 with no further success loss. If the index is also
guessed, the index-selection probability must be charged. This is an exact
reachable-output game, not a reduction from BadRoots: in §2 the prover always
returns `v0`, so every such reset experiment has conflict probability zero.
No assumed continuation coverage or cheap complete response table follows
from semantic existence. CR-based interactive compiler proofs may establish
different reachable-oracle games; this audit makes no impossibility claim
about those games.

[DERIVED requirements] The reset model must specify restoration of private
coins, state, external service state and the common hash function/cache;
ordinary Merkle verification gives none of that access. The log model instead
needs oracle-query visibility and an immutable snapshot at the right time.
Giving unlogged oracle-dependent auxiliary information invalidates its fresh
uniform-response argument. Preprocessing can be admitted by logging and
charging it, or by a separate initialized-cache theorem with its hypotheses.
Independent classical advice can be fixed pointwise. Copying quantum private
state or reading superposition queries is not permitted by this model;
there is no claimed QROM or QPT extension of the derived log reduction.

[OPEN actual deployment] Concrete Poseidon-based hashing is a deterministic
public implementation, not the lazy random function assumed above. Connecting
it to this model requires its own justified assumption/idealization, and the
Fiat–Shamir/PoW challenge interface needs a separate compiler proof. The
prefix-log theorem alone does not address initial PCS relation/farness,
variable-arity injected inputs, cap layout, bit-reversed indexing or quantum
adversaries. None is repaired by merely assigning collision bits.

## 7. Handoff before formalization

[DERIVED recommendation] First formalize the efficient two-supplied-opening
output algorithm, if a computational collision-game wrapper is desired.
For the FRI bridge, propose a successor actual-transcript/checkpoint-word
theorem with §4's explicit ROM, timing and farness contract, preferably
adapting the already available VCVio checkpoint interface. Preserve the
frozen semantic theorem as a separate valid statement. Root should decide
that contract before any formalization or companion patch.

[EXECUTED scope] Read-only companion and frozen artifacts; no Lean, crypto,
lattice attack, runtime benchmark or protocol execution. Only finite function
tables/public integer arithmetic ran. Source discovery used three web search
queries, zero Scry SQL and two local-mirror PDFs; no PDF downloads. This is
a targeted audit of named sources/interfaces, not an absence survey. No
shared ledger, verdict, security label or commit was changed.
