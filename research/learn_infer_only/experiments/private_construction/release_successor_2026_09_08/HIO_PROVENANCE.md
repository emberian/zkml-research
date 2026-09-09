# Public provenance for bounded private continuation issuance

[DERIVED, 2026-09-08] A public certificate of exact private specialization can
replace the honest issuance registry assumed in `HIO.md`. Every private issuer
checks a complete path from its pinned genesis before obtaining the new private
command. The certificate witness is that command and the compiler randomness;
it contains no plaintext resident state or continuing writer master. This is a
conditional construction using iO and a precisely specified proof system, with
the same finite horizon and size limitations as the ordinary-iO wrapper.

[DERIVED proof improvement] Canonical replay substitution is unnecessary for
the privacy proof. Switch `iO(Q(parent,cmd0))` directly to
`iO(Q(parent,cmd1))` while retaining the same parent bytes. The paired residual
invariant makes these circuits equivalent. Their certificate statements remain
true, although the iO reduction does not know the challenge compiler coins.
Thus this route needs simulation for true statements with unknown witnesses;
it avoids requiring simulation of false statements. Section 5 explains the
stronger requirement if canonical replay hybrids are used instead.

## 1. Public object and exact certificate relation

[DERIVED parameters] Pin an authenticated genesis descriptor

```
G = (proof CRS, iO suite and parameter, Step/version/policy,
     canonical encodings, horizon T, all depth-dependent resource bounds, O0).
```

Here `O0` is the honestly initialized obfuscation of `R_s0^T` from `HIO.md`.
The actual genesis bytes, including the CRS, are pinned; an attacker-supplied
replacement is not accepted. Honest initialization and retirement of the raw
initial state remain assumptions. This note does not prove a malicious
initializer used the intended private state or erased its records.

[DERIVED pinning scope] Authentication pins the descriptor produced by setup
in each execution. The proof compares real and simulated **setup
distributions**, including their authenticated descriptors; it does not
construct a simulator for one externally hardcoded CRS bitstring.

[DERIVED encoding] Use full parent and child bytes in the statement. This
avoids adding a hash-collision assumption to the theorem. A node is `(d,O)`.
An edge statement is `x=(G,d,O_parent,y,O_child)`, with child depth `d+1`.
Full ancestry consists of such statements and their proofs, in increasing
depth, with exact byte equality at every join. The root is `(0,O0)`. No
registry, signing key, online authority, or unique-current-branch assumption
is used. The host may retain, replay, or fork every certified node.

[DERIVED NP relation] Let `Q(d,O,c)` be the deterministic, publicly specified
wrapper in `HIO.md`: on a canonical residual tape of length at most `T-d-1`,
evaluate `O` on `c` prepended to the tape and remove exactly its first release.
Reject invalid encodings identically. Define the polynomial-time relation

```
R_edge(x; c,r) = 1 iff
    x has the pinned suite, valid public sizes and 0 <= d < T;
    c is an admitted canonical command at depth d;
    y is the first release of Eval(O_parent, [c]);
    O_child = iO(pad_d(Q(d,O_parent,c)); r).
```

The last equality is exact byte equality, with the pinned compiler run as a
deterministic algorithm on explicit coins `r`. Compiler time, coin length,
program size and evaluator time have public bounds. Output and proof lengths
must be fixed or padded to public bounds, or explicitly counted as leakage.
This relation does not contain a universal functional-equivalence test.

[DERIVED correctness premise] The compiler must preserve functionality for
**every admitted coin string**, including adversarially chosen coins. A
statement that compilation is correct only with overwhelming probability over
honest random coins does not by itself suffice: an attacker could choose a bad
coin string and prove its exact compilation. An alternative needs an explicit
publicly verifiable restriction on coins that implies correctness. No such
restriction is silently supplied here. Evaluation is a total, fuel-bounded
public algorithm; the resource bounds are those of actual valid programs.

[SOURCE and DERIVED specialization] Eprint 2023/925, Section 3.3, printed p10,
defines iO functionality with probability exactly one for each circuit and
input. For a bounded finite uniform compiler coin tape, every coin string
has positive probability, so that definition implies correctness for every
such admitted string. Thus the abstract source model supports the premise;
any selected concrete compiler still needs its own correctness guarantee.

[DERIVED issuance algorithm]

```
PrivateIssue(G, proposed_parent, full_ancestry, command_source):
    validate root, every depth and byte join, and every edge proof;
    reject any invalid or over-bound path;
    only after acceptance, obtain private command c from command_source;
    compute y and O_child with fresh compiler coins r;
    prove R_edge(x; c,r), using fresh proof randomness;
    publish (y, O_child, proof) and its public path information.
```

[DERIVED functionality] Anyone knowing a command can extend a valid public
parent and prove this relation. A new private issuer needs only its own command
and that public ancestry. The issuer does not need earlier private commands,
the parent's compilation coins, or resident state. Real-world soundness and
all-coins compiler correctness imply by induction that every accepted path
represents successive bounded Step transitions from the pinned root. The
certificate proves permitted derivation, not human consent to a command,
single-branch continuity, freshness of an observation, or freedom from
poisoning through otherwise admitted commands. Additional authorization, if
part of Step's policy, must itself appear in the relation and credential model.

## 2. Exact proof-system assumptions

[HYPOTHESIS: specified proof primitive, not an instantiated backend] Use an
NP proof system for `R_edge` with `Setup`, `Prove`, and public `Verify`, and
the following reduction interfaces. The names below define what is needed;
an implementation called “simulation-extractable NIZK” is not automatically
being asserted to satisfy them.

1. **Completeness and real-CRS soundness.** Honest witnesses give accepting
   proofs. Under honest setup, a polynomial adversary cannot certify a false
   fresh edge, including after seeing other honest proofs.
2. **Adaptive, auxiliary-input, multi-theorem zero knowledge.** A
   `SimSetup` produces `(crs_sim,tau_sim,tau_ext)`. Real CRS plus all honest
   proofs is indistinguishable from simulated CRS plus `SimProve(tau_sim,x)`
   for adaptively selected true statements. The simulator receives no witness.
   The indistinguishability includes all obfuscations, releases, hostile
   proofs, retained ancestors and subsequent issuance behavior. In particular,
   the reduction can simulate a true statement for which the only unavailable
   witness component is its iO challenge's randomness.
3. **Accepting simulation on true statements.** In the direct proof below,
   every simulator-issued statement is true. For all such statements the
   simulated proof verifies. No claim of accepting simulation for arbitrary
   false statements is required for that proof.
4. **Online extraction after simulation.** Maintain the set `S` of exact
   statements for which the simulator issued proofs. For every fresh
   accepting `(x,pi)` with `x` outside `S`, an online trapdoor extractor
   returns `w=(c,r)` satisfying `R_edge(x;w)`, except with a stated
   multi-statement failure probability. Extraction works during the same
   adaptive interaction, before the next private issuance; an eventual
   rewinding extractor with unspecified interaction effects is insufficient.
   Subsequent simulator queries may depend on previously extracted witnesses.
   Require security under that feedback: equivalently, expose a controlled
   extraction interface on fresh statements which returns only a checked
   witness or failure, alongside the simulation interface. Do not grant the
   adversary the raw trapdoors. The bound covers the whole bounded sequence
   of such requests, not just one final proof.

[DERIVED replay handling] Statement-new extraction is enough; proof-new
extraction is unnecessary. If `x` is in `S`, its child semantics is already in
the reduction's table. Replaying or rerandomizing a proof of exactly that
statement does not require extraction. Changing the parent, child, release,
depth or genesis changes the statement, so it requires a new valid witness.
All ancestry edges are processed from the root; a known simulated child does
not allow skipping a mismatched parent path.

[DERIVED setup boundary] The simulation/extraction trapdoors exist only in the
reduction. Honest deployed setup retains only the CRS. Any setup coins or
intermediates that enable forgery or witness recovery must be erased under
the honest-initialization assumption, or their harmlessness must be proved
for the selected proof system. This is an additional setup requirement, not
a claim of transparent setup. Retaining a certificate extraction credential
could expose private commands; retaining a simulation credential could permit
input-stealing parent substitution. Neither is a permitted continuing role.

## 3. Paired invariant and adversarial descendants

[DERIVED privacy experiment] There are polynomially bounded numbers of honest
private issuances and submitted ancestry edges, all inside fixed public
resource bounds. At a protected issuance the environment supplies a paired
command policy `(c0,c1)`; only `c_b` is given privately to the real issuer in
world `b`. The host sees the complete public forest, including every release
and proof, may submit arbitrary paths and proofs adaptively, and may locally
compile descendants using its own known commands and coins. Private command,
compiler and proof records of the protected issuances are excluded from host
exposure. Output timing and implementation side channels are not modeled.

[DERIVED admissibility] The paired input policy is an efficiently samplable
coupling of two legal private command sources. Each actual source runs from
its own private inputs/randomness and public interaction; it is not given a
plaintext-state oracle. The reduction can sample the pair and maintain its
paired logical states to prove admissibility. At each protected issuance
require equal immediate releases and

```
R_(Step(s0,c0).state)^(H-1) = R_(Step(s1,c1).state)^(H-1)
```

as functions on the entire remaining encoded domain, where the accepted
parent is represented by both `R_s0^H` and `R_s1^H`. This is an admissibility
premise, not an efficient equality test performed by the issuer. It must hold
through the mixed issuance schedules used in the proof, not only along one
completed honest path. The fixed margin policy described below satisfies the
required invariant directly.

[DERIVED reduction table] Associate an accepted parent with a pair
`(s0,s1,H)` whose residual functions agree. The root pair is given by the
challenge. For a simulator-issued honest node, record the paired successors
at issuance. For every other accepted edge, extract `c,r`, check the relation,
and update **both** logical states using that same command `c`. Full parent
residual equivalence implies equal first releases and equal residuals after
every common command, by evaluating tapes `c::h`. Exact compilation therefore
preserves the invariant even for hostile privately compiled descendants.
No assumption that the host reveals its chosen command is needed.

[DERIVED witness ambiguity] An extracted witness need not equal the coins or
command originally used by the host. Any valid witness establishes the actual
child's residual semantics. If different histories can certify the same
public program, the theorem protects the resulting continuation function; it
does not prove unique hidden history. A state-dependent paired policy must
be valid for the representative chosen by extraction or be specified so that
representative choice is irrelevant. The margin policy is of the latter kind.

## 4. Direct joint-view theorem

[DERIVED conditional theorem] Under the premises above and auxiliary-input iO
at the largest actual circuits and interaction resources, the two entire
public issuance forests are computationally indistinguishable. This includes
accepted adversarial ancestry and its continued use as a private issuer's
input. The real issuer uses public verification only; the extraction table is
a proof device and is not a registry or deployed secret state.

[DERIVED proof] First replace the real CRS and every honest certificate in
world 0 with simulated CRS and simulated proofs. These are true statements
and the multi-theorem zero-knowledge assumption covers the whole interaction.
Track accepted ancestry with the table and extractor; stop the proof
experiment on a fresh accepting statement for which extraction fails.

Switch the root and protected issuance outputs one at a time in chronological
issuance order, up to a fixed public upper bound; unused challenge positions
after termination are dummy positions. At a nonroot challenge, the **same actual parent bytes**
represent both paired logical residual functions. Consequently

```
Q(d,O_parent,c0)(h) = R_s0_after_c0^(H-1)(h)
                    = R_s1_after_c1^(H-1)(h)
                    = Q(d,O_parent,c1)(h)
```

on every encoded input, including invalid encodings. The circuits are padded
equally. Feed these circuits to the iO challenger, obtain its child bytes,
and simulate that child's certificate. The statement is true for whichever
branch was chosen: some valid compiler coins exist even though the reduction
does not have them. Equal immediate releases permit the same public `y`.
Earlier retained objects are auxiliary information; later host computations
and issuances are performed using the returned child. Induction from
Section 3 handles new hostile edges throughout this interaction. Finally
replace simulated CRS and proofs with real ones in world 1.

[DERIVED conservative loss] Let `N` count the root switches and honest
private-output switches, and let `epsilon_ext` bound any extraction failure
over a complete interaction with the declared edge/query limits. One loose
triangle/abort accounting is

```
Adv_forest <= N epsilon_iO + 2 epsilon_MT-ZK
              + 2 (N+1) epsilon_ext.
```

Each term is evaluated at the full reduction resources. If extraction is
instead bounded per submitted fresh edge, replace `epsilon_ext` by the union
bound over those edges. Add any explicitly admitted correctness/completeness
failure probabilities. No finite security bits are inferred from this
symbolic bound. The iO reduction supplies an equivalent dummy pair if a
detected extraction failure occurs before its challenge; its experiment
aborts rather than using an uncertified parent's semantics.

[DERIVED frozen witness] The two-coordinate learner and horizon in `HIO.md`
remain unchanged. Starting with second weight `T+1` or `T+2`, every valid
depth-`t` path has second weight at least `T+1-t`, since each admitted command
lowers it by at most one. Any remaining tape has at most `T-t` commands,
so the second coordinate stays positive. Identical paired commands, or the
pair `Learn(1,-1)` / `Learn(1,+1)`, preserve all remaining trace functions;
the same actual parent handles both sides' first-coordinate behavior.
Coordinate 0 still supports the active learning example already proved in
`HIO.md`. No extended horizon or renewal is introduced.

[DERIVED witness-specific weakening] For this fixed command-pair policy,
equivalence follows for **every** rooted reachable parent of the stated
depth, without recovering its particular history. A separate proof can use
simulation soundness after true-statement simulation and existential witness
induction instead of extracting commands. It needs the distributional iO
form in which a negligible probability of invalid circuit pairs contributes
that probability to the advantage bound. The general online-extraction
theorem above avoids relying on that unstated formulation and accommodates
paired policies which actually need extracted logical states. This paragraph
does not instantiate a weaker NIZK backend.

## 5. Why the canonicalization proof needs more

[DERIVED canonical-hybrid issue] Replacing an honest child with an independent
`iO(R_s_after_c^(H-1))` preserves functionality, but its byte string need not
equal `iO(Q(parent,c);r)` for any `c,r`. Therefore its exact-compilation
statement may be false. Ordinary zero knowledge does not promise an accepting
proof for an arbitrary false statement under an honest CRS. Even for the
direct true-statement switch, ordinary proving cannot be substituted for
simulation: the iO challenger does not reveal its coins.

[HYPOTHESIS: stronger sufficient primitive] Canonical replay hybrids can be
made coherent if the simulated-CRS proof system additionally simulates
accepting proofs for all required **false** edge statements, and online
extraction remains secure after adaptively issued false-statement simulations.
The reduction records every such statement and its canonical semantics.
Unknown fresh edges must still extract exact wrapper witnesses; their parents
can be previously simulated canonical nodes. This gives the same rooted
semantic induction. Real-world endpoints contain only true statements; the
false certificates occur solely under simulated CRS in the proof. There is
no contradiction with real-CRS soundness. This is a stronger named assumption,
not a property inferred from the letters “NIZK.”

[DERIVED WI limitation] Witness indistinguishability alone does not replace
this mechanism. It compares proofs from different witnesses for the **same
true statement**, and a private specialization can have only one admissible
command witness. Adding an OR branch saying “this child is a certified
functionally equivalent replay program” requires an actual efficiently
checkable certificate and available witness. General circuit equivalence is
not an NP check supplied by the wrapper relation. A sound formal proof of
equivalence might provide a restricted NP certificate, but its production and
coverage must be constructed. Moreover, a branch demanding the canonical
compiler's coins still has the iO-challenge witness problem. No such alternate
relation or WI-only compiler is established here.

## 6. Credentials, cost and handoff

[DERIVED credential inventory]

| Artifact/role | Required authority and exposure boundary |
|---|---|
| Pinned genesis and CRS | Public and authenticated. Cannot be replaced by the host. |
| State initializer | Knows initial state and root compilation inputs; retires those records as already required by `HIO.md`. |
| Proof setup | Publishes CRS; retains no forging/extraction setup material. Actual setup realization remains an assumption. |
| Private issuer | Knows only its own command, public ancestry, and fresh compiler/proof coins. Protected private records are not exposed. |
| Host/public prover | May compile and certify any policy-admitted command on any valid parent; no state-reader credential is issued. |
| Simulation/extraction trapdoors | Reduction-only. No deployment process needs them. |

[DERIVED scope of certification] A certificate proves that the specified
compiler was run correctly. It does not make that compiler private. In
particular, this theorem is for the ordinary-iO wrapper defined above; it
does not transfer privacy to a different, boundary-exposing composition
algorithm merely by certifying that algorithm's honest execution.

[DERIVED cost] A depth-`d` parent requires checking `d` edge proofs plus exact
path joins, with access to all corresponding program bytes. The new prover
proves a bounded execution of the iO compiler and the singleton parent
evaluation in `R_edge`; its work cannot be priced as merely one short
signature. No succinct NIZK, recursive proof, aggregation or constant-size
ancestry is assumed. The recursive iO size recurrence in `HIO.md` remains;
certificates do not flatten it. All statements and proof computations must
fit the actual resource bounds at which the assumptions are invoked.

[DERIVED status/next] This closes the **conditional public provenance
interface** of bounded ordinary-iO issuance without retaining an issuer master
or trusting an online registry. It does not close efficient repeated size,
unbounded continuation, malicious setup, private-issuer memory exposure, or
practical/PQ instantiation. The next substantive step is to select a proof
system and match its exact simulation/extraction theorem to Section 2, or use
the witness-specific weaker route with its security formulation made explicit.
No implementation or new experiment is proposed by this note.

[SOURCE: local construction record] `HIO.md`, Sections 3–4, inspected in full,
supplies the fixed-horizon wrapper, finite-forest baseline, margin witness,
authentic-parent gap, and size recurrence being extended. The protocols and
conditional reductions in this file are our derivations, not claims attributed
to the HIO paper or to a particular NIZK source.

[DERIVED work record] Local notes and repository instructions were read with
`cat`, `sed`, and `rg`; no web query, Scry query, PDF download, cryptographic
execution or estimator run was performed for this subtask. Only this file was
written. Parent-owned `HIO.md`, source ledgers, STATUS/NEXT files, and companion
trees were left to their owners.
