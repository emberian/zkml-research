# An independent-key ladder for two private transitions

[DERIVED conditional positive; 2026-09-06] A fixed two-transition ladder can use
the computational-output **pre-public-key** game of Goyal–Jain–Koppula–Sahai
randomized FE. Generate its independent FE instances from the terminal layer
backwards. Each transition function then embeds a future public key that exists
before its own setup. Backward induction includes the entire exposed future
package as auxiliary information. It does not assume that an exposed future key
is absent from the adversary's view.

[DERIVED scope] This is a source-conditional tier-A **bounded**, selective-state
privacy candidate with public commands, honest initialization/erasure, full
forking and no finality gate. It retains encrypted raw state, rather than storing
a precomputed response tree. It is not an indefinite learner, a post-quantum
construction, a practical implementation or a claim about private fresh input.

[EXECUTED] `python3 finite_ladder.py` runs a symbolic setup schedule and a typed
ideal interface. `finite_ladder.stdout.txt` and `results/finite_ladder_results.json`
retain its output, source hash and accounting. No encryption is implemented.
Opaque handles in the test are registry entries, not a proposed cryptosystem.

## The primary theorem used

[SOURCE: syntax/game/algorithm/theorem statement read]
[Functional Encryption for Randomized Functionalities](https://eprint.iacr.org/2013/729),
Definition 2.4, printed pp.7–8, has this order:

```text
A1(z) -> (x0,x1,{f},st1)       # before this instance's public key
(MPK,MSK) <- Setup
{SK_f} <- KeyGen(MSK,{f})
A2 receives (MPK,{SK_f},st1)
CT* <- Enc(MPK,x_b)
A3 receives (CT*,st2)
```

[SOURCE] Its compatibility condition is computational indistinguishability of
the **joint** laws `(st1,{f(x0)})` and `(st1,{f(x1)})`. It is not merely an
individual-output condition. Definition 2.1 p.5 describes ideal randomized
function evaluations with independently sampled coins across the input/function
matrix. Remark 2.5 p.8 extends IND_pre to multiple challenge messages by ordinary
hybrids. Lemma 2.9 p.9 derives this IND_pre security from 1-SIM security.
Theorem 4.1 p.14 states 1-SIM security from iO for polynomial-time circuits and
one-way functions. The full cryptographic reduction was not re-proved here.

[SOURCE] In §4 pp.12–14, public encryption creates two PKE encryptions of the
message, a consistency NIWI, and a one-time signature. Setup's public values and
encryption algorithm do not contain the authorized f. A function key is an
obfuscation of a program containing its own PKE secret and a private PRF key;
the program checks validity, decrypts, derives coins from the ciphertext and
evaluates f. Encryption requires no persistent writer master. The q-SIM key
padding discussion is not a restriction to q function keys: q counts challenge
messages. We use the stated IND_pre primitive, with its multi-key game, rather
than silently treating a one-function-key theorem as a many-key theorem.

## Exact H=2 functionality and setup

[DERIVED definition] Let `Step(s,c)=(T_c(s),a_c(s))` be deterministic circuits
for commands c in a fixed finite C. After two commands, allow a fixed terminal
read `g(s)` and no third transition. Define finite relations:

```text
R2(u,v) iff g(u)=g(v).
R1(u,v) iff for every c: a_c(u)=a_c(v) and R2(T_c(u),T_c(v)).
R0(u,v) iff for every c: a_c(u)=a_c(v) and R1(T_c(u),T_c(v)).
```

[DERIVED candidate] Use three independent instances, numbered 0,1,2. The
initializer issues the terminal key for g under instance 2 and transition keys
under instances 0 and 1:

```text
F_i,c(s; r) = (Enc_{i+1}(pk_{i+1},T_c(s);r), a_c(s)),  i in {0,1}.

Define g;                  Setup_2; issue K_2,g; erase raw layer 2 secrets.
Define {F_1,c} using pk2;   Setup_1; issue {K_1,c}; erase raw layer 1 secrets.
Define {F_0,c} using pk1;   Setup_0; issue {K_0,c}; erase raw layer 0 secrets.
Encrypt the initial s under pk0; erase all initializer plaintext/coin copies.
Deploy every public key, every issued function key, and ct0.
```

[DERIVED] A host selects c0, obtains `(ct1,a0)`, selects c1, obtains `(ct2,a1)`,
then obtains g(s2). Each next ciphertext is a fresh encryption of the actual
next state under an independent instance; the state does not become the previous
ciphertext as a plaintext. The raw state remains represented at layer 2, but this
deployment has no key that advances it again. An `infer` command in C also
consumes a transition slot even when T_infer leaves raw state unchanged; only
the terminal read can be repeated without advancing a layer.

[DERIVED input boundary] Commands may be chosen adaptively and need not be
known at setup. These are **public command values**. A fixed bit-ingestion
protocol can represent public observations, at the cost of consuming its bounded
number of transition slots. The H=2 witness has only two command slots. There
is no method here for combining the existing private state with a fresh private
observation ciphertext. Merely possessing public encryption does not add that
two-input operation. Initial uncertainty must come from the initializer/input;
encryption coins alone do not create unknown development, and no fresh lifetime
entropy guarantee is claimed.

## Backward induction, including correlated future material

[DERIVED conditional statement] Assume the stated IND_pre theorem for this
randomized function family. Let the same-length initial challenge pair `(s0,s1)`
be chosen before **all** ladder setup randomness, with R0(s0,s1). Then the joint
distributions of the complete exposed package and `Enc_0(pk0,s_b)` are
computationally indistinguishable. This covers any PPT host computation with the
published objects, including adaptive command selection, copying and repeated
evaluation. It proves an IND-style interface-equivalence claim; a full
simulation theorem from only opaque state handles is not asserted.

[DERIVED package definition] Let P_i contain `(pk_i, all issued keys at i, P_{i+1})`,
with P_2 consisting of pk2 and K_2,g. Raw masters are excluded by the honest
erasure premise. Define L_i(u,v) as indistinguishability of
`(P_i,Enc_i(pk_i,u))` and `(P_i,Enc_i(pk_i,v))` for a selectively chosen pair in
R_i. All the keys inside P_i are exposed to the distinguisher.

[DERIVED joint-ciphertext lemma] If L_i holds for each pair `(u_j,v_j)` in a
fixed finite list, it also holds for
`(P_i,{Enc_i(pk_i,u_j)}_j)` versus `(P_i,{Enc_i(pk_i,v_j)}_j)` with independent
encryption coins. Use one common P_i in every hybrid. A reduction given P_i and
one challenge ciphertext publicly encrypts every other known candidate message
under that same pk_i, using fresh coins. Thus it preserves all correlations
between the public key and **every exposed function key**, while preserving the
required conditional independence of honest encryption coins. This argument
does not replace joint security with marginal indistinguishability.

[DERIVED base] For L_2, g is fixed before Setup_2 and g(u)=g(v) by R2. The
IND_pre compatibility outputs agree exactly. The source game supplies both pk2
and its terminal function key to the adversary, so the terminal key is included
in the confidentiality claim.

[DERIVED step from L_2 to L_1] The layer 1 IND_pre adversary's A1 honestly
generates the entire P_2 first, erases raw setup secrets, defines every F_1,c
using pk2, and sets `st1=P_2` plus public descriptions/auxiliary input. It has not
seen pk1. Its joint compatibility outputs are

```text
(P_2, {(Enc_2(pk2,T_c(u);r_c), a_c(u))}_{c in C}).
```

[DERIVED] For R1(u,v), all answer entries agree and every next-state pair is in
R2. The joint-ciphertext lemma from L_2 therefore establishes precisely this
compatibility condition, with all future keys in the auxiliary state. The
layer 1 IND_pre theorem then supplies indistinguishability with pk1 and **its
own** command keys exposed. Those current-layer keys are supplied by the source
game after setup; we do not improperly insert them into a pre-setup auxiliary
state that could not yet contain them. This yields L_1.

[DERIVED step from L_1 to L_0] Repeat the same argument with `st1=P_1` and
functions F_0,c defined before Setup_0. R0 ensures equal current answers and
R1 next-state pairs. The joint-ciphertext lemma from L_1 supplies compatibility,
and the layer 0 theorem yields L_0, the claimed package privacy.

[DERIVED selectivity and dependencies] This proof selects challenge states
before the deepest setup. It does not promote them to adaptively selected secret
states after public parameters. The future packages are independently generated
and may be correlated internally; their entire exposed distribution appears in
st1. Each F_i,c embeds only the **public** next key, not that instance's master
or issued function keys. These are the two load-bearing premises. A same-key
recurrence has no such reverse setup order. Closing a terminal-to-root edge
likewise creates a timing cycle and is not covered by this proof.

[DERIVED selective hybrid check] Step and the initial candidate states are fixed
independently of setup randomness. Hence every child pair `(T_c(u),T_c(v))` used
in the ciphertext hybrids can be computed **before** generating its future
package. Generating that package first in the descriptive recursion does not
make these pairs adaptive to its public key. If Step or the private challenge
states instead depended on those freshly sampled public parameters, this
reordering argument would need a different theorem.

## Object count versus proof complexity

[SOURCE / DERIVED] The inspected §4 encryption syntax has a fixed plaintext
width, two PKE ciphertexts, a consistency proof and a signature; it does not
repeat encryption once per function-output bit. Holding the primitive/state
parameters fixed, all ladder layers use that same ciphertext shape. Each F_i,c
contains one next-public-key literal and the public encryption/Step circuits,
not the full future package or its function-key code. This avoids a recursively
growing circuit description. It is a source-level compactness observation, not
an implementation cost estimate.

[DERIVED count] For horizon H and B commands, the schedule has H+1 FE public
key objects and HB+1 function-key objects including one terminal key. At H=2,
B=3 this is three public keys and seven function keys; each FE public key itself
contains two PKE public keys and the other published setup objects. Obfuscated
program sizes, NIWI costs and security parameter choices still matter. Counting
objects is not counting bytes, time or practical overhead.

[DERIVED proof accounting] The explicit backward proof branches over command
outputs. Its dependency tree has `1+B+...+B^H` local theorem/hybrid obligations:
13 nodes and nine terminal paths for H=2,B=3. This is not an extracted numerical
advantage bound of 13 times some base error. The source reductions have their
own losses. The proof here uses fixed H=2, so finitely many negligible terms
remain negligible. A horizon growing with the security parameter needs a
separate uniform reduction and quantitative accounting. Linear object count
does not establish security for a polynomial-length horizon.

## Executed witnesses and failure controls

[EXECUTED] The byte witness uses commands `+1 mod256`, `double mod256` and
`infer highest bit`, with terminal highest-bit read. All 256 initial states and
all nine two-command paths pass, for 2,304 complete path checks. There are 14
finite behavioral classes; the class containing 0 is exactly 0 through 31. States 0
and 1 remain an admissible nonidentical challenge pair. These are finite ideal
interface facts, not counts of cryptographic security bits.

[EXECUTED] Update order has meaningful effects: initial 63 follows
`63 -> 64 -> 128` for add-then-double and `63 -> 126 -> 127` for
double-then-add, giving terminal bits 1 and 0. The protected raw state can therefore
matter to later authorized behavior within the horizon. Differences inside one
R0 class are intentionally unobservable for the entire allowed horizon; issuing
more capabilities would require recomputing that relation.

[EXECUTED] The symbolic scheduler verifies every F_i,c is defined before its
own Setup_i and after the next public key exists, exposes every issued future
key, and refuses all three post-erasure identity-key requests. Its dependency
graph is acyclic; adding a terminal-to-root encryption edge makes it cyclic.
Repeated symbolic ciphertext/key calls return the same handle. Wrong-layer
handles are rejected by the test's type rules only; this is not executed
cryptographic evidence of malformed-ciphertext rejection.

[DERIVED] In the actual conditional privacy argument, an adversary already has
the key programs and can try arbitrary byte strings, including cross-layer
ciphertexts. The IND theorem, not the symbolic type check, carries privacy
against those computations on the honest initial challenge. Public replacement
with a known state is allowed, and restoring ct0 permits both update orders.
No statement binds outputs to genesis, parent, recipient, a receipt or finality.

[SOURCE / DERIVED erasure negative] The source's raw PKE SK1 reads all states
at its layer. The independently generated SK2 does as well, despite not being
the returned FE master. Erase both, raw PRF keys, un-obfuscated G programs and
all setup/key-generation copies. Issued obfuscated programs remain exposed and
contain read-all material internally; only the assumed FE theorem justifies
their restricted exposed capability. Retaining any raw layer master invalidates
the package used by the induction.

[DERIVED randomness/ingress limit] The old randomized-FE proof is not silently
upgraded to 2025/330's revised malicious-encryptor randomness guarantee. The
privacy claim here starts with an honestly encrypted private root and erased
initial encryption coins. Hosts may act maliciously with the exposed package,
as in its IND game. No additional theorem is claimed for maliciously generated
fresh **private** observations, ideal unbiased random development, or secrecy
from a creator that retained that observation's plaintext/coins. Deterministic
Step means encryption coins serve representation privacy, not a stochastic
learning contract. Identical ciphertext/key calls are repeat-deterministic;
fork-selected lifetime outcomes are permitted by this interface.

[OPEN next] Audit a uniform growing-horizon reduction before increasing H beyond
the fixed construction, or study a different composable dynamic primitive for
indefinite continuation. Adding private ingress requires an actual two-input
transition and its joint issuance/exposure game. The separate same-key theorem
obstruction and static predicate positive remain unchanged.

[EXECUTED accounting] No new Scry, schema or web queries; the prior primary
source was reread locally. Cumulative lane totals remain eight Scry SQL plus one
schema, Kagi 0 and web 28. No PDF download or package installation.
