# Public environments remove the literal key-in-plaintext recursion

[DERIVED; conditional mathematical construction] A public-environment variant
of the reviewed B/P/G/X bridge removes the need to encrypt the future public
keys inside each node. Its setup runs from leaves toward the root. An outer
encoding is specialized to the already generated inner encoding key; a parent
level is specialized to the already generated child encoding key. The simulator
regenerates outer setups when an inner simulated public key changes.

[DERIVED positive closure] The resulting polynomial parameter choice needs
effective encoding keys and encryption work bounded by
`poly(kappa,N,log S)`, where N is the encrypted message bound and S the supported
function circuit-size bound. It does **not** need the original stronger
`|pk|<=p0(kappa)` independent of N. In particular `|pk|>=4N` is compatible with
this construction: no requirement `N>=|pk|` remains.

[DERIVED second sufficient seam] A fixed, efficiently constructible encryption
circuit with gates **plus output bindings** bounded by `poly(kappa,N,log S)`
gives an effective encoding key of that
size by retaining only the public-key bits actually used by the circuit.
This is an exact classical compilation, not a new cryptographic assumption.
Its computation-model premise is explicit below. A generic unit-cost RAM
lookup into an arbitrarily large key does not by itself provide this circuit.

[OPEN] This is not a complete LWE instantiation. Raw GKP encryption/public-key
cost depends on prescribed depth d; obtaining the necessary compact circuit
for the specialized **outer** function remains a depth/compactness obligation.
The source audit and its independently reviewed findings stay frozen.

## 1. Inputs, source scope and changed interface

[SOURCE] The starting algorithms and hybrid losses are the frozen
`qio_instantiation/bootstrap_lift/BOOTSTRAP_LIFT.md`, especially its Sections2–4,
and the primary sources 2015/720 Theorems11–13/Section6 pp30–36 and 2016/006
Theorems6–7 pp9–11. `BASE_FE_AUDIT.md` records the literal GKP/GVW formulas.
The independent review `adversarial_review/base_fe/REPORT.md` derives the
uncompressed tuple bound `|pk_GKP|>=4N` and proposes this public-environment
direction. This note is our construction and proof, not an attribution of it
to the papers. Source and frozen-input hashes are recorded separately.

[HYPOTHESIS B with public bounds] Retain the reviewed static one-key Boolean FE
game: classical f,m0,m1 fixed before fresh Setup, equal outputs, one arbitrary
quantum advice state independent of fresh coins. Use explicit public bounds
`B.Setup(kappa,N,S)`; Setup does not inspect f. KeyGen accepts every admitted
classical f of input width N and size at most S. Setup, full key length,
key generation and decryption are polynomial in `(kappa,N,S)`. The encoding
key and encryption work are at most a fixed polynomial in `(kappa,N,log S)`.
The last key bound can alternatively be supplied by Section3's compiler.
All circuits/tapes are bounded and padded. Correctness is either the reviewed
perfect contract or its separately tracked uniform fresh-error supplement.

[HYPOTHESIS unchanged primitives] P, G and X have the reviewed quantum-advice
games and resource bounds. In particular G can produce a requested polynomial
number of bits in output length times `poly(kappa,log output length)`, and
X obfuscates logarithmic-input circuits with the stated sublinear size bound.
No public-environment oracle is granted to X: its input remains an ordinary
classical circuit containing its effective current encoding key explicitly.

[DERIVED environment game] Fix a public classical environment E, padded bounds,
and a fixed public interpreter `V_E`. An encrypted payload m is short; the
interpreted output is `V_E(m)`. Define

```text
Setup_R(E,bounds) -> (ek,crs,aux)
Enc_R(ek,m;r)     -> ct
Eval_R(crs,ct)    -> V_E(m)
Sim_R(E,V_E(m),metadata) -> (ek',crs',aux',ct').
```

[DERIVED] The required comparison is between the real and simulated joint
views `(E,Z,ek,crs,aux,ct,rho)`, where Z may be the entire later public setup
package. The simulator preserves E and Z and receives no hidden payload or
seed. E,Z,m and an allowed advice state are fixed before fresh current setup.
Uniform bounds over these fixed tuples also cover independently sampled
later packages by averaging. We make no claim to hide E itself. Actual node
environments contain future encoding keys, not the challenge circuit C.

## 2. Acyclic setup and an explicit simulator

[DERIVED weak component] For any fixed E, the weak RE `R_W^E` uses the reviewed
pad/Boolean-index construction. Before the current inner B setup, choose its
pad c and fix the Boolean function that returns

```text
[V_E(m)]_j              on the real branch,
c_j XOR [G(s,l)]_j     on the simulated branch.
```

[DERIVED] Its public key is the effective inner B key `ek_W`; its CRS is the
one indexed function key. The encryption circuit passed to X computes
`B.Enc(ek_W,(m,j);P_K(j))`. E is in the function key, not in m or this encryption
circuit. The simulator `Sim_W(E,y,metadata)` chooses the programmed pad from
y, generates fresh inner setup/key, and encrypts the simulated branch.
The reviewed bound remains `eps_RW<=2 eps_G+(2s+2)eps_X+2s eps_P+s eps_B`.

[DERIVED outer specialization] After generating `ek_W`, define the public
outer environment J to contain `ek_W`, the fixed algorithm `R_W.Enc`, and
padded bounds. Its interpreter is

```text
H_J(m,zeta) = R_W.Enc(ek_W,m;G(zeta,r_W)).
```

[DERIVED] It does not contain the private inner setup coins or inner function
key. Generate a fresh outer B setup and issue one key for the reviewed
bit-indexed, pad-switching function for `H_J`. This is the succinct outer
`R_S^J`; it has `l_H` ordinary ciphertexts under one B key and one function key.
The outer messages contain `(m,zeta,index,mode,pad_seed)`, not `ek_W`.
J is fixed before this outer setup, meeting static B timing.

[DERIVED composed algorithms] Publish outer encoding key `ek=ek_S`, CRS
`(crs_S,crs_W)`, and optionally the inner key as public aux. To encode m, sample
zeta and run `R_S.Enc(ek_S,(m,zeta))`. Neither `H_J` nor `R_W.Enc` is executed
by this encoder: the outer function key performs that computation during
evaluation. Decode with `crs_S` to recover the inner ciphertext, then decode
that with `crs_W`. Thus a parent encoder needs only its child's `ek_S`.

[DERIVED simulator] On `(E,y,metadata)`, first run
`(ek_W,crs_W,ct_W)<-Sim_W(E,y,metadata)`. Form J from that very `ek_W` and run
`(ek_S,crs_S,ct_S)<-Sim_S(J,ct_W,metadata)`. Return the same assembled package
as the real setup/encoding. Both simulators know their public environment;
neither requires m, zeta or a hidden descendant seed.

[DERIVED composition proof] First replace the real outer package by
`Sim_S(J,H_J(m,zeta))`, keeping the real inner package. Then replace the inner
PRG tape by uniform coins. Finally replace the whole inner tuple by
`Sim_W(E,y)`. In that last step, apply the classical randomized channel

```text
(ek_W,crs_W,ct_W) ->
    J := environment using ek_W;
    (ek_S,crs_S,ct_S) <- Sim_S(J,ct_W);
    return assembled tuple.
```

[DERIVED] This channel intentionally regenerates the outer setup/function key
using the changed inner public key. Keeping an old outer CRS after changing
the inner key would be incorrect. The channel uses only the supplied tuple
and public metadata, so one invocation of the final quantum distinguisher
suffices. The reviewed loss is unchanged:

```text
eps_R <= (l_H+s)eps_B + (2s+2)eps_X + 2s eps_P + 5eps_G.
```

[DERIVED tree setup] At depth n use a leaf interpreter returning padded C(v)
from payload `(C,v,seed,bounds)`, with no future-key environment. Generate its
inner setup, then its outer setup. For i=n-1 down to0, set E_i to the already
sampled next-level **outer encoding key** and the fixed node template/bounds;
then generate the current inner setup and current outer setup in that order.
Every current B function is fixed independently before its own fresh Setup.
The dependency DAG is `W_n -> S_n -> W_(n-1) -> S_(n-1) -> ... -> W_0 -> S_0`.

[DERIVED nodes] A nonleaf interpreter expands the payload seed into two child
seeds and two complete encoding tapes; it publicly encrypts the two short
child payloads under the fixed `ek_S,(i+1)` in E_i. Payloads contain C, prefix,
seed and logarithmic bounds; they contain no environment, function key or
encoding key. Tagged templates construct child payloads without inlining
descendant source code. Publish the root ciphertext and all level CRS values;
publishing all encoding keys and auxiliary inner keys is also allowed.

[DERIVED privacy induction] Retain the current and all later packages jointly.
After simulating a parent, its child switch is postprocessed by parent
`Sim_R(E_i,new_child_pair)`, with E_i rebuilt from the supplied child encoding
key. Generate the sibling under that **same supplied key**. This handles the
dependence of the parent CRS on the child key; no fixed old parent CRS is
carried through the switch. The reviewed recurrence therefore stays
`a_n<=2eps_R`, `a_i<=2eps_R+2eps_G+2a_(i+1)` with uniform environment/resource
envelopes. The exponential number of hybrids is a loss factor; each reduction
has only polynomial setup/channel work and one continuing advice state.

## 3. Exact public-key dependency compression

[DERIVED lemma] Let a fixed encryption circuit `E_B(pk,m,r)` have at most g
bounded-fanin gates and o output bits, with `g+o+|r|=poly(kappa,N,log S)`.
Compact bit-operation work bounds both written output and consumed randomness;
a gate-count-only premise does not. The template depends only on
public `(kappa,N,S)`. Let J be the distinct public-key input positions feeding
a gate or an output wire. Then `|J|<=2g+o` for fan-in2. Retain `pk[J]`, rename
those input positions and delete unused key inputs. The resulting circuit
`E'_B(pk[J],m,r)` has exactly the same output for **every** pk,m,r; this follows
gate by gate and includes outputs connected directly to input bits.

[DERIVED] KeyGen and decryption remain unchanged. Setup computes the
projection after ordinary B setup. The transformed key can include the
remapped circuit template if needed; its serialization is
`O((g+o)*(1+log(g+N+|r|+o)))` plus at most `2g+o` retained bits. Original key
indices can be discarded after remapping. Uniform template construction and
setup projection may take `poly(kappa,N,S)` work, while encoding evaluates only
the small remapped circuit. A B reduction receiving the full original pk
computes this projection and exposes the reduced view, preserving the exact
probability gap and correctness, apart from its charged classical overhead.

[DERIVED computation-model scope] This lemma applies directly when encryption
has an efficiently constructible circuit of the stated size. A clocked
sequential multi-tape Turing-machine encoder with a separate public-key input
tape and `t=poly(kappa,N,log S)` steps also supplies one: its key head visits
only a bounded prefix, and a standard explicit transition unrolling gives a
polynomial-in-t circuit. Count lengths/end markers and pad inputs consistently;
bounded random tape length and any clock failure belong in the correctness
contract. We do not infer this circuit bound merely from unit-cost random
access into a huge key. We also do not claim arbitrary key compression or
removal of key-generation authority: only unused public encoding input bits
are removed, with exact ciphertext equality.

[DERIVED constructive TM bound] During t steps a key-tape head starting at
cell0 cannot reach a cell beyond t. Keep that prefix and any reachable original
end marker. Encode the finitely many tape cells, machine state and head
positions explicitly for each time step; each next configuration is a Boolean
function of the current one. Unrolling these t transitions uses polynomially
many gates (a direct one-hot construction suffices) and O(t) random bits for a
fixed machine with bounded random-bit instructions per step. This explains the
model-dependent circuit bound without granting constant-cost arbitrary lookup.

## 4. Closing widths, time and issuance bounds

[DERIVED parameter lemma] Let `U=kappa+|C|+n+1`. Use one common time bound T,
one common message bound N and one common function-size bound S. The fixed
node/outer tagged payloads and their index fields satisfy
`N<=a*(U+log(T+2))`; the important missing term is the public-key length.
Assume effective key length and encoder circuit/work are fixed polynomials
in `(kappa,N,log S)`, either directly or by Section3.

[DERIVED] The actual specialized functions include the environment as
constants and are compiled within `S<=poly(U,T,K)`: the node interpreter runs
two encoders; the outer interpreter runs the polynomial-time weak encoder and
PRG. This bound explicitly includes X's obfuscation algorithm inside that
outer computation. Choose `S=(c*(U+T))^r` for a sufficiently large fixed r.
Then `log S=O(log U+log T)` and
`K,g<=poly(U,log(T+2))`. Substituting this bound back into the specialized
function sizes closes S after enlarging the fixed c,r once; no actual sampled
key contents enter the choice. Environments/function keys may be long, but
their size is charged to Setup/KeyGen and never to N.

[DERIVED] The weak encoder's xiO circuit contains K effective key bits, so its
size is `poly(U,log T)`. With output bound l<=T, its ciphertext length is at
most `T^(1-alpha)*poly(U,log T)`. The outer succinct encoder repeats small B
encryption `l_H` times; hence the composed encoder and its complete random tape
have the same bound after changing that polynomial. Two child encodings,
near-linear-output PRG expansion and tagged payload work fit

```text
node_work(T) <= A*U^a*(1+log(T+2))^b*T^(1-alpha) + B*U^d.
```

[DERIVED explicit closure] Absorb the logarithmic factor into
`C*T^(alpha/2)`. Put beta=alpha/2 and increase constants. Choose an integer T
satisfying `T>=2B*U^d` and `T^beta>=2AC*U^a`, also covering leaf work and output
padding. For example `T=(c0*U)^D` works for fixed sufficiently large c0 and
`D>=max(d,a/beta)`, increasing D once for leaf work. All N,K,S and CRS sizes are
then polynomial in U. There are n+1 levels and two B instances per level.
The choice is a single polynomial bound, not an exponentiation repeated n
times. `K>=4N` causes no contradiction because the key is public environment
data and does not occupy the encrypted payload.

[DERIVED correctness] The dependency order permits the reviewed fresh-error
arguments to condition on the future package before current setup. Outer
functions contain only the already sampled inner public key, independent of
their own fresh setup. Exact key projection adds no error. Apply the reviewed
pointwise-correctness supplement with the same `s,l_H` and explicit PRF/PRG
failure-test gaps; its all-node union bound still applies. An environment is
not evidence of honest sampling, and no source negligible term is silently
upgraded to a stretched-exponential bound.

## 5. What this closes and what it does not

[DERIVED] This construction supplies the public-environment game, simulator,
setup DAG, unchanged privacy recurrence and one actual conditional polynomial
parameter closure. The short-key premise can be weakened to an effective
encoding key polynomial in message length and logarithmic function bound;
bounded-size encryption circuits suffice to derive such a key. No extra FE
key, secret oracle, quantum state copy or public-environment xiO primitive is
introduced. This is a variant of the frozen bridge, not a silent revision of
its theorem.

[OPEN raw GKP seam] Its literal pk and encryption cost are polynomial in
message width and prescribed depth d, rather than established here as
polynomial in logarithmic arbitrary function size. The outer specialized
function computes `R_W.Enc`, including X's obfuscation algorithm. Its depth is
not bounded by `poly(U,log T)` merely because node payloads became short.
Using only the generic time bound can make d polynomial in T; inserting that
into B encryption and the current-key-containing xiO circuit can erase the
sublinear saving. Function-key issuance moves work into Setup but does not
justify deleting this dependency. A compact P/poly base implementation, or an
explicit shallow realization and resulting parameter inequalities, remains
necessary. The cited Boolean-to-multi-output/depth route and all concrete QA
primitive/statistical rates still require their separate source obligations.

[OPEN review status] This is a mathematical proof draft for independent review.
Any executable ledger below checks finite algebra/size examples only, not FE
privacy, an LWE reduction or a full compiler implementation. No frozen parent,
shared ledger, companion, service, protected output or commit is changed.

[EXECUTED finite witnesses] `circuit_dependency.py` checks 32,768 exact
evaluations of a 12-bit public keyed circuit before and after projection to
four used key bits; 28,672 have nonzero output. A direct key-to-output wire
falsifies gate-only dependency extraction. Zero-gate passthrough examples
explain why output bindings must count. Eight exact after-log-absorption
inequalities exhibit one common polynomial T while the effective key exceeds
the message bound. These are ordinary Boolean/integer models, not encryption.

[EXECUTED provenance] Run
`python3 research/learn_infer_only/experiments/pq_composition/base_fe_audit/public_environment/validate.py`.
It verifies the 14 read-only inputs pinned in `inputs.json` and retains commands
and outputs in `validation.json`; `artifact_hashes.json` pins delivered files.
No new web, Scry or Kagi query, PDF extraction or download was needed. These
checks do not certify the mathematical privacy or asymptotic parameter proof.
