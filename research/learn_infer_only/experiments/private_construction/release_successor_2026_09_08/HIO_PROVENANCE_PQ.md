# A lattice certificate backend with adaptive extraction feedback

[DERIVED, 2026-09-09] The public continuation certificate can use **two
ordinary Regev ciphertexts and one post-quantum simulation-sound NP proof**.
The two ciphertexts encrypt the same tagged compiler witness. During the
privacy proof, the reduction decrypts one half while switching the other.
This instantiates the online feedback interface of `HIO_PROVENANCE.md`
without a CCA encryption scheme or an additional nested proof inside each
ciphertext. Bounded key noise gives correctness for every encryption coin
string admitted by the certificate relation. This is an algorithm-level,
source-backed conditional construction, not an implementation or practical
parameter recommendation.

[DERIVED scope] This advances the **certificate backend**. It does not
instantiate a post-quantum iO compiler, repair the ACE retained-block leak,
make ordinary nested obfuscations polynomial in the number of hops, or extend
the resident's bounded behavioral privacy relation. The prior HIO notes and
`HIO_PROVENANCE_BACKEND.md` remain unchanged. The new route preserves their
exact edge statement and private-issuer boundary.

## 1. Selected source algorithms and games

[SOURCE] Jawale–Khurana, *Unclonable Non-Interactive Zero-Knowledge*, local
eprint **2023/1532**, Definitions 3.5/3.7, printed pp16–18, specifies
post-quantum adaptive multi-theorem NIZK and **statement-new** simulation
soundness. Theorem 3.6 uses Peikert–Shiehian's LWE NIZK; Theorem 3.8 uses the
Sahai/DDOSS compiler; Corollary 3.9 explicitly gives the resulting
post-quantum simulation-sound NIZK from polynomial quantum hardness of LWE.
Theorem 4.2 and Figure 1, pp22–24, already construct encrypted-witness
post-quantum simulation extractability from perfectly correct CPA encryption.
That theorem extracts at the end of the experiment. It does not state the
online feedback property needed here. The two-key construction below supplies
that property explicitly. [Primary paper](https://eprint.iacr.org/2023/1532).

[SOURCE] The selected base NIZK is the **statistically sound, adaptively
computational zero-knowledge CRS mode** of Peikert–Shiehian, local
**2019/158**, Definition 2.2 p7–8 and Theorems 5.3/5.4 p19. Its compiler uses
the modified graph-Hamiltonicity protocol and correlation-intractable hashing;
this is not ordinary Fiat–Shamir with SHAKE. Constructions 2.9/3.1, pp12–13,
give the homomorphic matrix commitment and actual hash algorithms. Remark
5.5 p19 explains the logarithmic-depth bad-challenge circuit, including the
explicit permutation check, which avoids requiring FHE bootstrapping for this
NIZK. The source explicitly limits its native ZK property to one theorem
(p7). The simulation-sound compiler supplies the required many-proof mode.
[Primary paper](https://eprint.iacr.org/2019/158).

[SOURCE] Abdolmaleki–Chevalier–Ebrahimi–Malavolta–Vu, *On Quantum
Simulation-Soundness*, local **2023/1702**, Section 6 Construction 3 and
Theorem 2, pp17–18, Appendix E pp37–41, gives the actual Sahai compiler and
its quantum security hybrids. It uses a PRG, a PRF, a one-time signature and
a single-theorem NIZK for the following OR language:

```
L'(z,u,vk,crs1,crs2) iff
    z is in the target NP language
 OR crs1 opens to a PRF seed s and u=PRF(s,vk)
 OR crs2=PRG(d) for some d.
```

[SOURCE / DERIVED algorithm reading] Real `crs1` is a random string of
`6 lambda^2` bits, `crs2` is random of `3 lambda` bits, and `crs3` comes from
the base NIZK setup. An honest proof uses the first branch and a fresh
one-time signing key. Simulated setup commits to a secret seed `s`; to prove
**any** `z`, including false `z`, the simulator computes `u=PRF(s,vk)` and
uses its commitment openings as an ordinary valid witness for the second
branch. It signs the statement, `u`, and the base proof. The paper's simulator
figure labels the witness-taking base call `S2'`; the executable operation
here is `Pi'.Prove` with those displayed openings, consistent with the
Appendix E proof's witness-switch argument. No false statement is proved
inside the base sound proof system. Bind the externally supplied statement
to the statement carried/signed by the proof exactly.

[SOURCE / scope] Theorem 2 of 2023/1702 targets the stronger setting of
superposition access to the simulator and assumes the corresponding stronger
base-NIZK ZK property. We do **not** claim Peikert–Shiehian automatically
satisfies that stronger premise. The resident interface has classical
statements and classical responses; the post-quantum classical-query result
in 2023/1532 Corollary 3.9 is the selected theorem. The inspected
2023/1702 algorithms and hybrids explain how arbitrary-statement simulation
and statement binding actually work.
[Journal primary paper](https://cic.iacr.org/p/1/4/18/pdf).

[SOURCE] These components have established polynomial algorithms: the
Sahai compiler does not add an obfuscation assumption. Zhandry, local
**2012/182**, pp2–3 and Section 4.1 Construction 1/Theorem 4.5 pp7–8,
records the quantum lift of the OWF-to-PRG construction and the GGM tree
construction of PRFs. This supports the source compiler's ordinary primitive
chain; no concrete hash, signature library or security parameter set is
silently substituted. [Primary paper](https://eprint.iacr.org/2012/182).

## 2. Regev encryption with no adversarial bad-coin exception

[SOURCE] Regev's author-hosted 2009 full paper, Section 5 pp31–35, specifies
the subset-sum encryption algorithm, its correctness calculation (Lemma 5.1)
and the leftover-hash calculation (Claim 5.3). Its displayed parameter choice
gives a small average decryption error. We use the same encryption and
decryption algorithms but strengthen the **setup noise support and parameter
margin**, as derived next. This is a modification, not a claim that the
source's displayed parameters already give perfect correctness.
[Author's primary paper](https://www.cims.nyu.edu/~regev/papers/qcrypto.pdf).

[DERIVED parameters] For one public key, let `q` be an odd prime,
`A in Z_q^(m x n)`, `s in Z_q^n`, and `e in [-B,B]^m`, with

```
b = A s + e mod q
pk=(A,b); sk=s; Delta=floor(q/2)
2 m B < Delta.
```

Keys use bounded-time finite-coin approximations to uniform `A,s` and to the
rounded Gaussian error distribution, specified below. Their statistical
distance from the standard LWE key distribution is charged explicitly;
all key-generation coin strings produce errors within the bound. For a `D`-bit message
`M`, encrypt each bit independently using a column of `R in {0,1}^{m x D}`:

```
U = A^T R mod q
v = b^T R + Delta M mod q
Enc(pk,M;R)=(U,v).
```

Decrypt coordinate `j` by whether `v_j-s^T U_j` is nearer to `0` or `Delta`
on the circle `Z_q`; fix a tie rule for arbitrary ciphertexts. Reject malformed
encodings. Ciphertexts made by `Enc` never reach a tie.

[DERIVED all-coins lemma] For **every** honestly generated key and
**every binary** `R`, the residual of each bit is

```
v_j - s^T U_j = Delta M_j + e^T R_j mod q
|e^T R_j| <= m B < Delta/2.
```

Hence decryption returns `M`, simultaneously for all messages and all
encryption coin strings, including chosen coins. No honest-random-coins
probability appears in this conclusion. The certificate checks the binary
type/length of both `R` witnesses; arbitrary modular matrices are not admitted
as encryption coins. Key generation remains honest and pinned, as in the
prior backend. This is not a correctness promise for host-selected keys.

[DERIVED nonempty asymptotic family] One conservative choice, solely to
exhibit compatible polynomial bounds, is sufficiently large `n`, prime
`n^4 < q < 2 n^4`, Gaussian width `alpha*q=n`,
`B=ceil(n log_2 n)`, and
`m=ceil((n+1)log_2(q))+2n`. Then `2mB<floor(q/2)` eventually;
the omitted Gaussian tail is superpolynomially small, while `alpha*q>2sqrt(n)`
and `n/alpha` are polynomial in `n`. This example supplies no finite
security bits or practical lattice dimension. The NIZK's LWE parameter
families are separate and must satisfy their own source conditions.

[DERIVED bounded-time sampler] Fix the table at parameter generation; do not
use rejection sampling. Let `Y` be the unwrapped Gaussian whose reduction and
rounding gives the source distribution `bar(Psi_alpha)`; in the source's
normalization its density before reduction modulo `q` is
`exp(-pi*y^2/(alpha*q)^2)/(alpha*q)`. Let `Z=round(Y)`. For each integer
`j in [-B,B]`, compute a rational approximation to

```
p_j = Pr[Z=j | |Z|<=B]
    = integral_(j-1/2)^(j+1/2) exp(-pi*y^2/(alpha*q)^2) dy
      / integral_(-B-1/2)^(B+1/2) exp(-pi*y^2/(alpha*q)^2) dy.
```

There are `K=2B+1` entries. Gaussian integrals on this polynomially bounded
interval can be approximated to a specified polynomial number of bits in
polynomial time; use sufficient precision that a nonnegative normalized
rational vector `p_hat` has total variation at most `eta/2` from `p`.
Choose fixed `k` with `K/2^k <= eta/2`. Assign each integer bin initially
`floor(2^k*p_hat_j)` values, then distribute the remaining values, one per
bin in a fixed order. A `k`-bit uniform integer indexes this partition.
The resulting distribution is within `eta` of the truncated distribution.
Every possible index lies in exactly one bin in `[-B,B]`; there is no retry,
overflow branch, exceptional coin string or unbounded loop. A binary search
in the fixed cumulative table takes `O(log K)` comparisons of `k`-bit
integers. For example, `eta=2^(-2n)/m` uses polynomial `k` and table size.

[DERIVED finite field sampling] For each of the `N_F=mn+n` coefficients of
`A,s`, use a fixed `k_F`-bit integer `u` and return
`floor(q*u/2^k_F)`. This is in `Z_q` for every coin string and is within
`q/2^k_F` of uniform in total variation. Choose
`k_F >= ceil(log_2 q)+ceil(log_2 N_F)+2n`, giving aggregate distance
`delta_field <= 2^(-2n)`. Thus all key-generation randomness has one fixed
polynomial bit length. Public prime `q` can be chosen deterministically by
bounded enumeration and primality testing in the displayed polynomial-size
interval; it does not require random rejection sampling either.

[DERIVED CPA ledger] Let `delta_key` be the full public-key distribution
distance caused by these finite samplers. Set
`delta_tail=Pr[|round(Y)|>B]` for the **unwrapped source Gaussian above**.
Reduction modulo `q` cannot increase statistical distance, so
`delta_key <= delta_field + m(delta_tail+eta)`. This attributes the error to
the actual source distribution, not an unspecified bounded-noise LWE variant.
Under decisional LWE,
replace `(A,b)` by a uniform matrix/vector. For the resulting subset-sum
hash, use the conservative distance

```
delta_LH = sqrt(q^(n+1) / 2^m).
epsilon_CPA(D) <= 2 epsilon_LWE + 2 delta_key + 2 D delta_LH.
```

This loose probability-gap bound follows by comparing both challenge bits
with independent uniform ciphertext coordinates. The statistical step is a
joint bound including the public key, so an attacker may choose its message
after seeing that key and keep quantum work state. It does not multiply by
the number of locally computed public encryptions. Each CPA reduction below
has one `D`-bit challenge and its full surrounding runtime charged.

[DERIVED chosen coins versus privacy] Perfect all-coins correctness does not
assert privacy for maliciously chosen encryption randomness. Protected
issuers sample fresh uniform binary matrices. A host certifying a command
with deliberately revealing coins exposes its own witness; the model never
promised to hide information it already supplied.

## 3. Direct two-ciphertext certificate

[DERIVED fixed context] Keep `x=(G0,d,parent,child,y)`, the exact bounded
`R_edge(x;w)` with `w=(cmd,r_iO)`, and canonical equal-length `M1(x,w)` /
`M0(x)` from `HIO_PROVENANCE_BACKEND.md`. `M1` has flag 1 and the full tagged
witness; `M0` has flag 0 and padding. The variable statement excludes its own
certificate and proof CRS. Genesis pins the final public keys, proof CRS,
suite and bounds. Build those parameters in that order; there is no
statement/CRS length self-reference.

[DERIVED relation] With two independently generated Regev public keys,
instantiate the selected SS-NIZK for

```
z=(pk0,pk1,x,C0,C1)
R_2(z;w,R0,R1) iff
    R_edge(x;w)
    C0=Enc(pk0,M1(x,w);R0)
    C1=Enc(pk1,M1(x,w);R1)
    all canonical encodings, binary coins and bounds hold.
```

No equality-of-obfuscated-functions predicate is introduced. The original
relation still checks an exact bounded compiler execution and first release.

[DERIVED algorithms]

```
RealSetup:
    independently generate (pk0,sk0),(pk1,sk1)
    crs=SS.Setup(R_2, bounds)
    publish and pin (pk0,pk1,crs)
    retire both secret keys and any proof setup secrets

ProveEdge(x,w):
    C0=Enc(pk0,M1(x,w);fresh R0)
    C1=Enc(pk1,M1(x,w);fresh R1)
    pi=SS.Prove(crs,z,(w,R0,R1))
    record x in S before exposing the certificate in the feedback experiment
    return (C0,C1,pi)

SimSetup:
    generate both encryption keys
    (crs,tau)=SS.SimSetup(R_2,bounds)
    keep tau,sk0,sk1 only as reduction state

SimEdge(x):
    C0=Enc(pk0,M0(x);fresh R0)
    C1=Enc(pk1,M0(x);fresh R1)
    pi=SS.SimProve(tau,z)
    record x in S before exposing the certificate
    return (C0,C1,pi)

Extract_j(x,cert):
    reject if canonical parsing, pinned context or SS.Verify fails
    return KNOWN_STATEMENT if x is in S
    decrypt Cj with skj
    require exact flag 1, exact tag x, and R_edge(x;w)
    return w, or FAILURE if any check fails
```

[DERIVED] The public verifier has no decryption step. Deployment has no
extraction service. The actual simulation/extraction interface uses
`Extract_0`; `Extract_1` is a hybrid device only. Repeated or modified
certificates at an issued outer statement remain `KNOWN_STATEMENT`, exactly
as required by the previous provenance proof.

## 4. Proof of adaptive online feedback security

[DERIVED fresh extraction theorem] After arbitrary adaptive `SimEdge`
queries, including false outer statements and queries depending on earlier
extracted witnesses,

```
Pr[a fresh accepting Extract_0 returns FAILURE] <= epsilon_SS.
```

A reduction to statement-new simulation soundness generates both encryption
keys itself, answers every extraction query immediately, and uses the source
simulation oracle for inner proofs. At its first failure, if `R_2` were true,
the all-coins lemma would make decryption return the certified tagged witness,
contradicting failure. The inner statement is therefore false. Its outer `x`
was never issued, so it was never an inner simulation query. The reduction
outputs that statement/proof, without guessing the failed query or rewinding.

[DERIVED switch lemma] In the same kind of simulated-proof interaction,
replacing `Extract_0` by `Extract_1` changes the entire view by at most
`epsilon_SS`. Couple the two executions until their first different response.
Parsing, public verification and `S` checks agree. If the inner relation were
true, both ciphertexts would decrypt to the **same** `M1(x,w)`, so the
responses would agree. A differing response therefore supplies a new false
inner proof. The reduction knows both keys and detects that first difference.
Both failures returning the same `FAILURE` require no event. Statement-new
soundness suffices even when a proof is rerandomized for an old statement,
because extraction never decrypts at that old outer statement.

[DERIVED ZK with feedback] For at most `q_s` protected proof queries, compare
real proving with simulation while exposing the checked extraction interface:

1. Replace the real CRS/proofs by simulated CRS/proofs, leaving both
   ciphertexts real and extraction on key 0. The adaptive multi-theorem ZK
   reduction knows both keys and answers all feedback. Cost `epsilon_MT-ZK`.
2. Switch extraction to key 1. Cost at most `epsilon_SS` by the switch lemma.
3. Replace the key-0 ciphertexts, in adaptive issuance order, from `M1` to
   `M0`. Each CPA reduction knows key 1 and the proof simulation trapdoor,
   so it answers every extraction response **exactly**, with no decryption
   oracle for the challenge key. Cost `q_s epsilon_CPA`.
4. Switch extraction back to key 0. Both keys are known to this separate
   switch-lemma reduction; arbitrary simulated false proofs are permitted.
   Cost at most `epsilon_SS`.
5. Replace the key-1 ciphertexts from `M1` to `M0`, answering extraction with
   known key 0. Cost `q_s epsilon_CPA`. The resulting experiment is exactly
   `SimSetup`, `SimEdge`, `Extract_0`.

[DERIVED resulting bounds] Using probability gaps and maximum actual
resources across the hybrids,

```
epsilon_backend-ZK <= epsilon_MT-ZK + 2 q_s epsilon_CPA + 2 epsilon_SS
epsilon_backend-extract <= epsilon_SS.
```

There is no CCA or proof-new extraction assumption. A fixed public query
bound handles adaptive termination with inactive positions. `q_e`, the
extraction query count, enters running time and the SS adversary's resources,
not an additional guessed-query factor. Simulated responses may be arbitrary
false statements; real endpoint proof queries have valid supplied witnesses,
as in ordinary adaptive ZK. An iO hybrid can subsequently call `SimEdge`
without knowing the challenge compiler coins.

[DERIVED quantum state accounting] All oracle requests and responses in this
theorem are classical. The adversary may otherwise be QPT, evaluate public
code coherently and retain its quantum work register across the entire
interaction. Each reduction invokes it once and resumes it without copying
or resetting that register. The first-difference coupling compares classical
responses; before that response the quantum channels are identical. There
is no rewinding, measurement of a hidden witness register, or extractability
assumption about a QROM.

[DERIVED / OPEN external advice scope] The same straight-line compiler proof
supports one supplied polynomial-size quantum auxiliary register if the LWE,
NIZK, PRG/PRF and signature security games permit that register. It passes the
register once to the adversary; it does not prepare extra copies. The source
NIZK definitions explicitly retain quantum work state; 2023/1702 Definition 3
also writes a quantum auxiliary state `rho_lambda`, but its stronger
superposition theorem is not being instantiated here. A headline assumption
of **uniform** quantum LWE hardness alone does not automatically assert
hardness against arbitrary nonuniform quantum advice. Thus the ordinary QPT
result is source-backed; the arbitrary-advice extension keeps that stronger
base-hardness convention explicit. No advice correlated with honest setup
secret keys is admitted. Public setup-derived correlations are generated
inside the experiment, where the reductions already handle them.

## 5. Cost, lifecycle and what this closes

[DERIVED concrete encryption accounting] Let `ell=ceil(log_2 q)` and `D` be
the exact padded payload bit bound at the edge's depth. Before framing:

| Object/work | Size or operation count |
|---|---|
| Two explicit Regev public keys | `2 m(n+1) ell` bits |
| Two ciphertexts | `2 D(n+1) ell` bits |
| Encryption witness matrices | `2 m D` bits |
| Secret extraction keys in a reduction | `2 n ell` bits |
| Both encryptions | at most `2 m D(n+1)` conditional additions modulo `q` |
| One extraction decryption | `D n` modular multiply-adds, then `R_edge` check |

No public-key seed expansion or packed encryption is assumed in these counts.
Schoolbook binary circuits implement the encryption checks in
`O(m D(n+1) ell)` gates using conditional addition/reduction. If `V_edge`
is the fixed circuit size of the exact compiler/evaluation relation, the
target relation has size

```
V_2 = O(V_edge + m D(n+1) ell + |x|).
```

[DERIVED proof accounting] The source SS wrapper adds `6 lambda^2 + 3 lambda`
CRS bits besides the selected base NIZK CRS, one fresh one-time signing key,
one PRF evaluation in simulation, and **one** base NP proof for the OR
relation. If `V_OR` includes `V_2`, the PRF/commitment checks and encoding
checks, the base proof is exactly the Peikert–Shiehian proof for that bounded
NP relation after its standard NP reduction. Its proof/prover size is
polynomial in `(lambda,V_OR)`, not succinct and not linear in `V_edge` by a
theorem used here. The literal source proof also carries its full inner
statement, so it duplicates `z` unless an explicitly analyzed serializer
deduplicates it. Let `P_PS(lambda,V_OR)` be that construction's proof length
and `K_OTS,S_OTS` its selected signature lengths. A literal certificate has
the explicit compositional bound

```
2 D(n+1) ell + |z| + K_OTS + lambda
                + P_PS(lambda,V_OR) + S_OTS + framing.
```

[SOURCE / cost limitation] Peikert–Shiehian Construction 2.9 commits an
`S`-bit circuit description as an `n_h x (S m_h)` matrix over `Z_qh`, where
`m_h=n_h ceil(log_2 q_h)`. Construction 3.1 actually evaluates its universal
circuit on that commitment and applies the gadget/inert map. Those matrices,
the NP reduction and all signature/PRF computations must be charged; this is
not a STARK performance estimate. Local 2019/908, Section 6.2 pp29–30,
specifically explains why generic graph-Hamiltonicity reductions are costly
even for the much simpler Regev plaintext-equality relation. No finite
latency or byte estimate for the enormous iO relation is justified by these
sources. The original CCA route, if realized by Naor–Yung, would additionally
prove ciphertext consistency **inside** each encryption; the direct relation
above removes that nested proof computation.

[DERIVED polynomial boundary] For a polynomially bounded edge relation,
payload and public resource descriptor, every algorithm and object added by
this backend has polynomial size. An ancestry with `h` bounded edges costs
the sum of those edge/certificate bounds, with no recursive ancestry proof
required inside `R_edge`. This proves polynomial overhead **in the actual
program and compiler bounds**. It does not prove those bounds polynomial in
`h`: the ordinary-iO recurrence from `HIO.md` can still grow superpolynomially
with hop count. Nor does it make a fixed horizon renewable.

[DERIVED forest substitution] Substitute these two backend bounds in the
existing parent-preserving hybrid of `HIO_PROVENANCE.md`. With the same
root/protected-output switch bound `N`, a conservative ledger is

```
Adv_forest <= N epsilon_iO + 2 epsilon_MT-ZK
              + 4 q_s epsilon_CPA + (2N+6) epsilon_SS.
```

The NIZK/encryption legs now have a standard-model lattice instantiation;
the `epsilon_iO` term, all-coins iO correctness, paired residual invariant,
honest pinned genesis and retired initialization records remain premises.
This formula is not an unconditional or implemented post-quantum resident.

[DERIVED credentials] Public actors receive two public encryption keys, a
proof CRS and certified ancestry. Each protected issuer holds only its own
command and fresh compiler/encryption/proof coins. Either retained Regev
secret key would decrypt the certificate witnesses, including protected
commands, so **both** are retired at honest setup. A retained SS simulation
trapdoor would authorize false ancestry and is also forbidden. No deployed
quorum, extraction service or recovery credential is introduced. The
initialization/erasure assumption remains tier A; malicious setup is not
solved.

[DERIVED decision] Use this direct backend for the next provenance theorem
instead of implementing a general CCA layer first. It closes the online
feedback construction and malicious encryption-coins gap with established
algorithms. The decisive remaining construction problem is the protected
program itself: an actual jointly secure continuation compiler with useful
size, and, for a full PQ conclusion, compatible iO security/correctness and
the declared quantum auxiliary-state convention. No toy cryptographic demo,
new validation grid or changes to the companion trees were made.

## Source record

[EXECUTED] The separate `sources/hio_provenance_pq_sources.json` records
source hashes, inspected sections and discovery queries for integration into
the shared ledger by the root owner. This run made ten web search queries,
two direct page opens, one author-PDF link click and one page find; one
author-hosted PDF was downloaded for local text inspection. Five local mirror
PDFs were extracted. Zero Scry queries and zero eprint PDF downloads.
