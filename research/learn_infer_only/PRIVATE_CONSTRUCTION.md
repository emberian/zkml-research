# Restricted private continuation: positive controls and their limits

[DERIVED; 2026-09-06] A fixed transition does not need general
iO merely to accept new observations or to continue twice. A finite response-tree
compilation below realizes a much smaller target after honest initialization:
public commands, finite alphabet and horizon, full fork access, and privacy only
between states with identical complete permitted response trees. Its setup and
artifact grow exponentially in the horizon. It preserves behavior through that
horizon, not the raw state or a capacity for indefinite development.

[EXECUTED] A second, compact control below uses actual DDH inner-product FE
ciphertexts for two additive updates and a fixed projection. It retains the raw
encrypted vector and requires no online master key. Its hidden common-kernel
coordinates never affect the permitted future projections. The authorized
projection of each separately supplied input is readable immediately.

[DERIVED] The LWE modular control below also permits arbitrarily many **public
constant additions** without increasing noise. Fresh encrypted observations add
noise. [OPEN] These controls do not supply the resident's compact private nonlinear
learning, hidden fresh entropy, single-history release, or protected execution
integrity. A secure concrete LWE instantiation and quantum composition audit remain.

## Exact construction and exposure

[DERIVED specification] Let `Step : S × C → S × O`, with public finite command
alphabet `C`, cardinality `B`, and fixed maximum path length `H`. Honest initializer
knows secret `s0`. For each command history `h` of length at most `H`, compute the
resulting semantic state `s_h`; sample an independent node key `k_h`. For each
`|h| < H` and command `c`, publish the fixed-size record
`AEAD.Enc(k_h, nonce(c), (k_(h,c), out(s_h,c)); aad=(genesis,h,c))`.
The current protected representation is `(h,k_h)`. A step decrypts the selected
record and replaces the representation with `(h||c,k_(h,c))`. At depth H it refuses.
The table is a complete B-ary tree: no state-dependent pruning or node sharing.

[DERIVED] Expose the entire table, root token, program, alphabet, horizon, and all
subsequently visited tokens. Erase raw states, all setup copies and the node-to-state
mapping. Each future public observation selects a command already supported by the
alphabet; its actual value need not be known at setup. No online encoder key exists.
The root token permits obtaining every child token by permitted traversal; it does
not decrypt an original-state ciphertext, because none exists. The constructor has
compiled the bounded behavioral representation and discarded raw representation.

[DERIVED] This is a functionality-preserving bounded unfolding/observational quotient.
It must not be sold as encrypting and preserving every initial state bit. Two initial
states may share the same bounded behavior yet have different behavior after H; that
future behavior has been intentionally discarded by the finite functionality.

## Privacy statement and the price of the ideal

[DERIVED proof sketch] Define `s ≡_H t` when every command word of length at most H
has the same output trace. Couple two setups by using identical independent node
keys and the same fixed encodings at corresponding histories. Their topology, AAD,
nonces, child tokens and all output symbols are identical, so every ciphertext and
the full exposed artifact are byte-identical. Therefore the artifact distributions
are equal for `s ≡_H t`; this equality argument needs no cryptographic assumption.
AES provides a concrete traversal encoding, not the reason equivalent states hide.

[DERIVED scope] The ideal permits all local forks and restores. A simulator can
query the entire depth-H response tree and generate the exact real distribution,
using one ideal transition query per edge. This is polynomial in the **artifact
size**, and exponential in H. It does not give a simulator with a small prescribed
query quota. The host can decrypt the whole tree and obtain all allowed future
responses immediately; any stronger quota or one-history ideal is false here.
For a conventional polynomial-setup cryptographic family, require `B^H` polynomial
in the security parameter/input-description size. Fixing H or choosing logarithmic
H for fixed B does that. Arbitrary polynomial H with B>1 does not.

## Source audit: what ordinary reusable garbling actually supplies

[SOURCE: construction and game read] Goldwasser–Kalai–Popa–Vaikuntanathan–Zeldovich,
[*Reusable Garbled Circuits and Succinct Functional Encryption*](https://eprint.iacr.org/2012/733),
local revision dated 2013-03-24, §4 Def.4.1 printed p.30: the adversary receives the garbling and an
encoding **oracle**, not the encoding key. §4.1 printed pp.31–32 sets
`gsk=(fmpk,sk)`, `E=Sym.Enc(sk,C)`, `Gamma=FE.KeyGen(fmsk,U_E)`, and
`Encode(gsk,x)=FE.Enc(fmpk,(sk,x))`. `U_E` decrypts the hardwired E with the supplied
sk and runs the resulting C. The source explicitly treats the issuer as retaining
secret state; its theorem is not an all-roles exposure theorem.

[DERIVED scope] Giving gsk to the host is not justified by Def.4.1. In particular,
the FE theorem does not promise function hiding for `U_E`: a compatible FE scheme
can append `U_E` (and hence E) to its function key without damaging that FE theorem.
With that valid instantiation, `gsk + Gamma` reveals C by symmetric decryption.
This is a counterexample to deriving issuer-exposure security from the stated
generic construction, not a claim that every concrete FE key exposes its function.

[SOURCE: discussion read] The same paper, Remark3.7 printed p.23, explicitly
considers FE outputs that contain a new FE encryption for later evaluation. For
**its scheme**, ciphertext growth becomes exponential in the number of composed
steps. That is a concrete cost obstruction, not a theorem that all restricted
continuation requires iO. §1.1.2 printed p.7 and §4.1 printed p.32 distinguish
secret input tokens from a publicly reusable general circuit obfuscator.

[SOURCE: construction/game read via already-landed audit, plus local syntax read]
2024/1294 §3.1 fixes functions, not their input values. `f(s,observation)` remains a
fixed function. The outstanding sPCE problem is issuing the *next protected input*,
not a syntactic prohibition on observations. See `CANDIDATES.md` Route1 for the
existing correction; this note does not duplicate its full source audit.

## Capability and falsifier ledger

| [DERIVED] artifact | exposed role | surviving capability / limit |
|---|---|---|
| raw s0 and setup traversal states | initializer only, erased | retaining them violates the tier-A setup assumption |
| setup map from node to semantic state | initializer only, erased | retained map directly reads represented states |
| root token and fixed encrypted tree | host | every authorized bounded branch; no promise of a quota |
| current history and token | host | one next public command, snapshot, restore, or fork |
| AEAD keys reached by traversal | host | can forge new ciphertexts under those keys; AEAD is not genesis authorization |
| public fixed genesis/table digest | independent verifier if supplied | pins the precomputed table; alone cannot force a malicious host to obey |

[DERIVED] Private observations do not enter safely by handing the host a selected
child token: holding the parent token lets it decrypt every candidate edge and
match the selected child, recovering the command. The actual prototype leaks even
more directly: the last command is `(node-1) mod B`, and repeated integer division
recovers its full history from public node indices alone. Independent child keys prevent
accidental label equality but do not stop this comparison attack.

[DERIVED] Sharing a token whenever two paths reach equal raw states leaks that
equality, which need not follow from outward traces. Independent history tokens
avoid this leak. Similarly, state-dependent pruning leaks topology. These are
reasons to retain the expensive full unfolding, not claims that every compact
garbling has those defects.

[DERIVED] Restoration repeats the same response and enables alternative commands;
the remaining-step counter in `(h,k_h)` cannot prevent root restoration. A separate
continuity authority can authorize which outputs count, but cannot make already
decryptable alternate outputs unknown. This candidate supports the forkable ideal
only. If setup samples per-history development coins, each branch is precommitted;
the host can select among sampled branches. No post-setup entropy is created.

## Executed bounded witness and exact costs

[EXECUTED] `python3 experiments/private_construction/bounded_tree.py audit`
(from this directory; full output `experiments/private_construction/audit.stdout.txt`)
checks all 256 initial byte states and 92,928 legal transition edges at H=5.
The public alphabet is {learn +1, learn ×2, infer high bit}; learn acknowledgments
are 255. There are 62 behavioral classes; the class of 0 is {0,…,7}. Coupling test
coins yields 194 exact serialized-artifact equalities against class representatives.
These tests validate the implementation's finite identities; they are not a
cryptanalytic security estimate. Coupling coins and synthetic states are public.

[EXECUTED] Two continuing updates have actual outward consequences: initial 63,
`+1; ×2; infer` produces {ack,ack,1}; `×2; +1; infer` produces {ack,ack,0}.
The raw-state distinction 63 versus 64 is preserved where it affects permitted
future outputs. Pair 0 versus 1 is hidden at H=5 and distinguishable at H=8.
Each command value is selected online. A separately launched builder emits a
25,951-byte serialized artifact; a separate runtime process receives only that
artifact and produces the first trace. Process separation demonstrates the data
interface; Python cannot verify setup erasure from memory, disk, swap or logs.

[EXECUTED] Negative controls reject wrong keys, ciphertext corruption, an unlisted
command and depth exhaustion. Deliberate failures are preserved: merge-equal-state
labels distinguish 0/1; node indices reveal private command selection; a root-key
holder forges output 42; root restoration selects alternative outward responses.
All are in `results/results.json`. A digest would detect the changed table only
when an independent verifier authenticates and enforces the accepted digest.

[EXECUTED: independent review] `experiments/adversarial_review/tree_horizon_partition.json`
finds class counts H=0…8 of 1,2,6,14,30,62,122,208,256. Its encrypted-artifact
check recovers every byte at H=8 using eight inference observations and 36 primitive
transitions across restored roots. There is then no distinct admissible pair;
extending the horizon destroys this example's nonvacuity without breaking privacy.

[DERIVED from exact counts] There are `E=B(B^H-1)/(B-1)` records and `E+1` keys.
With B=3 and AESGCM from installed `cryptography==50.0.1`, the fixed 33-byte payload
(32-byte child key + output byte) becomes 49 ciphertext bytes. H=5 has 363 records,
17,787 raw ciphertext bytes and 11,648 setup key bytes. H=20 would require
5,230,176,600 records / 256,278,653,400 ciphertext bytes before serialization;
that horizon was not built. One online step is one AEAD decrypt, one fixed table
access and no online input encoding, proof, refresh or key issuance. Setup pays
every Step evaluation and every encryption in the full tree. Table access/history
is public. Counts, not latency or a neural utility comparison.

## Compact control: additive encrypted state with a fixed linear readout

[SOURCE: full construction, game and proof sketch read] Abdalla–Bourse–De Caro–
Pointcheval, [*Simple Functional Encryption Schemes for Inner Products*](https://eprint.iacr.org/2015/017),
revision dated 2015-10-01, Fig.2/§2.3 printed pp.6–7 and Construction3.1 /
Theorem3.2 pp.7–8. For prime-order group G, master vector s, and h_i=g^s_i:

```text
mpk=(h_i); msk=s; sk_y=<s,y> mod |G|
Enc(mpk,x;r)=(g^r, (h_i^r g^x_i)_i)
Project(ct,sk_y)= product_i ct_i^y_i / ct_0^sk_y = g^<x,y>
```

[SOURCE] The source's theorem is **selective IND-FE-CPA under DDH**, not simulation,
malicious-setup security, or PQ security. Its ciphertext decryption needs a discrete
log to recover the integer inner product; the paper explicitly names that limitation.

[DERIVED construction] Fix readout vectors Y before honest setup; issue their keys,
then erase msk, plaintext initialization and its encryption coins. A public issuer
encrypts each additive observation u under mpk. The host updates ciphertexts by
componentwise multiplication: `Enc(x;r)*Enc(u;t)=Enc(x+u;r+t)`.
Two or more updates preserve the same size and need no new secret key. The actual
raw vector stays encrypted; unlike the response tree, it was not compiled away.
Scalar public multiplication is also algebraically available by exponentiation;
the executed loop uses addition only.

[DERIVED privacy reduction] Let `V=span(Y)` over the group-order field. Exposed
function keys derive all keys in V by the same linear combinations; rank r leaves
common kernel dimension d-r. Challenge states differ by δ in `V^perp` and agree on
all authorized projections. Public adaptive additions preserve δ. A reduction given
the honest initial FE challenge ciphertext can generate every subsequent public
input ciphertext, homomorphic update, output and restored branch with the exposed
keys. The entire adversarial view is postprocessing of that FE game. This supports
the source's **selective initial-state indistinguishability** for the specified
public-addition/forkable interface. It adds no simulator theorem and does not claim
private future input histories from an unaudited multi-challenge reduction.

[DERIVED semantic limit] The retained common-kernel distinctions cannot affect any
future permitted output. For this exact interface the plaintext vector `Y*x` is a
functionality-preserving quotient; the larger encrypted vector buys representation
privacy, not demonstrated private cognition. Adding a public operation A requires
`A^T V ⊆ V` to preserve the same hidden equivalence. Hidden nonlinear learning or
an enlarged inference family may destroy that property. In full rank, issued keys
recover every projection (and the master vector by linear algebra); there is no
remaining kernel secrecy to claim.

[EXECUTED] `python3 experiments/private_construction/additive_ipfe.py` instantiates
the equations using RFC3526 §3 group14 (2048-bit modulus; no security-bit estimate)
and Python modular arithmetic. Dimension3, Y={(1,1,0)} gives rank1/kernel dimension2.
The raw state evolves `(1,4,6) → (4,5,8) → (3,7,4)`, releasing `5 → 9 → 10`.
Both fixed-coin algebra identities and fresh-randomness ciphertexts pass. State
`(2,3,11)` has the same readout and remains equivalent under the 605 tested public
additions. Six scalar-derived projection keys behave as their linear span predicts.
The first-coordinate square would instead reveal 5 versus 7 and is not supplied.

[EXECUTED] Deliberate attacks: retained msk reads all final coordinates; retained
input encryption coins recover all that input's coordinates; the standalone
observation ciphertexts reveal projections 4 and 1 before any release receipt;
publicly encrypting an attacker-selected replacement returns 42; restoring the
old ciphertext still returns 5. The wrapper rejects three malformed group elements,
but neither source nor wrapper authenticates provenance or a transition history.
Source IND security already allows arbitrary local computation by the exposed
function-key holder; it does not turn such malformed/replacement inputs into an
authorized next resident state.

[DERIVED decision] Private ingress here has no enduring writer master, but it is
NOT the handoff's acknowledgment-only Learn interface: the host immediately learns
each input's authorized projection. Treat public input values, or explicitly leak
those projections in the ideal. Do not silently count this as proof-bound release.
An input issuer knows its own input/coins; erasing those is necessary if later
issuer exposure is meant to conceal that input. No credential reads other issuers'
orthogonal coordinates merely because it can encrypt.

[DERIVED / EXECUTED counts] The dimension3 prototype uses four 256-byte group
elements per state (1,024 raw bytes), three public-key elements and one exposed
scalar function key. Fresh encoding executes seven modular exponentiations and
three multiplies; encrypted Learn addition executes four group multiplies.
General projection executes four exponentiations, one inverse and its multiplies,
plus four subgroup-membership exponentiations in the wrapper. The integer readout
uses a 129-entry table for the declared interval [-64,64], precomputed here with
129 exponentiations. Out-of-range integer decoding refuses, but the holder still
obtains `g^<x,y>` and can compare it to arbitrary candidate outputs. The executed
77-output falsifier demonstrates this beyond [-64,64]. That interval is a runtime
decoding choice, never a cryptographic release gate. Modular algebra by itself does
not justify unbounded efficiently decoded integer outputs. No benchmark, utility,
side-channel, or constant-time claim: Python `pow` is an algebra reference.

## LWE continuation: distinguish public offsets from fresh encrypted observations

[SOURCE: separate constructions] ABDP2015/017 Construction6.5, printed pp.22–23,
uses `pk_i=A*s_i+e_i`, `ct0=A^T*r`,
`ct_i=<pk_i,r>+floor(q/p)*x_i`, with bounded integer plaintexts. The following
positive modular result instead uses Agrawal–Libert–Stehlé,
[*Fully Secure Functional Encryption for Inner Products, from Standard Assumptions*](https://eprint.iacr.org/2015/608),
revision 2016-11-21, §4.2 pp.16–18. Do not transfer one source's game to the other.

[SOURCE: algorithms/game/reduction statements read] ALS chooses prime p and
`q=p^k`, `Δ=q/p`, uniform `A∈Z_q^(m×n)`, secret short `Z∈Z^(d×m)` from its
specified distribution τ, and public `U=Z*A mod q`. For one fixed canonical
readout `y∈F_p^d`, the issued integer key is `z_y=y^T*Z`:

```text
Enc(x;s,e0,e1): c0=A*s+e0; c1=U*s+e1+Δ*x          (mod q)
Phase_y(c):    y·c1-z_y·c0 = Δ*(y·x mod p)+ε_y   (mod q)
ε_y = y·e1-z_y·e0; decode to nearest one of p slots
```

[DERIVED closed Step] `LearnPublic(c,u)=(c0,c1+Δ*u mod q)` is exactly
`Enc((x+u) mod p;s,e0,e1)`. Each plaintext wrap contributes `pΔ=q=0 mod q`,
so noise is unchanged for any finite sequence of public offsets, including forks.
This is compact indefinitely continuable **finite linear state**, conditional on
the initial correctness event. It supplies no unknown observations or new entropy.
By contrast, `LearnEncrypted(c,Enc(u))=c+Enc(u)` adds the encryption errors. With
per-ciphertext projected error bounds E_i, a sufficient correctness contract is
`2*(|ε_initial|+Σ_i E_i)<Δ`. This route has a finite fresh-input noise horizon.
Adding a fresh encryption of zero is not noise refresh.

[DERIVED privacy/lifecycle] Honest setup issues the fixed y key, then erases Z,
the issuer state, initial x, s and initial error coins. Public A,U and one short
projection key remain; neither public update nor private-input encryption needs
an online writer master. Public updates/forks are local postprocessing of an
initial source FE challenge, so equal-y challenge pairs stay admissible. The host
already possesses the phase computation and cannot be forced to await a receipt.
Retained Z reads all coordinates; fresh private input projections are immediately
readable. Common-kernel distinctions are again behaviorally irrelevant forever.

[SOURCE: issuance trap, §4.2 p.16] Multiple modular keys require stateful issuance:
mod-p dependent requested vectors must receive integer-dependent **lifted** vectors
and keys. Independent canonical lifting can reveal Z despite modular dependence.
For p=5, requests `(1,2)` and `(3,1)=3*(1,2) mod5` have integer determinant −5;
their naive integer keys recover both rows of Z. The correct second lift is `(3,6)`
with key three times the first. All keys needed by this fixed Step can be issued
at initialization; stateful issuance does not require an enduring writer master.

[SOURCE: security scope] Appendix A Definition8 pp.30–31 is adaptive IND-CPA for
PPT adversaries with polynomially many admissible key queries, not simulation or
malicious setup. Theorem3 p.18 gives the modular stateful scheme's full security
under `mheLWE(q,α,m,d,τ)` and its parameter conditions. Theorem4 pp.20–22, for
`d<n`, reduces ordinary LWE in dimension `n−d` to the multi-hint problem, with
noise enlargement factor `ξ≤O(n^4*m^2*log^(5/2)n)` and the specified efficiently
sampleable τ. Dimension and Gaussian widths are part of the reduction. In §4.2,
`K'=(sqrt(d)*p)^d` enters those widths; this is not a small practical parameter set.
The classical reduction statements and relevant algorithms were read; a full
QPT lifting/composition proof was not audited. LWE is a PQ candidate assumption
here, not an executed PQ-security claim or an estimate of concrete security bits.

[EXECUTED equation/noise witness] `python3 experiments/private_construction/lwe_additive.py`
uses deliberately insecure p=5,q=15625,d=3,n=2,m=6, bounded small uniform secrets
and errors, **not source τ or Gaussian/security parameters**. State
`(1,4,3) → (4,0,0) → (3,2,4)` releases `0 → 4 → 0` under y=(1,1,0), with
unchanged projected noise 3. Alternative `(2,3,1)` is an equal-y challenge.
All 15,625 state/command edges and 10,000 continuing public updates preserve the
exact ciphertext identity and noise. Two fresh encrypted updates close correctly
but alter noise. With this toy key, a worst-case per-ciphertext bound E=8 yields
195 safe zero-plaintext additions from zero error; the 196th gives error1568,
exceeding Δ/2 and decoding to 1. This is a bounded-noise correctness falsifier,
not an honest-encryption failure probability or a secure implementation benchmark.

[EXECUTED negatives] The script reproduces naive dependent-key master recovery,
pre-gate private-input projection, unkeyed replacement output3, and retained-master
state recovery. A separate naive floor-scaled modular port (q101,p5,Δ20) fails
on the 51st public +1 update after ten wraps: each wrap contributes residual −1.
This does not attack ALS's exact modular construction. For the bounded-integer
ABDP/ALS§4.1 variants, no-noise public additions require an unwrapped trajectory
within the message/output bounds, or explicit accounting for that carry residual.

[DERIVED exact cost] ALS has `(m+d)*n` public residues, `m+d` ciphertext residues
and m integer entries per fixed key; public addition costs d scalar multiplies
and d additions, encrypted-input addition m+d additions. Fresh encryption uses
`(m+d)*n+d` scalar multiplies, projection m+d. Toy counts are18/9/6 stored entries,
3+3 public-update operations, 9 private additions, 21 encoding and9 projection
multiplies. No source τ sampler, secure parameter selection, or latency test ran.

[SOURCE: practical follow-up, limited scope] Mera–Karmakar–Marc–Soleimanian,
[*Efficient Lattice-Based Inner-Product Functional Encryption*](https://eprint.iacr.org/2021/046),
§4 p.16 has a different RLWE selective scheme; §5 p.21 has a different adaptive
scheme. Both bounded-integer encodings use `floor(q/K)`, not ALS's exact modular
encoding. §7.2/Table1 p.27 benchmarks the **selective** scheme: its medium row
reports n4096,d785,log2(q)=86 and 119.2 estimated PQ bits, while §7.3 prose says129.
Use neither estimate as verified here. Construction, theorem statements and cost
table were inspected; reduction details and implementation were not audited.
[SOURCE / EXECUTED follow-up] `experiments/private_construction/RLWE_AUDIT.md`
now pins both author repos and audits2023/721's selective algorithms. Native full
build failed at AVX2/arm64; no sampler was replaced. Both checked repos use
uninitialized secret/error PRG contexts; the optimized one also shares mutable
PRG contexts across parallel calls. These are source-level findings, not exploits.
An exact extracted GMP decoder from each repo was compiled: zero-output phase
q−1 decodes to K=50,241 rather than0; output5 is a passing control. No full RLWE
encryption ran. Default medium ciphertext size is38,633,472 bytes and fixed key
49,152 bytes; machine-readable counts and decoder logs are preserved.

## Status / next / proposed coordinator ledger changes

[EXECUTED] All three controls and their falsifiers pass. [OPEN] Ask whether any compact
restricted primitive preserves this functionality without giving the host a private
input comparison oracle. Do not weaken the private-ingress requirement silently.

[DERIVED proposed CANDIDATES addition] Keep bounded response-tree compilation as a
tier-A behavioral positive control with exponential preprocessing, public commands,
and full fork leakage. It refutes an overbroad “two continuations require general
iO” inference. It does not change the leading resident's privacy/closure decision.

[DERIVED proposed CANDIDATES / CREDENTIALS / COSTS additions] Add DDH-IPFE additive
state as a classical tier-A restricted positive row: no writer master after setup,
fixed projection-span privacy, raw vector retained, public or projection-leaking
input, no nonlinear utility/continuity/output mediation. Record msk erasure,
per-input coins, projection-key span, snapshot readout and bounded integer decode.
Add ALS modular LWE as a source-conditional restricted row: constant noise for
public offsets, growing noise for fresh encrypted observations; no secure parameter
instantiation or audited quantum composition. Record setup Z/coin erasure and the
stateful modular-key lift rule. Do not apply its no-wrap-cost result to floor-scaled
bounded-integer schemes. No resident construction verdict changes.

[EXECUTED tooling inventory] Python 3.14.7, installed `cryptography==50.0.1`, AESGCM
available. No package installation. Source hashes, commands and results are in
`experiments/private_construction/sources_manifest.json` and adjacent logs. Scry
counts: one schema call, three SQL queries; Kagi zero. No ePrint PDF download.

[SOURCE / DERIVED / EXECUTED follow-up] `experiments/private_construction/PREDICATE_CLOSURE.md`
audits a narrower one-key full-hiding PE candidate (2025/361) and its missing public
update. Publishing its natural outer-encoding repair helper reveals the entire
inner secret; a finite equation witness recovers all six encoded bits. Independently,
sign plus public translations recovers all256 bounded scores in eight observations,
without forks. KSW aggregation and targeted HABE do not supply exact sign-only
state addition. This follow-up uses four additional Scry SQL queries (seven total).

[SOURCE / DERIVED / EXECUTED follow-up] `experiments/private_construction/RFE_RECURRENCE.md`
finds same-scheme encrypted-output closure syntactically possible in2025/330's
compact iO-based randomized FE. Its theorem does not cover the proposed private
transition: a public first-component encryption comparison has gap at least
2^(-lambda), above its required epsilon2^(-2s-lambda), for distinct next states.
This is a compatibility-premise failure, not a security break. Exact fraction,
size and continuing-interface controls are preserved. One additional Scry query
brings this lane to eight SQL plus one schema; the static predicate positive stays.

## Bounded encrypted-state successor

[SOURCE/DERIVED/EXECUTED] [FINITE_LADDER.md](experiments/private_construction/FINITE_LADDER.md) records the H2 reverse-setup randomized-FE construction, complete future-key exposure and symbolic witnesses. [HORIZON.md](experiments/private_construction/horizon/HORIZON.md) gives the reviewed uniform logarithmic-horizon extension and exact padded-selector reduction, with uniform host/initial-sampler premises. These are classical conditional constructions after honest erasure, with public commands and full forks. They do not supply private fresh ingress, indefinite extension, practical obfuscation or PQ security. The independent review is in ADVERSARIAL_REVIEW.md section17; finite arithmetic has a separate40-pin proposed patch.
