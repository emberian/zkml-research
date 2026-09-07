# Direct vector GKP: one function key, but encryption still grows with output

[DERIVED result; 2026-09-07] A direct single-key vector-output extension of
GKP2012/733 is possible: share one fresh FHE setup and encrypted input, garble
all output decryptions as one circuit, and use a distinct ABE2 instance for
each garbled input position. Its static security proof is the same three
straight-line hybrid stages, with the whole vector handled in one garbling
simulation. It does not require first obtaining `M` FE keys under one Boolean
FE setup or paying the inspected `Q*M` bounded-key amplification.

[DERIVED stopping point] This extension still puts `M*L` ABE2 ciphertexts
and a fresh vector garbling in **public encryption**, where `M` is output
arity and `L` is a single-bit evaluated FHE ciphertext's width. It therefore
does not supply the output-independent compact encryption/effective-key
interface required by the public-environment bootstrap. The exact source
dependency is that the garbled decryptor belongs to **FE.Enc**, which first
samples its fresh FHE secret key; prior FE.KeyGen does not know that key or
the resulting garbled label pairs. Moving that garbling to the function key
is a changed primitive interface, not a rearrangement of the printed algorithm.

[DERIVED scope] This is a constructive algorithm/source audit, not a
refutation of the published Boolean depth-upgrade theorem or of every possible
vector FE construction. The direct vector improvement avoids a particular
black-box collusion substitution; it does not improve the source's basic
linear-output scaling to output-independent encryption. No cryptographic
algorithm, protected-output test or adversary was run. No frozen predecessor,
shared ledger or companion file was changed. `inputs.json` and `commands.txt`
pin the local papers, exact read locations, extraction commands and query
counts. Extracts are ignored; no PDF was downloaded.

## 1. Source pins and the four separate widths

[SOURCE: construction, game and reduction] The local GKP paper is
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2012/733.pdf`, SHA256
`117f9a5a3c2d7eed51c939af7c01f59aa34a33298a06b82fda99157aa28c4d97`.
Read via its complete `pdftotext -layout` extraction: FHE definitions and
Theorem 2.1, printed pp12–13; one-time garbling Definitions 2.6–2.7, pp13–15;
ABE2 Definitions 2.10–2.11, pp17–18; FE games, pp18–20; Theorem 3.1,
Corollary 3.5 and Remarks 3.6–3.7, pp20–23; the complete constructor and
Lemmas 3.9–3.11, pp23–29; ABE2 wrapper, Appendix B pp47–49. These are
algorithm/game/reduction reads, not an abstract-only interpretation.

[SOURCE] In §3.1, FE.Setup makes `L` independent ABE2 instances. FE.KeyGen
issues the predicates computing each bit of the homomorphic evaluation of
one Boolean function. FE.Enc then generates a fresh `(hpk,hsk)`, encrypts the
input bits, garbles `Dec(hsk,·)`, and ABE2-encrypts both labels for each of its
`L` garbled input positions. The ciphertext includes that garbling. Appendix B
uses two independent ordinary ABE setups per ABE2 instance.

[DERIVED notation] Keep the following parameters separate:

| Parameter | Meaning |
|---|---|
| `n` | Original plaintext bit length |
| `M` | Number of bits returned by one vector function |
| `L=L(kappa,D)` | Padded bit length of one evaluated **single-bit** FHE ciphertext |
| `h=|hpk|+n*L` | Public ABE attribute width for `(hpk,psi)` |
| `S,D` | Prescribed vector-function size and maximum component depth |
| `J=M*L` | Number of input positions in the explicit vector decryption circuit |

[HYPOTHESIS parameter contract] Fix public bounds before setup and use uniform
padded algorithms for them. Every admitted vector circuit
`f=(f_1,...,f_M):{0,1}^n -> {0,1}^M` has size at most `S`; each component is
supported by the chosen leveled FHE and its evaluated-bit ABE predicate family.
The FHE ciphertext/key/decryption templates have public fixed lengths for
these bounds. Setup cannot inspect the particular function or message.
The derived construction below uses the source's bitwise FHE representation;
it does not silently substitute a packed or compressed vector ciphertext.

## 2. Concrete direct one-key vector constructor

[DERIVED algorithm] Let `j` index output bits and `i` index bits of one FHE
ciphertext. The following is a direct constructor, not a source quotation.

```
Setup(kappa,n,D,M,S):
    for (j,i) in [M] x [L]:
        (apk[j,i], ask[j,i]) <- ABE2.Setup(the common prescribed bounds)
    return the public tuple apk and master tuple ask

KeyGen(ask,f):
    P[j,i](hpk,psi) := bit_i(FHE.Eval(hpk,f_j,psi))
    for (j,i): tk[j,i] <- ABE2.KeyGen(ask[j,i],P[j,i])
    return the one vector-function key (tk[j,i])_(j,i)

Enc(apk,x):
    (hpk,hsk) <- FHE.KeyGen(kappa,D)
    psi <- (FHE.Enc(hpk,x_a))_(a in [n])
    X := (hpk,psi)
    define Dvec_hsk(z_1,...,z_M) := (FHE.Dec(hsk,z_j))_(j in [M])
          where every z_j is an L-bit string
    (Gamma, {L[j,i,0],L[j,i,1]}) <- Garble(Dvec_hsk)
    for (j,i): c[j,i] <- ABE2.Enc(apk[j,i],X,L[j,i,0],L[j,i,1])
    return (Gamma,(c[j,i])_(j,i))

Dec(tk,ct):
    for (j,i): ell[j,i] <- ABE2.Dec(tk[j,i],c[j,i])
    return Garble.Eval(Gamma,(ell[j,i])_(j,i))
```

[DERIVED] The garbling is one circuit on **one concatenated `M*L`-bit
input**, not one garbled `L`-bit circuit reused on `M` inputs. Each ABE2
instance exposes only one predicate key. Its label selection is the
corresponding bit of the appropriate evaluated FHE ciphertext, so the
garbled vector output is `(f_j(x))_j`, subject to the component errors below.
The FHE key and input ciphertexts are shared across all outputs; their
correlation is retained. The ABE setup coins are independent across positions.

[DERIVED] Packaging the `M*L` tokens as one FE key is legitimate here because
each token is under a separately generated ABE2 key. It does not relabel `M`
keys exposed under one Boolean FE public key as a single query. For the
present target the external FE key bound is one. This note does not give a
free extension to multiple vector-function keys under the same master setup.

## 3. Static security and fresh correctness, including one quantum advice state

[HYPOTHESIS games] Fix a classical nonuniform vector circuit `f`, messages
`x0,x1` with `f(x0)=f(x1)` as **entire vectors**, and one arbitrary polynomial
quantum advice state `rho`, all before fresh setup/encryption coins. The state
may depend on the fixed classical tuple; it is not correlated with fresh
secret coins. Assume resource-indexed, uniform probability-gap bounds for:

- QA single-bit FHE IND-CPA, `epsilon_FHE`;
- QA selective single-key ABE2 hidden-label security for every `P[j,i]` and
  its required complement, `epsilon_ABE2`;
- QA one-time input-and-circuit garbling simulation for the vector circuit
  `Dvec_hsk` and its `M*L`-bit input, `epsilon_GC,vec`.

[HYPOTHESIS] The garbling game carries the generator's classical side records
and the one retained quantum state jointly. All reductions use classical
messages, functions, attributes and primitive challenge interfaces; no
coherent key/encryption oracle is used. Uniform envelopes cover the larger
vector circuit and full view sizes. These are explicit conditional primitive
games, not an instantiation from a phrase such as “post-quantum LWE.”

[DERIVED proof] For each fixed plaintext `x`, use the following three stages.
They are the vector counterparts of GKP Lemmas 3.11, 3.10 and 3.9, respectively.

1. For each of `J=M*L` independent ABE2 instances, replace the label of the
   unopened branch by the label of the opened branch. At that position there
   is only one predicate key, so the changed branch is exactly the one hidden
   in Definition 2.11. For the static selective game, sample the shared fresh
   FHE tuple and garbling before the selected ABE setup: their real coins are
   independent of ABE setup. This fixes `X` and all classical predicate values
   before the selected setup. Other ABE instances are generated locally.
2. Replace the one real vector garbling and its one selected vector of labels
   by its simulation. Its actual output is the vector of FHE decryptions.
   Replacing that vector by `f(x)` costs at most `delta_FHE,vec`. The simulation
   then depends only on `f(x)` and public padded sizes.
3. Replace the FHE encryption of `x` by an encryption of `0^n`. The garbling
   is already simulated and its selected labels are duplicated in both ABE2
   branches. The usual `n` single-bit FHE hybrids handle the common-key input
   tuple. The simulator does not need the challenge FHE secret key; the
   garbling template's dimensions are fixed public bounds.

[DERIVED bound] The common simulated endpoint is determined by the equal
vector outputs, giving

```
gap_vector <= 2*(n*epsilon_FHE
                + epsilon_GC,vec
                + M*L*epsilon_ABE2
                + delta_FHE,vec).
```

[DERIVED resource scope] Every primitive bound is evaluated at the actual
reduction resources, including up to `M*L` local setups/keys/ciphertexts,
evaluation of the required classical component predicates and the vector
garbling size. A single reduction invokes the final quantum distinguisher
once with the original `rho`; there is no cloning, rewind, extraction or
conditioning/repreparation of that state. The hybrid sum is over classical
indices with a common resource envelope, not repeated physical use of one
state. Statistical replacements retain their classical total-variation bounds
after adjoining the same independent advice and applying the final channel.

[DERIVED correctness ledger] If `delta_FHE` is a uniform fresh correctness
bound for a component `f_j`, then union bounding, without assuming independent
output errors, gives

```
delta_FHE,vec <= M*delta_FHE,
delta_vector <= delta_FHE,vec + delta_GC,vec + M*L*delta_ABE2.
```

[DERIVED] Here `delta_GC,vec` concerns the single vector garbling and
`delta_ABE2` each selected-label decryption. This remains a fresh-message
correctness guarantee. Neither source negligible error nor this union bound
provides perfect correctness or the bootstrap's quantitative subexponential
error envelope automatically. Full uniform all-input correctness must still
be obtained through the reviewed outer error accounting at actual resources.

[DERIVED Boolean-garbling specialization] No new compact vector-garbling
primitive is needed for this positive. If the supplied QA garbling contract
only covers Boolean outputs, implement the parallel circuit by `M`
independently garbled copies of `Dec(hsk,·)`, with distinct input-label
positions, and regard their tuple as the composite garbling. A standard
component hybrid gives `epsilon_GC,vec <= M*epsilon_GC,bit` and a union bound
gives `delta_GC,vec <= M*delta_GC,bit`, at the enlarged joint-view resources.
The shared FHE secret key and evaluated input tuple remain in the generator's
classical side state; only garbling coins are independent. This instantiates
the vector-garbling game conditionally from the matching one-time Boolean QA
game, still with one retained advice state. It also retains all `M` garbling
outputs/work in Enc and supplies no compactness improvement.

## 4. Where the output-length cost lands

[SOURCE] GKP Theorem 3.1, pp20–21, charges `L` ABE2 ciphertexts and the
garbling of an `L`-input decryptor. The complete constructor and size proof on
pp23–24 place both in FE.Enc. Its p22 discussion preceding Corollary 3.5 notes
that packed FHE may improve multi-output efficiency; it supplies no
output-independent packed parameter substitution there.

[DERIVED size ledger] Let `K_A(h,D_A)` and `C_A(h,ell,D_A)` be the ordinary
ABE public-key and ciphertext lengths, with label length `ell`, and let
`Gsize_vec`, `Gtime_vec` be the actual garbling length/work. Ignoring only
explicit tuple/parameter serialization overhead, this constructor has:

| Operation/artifact | Source-algorithm substitution |
|---|---|
| Full FE public key | `2*M*L*K_A(h,D_A)` |
| Vector function key | `M*L` ABE2 predicate tokens |
| Encryption work | one FHE setup, `n` FHE encryptions, `Gtime_vec`, and `2*M*L` ordinary ABE encryptions |
| Ciphertext body | `2*M*L*C_A(h,ell,D_A) + Gsize_vec` |
| Garbled input label positions | `M*L`, with two labels per position at garbling time |
| Decryption work/output | `M*L` ABE2 decryptions, vector garbling evaluation and `M` output writes |

[DERIVED] In the explicit layout there are `M*L` nonempty ABE2 ciphertext
components, so ciphertext output writes alone cost at least `Omega(M*L)`
bit operations. Even a hypothetical unrelated compression of the public key
would not remove those writes. This is a bound on this constructor's literal
format, not an information-theoretic lower bound on every vector FE ciphertext.

[SOURCE / DERIVED effective-key dependency] GVW2013/337 §6.1, printed p16,
generates `2*h+1` TOR public keys in each ordinary ABE setup. Its encryption
reads the attribute-selected input-wire public keys and the output public
key, and emits `h` encodings plus a masked message. In this direct vector
substitution those operations occur in each of `2*M*L` ordinary ABE instances.
The public-environment compiler deletes unused key-input positions of a
**fixed small encryption circuit**; these independently addressed encryption
instances are still executed and their outputs still written. The literal
substitution therefore provides neither its small circuit nor an effective-key
bound independent of `M`. No lower bound on arbitrary alternative public-key
compression is asserted.

[SOURCE target] The independently reviewed
[public-environment note](../public_environment/PUBLIC_ENVIRONMENT.md), §1 and
§§3–4, requires encoding-key dependency and **total encryption work including
output bindings/randomness** bounded by a fixed polynomial in
`(kappa,n,log S)`. Long setup, function-key generation and decryption may depend
polynomially on `S`. ABSV2014/917 §4/Figure 2, pp12–13, puts the entire
randomized-encoding vector in the shallow function's output while its
ciphertext encrypts only `(x,KP,0,0)`. Thus its output bound `M` can grow
polynomially with the target function size, rather than logarithmically.

[DERIVED substitution verdict] The direct constructor puts `M` in the
allowed Setup/KeyGen/Dec costs **and also in forbidden Enc/output costs**.
It avoids the particular `Q*M` FE-query amplification for external `Q=1`,
but still fails this compact shallow interface. Calling `M(kappa)` a polynomial
for a preselected family does not produce the one fixed polynomial in
`(kappa,n,log S)` needed before the function-size bound is chosen. No conclusion
about failure of the published Boolean depth theorem follows from this
failure of one inspected substitution.

## 5. Why the proposed cost moves do not follow from these algorithms

[DERIVED: garbling in the function key] The dependency chain is

```
Enc's fresh hsk -> Dvec_hsk -> fresh Gamma and label pairs
               -> ABE ciphertexts at Enc's attribute X=(hpk,psi).
```

[DERIVED] Prior KeyGen receives the ABE master keys and `f`, but none of
these fresh encryption objects. It cannot perform the source Garble call
there by mere scheduling. Garbling a universal circuit with `hsk` as a later
input would instead require a new public mechanism to deliver the correct
secret garbled encoding of `hsk` under a key-generated garbling. That mechanism
is not supplied by source ABE2 or ordinary one-time Yao garbling. Moving a
per-encryption preprocessing phase earlier in wall-clock time also does not
make its work part of one reusable Setup under the required Enc accounting.

[DERIVED: reusing only L label pairs] An attempted alternative retains one
`L`-input garbled decryptor and lets each of the `M` output predicates select
labels from the same `L` ABE2 ciphertexts. This both exposes multiple predicate
keys per ABE2 instance and supplies multiple encodings to the same garbling.
GKP Definition 2.7 on pp14–15 grants only one encoded input. More concretely,
Lemma 3.11 duplicates the one selected label because the opposite label is
unopened by **every issued key at that instance**. If two component predicates
select opposite bits at the same attribute/position, both branches are opened;
that replacement no longer meets the ABE hidden-label game.

[DERIVED symbolic control] Take a vector function whose first two outputs
are constants zero and one. Whenever both FHE evaluations decrypt correctly,
their evaluated ciphertext strings must differ at some position, since the
same deterministic secret-key decryption cannot map an identical string to
both values. In the shared-label attempt the two predicate keys at that
position therefore open opposite label branches. This is a precise
admissibility failure of the proposed source hybrid, not a claimed complete
attack on every modified garbling construction. The distinct `M*L`-position
constructor above avoids it, at the stated encryption cost.

[DERIVED: packing] A genuinely packed vector FHE variant would replace `M*L`
by its **actual evaluated vector ciphertext width** `L_out` and use its actual
vector-decryption garbling. It would need bounds for `L_out`, the input FHE
attribute width, FHE parameters and the entire Garble work/output, uniformly
in `(kappa,n,log S)`. The source's packing remark supplies no such bound.
For the explicit parallel bit-decryption layout inspected here, label positions
and output ports grow with `M`. Merely renaming that layout a single ciphertext
or a single garbled circuit does not change the work. This note makes no claim
that all conceivable packed representations obey the same lower bound.

[DERIVED: public environments] Specializing a function key or CRS to an
already generated public environment can remove a future public key from
the encrypted node payload. It does not remove fresh encryption-owned garbled
labels, current ABE ciphertext outputs, or the need to bind a key-generated
garbling to later fresh hidden inputs. A compact authorized generator that
defers those outputs to decoding would be additional construction work; it
is not implemented by the existing exact key-input projection lemma. The
separate AJ compact-TMRE lane is not imported as an assumption here.

## 6. Exact conclusion and review handoff

[DERIVED] The supported positive is an explicit direct one-key vector GKP
scheme and its conditional one-copy QA hybrid/correctness bounds. The first
unmet premise for the requested bootstrap substitution is still compact
**public encryption** of the vector interface: in the audited source API,
the fresh encryption-owned decryptor requires all its selected-label
ciphertexts to be materialized by Enc. The function-key relocation and
shared-label shortcuts do not preserve the source algorithm/game.

[OPEN] Closing this route would require an explicit public encoding mechanism
that supplies the needed joint vector functionality while keeping both its
effective key dependency and total Enc work within the fixed compact bound,
with a matching security/correctness reduction. That is a sharply identified
construction premise, not an absence claim about the field. This audit has
not supplied it, a new LWE-only theorem, quantitative PQ instantiation or an
implementation. The direct vector lemma is ready for independent review;
author analysis is not labeled independent acceptance.
