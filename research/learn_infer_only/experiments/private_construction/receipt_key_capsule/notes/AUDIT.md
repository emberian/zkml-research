# A receipt-gated FHE-key capsule: exact result and missing game

[DERIVED decision, 2026-09-08] The proposed two-input capsule has concrete
algorithms, but 2013/727 does **not** establish its selected-receipt privacy.
Its public slot requires exact equality on all encoded inputs. Valid signatures
that an efficient host cannot obtain still count. This is a scoped failure of
this theorem application, not a break of MIFE or a field-wide impossibility.
A separate positive, source-backed repair for **release of a fixed preencrypted
capability** is signature-based witness encryption (SWE), audited below. It
does not itself implement a repeatedly accepting FHE decryptor.

[EXECUTED scope] Only source extraction, provenance checks, public metadata
access and mathematical review were performed. No cryptographic implementation,
disclosure/routing/extraction control or malformed-input experiment was run.
The two earlier safety-stopped tasks remain stopped. Shared ledgers, frozen
artifacts, VERDICTS and companion trees are untouched.

## 1. Concrete capsule algorithms

[HYPOTHESIS specification] Fix finite polynomial bounds on secret-key length,
FHE ciphertext length, proof/signature length, context encoding, output length,
number of events and circuit depth. All parsers are total: padding is canonical
and rejected encodings return a distinguished `reject`, not a data value.
`DecBounded` is the chosen deterministic FHE decode plus a fixed output
projection; its correctness/noise premise applies to authorized ciphertexts.
A length bound on the returned value does not constrain which information it is.

[HYPOTHESIS fixed context] Let `ctx` contain the exact FHE parameter/key identity,
resident/genesis identity, transition-program and arithmetic version, signature
verification key, output projection and allowed recipient. Each receipt body
`r` binds that context, event identity, parent and next-state identities,
command/input commitments, exact output ciphertext bytes, selected output and
randomness rule. Use full canonical bytes here; replacing them by hashes adds
collision resistance. Recipient checking alone does not hide a plaintext
output from the host holding the function key. The algorithms below model the
host as an authorized output observer; designated private delivery needs an
additional, separately proved recipient-encryption mechanism.

[HYPOTHESIS gate] With `z = (r, sigma, c, proof)` in the second input domain,

```
G_ctx(s, z):
    parse z and check every fixed context/length/canonical-encoding condition
    require r.output_ciphertext == c
    require Verify(ctx.vk, r, sigma) == accept
    require ReceiptRelation(ctx, r, c, proof) == accept   [if deployed]
    return DecBounded(s, c)
```

[DERIVED scope] The candidate initially only checks signature/context. In that
case `ReceiptRelation` is constantly accepting after the preceding checks; an
honest external signer must enforce the transition/finality policy. Adding a
public proof is useful but gives only the relation actually checked. In the
following quantifier argument, include that check in `V_ctx(z)` when present.
Signature existence alone does not manufacture a false proof of an additional
perfectly sound relation.

[HYPOTHESIS setup and deployment]

1. Run `(pk, evk, sk) <- HE.KeyGen`. The FHE security interface includes every
   published evaluation/bootstrapping/key-switch object actually required.
2. Independently run `(vk, ask) <- Sig.KeyGen`, and fix `ctx`. The external
   receipt authority keeps `ask` and independent continuity state `Gamma`.
3. Run `(EK1, EK2, MSK) <- MIFE.Setup(1^lambda, 2)`. Encode both slots in the
   common bounded domain required by 2013/727 §2.1.
4. Compute `K_G <- MIFE.Keygen(MSK, G_ctx)` and
   `C_key <- MIFE.Enc(EK1, Encode(sk))`.
5. Publish `(ctx, pk, evk, EK2, K_G, C_key)` and the encrypted initial state.
   Erase `MSK`, `EK1`, plaintext `sk`, initializer plaintexts/coins/copies and
   the unobfuscated descriptions containing any secret. `EK1` need not be
   public for the application, so analyze the minimal exposed set `I={2}`.
6. Fresh private issuers use public `pk` for observations. The host applies
   the prescribed FHE transitions to obtain subsequent encrypted states.
   The authority checks the exact allowed event against `Gamma`, then signs
   its receipt. It holds no FHE secret in this specification.
7. Anyone holding the public capsule computes
   `C_z <- MIFE.Enc(EK2, Encode(z))`, then
   `MIFE.Dec(K_G, C_key, C_z)`. Stored capsule and receipt bytes remain copyable.

[DERIVED closure and continuity] FHE ciphertext closure supplies the next
protected state only within its leveled/noise budget; no new FE master is
needed for these algorithms. A stateless signature check cannot know that a
newer receipt exists or revoke an already signed receipt. The correct ideal
therefore includes replay of all released capabilities/answers. Selecting a
single continuing history is a separate honest, persistent authority premise.
After compromise of `ask`, the signature-only policy loses its authorization
boundary; a proof-bound gate keeps only its independently checked relation.

## 2. Every surviving credential

| Artifact | Creator; lifetime; exposed coalition | What it enables; erasure or premise |
|---|---|---|
| [HYPOTHESIS] HE `pk,evk` | initializer; permanent; host/issuers | Encrypt and evaluate; all correlated key material enters HE security. |
| [HYPOTHESIS] HE `sk` | initializer; setup only | Full HE reading before erasure; no claim against retained setup coins. |
| [HYPOTHESIS] MIFE `MSK` | FE setup; setup only | Arbitrary function-key generation; erase all raw internal PKE/PRF/obfuscator secret copies outside the issued cryptographic objects. |
| [HYPOTHESIS] `EK1` | FE setup; setup only | Slot-1 issuance; erased in the minimal-exposure candidate. Publicizing it adds compatibility conditions. |
| [HYPOTHESIS] `EK2` | FE setup; permanent; everybody | Arbitrary slot-2 issuance, including any mathematically valid receipt encoding. |
| [HYPOTHESIS] `C_key,K_G` | initializer; permanent; host | Evaluate the fixed gate; source security, not a filename or opaque code convention, must justify raw-secret hiding. |
| [HYPOTHESIS] `vk,ctx` | authority/initializer; permanent; everybody | Public authentication and policy description; must be identical in an ordinary FE comparison. |
| [HYPOTHESIS] `ask,Gamma` | independent authority; ongoing; excluded from host corruption | Issue/finalize receipts; no HE secret, but active control of the signature-only release policy. |
| [HYPOTHESIS] issuer plaintext/coins | each issuer; per observation | Knows its own observation; erasure or explicit leakage needed for later issuer corruption. |
| [HYPOTHESIS] state ciphertexts, receipts, archives | host/authority; permanent; host | All enabled evaluation/replay, their public lengths/access patterns and history. No local software freshness enforcement is inferred. |

[DERIVED] This is honest-initialization tier A with an additional trusted
receipt authority, not malicious-setup tier B. Exposing every software role
including `ask` is a different game. A signature-only authority is a powerful
surviving release credential even though it is not literally `HE.sk`.

## 3. What 2013/727 actually proves

[SOURCE: game read] Goldwasser–Goyal–Jain–Sahai's four-author local precursor,
2013/727, §2.2.1, printed pp.10–11, Definitions 2–3, requires `I`-compatibility
for every function-key query and every arbitrary replacement in every exposed
slot. With `n=2`, one challenge in slot 1 and `I={2}`, this includes exactly

```
                         for every z: G_ctx(s0,z) = G_ctx(s1,z).       (U)
```

[SOURCE: theorem/reduction read] Theorem 14, printed p.17, gives selective IND
under iO plus OWFs; messages must be selected before FE setup (p.11). The
compatibility step in the H4/H5 proof is printed pp.30–31. Theorem 16, p.21,
gives adaptive IND using differing-inputs obfuscation, while retaining the
same Definition-3 compatibility. Merely choosing that theorem does not replace
(U) by a computationally hard-to-find difference.

[DERIVED signature quantifier lemma] Write
`G_ctx(s,z) = if V_ctx(z) then D_s(z.c) else reject`.
Then (U) is equivalent to
`for every z with V_ctx(z): D_s0(z.c)=D_s1(z.c)`.
For a signature-only gate, let `B_ctx(r,c)` denote its public binding checks.
If for every `r,c` satisfying `B_ctx` there exists a signature accepted by `vk`,
then (U) further requires equality for every such `r,c`. Perfect signature
correctness supplies that existence for honest keys and signable bodies;
the signer need not actually have issued the signature. With probabilistic
correctness use the explicit set of bodies that possess an accepted signature,
not an unsupported simultaneous perfect-correctness claim.

[DERIVED finite mathematical tooth] Suppose there is one well-formed body and
ciphertext `r*,c*` in that accepted set for which `D_s0(c*) != D_s1(c*)`.
Choose an existing accepted signature `sigma*` (an existential choice, not an
algorithm). The tuple witnesses failure of (U). Its generation time is
irrelevant to the source admissibility condition. This argument does **not**
say the host can obtain it or break the deployed construction. If an additional
proof check makes every such differing tuple unsatisfiable, this tooth does not
apply; one must prove that stronger exact equivalence.

[DERIVED positive conditional theorem] Let a PPT sampler, before FE setup,
produce a common auxiliary package `AUX`, a fixed `ctx`, equal-length messages
`s0,s1`, and one common dummy second-slot message `z0`. Suppose (U) holds
pointwise for every sampler outcome. Under the selective MIFE theorem just
cited, the two distributions

```
(AUX, ctx, EK2, K_G, MIFE.Enc(EK1,s_b))                for b=0,1
```

are computationally indistinguishable. Proof: submit `(s0,z0),(s1,z0)` with
`I={2}`, request only `G_ctx`, and discard the common second-slot challenge.
Both the unchanged challenge-tuple equality and public replacement conditions
follow from (U). Preserve `AUX` in the adversary state. This is a direct
reduction with no multiplicative loss when using the same binary-experiment
advantage convention. Public local evaluations and later PPT postprocessing
are already included. This is IND, not oracle simulation, and the sampler must
be able to produce the **entire joint auxiliary distribution** without a
secret unavailable in its FE experiment.

[DERIVED nonvacuity of this exact theorem] Let a padded key message be `(s,u)`
and let the gate ignore `u`. Then `(s,0)` and `(s,1)` are distinct, compatible
messages, and there may still be valid receipts giving different answers for
different ciphertexts under `s`. The theorem really hides the unused bit.
It does not show that two different effective FHE decryption keys are compatible
or that a meaningful learned-state predicate is protected. This weak witness
is included explicitly to avoid turning syntactic key nonidentity into a
substantive resident claim.

## 4. Correlated FHE public keys/ciphertexts are an independent seam

[DERIVED] FE can encrypt a message that is an FHE secret key. Cross-scheme
nesting alone is not an automatic circular-security violation. The question is
whether the intended hybrid can be embedded with a common joint auxiliary
package and with (U). A reduction that samples both `s0,s1` can retain public
material derived from either in the *same* `AUX`; the source does not require
that auxiliary material be statistically independent of these messages.

[DERIVED failed dummy-key proof] Keep `pk,evk,c_history` fixed and switch the
FE capsule from the genuine HE secret to a dummy key. Unless the two resulting
gates agree on every accepted tuple, (U) fails. If instead one regenerates
`pk_b,evk_b,c_history,b` to match `s_b`, the surrounding public package changes
with the FE challenge bit. The above one-challenge FE reduction cannot simply
supply that unknown-bit-dependent package. A separate joint hybrid is needed.
Public keys being individually well distributed proves neither compatibility
nor the cross-scheme joint claim.

[DERIVED failed standalone FHE proof] Keep the FE plaintext equal in the two
worlds and appeal to FHE IND-CPA for the learned state. An ordinary FHE challenge
reduction receives `pk,evk` and a ciphertext but not `sk`; it cannot manufacture
`MIFE.Enc(EK1,sk)` by invoking FE encryption on an unknown plaintext. Postulating
that it can is exactly the additional key-dependent auxiliary/release interface
needing proof. FHE evaluation-key security covers only the auxiliary objects
included in that FHE theorem, not arbitrary secret-key capsules.

[OPEN exact missing primitive game] A distribution-specific capsule theorem
would give an efficient simulator for the exposed `(EK2,K_G,C_key)` jointly
with the actual `(pk,evk,c_history,AUX)`, without `sk`, using only the fixed
receipt-gated decryption oracle. Its input/query bounds, auxiliary correlations,
honest/corrupted signer roles and permitted signatures must be explicit.
The ideal oracle includes every already obtainable valid receipt and replay;
it cannot hide answers the real host is authorized to compute. This is a
restricted simulation/VBB-style requirement for this gate family, not supplied
by generic IND syntax.

[SOURCE boundary] The source's Theorems 15 and 17, printed pp.18,21, give SIM
only for `t=0`. Theorem 21, pp.23–24, explains why general two-input SIM with
one public slot gives general VBB; Theorems 22–23 cover the corresponding
general-function impossibility even with one nonadaptive key. These statements
prevent importing a generic missing SIM theorem. They do not rule out the
specific receipt-gated family or distribution just described.

[DERIVED nonvacuity obligation for the application] A resident privacy game
must separately supply two reachable histories with equal permitted outputs
and different protected predicates. For example, an abstract state `(a,h)`
with `Learn(u,v):(a,h)->(a xor u,h xor v)` and `Infer():a` has related states
`(0,0)` and `(0,1)`, equal adaptive traces and different `h`. This witnesses a
nonempty ideal relation and genuine evolving hidden state, but is not an FE
implementation or utility result. Equality of outputs only on one already
selected receipt list is weaker than (U), and the missing game must justify
that change rather than assume it.

## 5. Targeted source results: one actual repair, with limits

[SOURCE: SWE definitions and proof read] Avitabile et al., 2024/1477 (local
September20,2024 version), Definitions 19–22 printed pp.13–14, encrypt a fixed
message `m` under a reference tag `T` and signature verification keys `V`.
A threshold of valid signatures unlocks `m`. The selective game fixes the
challenge tag and corrupted positions before key generation; permits signatures
on other tags before and after challenge; and prohibits an honest signature on
the challenge tag. Theorem 3, pp.17–18, lists its full suite: strongly puncturable
signatures, an index-hiding/somewhere perfectly binding hash, TM iO, correct
IND-CPA symmetric encryption with pseudorandom ciphertexts, PRF and puncturable
PRF. This is not a theorem from ordinary signature unforgeability alone.

[SOURCE: crucial repair] Definitions 14–17, printed pp.11–12, distinguish
strong puncturing from ordinary puncturing: for the punctured verification key,
with overwhelming probability **no** signature verifies on the punctured tag.
The proof on p.18 changes honest verification keys to that distribution using
punctured-key indistinguishability, then conditions away the bad event before
using exact machine equivalences. Other-tag signatures remain supported.
Thus this source actually supplies the missing *kind* of computational-to-exact
hybrid in its own selective fixed-message setting.

[DERIVED exact narrow positive] Fix `n=2,t=1`, a target tag `T*` selected before
signature setup, and no corrupted signing key. A capability initializer samples
equal-length candidate capabilities `K0,K1` independently of signing secrets,
retaining any efficiently generated common auxiliary data. Deploy
`W <- SWE.Enc(V,T*,K_b)` and erase the plaintext chosen capability and its
copies. By Definition22/Theorem3, `W` hides the choice from a host with the
public package and signing access on other tags. By Definition20, a valid
signature on `T*` later recovers the chosen capability. The `t<n` restriction
in the printed security definition is respected by this minimal witness.
The conditional statement applies to any polynomial-size fixed secret
capability, not just a random token. Distinct tags can genuinely authorize other
successful releases while `T*` stays hidden; that is a nonvacuous positive.

[DERIVED bounded library extension] For a polynomial-size, predeclared library
of distinct tags and known fixed capabilities, public encryption lets the
reduction generate all other wrappers and answer permitted other-tag signatures.
A selective challenge at one unopened tag remains hidden under the same source
game, including already opened other wrappers. A hybrid across `J` specified
unopened entries costs the sum of their `J` distinguishing gaps. Capability
correlations must be sampled by that reduction and included in its retained
state; signer-secret-dependent capability generation is not covered for free.
There is no claim of secrecy for an entry after its own unlocking signature.

[DERIVED decisive limitation] Choosing `K=HE.sk` makes honest unlocking release
a full reader. Choosing `K` to be a source-proved restricted FE key can preserve
only that key's own allowed functionality. SWE does not compile `DecBounded`
into such a key, generate unknown future answers, or bind an already issued
unrestricted span credential to one ciphertext after the fact. The fixed tags
also need a policy linking their signatures to the exact intended event;
adaptively chosen receipt-body hashes are not the source's preselected tag.
This is a candidate ingredient for a finite preauthorized capability library,
not a completed evolving FHE capsule. No PQ or concrete efficiency claim is made.

[SOURCE/DERIVED public-input FE] Nguyen–Phan–Pointcheval, 2024/740, §3.1
Definitions3–6 printed pp.14–16, binds public attributes `z_i` during
`Enc(ek_i,x_i,z_i)`; they are not arbitrary fresh inputs to an already issued
capsule. Its exact existential inadmissibility condition is still semantic,
not an efficient-reachability test. The constructed class is bounded inner
products plus LSSS access control (Definition2 p.14, §1.1 p.7, Corollary13),
under pairing/ROM assumptions. It supplies neither general FHE decryption nor
a signature-verification receipt circuit. Moving the receipt to a corrupt
publicly issuable slot returns the replacement obligation. No break is claimed.

[SOURCE/DERIVED lockable follow-up] Kluczniak, 2021/1324, Definition5 pp.13–14
and Theorem2 p.16, retains distributional lockable security and a fixed released
message. Its introduction pp.4–5 still conditions target entropy on the circuit
and auxiliary input. A known accepting input predicts that target given the
full circuit, as the existing `../../lockable_gate/README.md` proves. This new
assumption/construction route does not repair that audited premise failure.

[SOURCE/DERIVED conditional-FHE source] 2025/045 §5 Definition2, printed
pp.23–24, has `HECD.Dec(sk,st,proof,inputs,output)` and states that verification
and decryption can be embedded in a GC. AppendixB pp.28–29 describes an
input-specific FE encryption producing a fresh FHE key, GC and ABE-delivered
labels. These inspected algorithms do not instantiate this lane's permanent
public receipt-slot capsule after all master erasures. A GC sentence is not a
complete reusable public label-issuance or all-software-exposure theorem.
No conclusions about that paper's experiments are used here.

## 6. Handoff

[DERIVED maintainer proposal] Keep the unfinished-capsule row as **source-game
mismatch verified; concrete algorithms and missing joint simulation game now
specified**. Add SWE only as a source-conditional fixed-capability release lead.
No current VERDICTS theorem, DDH result or instantiated PQ claim changes.
In particular, the designated DDH construction still exposes recipients' entire
per-input fixed span; absence of a scalar master is not absence of full semantic
read authority when that span determines the semantic image.

[OPEN next decisive work] Either instantiate the restricted capsule game with
a full correlated-key proof, or choose a finite restricted capability library
whose lifetime union remains within the intended output interface, then map
its exact tags/corruptions to SWE. The public-input FE and lockable sources
inspected here do not close the first route. Corpus/search counts, hashes and
precise access levels are in `SOURCES.md` and `SOURCE_MANIFEST.json`.
