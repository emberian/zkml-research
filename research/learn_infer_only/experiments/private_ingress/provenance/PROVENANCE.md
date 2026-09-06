# Proof-bound provenance inside a private transition

[OPEN collection status] The usage interruption stopped final review/packaging.
The parent reconstructed the five-source manifest from exact retained extracts
and saved the executed controls. This remains a sourced/derived candidate audit,
not an independently accepted private-construction proof.

[DERIVED decision; 2026-09-06] A public proof-generating key can replace an
unrestricted state-signing credential at the **capability** level. An internal
guard requiring a binding state opening and valid descent proof rejects the
chosen-state reader from `PRIVATE_INGRESS.md` when the allowed prefix has only
the fixed genesis state. Ancestry alone is insufficient when valid alternative
histories reach chosen offsets. Binding each private observation to the exact
parent state commitment removes that particular cross-history probe in the
executed ideal model. Neither result instantiates encryption or zero knowledge.

[DERIVED decision] The closest primary FE+NIZK compiler proves a useful
consistency/privacy composition, but returns the base function key unchanged;
its public verification wrapper can be bypassed by the hostile key holder.
Verifiable MIFE exists at the source, with a deterministic exact-output game
and a restricted circuit family. Neither inspected theorem establishes the
randomized, encrypted-output, provenance-preserving resident transition.
The earlier rMIFE epsilon obstruction survives adding proofs, and a
commitment/guard-preserving privacy hybrid is an additional missing premise.

[DERIVED scope] Fixed H=2, honest initialization/erasure, all deployed host
artifacts and issued transition/future keys exposed. Private observations
originate outside the host. This tranche preserves earlier ingress artifacts,
does not increase the horizon, and edits no shared ledger or companion tree.

## 1. A concrete two-input layout without a secret state signer

[HYPOTHESIS candidate] Use a binding, hiding commitment `Com`, an adaptively
secure zero-knowledge argument `(ProofSetup,Prove,Verify)` for a bounded NP
relation, and the independent-layer rMIFE syntax already audited. Setup fixes
the actual genesis commitment G, intended transition policy/version, proof
parameters, epoch schedule and input authorization policy. The proof prover
key PK and verifier key VK are public. Raw simulation/extraction/equivocation
trapdoors, if the chosen setup generates any, are erased rather than deployed.

[DERIVED fixed-H=2 layout] Carry the full bounded history witness privately
for this test. This avoids assuming a recursive proof theorem simply to write
the first construction. A state ciphertext encrypts `(s_i,r_i,H_i)` where
`C_i=Com(s_i;r_i)` and H_i contains the genesis opening and the at-most-two
transition witnesses needed to prove descent. Public state metadata is
`(G,epoch_i,C_i,pi_i)`. An observation issuer receives that public metadata and
encrypts `(x_i,G,epoch_i,C_i,pi_i,authorization_i)` in the observation slot.
Its parent C_i is inside the protected observation message. This binds the
fresh input to a particular state commitment; a free host-supplied label is
not substituted for that field.

[HYPOTHESIS exact guarded function] Each preissued transition function does:

```text
F_i((s,r,H), (x,G_claim,i_claim,C,pi,auth); coins):
    require G_claim = G and i_claim = i                 # literals in F_i
    require Verify(VK, (G,policy,i,C), pi) = accept
    require Com(s;r) = C
    require InputAuthorized(G,policy,i,C,x,auth)        # precise named predicate
    (s_next,answer) = Step_i(s,x)
    choose fresh commitment/encryption/proof coins from the rMIFE coin string
    C_next = Com(s_next;r_next)
    H_next = Extend(H,s,r,x,auth,s_next,r_next)
    pi_next = Prove(PK,(G,policy,i+1,C_next),H_next)
    ct_next = Enc(EK[i+1,S],(s_next,r_next,H_next))
    return (ct_next,C_next,pi_next,answer)
```

[DERIVED] The bounded relation verifies the genesis opening, each permitted
transition, input authorizations and the opening of the terminal commitment.
If an authorization names a parent, it names the same commitment verified in
that transition. For honest evaluation, H_next is available inside F because
H, the current opening and the fresh observation are plaintext inputs there.
The sensor sees neither state nor H. Proof generation requires computation and
a valid witness, not a state-certifying secret.

[DERIVED layout detail] The new proof is public metadata, not part of the
payload whose encryption it would itself certify. This avoids making
`pi_next` depend on a ciphertext containing `pi_next`. The next observation
slot carries the public proof back into the two-input function. The displayed
relation binds a semantic state commitment. It does not bind unique
ciphertext bytes, finality, an external release recipient, or a current-head
service. Re-encrypting the same committed state remains the same semantic
parent. A relation requiring byte-level ciphertext linkage needs its own
noncircular serialization and input-binding proof.

[DERIVED] PK, VK and G may appear in the public function description without
granting arbitrary certification. The crucial checks must be **inside F**.
A publicly mutable wrapper which checks the proof and then invokes an
unguarded issued function key is not this candidate. The erased FE masters
and protected history/openings remain exactly where the FE confidentiality
theorem is needed; an internal guard is not by itself an obfuscation theorem.

## 2. Exact semantic positives and failures that ran

[EXECUTED] Command and complete results are kept in `provenance_audit.stdout.txt`
and `results.json`, including source hash and Python/platform:

```sh
python3 research/learn_infer_only/experiments/private_ingress/provenance/provenance_audit.py
```

[EXECUTED] The code uses explicit ideal commitment/proof registries. It
implements no encryption, signature, hiding commitment, NIZK or SNARK. A
verified proof token is an ideal relation certificate, not a cryptographic
artifact. The private parent field is an ideal immutable observation field;
the tests do not prove an actual ciphertext's nonmalleability or authentication.

[EXECUTED fixed-prefix positive] Genesis is byte state 0. The first of two
transitions preserves state; the second ingests private x by addition mod256,
followed by a high-bit read. A public prover can certify state 0 after the
first transition. All 255 other byte-state witnesses are refused because
they do not satisfy descent. Copying an honest proof onto each of those 255
wrong openings is also refused. Unknown observations x=0 and x=1 have the
same authorized high-bit answer while causing distinct retained next states.

[EXECUTED wrapper falsifier] Disabling the check inside the function, while
retaining the proof objects, lets the base function key recover all 256
observations in eight chosen-offset probes each. This is precisely the
hostile-wrapper issue; the outer proof still exists.

[EXECUTED ancestry-only falsifier] Change the first transition to a Learn that
may ingest any authorized known byte. Every offset now has an honestly
provable history from genesis. The host proves each chosen prefix, pairs it
with the same fresh observation at the second transition, and recovers all
256 observation values in eight probes. All ancestry proofs in this attack
are true. Descendance from G must not be confused with being the particular
parent that the observation was authorized to enter.

[EXECUTED parent-binding positive] Binding the fresh observation to its
specific parent commitment rejects all 256 independently certified alternative
parents, including a fresh commitment to the same plaintext state. The
intended parent accepts. This removes this cross-history path while allowing
public proving and public state encryption. It does not establish security
against every mixed-input attack, ciphertext manipulation or issuer corruption.

## 3. The alternate signing credential really is different

[DERIVED capability audit] Suppose “valid state” instead means a signature
under a state-certificate verification key, and an unrestricted signing key
survives. The coalition holding that signing key, public state EK, a hidden
observation ciphertext and the issued transition/future keys can sign an
arbitrary chosen-state commitment as eligible. Without an immutable
observation-to-parent binding, that reinstates the eight-probe reader. No
state decryption key is used by the path.

[EXECUTED] The model recovers all 256 observations with this unrestricted
state-signing capability. This demonstrates a reader-enabling **coalition
capability**, not that signature secret keys directly decrypt ciphertexts.
In contrast, the public Prove interface rejects false descent witnesses.

[DERIVED scope] A commitment-bound parent field can still block this path
even if the state signer is exposed: signing a different state commitment
does not create another opening of the observation's existing parent. The
signer attack is therefore explicitly recorded **without that parent binding**.
Exposure of an authority that can also reauthorize/rebind an unknown input to
chosen parents would need an additional coalition audit. A protected program
containing the unrestricted signer is not justified by renaming its raw secret
to a “prover key”; it needs a theorem restricting that exposed program.

[DERIVED trapdoor audit] Public prover parameters are not automatically a
simulation or extraction trapdoor. If a retained trapdoor actually produces
accepted **false provenance** certificates, it has the same certification
capability in the ancestry-only model; that conditional path also recovers
all 256 observations. Not every ZK definition guarantees a simulator that can
prove false statements under an honest CRS, so this is an explicitly modeled
capability, not a universal claim about ZK simulators. A straight-line
trapdoor that recovers state/opening witnesses from retained public proofs
would be a reader directly. A rewinding extractor in a reduction is not
automatically such a deployed per-proof credential.

## 4. What the primary verifiable/consistent FE theorems actually prove

[SOURCE: construction/game/reduction read] Badertscher–Kiayias–Kohlweiss–Waldner,
[Consistency for Functional Encryption](https://eprint.iacr.org/2020/137),
§6.1 printed pp.28–32, Figures 14–15, gives an actual FE+NIZK compiler:
the ciphertext is `(ct,pi)` with a proof of `exists x,r:ct=Enc(mpk,x;r)`;
`KeyGen'` returns the base `sk_f` unchanged; public `Dec'` verifies pi before
calling the base decryption. Theorem 6.1 bounds input inconsistency by NIZK
soundness. Its stated Extract algorithm always returns `unknown`.

[SOURCE] Theorem 6.2 p.31 proves CPA privacy preservation with the bound
`Adv_compiled <= 2 Adv_ZK + Adv_FE`. Lemmas 6.3–6.4 pp.31–32 first simulate
the CRS/proofs, then switch the base FE challenge, then restore honest proofs.
Theorem 6.5 pp.32–33 similarly preserves a separately assumed composable-FE
notion. These are actual composition arguments, not a slogan that proofs
preserve privacy.

[DERIVED exact mismatch] Their predicate is membership in the encryption
algorithm's range. It is not descent from a resident genesis. More decisively
for forced mediation, the hostile holder has the unmodified base key and can
invoke base Dec directly on ct. The consistency theorem concerns the defined
decryption algorithm and correctness for its receiver; it does not make
proof verification unbypassable for the exposed-key adversary. Instantiating
the base function with the **internally guarded** F above changes the
load-bearing function/game and still requires its FE privacy proof.

[SOURCE / DERIVED composability limit] Definition 2.5 pp.6–7 specifies CFE
for single-input deterministic f. Theorem 7.2 pp.52–53 gives a static-corruption
UC repository realization under appropriate CFE/consistency/extractability
premises, with an input provider that knows the plaintext and a manager
retaining the master and issuing function keys. It does not instantiate a
randomized two-input transition returning encrypted state, or justify
post-erasure corruption of the complete resident package. The name
“composable” does not remove those premises.

[SOURCE: complete relevant MIFE appendix read] Badrinarayanan–Goyal–Jain–Sahai,
[Verifiable Functional Encryption](https://eprint.iacr.org/2016/629),
Appendix D pp.35–37 and Appendix G pp.53–56, supplies genuine verifiable-MIFE
algorithms, a mixed-input game and a construction. Definition 12 ensures
verified ciphertexts and keys give functional outputs consistent with input
plaintexts even for malicious public parameters/keys. Definitions 13–14
retain exact I-compatibility for all stored/replaced input combinations.
Theorem 8 p.56 is selective, deterministic, and for the special family Feq:
whenever two partially fixed residual circuits are equivalent, there must be
an efficiently sized equivalence witness (Definition 15 p.54).

[DERIVED] The candidate randomized encrypted-output function is not covered
by that theorem as stated. No Feq membership witness or randomized extension
for this guard was constructed. Public VerifyK checks a key relative to its
specified f; it does not select the intended policy/genesis for an adversary.
Neither its exact-output game nor its NIWI proofs import the 2013 rFE
pre-setup computational-output theorem into two inputs.

[SOURCE: syntax/privacy game read] Nguyen–Phan–Pointcheval,
[Verifiable Decentralized Multi-Client FE for Inner Product](https://eprint.iacr.org/2023/268),
§4 Definitions 8–9 pp.12–15, goes further on input predicates: encryption
and verification name a polynomial-time message predicate, and the IND game
requires **both** challenge values to satisfy that predicate. It also binds
ciphertexts to labels, permits one challenge query per client/label and
requires equal challenge values for corrupted issuers. Its construction is
range-verifiable inner-product MCFE with private issuer encryption keys,
not the required arbitrary randomized state transition. This is useful
source evidence that validity requirements belong in the privacy game's
challenge condition, not a realization of the resident repair.

[SOURCE: exact scope read] Géraud–Naccache–Roşie,
[Robust Encryption, Extended](https://eprint.iacr.org/2019/238), §3.2 pp.11–12,
Definition 5, addresses accepting ciphertexts under functional keys derived
from different master authorities. That robustness does not restrict a
correctly issued ciphertext of an unauthorized state under the correct EK.
It supplies no descent predicate or private-state closure theorem.

## 5. The first missing privacy reduction premise

[DERIVED inherited obstruction] In the actual 2025/330 rMIFE game, adding
public commitments/proofs to F's encrypted next-state output does not remove
the first-component ciphertext equality test. For distinct next payloads at
equal parameters its gap remains at least `2^(-lambda_next)`, exceeding
`epsilon_i=2^(-4*s_i-lambda_i)`. An internal provenance guard can reject bad
states and still fail the theorem's randomized-output compatibility premise
on two honest valid states. The previous note's unequal-parameter caveat
continues to apply.

[DERIVED additional hybrid boundary] Even under a stronger suitable rMIFE
theorem, one must prove privacy of the **joint** output

```text
(all exposed future and prior keys, C_i, pi_i, Enc_i(s_i,r_i,H_i)).
```

[DERIVED] A binding C cannot have valid openings to two distinct states.
If a proposed ordinary FE hybrid fixes public C and substitutes the payload
with a different state/opening, the internal opening/provenance guard can
change from accept to reject. The two candidate messages then fail the
required guarded-function compatibility. The executable fixed-commitment
control confirms precisely this acceptance discrepancy in the ideal model.
Zero knowledge of pi alone cannot repair a false **direct opening check**.

[DERIVED] If the hybrid changes C instead, it changes public auxiliary data
and the statements used by future/observation guards. A proof that Com hides
a state from someone without its opening does not by itself establish this
joint distribution when encrypted openings are consumed by exposed function
keys. The standard FE+NIZK compiler above changes neither a hardcoded genesis
nor these input-validity predicates during its FE challenge switch.

[DERIVED fixed-genesis distinction] Comparing two initial roots under the
same binding genesis commitment is particularly sharp: both distinct roots
cannot pass the same opening guard. Using different genesis commitments
instead changes the hardcoded F. Ordinary FE message privacy does not give
privacy between those two function-key descriptions, and ordinary iO applies
to equivalent programs, not arbitrary different genesis guards. This does
**not** rule out the central fresh-input case with one common actual genesis;
different honest observations can produce two valid descendant histories.
That case still needs the joint commitment/proof/encrypted-output argument.

[OPEN exact missing lemma] An acceptable proof would preserve guarded
evaluation behavior across the commitment/proof/ciphertext switch, including
all exposed prior/future keys and every allowed mixed state/observation
combination. A dual-mode/equivocal commitment plus suitable proof simulation
may be a route, but it must name the real/hybrid modes, their indistinguishability,
and the soundness or extraction guarantee after all simulated proofs. A
one-time simulation-sound lemma cannot silently cover unbounded local forks.
Any proof/extraction trapdoor used only by that reduction must remain outside
the real exposure set. No such lemma is asserted by the inspected statements.

[DERIVED recursive scope] The displayed fixed-H=2 construction carries a
bounded NP witness. Replacing it by recursion is additional work: define
which prior proof verifies inside the next relation, bind the exact state
openings/input authorizations at that boundary, and establish the required
recursive soundness and adaptive zero-knowledge properties. The existing
public integrity receipt and its classical ROM theorem do not automatically
provide zero knowledge or a source of private witnesses.

## Status, next, and provenance

[DERIVED status] **Keep the internal proof guard as a concrete capability
repair; do not label it a private resident construction.** Its public prover
key avoids the arbitrary state-certifying authority of an unrestricted
signing key, conditional on the actual relation and proof soundness. Exact
parent binding is essential where alternative true histories are reachable.
The first missing cryptographic step remains guarded, joint encrypted-output
compatibility, not the syntactic availability of a proving algorithm.

[OPEN next] State one same-genesis H=2 privacy lemma for the precise packet
layout above. Fix the authentic input-parent policy and prove its nonvacuity
under every mixed pair. Then attempt the joint commitment/proof/FE hybrid
with every trapdoor and exposed key named. This should precede recursion,
dynamic horizons or claims that verifiable FE completes the resident.

[EXECUTED accounting] This tranche used one Scry SQL query (25 returned rows,
recorded spend 0 nanodollars), no new schema query, four web search queries,
zero Kagi and zero PDF downloads. The Scry record retains the query response,
coverage and freshness; it is not a literature-absence instrument. Five new primary
PDF extracts were retained from the local mirror; the existing 2025/330 read is
registered in the parent ingress source manifest; `source_manifest.json` records
absolute paths, SHA-256, exact access levels and commands. The publicly
auditable-FE PDF 2023/629 received an abstract-only scope check and is not used
for a theorem claim. Full texts are ignored scratch. Prior tranche counts
are unchanged; combined ingress totals are one Scry SQL, six web searches.
