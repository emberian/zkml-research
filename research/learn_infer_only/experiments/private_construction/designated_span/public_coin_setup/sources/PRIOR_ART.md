# Public accepted-coin setup: bounded source comparison

**[DERIVED: scope]** The closest inspected literature supplies two relevant
ingredients: linear-share simulation in decentralized FE, and public group
sampling with efficiently samplable preimages. It does not supply the proposed
fixed-row public-key completion as a quoted FE construction theorem. This note
makes no novelty claim and leaves the proposal's independent mathematical
review to its assigned reviewer.

**[SOURCE: local input]** The target is [PROPOSAL.md](../PROPOSAL.md), observed
SHA-256 `4d30d6013642666081ebecfbcc4dbb0446afeda1e58d94f294202507a20f71c9`.
All four external papers below were read from local mirror PDFs. Exact paths,
hashes, page locations, access levels, and search counts are in
[sources.json](sources.json). No cryptographic runtime, attack experiment,
implementation change, or malicious-setup claim was made in this audit.

## Target and comparison criterion

**[SOURCE: proposal, “Scope and order” through “Exact joint distribution argument”]**
The target fixes a full-row-rank `m×d` matrix `Y`, `m<d`, and a static recipient
coalition before honest independent recipient keys `A_i=g^{a_i}`. After
registration it publishes independent accepted values `τ_i∈F_q` and
`U_j∈F_p*`, where `p=2q+1` is a safe prime. With `B_j=U_j²`, it completes `h`
in the group so that `∏_j h_j^{Y_ij}=A_i g^{τ_i}`. Encryption remains public.
The constructor never computes `log_g B_j` or a scalar vector `s`. A recipient
can compute only its own authorized projection scalar `a_i+τ_i`, subject to
the stated span leakage and full-coalition qualifications.

**[DERIVED: distinctions]** A matching initialization theorem would need to
account jointly for the public recipient keys, the exposed recipient secrets,
and the full accepted-coin transcript. Three weaker facts are insufficient by
themselves: the setup syntax omits a variable named `msk`; no single party
holds all distributed issuer keys; or the public output is marginally uniform
when sampler coins are hidden. The proposal specifically includes accepted
`U` values in the adversarial view and does not hide a writer credential.

## 1. Chotard et al.: decentralized secret writers and shared key generation

**[SOURCE: algorithms and game]** Chotard–Dufour Sans–Gay–Phan–Pointcheval,
*Decentralized Multi-Client Functional Encryption for Inner Product*,
[ePrint 2017/989](https://eprint.iacr.org/2017/989), ASIACRYPT 2018.
Definitions 4–5, PDF pp.9–10, specify sender setup, private encryption keys,
partial function keys, and corruption. In §5.1, PDF p.15, sender `i` samples
`s_i∈Z_p²`; the parties interactively obtain matrices `T_i` with `Σ_i T_i=0`.
It retains `ek_i=s_i` and `sk_i=(s_i,T_i)`. Encryption uses a label hash into
the group and `s_i`; function-key shares mask `y_i s_i` using `T_i` and a second
group hash. Theorem 9, PDF p.16, proves static-corruption security under SXDH
in the random-oracle model, while permitting adaptive encryption queries.
This is the exact theorem inspected, notwithstanding broader abstract wording.

**[DERIVED: comparison]** This removes the central function-key issuer by
distributing secret state among senders. It is not public-key completion from
accepted public field coins. Publishing all sender keys exposes the machinery
for producing all function-key shares. Its corruption game correspondingly
requires equal challenge plaintexts at every corrupted sender; it does not
claim nontrivial hidden inputs after every sender is corrupted. The proposal's
recipient scalars are fixed-row release capabilities, not these sender keys.

## 2. Abdalla et al.: a close linear simulator, with a different setup game

**[SOURCE: syntax, compiler, reduction]** Abdalla–Benhamouda–Kohlweiss–Waldner,
*Decentralizing Inner-Product Functional Encryption*,
[ePrint 2019/020](https://eprint.iacr.org/2019/020), PKC 2019.
Definition 2.4, PDF p.12, has no named master key but explicitly does not
require its setup definition to be decentralized. `KeyGen` outputs private
client keys, and `Enc` takes one. Definition 3.1, PDF p.14, requires special
linear key derivation. Figure 3, PDF p.15, adds secret mask vectors
`v_i∈Z_L^{mn}` with `Σ_i v_i=0`; partial keys contain
`<u_i,y_{i,f}>+<v_i,y_f>`. Theorem 3.2 preserves the underlying MCFE security
notion with no advantage loss. Its proof on PDF p.16 simulates linearly
independent queried values by additive sharing; dependent values follow their
linear relations. Definitions 2.3/2.5 govern corruption and valid challenge
pairs, PDF pp.10–12.

**[DERIVED: what carries conceptually]** This is close prior art for reasoning
about the *whole correlated key package* by a change of variables and linear
constraints. It is stronger evidence than an abstract promise of
decentralization. Theorem 3.2 applies to its specified MCFE compiler, however;
its no-loss bound cannot simply be copied onto a different public-key setup.
The proposal still needs its own joint-distribution lemma.

**[DERIVED: capability boundary]** The existence of private client keys remains
load-bearing: collecting them permits the complete key-derivation procedure
for new functions. Removing an explicit `msk` output does not establish a
fixed-span restriction on the complete surviving credential coalition. This
does not criticize the source model; its corruption game scopes that exposure.

## 3. Fan–Tang: distributed decryption shares retain ordinary master setup

**[SOURCE: algorithms and game]** Fan–Tang, *Making Public Key Functional
Encryption Function Private, Distributively*,
[ePrint 2018/250](https://eprint.iacr.org/2018/250), PKC 2018.
Section 3.1, PDF pp.8–11, splits each functional key into shares whose partial
decryptions reconstruct the function value. Its syntax still outputs
`(pp,msk)`. The concrete §3.3 setup, PDF p.14, calls ordinary `FE.Setup` and
sets `DFE.msk=FE.msk`. Definition 3.5, PDF pp.10–11, gives complete shares for
queried functions subject to equal challenge outputs. Theorem 3.11, PDF p.16,
reduces data privacy to the underlying FE. The introduction, PDF p.3,
expressly distinguishes distributed function shares from decentralizing
master-key generation.

**[DERIVED: comparison]** Public encryption and distributed evaluation do not
by themselves eliminate private master-key construction. This source is useful
for separating the three notions, but its displayed setup does not implement
the proposal's no-scalar-master execution.

## 4. Brier et al.: an exact precedent for the public-root transcript technique

**[SOURCE: definitions and reduction]** Brier–Coron–Icart–Madore–Randriam–Tibouchi,
*Efficient Indifferentiable Hashing into Ordinary Elliptic Curves*,
[ePrint 2009/340](https://eprint.iacr.org/2009/340), full version of CRYPTO 2010.
Definition 1, PDF p.4, recalls the Boneh–Franklin criterion: an efficiently
computable regular `ℓ`-to-one map with efficient uniform preimage sampling.
Definition 4, PDF p.6, generalizes this to statistical regularity/sampling.
Theorem 1, PDF pp.7–8, compares the joint systems `(F∘h,h)` and `(H,S^H)`;
the simulator answers lower-level hash queries by sampling a preimage of the
ideal group output. Its loss is `4Qε`, with simulator time `2Q t_I`. The
introduction, PDF p.3, explicitly distinguishes hashing into a group from
hashing to a scalar and multiplying a fixed generator: the latter exposes
the discrete-log relation.

**[DERIVED: exact instantiation of the encoding criterion]** For the proposal,
take `S=F_p*`, `R=QR_p`, and `F(U)=U²`. Every `B∈QR_p` has exactly two roots.
As `q` is odd, a uniform preimage sampler is

```
v = B^((q+1)/2) mod p
I(B) = v or −v, with an independent fair sign.
```

Thus the *encoding* meets the recalled criterion with `ℓ=2` and zero
statistical error. More directly, for every legal pair `(U,B)` satisfying
`U²=B`, both sampling orders assign it probability `1/(2q)`:

```
U uniform in F_p*, then B=U²;
B uniform in QR_p, then U uniform in F^−1(B).
```

**[DERIVED: relevance and limit]** This is a precise literature-backed
framework for the proposal's simulation of revealed accepted coins; it
addresses the joint pair, not only the marginal `B`. The finite-transcript
equality above is elementary and does not require assuming a random oracle.
The source's random-oracle theorem can support an appropriately specified
hash-to-group variant, but it is not a theorem about a concrete hash,
OS-generator seed, public beacon, adversarial grinding, or arbitrary setup
software. Those changes alter the transcript or its distribution and require
a separate argument.

**[DERIVED: assumption accounting]** For the proposal's exact accepted-coin
model, exposing `U` need not introduce a separate unknown-log hardness
assumption: `U` is efficiently simulatable from `B` with its exact conditional
distribution. The claimed FE privacy still rests on the original DDH game,
the proposal's full-key-package coupling, and honest independent sampling.
“No scalar master was computed” is an algorithmic statement; impossibility of
recovering one is computational and is not proved by public recomputation of
the setup equations alone.

## Conclusion and bounded next evidence

**[DERIVED]** The appropriate attribution is a local public initialization
lemma for the designated fixed span, related to established linear-share
simulation and regular preimage-samplable group encodings. The inspected
decentralized/distributed FE constructions solve different credential-placement
problems. No source theorem here supplies arbitrary malicious setup security,
a trusted beacon, or a novel-construction claim.

**[OPEN: bounded search scope]** This audit inspected four primary local PDFs,
following two OpenAlex/Scry queries and five focused metadata searches. It did
not survey all distributed FE or all setup ceremonies. No exact publication
of the full `Y=[Y_p Y_f]` group-completion recipe was identified in this scope;
that observation is not evidence of novelty.

**[DERIVED: next evidence]** Keep the independent review of the proposal's
complete public-coin coupling as the immediate proof obligation. If setup
later uses a concrete beacon or hash-derived seed, specify that complete
transcript and its selection rule before applying an encoding theorem.
