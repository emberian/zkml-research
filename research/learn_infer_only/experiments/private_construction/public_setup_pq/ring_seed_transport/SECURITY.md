# The public-seed computational obligation

[DERIVED] Fix a public binding b and a deterministic successful expansion
E(s, b) with m residues modulo q. The pair `(s, E(s, b))` is efficiently
distinguishable from `(s, U)`, with U independent uniform: recompute E and
compare. The acceptance probabilities are1 and q^-m. At fixed binding a
short seed also has far too few possible outputs for statistical uniformity.
Neither exact rejection nor ordinary hidden-seed PRG security removes this
obstruction. Concrete SHAKE outputs are public deterministic values.

[DERIVED actual chronology] This implementation honestly samples an A seed
and setup identifier before fresh recipient registration. A's expansion
domain fixes parameters and the recipient policy. The explicit products are
then fixed. A separate absent-row seed is sampled afterward, bound to the
exact registry digest and A descriptor. There is no circular dependency and
no executed seed search or grinding. This is the implemented chronology;
malicious seed/registry selection is not covered by it.

[HYPOTHESIS intended computational model] One possible route models the
address-separated XOF as an ideal programmable random oracle, with all
repeated queries answered consistently, and treats concrete SHAKE256 as
its computational instantiation. SHA256 context/registry digests additionally
need an appropriate collision-resistance assumption. These hypotheses are
separate from conventional uniform-matrix Ring-LWE. They are not themselves
a completed reduction for this functional-encryption construction.

[OPEN full joint reduction] Such a reduction must preserve the A seed,
registry, absent seed, all reconstructed rows, exposed recipient rows and
the entire oracle transcript together. It must embed a suitable Ring-LWE
challenge and justify the Gaussian setup/mask transitions consistently with
the publicly recomputable values. It must account for pre-disclosure queries,
later recomputation, adaptive transcript selection, rejection/cap failure,
and honest registry dependencies. A quantum-adversary or quantum-advice
claim needs the corresponding QROM programming/query bound and matching
advice class. A classical lazy-sampling explanation is insufficient.

[DERIVED important missing-row distinction] Merely assuming seeded Ring-LWE
for A does **not** justify replacing a missing public row
`P_i=Expand(seed_missing, registry, i)` by `Z_i*A` while preserving the
unprogrammed seed. The verifier can recompute the row from that seed. Even
a rank/smoothing statement about seeded A does not repair this inconsistent
joint distribution. The original absent-master proof's full-Gaussian setup
hybrid needs its own consistent oracle simulator or a new direct proof that
avoids this replacement. We do not state an impossible statistical joint
uniformity assumption as a substitute.

[SOURCE context only] The existing
[public-seed designated proposal](../../designated_span/public_coin_setup/public_seed/PROPOSAL.md)
explicitly works in a **classical programmable-ROM** DDH setting, with
registry chronology and rejection tapes, and excludes concrete-hash/QROM
transfer. We read its opening and §§1–3 as context. Its square-root/DDH
simulation is not a ring construction theorem and is not imported here.

[DERIVED limited ideal-XOF fact] The expander's exact masking/rejection
algorithm gives independent uniform accepted residues only when distinct
chunk addresses are assigned independent ideal random words. Its finite
cap raises an error without a substitute row. Under that idealization the
saved expander note bounds row failure below 2^-5461; a complete game must
charge failures rather than silently condition them away. This is not an
unconditional probability bound over fixed SHAKE256 seeds. The exact domain
and proof of that limited fact are in `expansion/SECURITY.md`.

[EXECUTED/OPEN] The engineering result is a40.057 x smaller public issuer
bundle and successful end-to-end role-separated computation. It supplies
neither the reduction above nor a certified PQ/full-privacy guarantee.
