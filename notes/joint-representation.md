# The joint representation problem — the rock nobody turned over

2026-08-13. Computed here, not sourced. The single-prime idea generalizes
into something bigger, and a first search says the constraint space is
*comfortable*, not tight.

## The structural observation

FHE people choose moduli for RNS efficiency and noise budget. Proof people
choose fields for NTT domains and soundness. **They are different
communities, they publish in different venues, and the two choices are made
independently — so nobody has ever posed the joint optimization.** Zama's
2026/027 and GBFV each grazed it from one side (make the ciphertext modulus,
resp. the plaintext modulus, a known proof prime), but both took an
*existing* proof prime and asked FHE to live with it. Nobody has run the
search in the other direction: **choose the algebraic representation to
satisfy both sets of constraints at once.**

The decision variables are not just the prime:
- **the prime** p — size (noise budget), 2-adicity (both NTT and FRI
  domains), algebraic form (reduction cost), ord_p(2) (twiddle cost)
- **the ring** — cyclotomic conductor (power-of-two vs Φ_{3^k} vs other);
  this is where today's `CyclotomicInertia` theorem already lives
- **the encoding** — coefficient vs slot vs hybrid (decides whether
  rotations are needed at all)
- **the plaintext modulus** t — decides nonlinearity degree, batching,
  transcipher compatibility
- **the limb structure** — RNS tower vs single prime

## First search result (computed, 2026-08-13)

Searching Solinas-form primes `2^a − 2^b + 1` for a ∈ [96,130]:

**93 primes found with 2-adicity ≥ 20**, and many with 2-adicity far beyond
what either side needs (FHE negacyclic at N=4096 needs ≥13; FRI domains want
~25–32). Examples in the exact band the BFV noise budget wants:
`2^108 − 2^50 + 1` (2-adicity 50), `2^109 − 2^58 + 1` (58),
`2^109 − 2^65 + 1` (65), `2^113 − 2^32 + 1` (32).

**So the joint constraint is not tight — it is comfortable.** The reason
nobody has a single-prime BFV/proof modulus is not that the number theory
resists; it is that nobody asked. That is the rock.

## Honest negative, found in the same search

**The Goldilocks barrel-shift twiddle trick does NOT transfer to this size.**
Zama's HPU NTT has no multipliers because ord(2) = 192 in Goldilocks makes
ω a small power of two. That needs *small* ord_p(2); at ~109 bits every
candidate's ord_p(2) is astronomically large (the shift exponents come out
at 10^25+), so pure-shift twiddles are structurally unavailable. What Solinas
form *does* still buy is cheap reduction — twiddle multiply becomes
shift-plus-Solinas-fold rather than a general modmul. Real, smaller, and
worth stating before anyone promises the Zama trick at 109 bits.

## Why this is ours to do

Two assets nobody else has pointed at this:
1. **Lean can turn a search result into a theorem.** Today's
   `Theory/CyclotomicInertia.lean` is the template: a representation choice
   (KoalaBear × Φ_{3^k}) whose consequences (irreducibility ⇒ field ⇒
   maximal inertia) are *proved*, with the failing cases exhibited as teeth.
   A joint-representation result should ship the same way — the parameters
   AND the proofs that they have the claimed properties.
2. **We hold both sides of the boundary**: a deployed BFV stack and a
   formalized proof system. Everyone else holds one and treats the other as
   an interface.

## The ambitious framing

Not "pick a better prime." **Pose and solve the joint algebraic
representation problem for verifiable homomorphic computation, and publish
the parameters with machine-checked proofs of their properties.** That is a
paper nobody can write without both halves, and it is upstream of every
performance number in the vFHE literature — because every one of those
numbers is paid on a representation somebody chose for one side only.
