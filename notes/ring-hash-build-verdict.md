# Ring hash: BUILD IT. Delegation is dead, and I guessed wrong about why.

2026-08-13, peer analysis scored against a bar. **This reverses my stated
guess** ("my honest guess is it comes back 'delegate'"). It doesn't, and the
mechanism is one I should have seen.

## Why delegation dies — the reason, not the number

**Delegation pays only when the hash is expensive IN-CIRCUIT. Poseidon-over-R_q
in 1127 is 856 constraints per permutation.** The 6–14× Keccacheck harvests
comes from Keccak-f being 20k–50k R1CS *because it is bitwise*. **1127's bill
is VOLUME (transcript size); delegation attacks UNIT COST.** There is nothing
to harvest.

Second, independent: **the delegated argument's own Fiat–Shamir lands back
in-circuit and is sequential** — one in-circuit hash per sumcheck round,
unbatchable ("168C … on the order of tens of thousands"). Applied to a
30-round Poseidon at 856 R_q constraints/perm: **820k → 1.23M → 2.87M**
depending on sumchecks per layer. Keccacheck's own shape at h=4096 is 2.59M,
**8.6× over the bar.** Delegation loses to *both* our candidates by 3–31×.

⚠ Also: the paper I cited as "2025/1764 Keccacheck" — our local
`ring-r1cs-…-2024-1764.pdf` is **2024/1764, a different paper with zero
"keccak" hits.** And **2026/551's** GKR-for-Poseidon is an Appendix C
sub-component with no benchmarks, whose §4.3 explicitly warns against our
exact use (*"should not be instantiated using Poseidon with the same
parameters … preferably an entirely different hash function"*).

## The scoreboard (bar = in-circuit verifier cost, R_q constraints)

Bar A = 302,141 (beat σ-Poseidon) · Bar B = 92,257 (beat Feistel) · today =
2,417,127.

| escape | in-circuit cost | verdict |
|---|---|---|
| **Symphony 2025/1905** | 65,536–131,072 **whole batch** | **the only TRUE escape** (hash→0), clears bar A by 2.3–4.6×, straddles bar B |
| ProtoGaLattice 2026/1317 | ~483k–720k (derived; paper states none) | 1.6–2.4× OVER bar A — a *reduction of the same bill* |
| 2026/551 | no benchmarks at all | not the paper the brief described |
| Keccacheck-shape → Poseidon | 820k–2.87M | **net loss, 2.7–31× over** |

**ProtoGaLattice's "100 → 4 RO calls" is a 25× cut of the WRONG QUANTITY** —
RO *calls* ≠ sponge *permutations* (~2,650 permutations across ~100 calls).
Sumcheck messages are **2.6%** of their transcript; removing sumcheck, their
whole thesis, cannot touch the other 97.4%. Their own Open Problem #1
concedes it.

## ⚑ The number that ends the argument

At 1127's **benchmarked** config (useful work 2.23e6/step):

| FS scheme | FS cost | step total | **FS share** |
|---|---|---|---|
| today | 2,417,127 | 4,645,351 | **52.0%** |
| σ-Poseidon | 302,141 | 2,530,365 | **11.9%** |
| **gadget-Feistel** | **92,257** | 2,320,481 | **4.0%** |

**The Feistel makes Fiat–Shamir 4% of the circuit. At that point the problem
is over** — Symphony's architectural advantage evaporates because there is
nothing left to remove; it could then only win by making the *useful work*
cheaper, which it cannot.

⚠ **And the Feistel beats the peer's own theoretical ceiling**: they computed
a "perfect" ring-native sponge at ~1.4e5 (recovering the d=16 encoding waste)
and **our Feistel is 9.2e4.** So it is not merely recovering packing — it must
also be winning on gadget/mode. **Flagged for checking, because a number that
beats a theoretical ceiling usually means a modelling slip.** If it holds it
is the strongest number in the comparison.

## The one experiment that could still overturn it

**Measure `R = (field-native blind-rotation constraints) / (R_q-CCS
blind-rotation constraints)`**, same TFHE blind rotation, N=1024, k=2, ℓ=1.
Arm A is already published (1127 §5.4: >2^16). Arm B is the same rotation in
a field-native CCS over Goldilocks.

**Decision rule (whole bootstrap, 694 rotations, 21 IVC steps): Symphony beats
the Feistel iff R < 1.04.** And R > 1 essentially by construction, since
R_q-CCS exists *because* it is cheaper for ring arithmetic. **If R ≥ 1.04,
build the hash and stop reading Symphony.**

## Corrections to carry

- **"It composes with our substrate" is unearned.** Ours is
  `variable {F : Type*} [Field F]` — **field-pinned**. A ring instantiation is
  a typeclass generalization *plus* a re-derivation of every soundness bound
  from `|F|` to `|A|` (the strong-sampling-set size). Write that, not "it
  composes."
- **The honest headline is "FS ≈ 52% of the benchmarked circuit,"** not
  "32–64×" — that ratio is the un-batched configuration the paper itself
  recommends against.
- Of six papers considered, **only 1127 and Keccacheck have implementations.**
- **SuperNeo (2026/242) COMPETES rather than composes** — make the transcript
  match the field instead of the hash match the ring. It diagnoses our problem
  by name, but ⚠ **its "128× more data" reads as a bits/bytes slip (512 B /
  32 B = 16×)**, and for 1127 the encoding-waste factor is exactly **d = 16**.
  That sets a **packing ceiling of 16×** — which our Feistel's 26× exceeds and
  σ-Poseidon's 8.0× at τ=4 does not, consistent with τ=4 using 4 of 16 slots.
  **Worth checking whether τ is the binding constraint on σ-Poseidon.**
- **ACLMT is dead as a proof, not broken** (no valid proof, no known attack) —
  do not say "broken."
- **Only Symphony genuinely addresses a ring with zero divisors** (strong
  sampling set via Lyubashevsky–Seiler). ProtoGaLattice is moot (no sumcheck);
  2026/551 decomposes to fields; Keccacheck is BN254 and silent — zero hits
  for ring/zero-divisor/cyclotomic/lattice/module.

## What I got wrong, and the generalizable lesson

I predicted "delegate" because delegation composes with the substrate we are
building anyway — an *architectural* argument. The peer scored it and found
delegation is **3–31× over the bar** because the two techniques attack
different quantities. **An architectural fit is not a cost argument.** I have
made this mistake in the other direction today too (calling the registry an
anchor because it fit the story).
