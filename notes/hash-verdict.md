# Hash verdict: keep Poseidon2, on KoalaBear, with one free fix riding the flag day

2026-08-13. Companion to `field-choice-verdict.md`; full memo published as an
artifact by the lane (23 papers in ~/paperbin). The lane caught and withdrew
its own mid-draft misread (a 2^110.1 attack figure judged against a 128-bit
bar when the right bar at 31 bits is generic 2^62 — capacity binds, not
algebra; every headline Gröbner number was computed at 128–512-bit fields).

## The answers

1. **Poseidon3 does not exist.** Both mirror mentions are citation
   collisions (a circomlib width-3 instance; a StarkWare parameter file).
   The family branches by FIELD, not version: Poseidon2b (binary, for
   Binius), Skyscraper-v2 (big primes). Wrong mental model to expect a
   version number.
2. **eprint 2026/409 is worth nothing as reassurance and should not be
   cited**: 16-bit toy prime, R_F=2/R_P=1/t=3, and its headline FRI table is
   captioned "no Poseidon trace vars" with a LINEAR stand-in hash. The FS
   attack that matters is KRS25 (2025/118), which breaks GKR-Fiat-Shamir
   for EVERY hash — and we verifiably do not run GKR-FS.
3. **The actionable finding — ride the flag day**: eprint 2026/306 attacks
   Poseidon2's non-MDS internal linear layer, and **our deployed shape is
   the attacked one**. The fix is free: transpose to M̄_ε = M₄ ⊗ P_{t/4},
   same fast matmul, **not shipped in any Plonky3**. One more line in the
   KoalaBear re-genesis.
4. **The lookup fork is closed, not deferred**: no 31-bit-prime Monolith
   exists anywhere (Plonky3's Monolith AIR rejects KoalaBear BY NAME in a
   source comment; BabyBear breaks the Bars bijection). Measured at matched
   degree: Poseidon2-KB **164 cols/perm** vs Monolith-31 **3,520** (21.5×),
   ~900 even granting LogUp (5.5×). No crossover; the deficit is marginal,
   not fixed. Our LogUp machinery does not change this.
5. **The field memo's 2.07×, mechanized**: BabyBear→KoalaBear hashing is
   **298 → 164 cols/perm = 1.82×** (deg-7 forces a committed intermediate
   register; deg-3 evaluates inline), ~1.51× total at the 75% hashing
   share. **Both configs already exist in our recursion fork — the
   migration is a config constant.** The missing KB-vs-GL benchmark just
   got cheaper.
6. **Mode is free**: minidregg's `SpongeIndiff` is parametric over the
   permutation, and our Merkle tree is sponge-mode — any sponge-permutation
   swap costs zero formal work. (Compression-mode literature findings do
   not reach us.)

## Oddity on the record

The EF's $992K Poseidon Collision Prize and the Density problem are both
**paused as of 2026-08-01, unexplained**, and the granted-teams list is
unpublished. Watch: an unexplained pause in a cryptanalysis bounty is
either administrative or interesting, and we should not assume which.
