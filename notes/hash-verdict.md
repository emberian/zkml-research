# Hash verdict: keep Poseidon2 — and if a flag day comes, one free fix rides it

> **Status first.** **Keep Poseidon2** is our state and is settled. The rest of
> this file is *conditional on a field migration that has not happened*:
> **deployed in both trees is BabyBear**, and **KoalaBear is a recommended,
> unexecuted target** (`docs/VERDICTS.md` §1). Read "on KoalaBear" below as "if
> we migrate," never as our parameters.
> ⚠ **And §3's "actionable finding" is not actionable on its own** — the
> 2026/306 round-skipping attack was audited to **no action needed**: our
> BabyBear t=16/t=24 instances carry a **+286-bit margin** and the attack
> cannot reach our bar even if every skippable round were free
> (`notes/poseidon2-audit-verdict.md`; VERDICTS §1). The transpose fix is free
> *if a flag day happens anyway*; it does not justify one.

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
3. **A free fix that rides a flag day** — ⚠ *audited to NO ACTION on its own;
   see the status block above*: eprint 2026/306 attacks
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
   > ⚠ 2026-09-04: **false for internal nodes.** breadstuffs compresses Merkle
   > internal nodes with `TruncatedPermutation<Perm16, 2, 8, 16>` (compression
   > mode, c=0, d=8, no feed-forward; `plonky3_prover.rs:71-72`, `stark_zk.rs:79-80`);
   > only leaves are sponge-mode (`PaddingFreeSponge<Perm16, 16, 8, 8>`).
   > Compression-mode findings DO reach us: eprint 2026/1792's nonlinear-trail
   > window at that node is 2·(t−d) = 16 ≥ R_P = 13 — and its own cost model prices
   > every attack there at ≥ 2^511.9 (`nst-1792-at-our-node.md`), so the claim survives
   > by margin, not by mode. `hash-delta-2026-09-04.md` §1.2.

## Oddity on the record

The EF's $992K Poseidon Collision Prize and the Density problem are both
**paused as of 2026-08-01, unexplained**, and the granted-teams list is
unpublished. Watch: an unexplained pause in a cryptanalysis bounty is
either administrative or interesting, and we should not assume which.
