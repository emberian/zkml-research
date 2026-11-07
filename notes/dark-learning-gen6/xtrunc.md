# Gen 6: exact truncation (program flag "XT")

Lane: gen 6 "exact truncation" (initiative #3). Status: design [DERIVED, checked by script]; build in progress.
Checks: `notes/dark-learning-gen6/xtrunc_check.py` (called check_circuit.py below); scratch `scratchpad/dl-gen5/xt/` (`budget_xt.py`).

## 1. The construction

Today (statistical): the step opens c = x + 2^K + r with r uniform in [0, 2^(K+40)). The opening is 2^-40-close to
uniform per truncation, and 16,384 truncations per step make it the run's dominant privacy term (2^-15 for 2000 steps
plus the release).

**XT.** The mask r is uniform in [0, p), as an integer, with all 61 bits authenticated. The online phase is the
statistical one unchanged, plus one public rule:

    c = x + 2^K + r mod p is opened (uniform in F_p for every x);
    if c < 2^(K+1): the step aborts ("XT: opening in the wrap zone"), and it is redone with fresh preprocessing;
    otherwise u = (c >> s) - 2^(K-s) - rhi - [c mod 2^s < r mod 2^s], exactly as today.

**Why it is exact.** Write x' = x + 2^K, in [0, 2^(K+1)) when |x| <= 2^K (the proved bound). Over the integers
x' + r = c + w p with the wrap w in {0, 1}, since x' + r < 2p. If w = 1, then c = x' + r - p < x' < 2^(K+1). So an
opening outside the wrap zone has w = 0 and c = x' + r over the integers. The low-bit comparison is then the borrow of
an integer subtraction, and the formula is floor(x / 2^s) exactly. The wrap bit is excluded publicly, so no secret
wrap bit is computed.

**Why it is perfectly hiding.** r is uniform on F_p, so c is uniform on F_p and independent of x. The abort depends on
c alone. It has probability 2^(K+1)/p for every x (2^-41 at K = 19, 2^-52 at K = 8; about 2^-27.4 per d = 4096 step,
2^-16.4 per 2000-step run). Given no abort, c is uniform on [2^(K+1), p), independent of x. An aborted step's openings
are fresh uniform masks, and its redo uses fresh preprocessing throughout. A custodian that shifts its share of c into
the zone causes only an abort, and it already knew c. The MAC check catches the shift in any case.
[EXECUTED: `check_circuit.py` enumerates every x and r in toy fields (p = 1021, 2039, 4093). Accepted c is uniform on
[2^(K+1), p) for every x, and every accepted opening has x' + r < p.]

Rejected alternatives:
- **Catrina-de Hoogh / BitLT on the full wrap.** This computes w = [c < r] with a 61-bit comparison circuit online:
  about 61 more products and 6 to 61 more rounds per truncation, every step. The public rule gets the same exactness
  for the price of an abort with probability 2^-41.
- **Escudero et al.'s edaBits (CRYPTO 2020).** These are built for mixed arithmetic-binary circuits. darkstep has no
  binary domain: its bits are F_p-authenticated (daBits-like, MP-SPDZ `get_random_bit`). Our need is a uniform-mod-p
  mask with its bits, which strict edaBits also give, but MP-SPDZ builds them with binary-circuit cut-and-choose. The
  check below is about 22 products per mask.
- **Rejected openings that leak.** Taking r uniform in [0, 2^61) and widening the zone to absorb r >= p does not
  work: the zone's own openings are then biased toward x (statistical distance (2^61 - p)/2^61 = 2^-39.4 per mask).
  A perfect mask needs support exactly [0, p).

## 2. The mask in preprocessing (darkprep)

A mask is 61 random authenticated bits b_i (MP-SPDZ `get_random_bit`), r = sum 2^i b_i, kept only if r < p.

**The test (opens one bit, `[r >= p]`, nothing else).** p = 2^61 - delta has T leading one bits. Let L = 61 - T and
P = p mod 2^L (bit L - 1 of P is 0).
- a = T - sum_(i >= L) b_i (linear, in [0, T]; 0 iff the top T bits are all ones).
- lt = [r mod 2^L < P] by the prefix chain against the public P, from the top: E_L = 1, E_i = E_(i+1) e_i with
  e_i = b_i if P_i = 1 else 1 - b_i. Then lt = sum over P_i = 1 of (E_(i+1) - E_i). This is L - 1 - m products,
  m the lowest set bit of P.
- y = a + lt is in [0, T + 1] and is 0 iff r >= p.
- Open rho y with rho a fresh joint random element (one product). It is 0 iff y = 0 (or rho = 0, probability 1/p,
  independent of r). Otherwise it is uniform on F_p*.

If any opened rho y in a chunk is 0, the chunk is discarded and regenerated. This happens with probability 2^-39.4
per mask and 2^-25.4 per step chunk. It reveals nothing about the masks kept: given acceptance, each is uniform on
[0, p), independent of everything opened. A fixed layout keeps the tape format unchanged.
[EXECUTED: `check_circuit.py`. y = 0 iff r >= p for every odd prime of 3 to 10 bits and every r, and for 20,000 random
and near-p r at each deployed p.]

| profile | p | T | L | P | products per mask (chain + rho y) | reject per mask |
|---|---|---:|---:|---|---:|---:|
| N = 4096 | 0x1ffffffffff92001 | 42 | 19 | 0x12001 | 19 | 2^-42.2 |
| demo, N = 8192 | 0x1fffffffffec4001 | 40 | 21 | 0xc4001 | 21 | 2^-40.7 |
| ledger, N = 16384 | 0x1fffffffffcf8001 | 39 | 22 | 0xf8001 | 22 | 2^-39.4 |

**Per truncation, ledger:**

| | statistical | XT |
|---|---|---|
| bits | K + 40 (59, or 48 at K = 8) | 61 |
| online products | 2(s - 1) | 2(s - 1) |
| check products | 0 | 22 (21 sequential rounds, batched over the chunk) |
| check openings | 0 | 1 (rho y) |
| joint randoms | 0 | 1 (rho) |

## 3. The tape (darkstep, darkproof)

**The layout is unchanged.** Each truncation still deals Tr, its s Trb bits, Trh, the K + 1 - s Trhb bits (RS), then
2(s - 1) triples. Only the distribution changes: r is uniform in [0, p) and Trh = r >> s has 61 - s bits. All of these
are linear in the 61 bits, which darkprep's assembly already uses. The ideal dealers (spdz.Dealer, darkstep
tape::Dealer, darkproof live) draw r = randrange(p) under XT, from the same stream position. The extra 61 - (K + 40)
bits and the check products stay inside darkprep's MPC run and are never dealt.

## 4. What the proof constrains

XT needs RS (and so RC). Under RS the proof is sound for any r and rhi (proof.md section 23, R1 and R2). The rows are
field identities, and only an honest witness needs no wrap, which the public rule now gives. So the rows are
unchanged: the TruncMask row, the low-bit borrow rows, the R1 chain to bit B with its high row, and the masked zero
test.

The one change is the public check on c. Today a c' = c - (2^K + a) outside [0, 2^(K+41)) is refused by name, which is
the statistical mask's honest range. Under XT an honest c is anywhere in [2^(K+1), p). The check becomes:
- the verifier refuses an opened c < 2^(K+1) by name ("XT: truncation opening in the wrap zone");
- c' >= 0 follows, since lo = 2^K + a <= 2^(K+1);
- R1's C_hi = floor(c' / 2^B) < p / 2^B, as R1 requires.

Refusal rows (to be EXECUTED):
1. **Wrong wrap.** The dealer's r is forced so that x' + r >= p, which puts c in the zone. The custodians ignore the
   abort and continue, so the MPC's u is wrong.
   - The verifier refuses by name (the public check).
   - With that check bypassed, the custodians' masked zero test refuses: the high row cannot hold, since the low B
     bits of c' - r are x - a - p, not x - a.
   - With the custodians' refusal also bypassed (a forced bundle), the ledger refuses (Ligero linear test).
2. **Wrong low-bit comparison.** A colluding custodian set flips a truncation's borrow (u off by one,
   MAC-consistently). The low-bit rows refuse it (Ligero linear test).

## 5. Privacy budget (privacy_budget.py's gen6 terms; `budget_xt.py`)

Under XT the trunc term is exactly 0. The objects per step rise by 438,272 (to 4,920,519) and the release's by
5,139,732 (to 68,586,614), which moves the sacrifice and authentication terms by about 0.1 bit.
[DERIVED: `budget_xt.py`; LowGear's drowning term is not rescaled for the extra batches (about +10%, 0.14 bit).]

| run | backend | statistical (today) | XT | dominant under XT |
|---|---|---:|---:|---|
| run of record (8 steps + release) | LowGear | 2^-21.6 | **2^-30.3** | prep_drowning |
| run of record | MASCOT tau = 5 | 2^-21.6 | 2^-32.1 | prep_auth |
| 2000 steps + release | LowGear | 2^-15.0 | **2^-23.8** | prep_drowning |
| 2000 steps + release | MASCOT tau = 5 | 2^-15.0 | 2^-25.5 | prep_auth |

The abort rule adds no term: its decision is a function of uniform public openings, and so is the chunk rejection.

## 6. Cost (d = 4096, GEN6, ledger-x2de + RS) [DERIVED from prep.md's measured unit prices; measurement in section 7]

Per step:
- bits rise from 225 d = 921,600 to 244 d = 999,424 (+77,824);
- check products 22 x 16,384 = 360,448;
- plus 16,384 joint randoms and 16,384 openings.

So +438,272 triple-equivalents on 4.48M (+9.8%). The release (213,980 truncations) adds about 5.14M on 63.4M (+8.1%).

| | MASCOT tau = 5 (362 kbit / triple-eq) | LowGear (37.8 kbit) |
|---|---:|---:|
| extra wire per step, all parties | 159 Gbit | 16.6 Gbit |
| extra per step on a 1 Gbit/s seat (a third of it) | 53 s | 5.5 s |
| 2000 steps on a 1 Gbit/s seat | **+29 h** | **+3.1 h** |
| extra per step via hbox (19.3 Mbit/s) | 46 min | 4.8 min |
| release extra via hbox | 8.9 h | 0.93 h (on 27.2 h) |

Online: the same openings, rounds and bytes, plus one public comparison per truncation. Proof: the same rows, atoms
and bundle size, and one public check per truncation instead of another.

## 7. Build log

(filled as pieces land)
