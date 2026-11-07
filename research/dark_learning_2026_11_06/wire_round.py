"""The switched, noise-rounded HE return (deploy lane, gen 6; native darkstep bfv::compress_return / round_wire).

A return (c0, c1) mod Q = q_0 ... q_{L-1} is sent as:
  1. modulus-switched to Q2 = q_0 q_1, dropping the last prime at a time: c <- (c - [c]_q) / q with [c]_q the
     centered remainder (= round(c / q));
  2. rounded: c0 to a multiple of 2^b0, c1 to a multiple of 2^b1 (round(v / 2^b) 2^b mod Q2), so only the top bits
     travel.
The recipient decrypts round(t (c0 + c1 s) / Q2) mod t. It is exact while the noise stays under Q2 / (2t) - 1:
  E (flood 2^F and the rest, scaled by Q2 / Q)  +  (1 + N) / 2 per dropped prime  +  2^(b0 - 1)  +  N 2^(b1 - 1).
round_bits gives b0, b1 as the largest with 2^(b0-1) <= T/2 and N 2^(b1-1) <= T/2, T = Q2/(2t) - 1 - E - switch.
Hiding: the rounded return is a deterministic function of the full one, so the decryptor learns nothing more
than from the full return; the flood term in the privacy budget is unchanged.
"""
import bfv_ref as bfv


def round_bits(primes, N, t, f_bits):
    """(b0, b1) for returns switched from Q = prod(primes) to the first two primes. Mirrors bfv::round_bits."""
    assert len(primes) > 2
    Q = 1
    for q in primes:
        Q *= q
    q2 = primes[0] * primes[1]
    # E: the flood bound 2^f plus the product and Enc_pk(0) noise bound N t 32, scaled to Q2, rounded up, plus one
    e = (((1 << f_bits) + N * t * 32) * q2 + Q - 1) // Q + 1
    sw = (1 + N) // 2 * (len(primes) - 2) + 1
    budget = q2 // (2 * t) - 1
    assert budget > e + sw, "no room for rounding"
    half = (budget - e - sw) // 2
    return half.bit_length(), (half // N).bit_length()


def switch(c, primes, k=2):
    """Drop primes[k:] from a coefficient vector mod prod(primes), last first, with centered remainders."""
    Q = 1
    for q in primes:
        Q *= q
    out = list(c)
    for top in reversed(range(k, len(primes))):
        q = primes[top]
        Q //= q
        out = [((v - (v % q if v % q <= q // 2 else v % q - q)) // q) % Q for v in out]
    return out


def rnd(v, b, q2):
    return (((v + (1 << (b - 1))) >> b) << b) % q2


def decrypt_wire(sch, ct, primes, b0, b1):
    """The recipient's decryption of a switched, rounded return (every coefficient)."""
    q2 = primes[0] * primes[1]
    c0 = [rnd(v, b0, q2) for v in switch(ct[0], primes)]
    c1 = [rnd(v, b1, q2) for v in switch(ct[1], primes)]
    prod, _ = bfv.negacyclic_mul(bfv.poly_centered(c1, q2), sch.s)
    acc = bfv.poly_centered([(x + y) % q2 for x, y in zip(c0, prod)], q2)
    t = sch.t
    return [((t * x * 2 + q2) // (2 * q2)) % t for x in acc]
