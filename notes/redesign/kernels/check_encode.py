#!/usr/bin/env python3
"""Bit-exact check of encode.c: every codeword coordinate equals the unique degree < k polynomial through
the message values on span(v_0..v_{ell-1}) (v_i = bit i), evaluated at that coordinate's domain point,
computed here by Lagrange interpolation over GF(2^16) with an independent port of minidregg's Fan-Paar
tower multiply. Also checks the T_4-scalar-acts-coordinatewise fact on Tower256 that makes R = 16*rows
the packed-Tower256 encode.   usage: check_encode.py <encode binary> [ell R]"""
import json, random, subprocess, sys

def mulgen(level, v):
    c = level - 1; w = 1 << c; m = (1 << w) - 1; lo, hi = v & m, (v >> w) & m
    rh = (lo ^ hi) if c == 0 else (lo ^ mulgen(c, hi))
    return hi | (rh << w)

def mul(level, a, b):
    if level == 0: return a & b & 1
    c = level - 1; w = 1 << c; m = (1 << w) - 1
    a0, a1, b0, b1 = a & m, (a >> w) & m, b & m, (b >> w) & m
    p0, p1 = mul(c, a0, b0), mul(c, a1, b1)
    mixed = mul(c, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1
    pc = p1 if c == 0 else mulgen(c, p1)
    return (p0 ^ p1) | ((mixed ^ pc) << w)

def inv16(a):  # a^(2^16-2)
    r, e, b = 1, 65534, a
    while e:
        if e & 1: r = mul(4, r, b)
        b = mul(4, b, b); e >>= 1
    return r

def main():
    exe = sys.argv[1]; ell = int(sys.argv[2]) if len(sys.argv) > 2 else 3; R = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    out = json.loads(subprocess.run([exe, "check", str(ell), str(R)], capture_output=True, text=True, check=True).stdout)
    k = 1 << ell; msg, cw = out["msg"], out["cw"]
    xs = list(range(k))  # domain point of index p is p itself (basis v_i = bit i)
    # barycentric weights
    wts = []
    for i in xs:
        d = 1
        for j in xs:
            if j != i: d = mul(4, d, i ^ j)
        wts.append(inv16(d))
    bad = 0
    for p in range(4 * k):
        for r in range(R):
            if p < k:
                want = msg[p * R + r]
            else:
                want = 0
                for i in xs:
                    num = wts[i]
                    for j in xs:
                        if j != i: num = mul(4, num, p ^ j)
                    want ^= mul(4, num, msg[i * R + r])
            if cw[p * R + r] != want: bad += 1
    # Tower256 scalar action: c in T_4 times x in T_8 equals chunkwise T_4 products
    rnd = random.Random(7); sc_bad = 0
    for _ in range(50):
        c = rnd.getrandbits(16); x = rnd.getrandbits(256)
        y = mul(8, c, x)
        z = 0
        for j in range(16): z |= mul(4, c, (x >> (16 * j)) & 0xffff) << (16 * j)
        sc_bad += y != z
    print(json.dumps({"ell": ell, "R": R, "codeword_symbols": 4 * k * R, "mismatches": bad,
                      "tower256_scalar_chunkwise_mismatches": sc_bad, "pass": bad == 0 and sc_bad == 0}))
    sys.exit(0 if bad == 0 and sc_bad == 0 else 1)

main()
