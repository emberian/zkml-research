"""Can one quadratic hint per 5-bit chi row make every coordinate of chi^-1 quadratic?

Coordinate i of chi^-1 has exactly one cubic monomial, y_{i+1} y_{i+3} y_{i+4}. A hint h
(quadratic in y) can cancel cubic terms only through the products h * y_j, so every target
monomial must lie in the GF(2) span of the cubic parts of h * y_0 .. h * y_4. This tries all
1023 nonzero quadratic forms h; linear and constant terms of h contribute no cubic part.
"""
from itertools import combinations

V = range(5)
quad = list(combinations(V, 2))
cub = list(combinations(V, 3))
ci = {c: i for i, c in enumerate(cub)}
targets = [ci[tuple(sorted(((i + 1) % 5, (i + 3) % 5, (i + 4) % 5)))] for i in V]


def in_span(vecs, t):
    basis = {}
    for v in vecs:
        for b in sorted(basis, reverse=True):
            if v >> b & 1:
                v ^= basis[b]
        if v:
            basis[v.bit_length() - 1] = v
    for b in sorted(basis, reverse=True):
        if t >> b & 1:
            t ^= basis[b]
    return t == 0


solutions = []
for mask in range(1, 1 << 10):
    h = [quad[k] for k in range(10) if mask >> k & 1]
    vecs = []
    for j in V:
        v = 0
        for a, b in h:
            if j not in (a, b):
                v ^= 1 << ci[tuple(sorted((a, b, j)))]
        vecs.append(v)
    if all(in_span(vecs, 1 << t) for t in targets):
        solutions.append(h)
print(f"quadratic hints tried: {(1 << 10) - 1}; single hints that suffice: {len(solutions)}")
# The deployed pair p = y0 y2, q = y0 y3 + y1 y4 does suffice:
pair = [[(0, 2)], [(0, 3), (1, 4)]]
vecs = []
for h in pair:
    for j in V:
        v = 0
        for a, b in h:
            if j not in (a, b):
                v ^= 1 << ci[tuple(sorted((a, b, j)))]
        vecs.append(v)
print("deployed two hints suffice:", all(in_span(vecs, 1 << t) for t in targets))
