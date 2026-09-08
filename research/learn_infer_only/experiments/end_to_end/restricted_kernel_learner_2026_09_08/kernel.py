"""Exact public feature arithmetic. This hash defines a map, not crypto coins."""
import hashlib

INPUT_DIMENSION = 576
COMPACT_DIMENSION = 32
RADIUS = 4
DIMENSION = 577
DOMAIN = b'restricted-kernel-learner-2026-09-08/map-v1/'
PAIRS = [(i, j) for i in range(COMPACT_DIMENSION)
         for j in range(i, COMPACT_DIMENSION)]
assert len(PAIRS) == 528

def projection_sign(i, j):
    return 1 if hashlib.sha256(DOMAIN + i.to_bytes(2, 'big')
                               + j.to_bytes(2, 'big')).digest()[0] & 1 else -1

SIGNS = [[projection_sign(i, j) for j in range(INPUT_DIMENSION)]
         for i in range(COMPACT_DIMENSION)]

def compact(vector):
    if len(vector) != DIMENSION or vector[-1] != 0:
        raise ValueError('Expected original 577-coordinate, final-zero vector')
    if any(type(v) is not int or abs(v) > 127 for v in vector):
        raise ValueError('Expected exact signed int8 source vector')
    z = [sum(s * v for s, v in zip(row, vector)) for row in SIGNS]
    maximum = max(map(abs, z))
    if maximum == 0:
        return [0] * COMPACT_DIMENSION
    # floor(4 |z_i| / maximum + 1/2): exact ties away from zero.
    return [(1 if v >= 0 else -1) * ((2 * RADIUS * abs(v) + maximum)
                                    // (2 * maximum)) for v in z]

def check_compact(x):
    if len(x) != COMPACT_DIMENSION or any(type(v) is not int or abs(v) > RADIUS for v in x):
        raise ValueError('Expected 32 exact bounded coordinates')

def lift(x):
    check_compact(x)
    return [x[i] * x[j] for i, j in PAIRS] + [0] * (DIMENSION - len(PAIRS))

def query_coefficients(q):
    check_compact(q)
    return [(1 if i == j else 2) * q[i] * q[j] for i, j in PAIRS] + [0] * (DIMENSION - len(PAIRS))

def kernel(x, q):
    check_compact(x)
    check_compact(q)
    return sum(v * w for v, w in zip(x, q)) ** 2

def encode_source(vector):
    return lift(compact(vector))
