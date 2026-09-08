"""Independent exact finite polynomial arithmetic. No Lean or cryptography.

Polynomials are tuples of coefficients from low degree upwards; zero is ().
Enumeration checks identities as polynomials, never merely at field points.
"""
from functools import lru_cache
from itertools import combinations, permutations, product
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ZERO = ()
ONE = (1,)


def clean(coeffs, p):
    out = [x % p for x in coeffs]
    while out and out[-1] == 0:
        out.pop()
    return tuple(out)


@lru_cache(None)
def add(a, b, p):
    return clean([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                  for i in range(max(len(a), len(b)))], p)


@lru_cache(None)
def neg(a, p):
    return clean([-x for x in a], p)


@lru_cache(None)
def mul(a, b, p):
    if not a or not b:
        return ZERO
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return clean(out, p)


def nat_degree(a):
    return max(0, len(a) - 1)


def monomial(n):
    return (0,) * n + ONE


def polys(p, degree):
    assert degree >= 0
    return tuple(clean(c, p) for c in product(range(p), repeat=degree + 1))


def dot(row, vector, p):
    total = ZERO
    for x, y in zip(row, vector, strict=True):
        total = add(total, mul(x, y, p), p)
    return total


def kernel(matrix, vector, p):
    return all(dot(row, vector, p) == ZERO for row in matrix)


def det(matrix, p):
    n = len(matrix)
    assert all(len(row) == n for row in matrix)
    total = ZERO
    for sigma in permutations(range(n)):
        inversions = sum(sigma[i] > sigma[j] for i in range(n) for j in range(i + 1, n))
        term = ONE
        for i in range(n):
            term = mul(term, matrix[i][sigma[i]], p)
        total = add(total, neg(term, p) if inversions % 2 else term, p)
    return total


def exhaustive(p, M, rows, columns):
    # Independently search all bounded polynomial vectors, not a cofactor formula.
    e = columns - 1
    assert rows >= columns
    entries = polys(p, M)
    vectors = tuple(a for a in product(polys(p, M * e), repeat=columns) if any(a))
    count = singular = determinants = 0
    minimum_witness_degree_histogram = {}
    for entries_flat in product(entries, repeat=rows * columns):
        matrix = tuple(entries_flat[i * columns:(i + 1) * columns] for i in range(rows))
        minors = tuple(det(tuple(matrix[i] for i in selected), p)
                       for selected in combinations(range(rows), columns))
        assert all(nat_degree(d) <= M * columns for d in minors)
        determinants += len(minors)
        count += 1
        if all(d == ZERO for d in minors):
            singular += 1
            witnesses = [a for a in vectors if kernel(matrix, a, p)]
            assert witnesses, (p, M, matrix)
            best = min(max(nat_degree(c) for c in a) for a in witnesses)
            minimum_witness_degree_histogram[best] = minimum_witness_degree_histogram.get(best, 0) + 1
            if columns == 1:
                assert not any(row[0] for row in matrix)
                assert kernel(matrix, (ONE,), p)
    return {"field_prime": p, "M": M, "e": e, "rows": rows, "columns": columns,
            "matrices": count, "determinants": determinants, "singular_matrices_with_witness": singular,
            "candidate_vectors_per_singular_matrix": len(vectors),
            "minimum_witness_degree_histogram": minimum_witness_degree_histogram}


exhaustive_results = []
for case in [(2, 0, 2, 2), (2, 1, 2, 2), (2, 2, 2, 2), (3, 1, 2, 2),
             (2, 1, 3, 2), (2, 0, 3, 3), (2, 0, 1, 1), (2, 1, 2, 1), (2, 2, 3, 1)]:
    exhaustive_results.append(exhaustive(*case))

parametric_fixtures = []
determinant_fixtures = []
falsifiers = []
for p, M, e in product((2, 3, 5), range(4), range(5)):
    n = e + 1
    z = monomial(M)
    # e recurrence rows plus one zero row: z*a_i + a_(i+1)=0.
    # The first e rows and last e columns form a unit triangular minor.
    matrix = tuple(tuple(z if j == i else ONE if j == i + 1 else ZERO for j in range(n))
                   for i in range(e)) + ((ZERO,) * n,)
    vector = tuple(clean([((-1) ** j) * x for x in monomial(M * j)], p) for j in range(n))
    assert vector[0] == ONE and any(vector)
    assert all(nat_degree(x) <= M for row in matrix for x in row)
    assert det(matrix, p) == ZERO
    assert det(tuple(row[1:] for row in matrix[:e]), p) == ONE
    assert kernel(matrix, vector, p)
    assert max(nat_degree(x) for x in vector) == M * e
    assert e == 0 or any(x for row in matrix for x in row)
    parametric_fixtures.append({"p": p, "M": M, "e": e, "max_kernel_degree": M * e,
                                "nonzero_rank_e_minor": [1], "nonzero_matrix": e > 0})
    # Identity falsifies deleting maximal-minor vanishing at every sampled M,e.
    identity = tuple(tuple(ONE if i == j else ZERO for j in range(n)) for i in range(n))
    assert det(identity, p) == ONE
    assert all(nat_degree(x) <= M for row in identity for x in row)
    assert tuple(dot(row, vector, p) for row in identity) == vector
    falsifiers.append({"kind": "identity", "p": p, "M": M, "e": e, "det": [1]})

for p, M, n in product((2, 3, 5), range(4), range(5)):
    diagonal = tuple(tuple(monomial(M) if i == j else ZERO for j in range(n)) for i in range(n))
    d = det(diagonal, p)
    assert d == monomial(M * n)
    assert nat_degree(d) == M * n
    determinant_fixtures.append({"p": p, "M": M, "n": n, "degree": nat_degree(d)})

# Explicit independent exhaustive strict-bound checks, including higher rank.
strict = []
for p, M, e in [(2, 1, 1), (2, 2, 1), (2, 3, 1), (3, 1, 1), (3, 2, 1),
                (2, 1, 2), (2, 2, 2), (3, 1, 2)]:
    n = e + 1
    z = monomial(M)
    matrix = tuple(tuple(z if j == i else ONE if j == i + 1 else ZERO for j in range(n))
                   for i in range(e)) + ((ZERO,) * n,)
    checked = 0
    for a in product(polys(p, M * e - 1), repeat=n):
        if any(a):
            checked += 1
            assert not kernel(matrix, a, p)
    strict.append({"p": p, "M": M, "e": e, "strict_degree_bound": M * e,
                   "nonzero_vectors_excluded": checked})

# Source's exact repeated-row witness, including M=0 and characteristic two.
source_witnesses = []
for p, M in product((2, 3, 5), range(4)):
    z = monomial(M)
    matrix = ((z, ONE), (z, ONE))
    vector = (ONE, neg(z, p))
    assert det(matrix, p) == ZERO and kernel(matrix, vector, p)
    assert max(nat_degree(x) for x in vector) == M
    source_witnesses.append({"p": p, "M": M, "matrix": matrix, "vector": vector})

# Entry-degree falsifier: [X,1] repeated admits no nonzero constant vector.
for p in (2, 3, 5):
    matrix = ((monomial(1), ONE), (monomial(1), ONE))
    for a in product(polys(p, 0), repeat=2):
        if any(a):
            assert not kernel(matrix, a, p)
    falsifiers.append({"kind": "entry_degree_required", "p": p, "excluded_constant_vectors": p * p - 1})

result = {"status": "PASS", "scope": "Exact polynomial identities over finite fields; no evaluation-only tests",
          "exhaustive": exhaustive_results, "parametric_chain_fixtures": parametric_fixtures,
          "determinant_diagonal_fixtures": determinant_fixtures, "source_repeated_row_witnesses": source_witnesses,
          "strict_bound_exhaustions": strict, "falsifiers": falsifiers,
          "zero_nat_degree": nat_degree(ZERO), "empty_determinant": det((), 2)}
(HERE / "math_check.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"status": "PASS", "exhaustive_matrices": sum(x["matrices"] for x in exhaustive_results),
                  "exhaustive_determinants": sum(x["determinants"] for x in exhaustive_results),
                  "singular_matrices_with_bounded_kernel": sum(x["singular_matrices_with_witness"] for x in exhaustive_results),
                  "chain_fixtures": len(parametric_fixtures), "diagonal_fixtures": len(determinant_fixtures),
                  "source_witnesses": len(source_witnesses),
                  "strict_vectors_excluded": sum(x["nonzero_vectors_excluded"] for x in strict)}))
