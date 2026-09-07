#!/usr/bin/env python3
"""Public query linear algebra only; no ciphertexts or private-state analysis."""
from pathlib import Path
import hashlib
import json
import math
import sys
import time
import sympy as sp

HERE = Path(__file__).resolve().parent
TASK = HERE.parents[2]
QUERIES = TASK / "end_to_end/utility/public_queries"
sys.path.insert(0, str(HERE.parents[1]))
from additive_ipfe import P, Q


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    paths = sorted(QUERIES.glob("q*.json"))
    assert len(paths) == 16
    rows = [json.loads(p.read_text()) for p in paths]
    assert all(len(row) == 577 and all(type(x) is int and abs(x) <= 127 for x in row)
               for row in rows)
    start = time.perf_counter_ns()
    matrix = sp.Matrix(rows)
    rref, pivots = matrix.rref()
    determinant = int(matrix[:, list(pivots)].det())
    rank_ns = time.perf_counter_ns() - start
    assert len(pivots) == 16 and determinant != 0 and abs(determinant) < Q
    free = [j for j in range(577) if j not in pivots]
    # Compact basis: N has identity on free rows and -RREF[:,free] on pivots.
    kernel_top = -rref[:, free]
    assert matrix[:, list(pivots)]*kernel_top+matrix[:, free] == sp.zeros(16, len(free))
    basis_serial = [[str(v) for v in kernel_top.row(i)] for i in range(16)]
    basis_sha = hashlib.sha256(json.dumps(basis_serial,separators=(",", ":")).encode()).hexdigest()
    # One bounded deterministic lattice pass, on public coefficients only.
    n, scale = 32, 10**6
    start = time.perf_counter_ns()
    lattice = sp.eye(n).row_join(scale * matrix[:, :n].T)
    reduced = lattice.lll()
    candidates = [[int(x) for x in reduced[i, :n]] for i in range(n)
                  if not any(reduced[i, n:])]
    assert candidates
    prefix = min(candidates, key=lambda w: sum(x*x for x in w))
    witness = prefix + [0] * (577-n)
    lll_ns = time.perf_counter_ns() - start
    assert any(witness) and max(map(abs, witness)) <= 3
    assert matrix * sp.Matrix(witness) == sp.zeros(16, 1)
    # Two explicitly bounded ambient-domain examples, not claimed encoder outputs.
    zero = [0] * 577
    assert zero != witness and all(-127 <= x <= 127 for x in witness)
    public_fixture_path = TASK / "end_to_end/utility/issuer_oracle/vectors/h0-e0001.json"
    public_fixture = json.loads(public_fixture_path.read_text())
    shifted = [x+w for x,w in zip(public_fixture, witness, strict=True)]
    assert all(abs(x) <= 127 for x in shifted)
    assert matrix*sp.Matrix(public_fixture) == matrix*sp.Matrix(shifted)
    l1 = [sum(map(abs, row)) for row in rows]
    bounds = [32*127*x for x in l1]
    bound = max(bounds)
    size = math.isqrt(2*bound+1)
    if size*size < 2*bound+1:
        size += 1
    byte_width = (P.bit_length()+7)//8
    report = {
        "passed": True,
        "scope": "public matrix rank and ambient bounded kernel; no protected-state extraction",
        "script_sha256": sha(__file__), "sympy_version": sp.__version__,
        "query_files_sha256": {str(p): sha(p) for p in paths},
        "shape": [16, 577], "rank_Q": len(pivots), "rank_mod_group_order": len(pivots),
        "pivot_columns": list(pivots), "pivot_minor_determinant": determinant,
        "kernel_dimension": 577-len(pivots),
        "basis": {"form": "N_free=I; N_pivot=-RREF[:,free]", "free_columns": free,
                  "top_block_rational_sha256": basis_sha, "columns_checked": len(free)},
        "kernel_witness": witness,
        "kernel_witness_max_abs": max(map(abs, witness)),
        "kernel_witness_l2_squared": sum(x*x for x in witness),
        "lll": {"columns": n, "scale": scale, "kernel_rows_returned": len(candidates),
                "calls": 1, "elapsed_ns": lll_ns},
        "rank_elapsed_ns": rank_ns,
        "nonvacuity_scope": "zero and witness in [-127,127]^577; encoder-image membership unproved",
        "public_fixture_shifted_pair": {"baseline_sha256": sha(public_fixture_path),
            "all_16_projections_equal": True, "shifted_range": [min(shifted), max(shifted)],
            "bias_unchanged": public_fixture[-1] == shifted[-1],
            "shifted_encoder_image_membership": "unproved"},
        "query_l1": l1, "query_window_score_bounds": bounds,
        "max_window_score_bound": bound, "generic_int8_bound": 577*32*127**2,
        "bsgs": {"common_interval": [-bound, bound], "baby_entries": size,
                 "giant_iterations_max": (2*bound)//size+1,
                 "raw_group_bytes": size*byte_width},
        "raw_sizes": {"group_element_bytes": byte_width,
            "public_key_bytes": 577*byte_width, "fixed_key_bytes": 16*byte_width,
            "ciphertext_bytes": 578*byte_width,
            "two_route_queue_and_aggregate_bytes": 66*578*byte_width},
        "searches": {"scry_sql": 0, "web": 0, "package_installs": 0},
    }
    (HERE / "linear_results.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({k: report[k] for k in ["passed", "shape", "rank_Q", "kernel_dimension",
        "pivot_minor_determinant", "kernel_witness_max_abs", "max_window_score_bound", "bsgs", "raw_sizes"]}, indent=2))


if __name__ == "__main__":
    main()
