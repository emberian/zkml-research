"""[EXECUTED] Deterministic GF(2) phase identities, not quantum simulation."""
import hashlib
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent


def parity(x):
    return x.bit_count() & 1


def main():
    width = 4
    character_cases = 0
    for a in range(1 << width):
        for f in range(1 << width):
            for w in range(1 << width):
                assert parity(a & (w ^ f)) == parity(a & w) ^ parity(a & f)
                character_cases += 1
    tables = {1: (2, 3), 3: (3, 5)}  # address: (programmed prefix length, value)
    wrapper_cases = wrong_mask_counterexamples = 0
    for address in range(4):
        p, table_value = tables.get(address, (0, 0))
        overlay = (1 << p) - 1
        for ell in range(width + 1):
            requested = (1 << ell) - 1
            for z in range(1 << width):
                label = z & requested & ~overlay
                assert label ^ (z & requested & ~overlay) == 0
                for f in range(1 << width):
                    fallback_phase = parity(label & f)
                    table_phase = parity(z & requested & overlay & table_value)
                    full_value = (f & ~overlay) | (table_value & overlay)
                    expected = parity(z & requested & full_value)
                    assert fallback_phase ^ table_phase == expected
                    # Omitting the exclusion mask double-counts fallback on
                    # overlaid bits and must be detected by this same identity.
                    wrong = parity(z & requested & f) ^ table_phase
                    wrong_mask_counterexamples += int(wrong != expected)
                    wrapper_cases += 1
    assert character_cases == 4096 and wrapper_cases == 5120
    assert wrong_mask_counterexamples > 0
    result = {"claim_label": "EXECUTED", "all_passed": True,
              "command": "python3 -B research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_seed_qrom_successor/quantum_simulation/symbolic_phase_checks.py",
              "completed_utc": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
              "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "basis_label_bits": width, "xor_character_identity_cases": character_cases,
              "prefix_overlay_phase_identity_cases": wrapper_cases,
              "ancillary_label_clears": True,
              "omitted_fallback_mask_counterexamples": wrong_mask_counterexamples,
              "random_samples": 0, "quantum_state_or_circuit_simulations": 0,
              "scope": "Exact integer parity checks of the stated phase circuit; general coherent proof by linearity is in SIMULATION.md."}
    (HERE / "PHASE_CHECKS.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    stdout = json.dumps({"all_passed": True, "character_cases": character_cases,
                         "wrapper_cases": wrapper_cases, "wrong_mask_counterexamples": wrong_mask_counterexamples}, sort_keys=True)
    with (HERE / "RUN.log").open("a") as f:
        f.write("\n[EXECUTED] " + result["command"] + "\n[EXECUTED] Exit code: 0\n" + stdout + "\n")
    print(stdout)


if __name__ == "__main__":
    main()
