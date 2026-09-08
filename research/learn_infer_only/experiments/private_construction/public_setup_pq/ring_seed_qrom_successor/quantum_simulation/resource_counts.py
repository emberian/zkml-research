"""[EXECUTED] Deterministic resource arithmetic, no quantum/random simulation."""
import hashlib
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent


def main():
    protocol = b"ring-seed-transport/public-rows/v1"
    seed_bytes, binding_bytes, family_bytes, q_bytes = 64, 32, 255, 37
    max_honest_address_bytes = (4 + len(protocol) + 4 + seed_bytes + 4 + binding_bytes
                                + 4 + family_bytes + 8 + 8 + 4 + q_bytes + 8)
    length_tag_bits = max_honest_address_bytes.bit_length()
    address_register_bits = 8 * max_honest_address_bytes + length_tag_bits
    chunk_bytes = 1024 * 37
    chunk_bits = 8 * chunk_bytes
    rows_a, rows_missing, cap_chunks = 64, 561, 80
    entries = (rows_a + rows_missing) * cap_chunks
    field_bits = 4096  # Illustrative fixed advice degree, subject to k <= 2^4096.
    lanes = (chunk_bits + field_bits - 1) // field_bits
    assert lanes * field_bits == chunk_bits
    result = {
        "claim_label": "EXECUTED", "command": "python3 -B research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_seed_qrom_successor/quantum_simulation/resource_counts.py",
        "completed_utc": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
        "arithmetic_only": True,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "profile": {"q_bits": 289, "raw_candidate_bits": 296, "chunk_words": 1024,
                    "chunk_bytes": chunk_bytes, "chunk_bits": chunk_bits,
                    "cap_chunks_per_row": cap_chunks, "A_rows": rows_a,
                    "missing_rows": rows_missing, "overlay_entries": entries},
        "ordinary_wrapper": {
            "overlay_value_bytes": entries * chunk_bytes,
            "max_valid_frozen_format_address_bytes": max_honest_address_bytes,
            "illustrative_input_bound_bytes": max_honest_address_bytes,
            "input_bound_qualification": "D must also cover the adversary's declared maximum query length; 466 is only the frozen-format maximum at q289.",
            "length_tag_bits": length_tag_bits,
            "address_register_bits_at_illustrative_D": address_register_bits,
            "packed_overlay_address_bytes_at_illustrative_D": (entries * address_register_bits + 7) // 8,
            "field_degree_example": field_bits,
            "independent_polynomial_lanes_at_L_equals_chunk_bits": lanes,
            "base_quantum_calls_per_exposed_query": 1,
            "required_independence": "k = 2*Q + c_base; parent case c_base=0",
            "fallback_seed_bits": "k * ceil(L/m) * m",
            "fallback_seed_bytes_at_example_and_c_base_zero": f"{2 * chunk_bytes} * Q",
            "field_mults_per_exposed_query_compute_uncompute": f"{2 * lanes} * (k-1)",
            "bit_gate_upper_order_per_query": "O(ceil(L/m)*k*m^2 + B*(d+L_chunk) + L*log(L))",
            "advice": "fixed public monic irreducible degree-m binary polynomial; deterministic validation; same allowed nonuniform advice class",
        },
        "giant_block_information_theoretic_only": {
            "separate_independent_family_oracles": True,
            "A_bytes_per_G_value": rows_a * cap_chunks * chunk_bytes,
            "A_bits_per_G_value_and_label_register": rows_a * cap_chunks * chunk_bits,
            "missing_bytes_per_G_value": rows_missing * cap_chunks * chunk_bytes,
            "missing_bits_per_G_value_and_label_register": rows_missing * cap_chunks * chunk_bits,
            "queries_to_each_target_G_per_exposed_H_query_via_phase_routing": 1,
            "GHM_prequery_counts_parent_chronology": "qhat_A=Q_before_A; qhat_missing=Q_before_missing; honest A read is not a missing-oracle query",
        },
        "quantum_circuits_executed": 0, "random_samples": 0, "crypto_executions": 0,
        "primary_web_search_queries": 2,
    }
    (HERE / "COUNTS.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    stdout = json.dumps({"overlay_entries": entries, "overlay_value_bytes": entries * chunk_bytes,
                         "chunk_bits": chunk_bits, "max_honest_address_bytes": max_honest_address_bytes,
                         "giant_G_bits": rows_missing * cap_chunks * chunk_bits,
                         "base_calls_per_exposed_query": 1, "independence": "2Q+c_base"}, sort_keys=True)
    (HERE / "RUN.log").write_text("[EXECUTED] " + result["command"] + "\n[EXECUTED] Exit code: 0\n" + stdout + "\n")
    print(stdout)


if __name__ == "__main__":
    main()
