#!/usr/bin/env python3
"""Function-key arity and normalized source monomials; no encryption is run."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
rows = []
chunks = []
for external_keys in (1, 2, 8):
    for re_output_bits in (1, 2, 8, 64):
        queries = {(f, bit) for f in range(external_keys) for bit in range(re_output_bits)}
        internal_bound = external_keys * re_output_bits
        assert len(queries) == internal_bound
        rows.append({
            "external_function_keys_Q": external_keys,
            "randomized_encoding_output_bits_M": re_output_bits,
            "direct_multioutput_underlying_keys": external_keys,
            "bit_split_underlying_boolean_keys": internal_bound,
            "indexed_single_key_RE_ciphertexts_per_message": re_output_bits,
            "normalized_N_q4_multiplier_vs_q_Q": re_output_bits**4,
            "normalized_share_q2_multiplier_vs_q_Q": re_output_bits**2,
        })
        for chunk_bits in (1, 8, 32):
            count = (re_output_bits + chunk_bits - 1) // chunk_bits
            output_work = chunk_bits * count
            assert output_work >= re_output_bits
            chunks.append({"Q": external_keys, "M": re_output_bits,
                "bits_per_chunk_b": chunk_bits,
                "underlying_chunk_functions": external_keys * count,
                "literal_GKP_output_slots_per_final_function": output_work})

result = {
    "schema": "depth-interface-arity-v1",
    "scope": "Exact combinatorial query counts and normalized symbolic polynomial substitutions. No cryptographic implementation, security test, benchmark, or choice of hidden Theta constants.",
    "source_formulas": {
        "t": "Theta(kappa*q^2)",
        "N_inst": "Theta(D^2*q^2*t) = Theta(kappa*D^2*q^4)",
        "S_share": "Theta(kappa*q^2)",
        "bit_split_substitution": "q=Q*M",
        "result_N_inst": "Theta(kappa*D^2*Q^4*M^4)",
        "result_S_share": "Theta(kappa*Q^2*M^2)",
        "normalized_multiplier_warning": "M^4 and M^2 are exact ratios of the displayed monomials, not exact ratios of implemented costs with unspecified Theta constants.",
    },
    "arity_rows": rows,
    "chunk_rows": chunks,
    "interface_distinction": {
        "NC_MO": "One ciphertext plus one vector-function key yields all M output bits; assumes output-independent ciphertext construction.",
        "indexed_RE": "One Boolean function key plus M ciphertexts yields M bits; encoding work explicitly depends on M.",
        "bounded_boolean_backend": "One logical tuple key exposes M underlying Boolean keys; encryption setup must tolerate that many collusions.",
    },
}
(HERE / "arity_substitution.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"arity_rows": len(rows), "chunk_rows": len(chunks),
                  "max_underlying_boolean_keys": max(r["bit_split_underlying_boolean_keys"] for r in rows),
                  "scope": result["scope"]}, indent=2))
