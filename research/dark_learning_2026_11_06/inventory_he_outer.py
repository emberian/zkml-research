"""The Astra scholar's MASCOT preprocessing inventory (scholar_preprocessing.py, imported UNMODIFIED), re-run, plus a
row for the MPC fork with both HE helpers (he_mpc_outer): the two dense outer-product tuples are replaced by
he_outer.HEOuter.

Control: every scholar row this script recomputes must equal scholar_preprocessing_results.json, and the script
exits 1 otherwise. The new row is the scholar's he_mpc row with these exact changes, in the scholar's own unit
prices (bits):
  - remove the 2 d^2 outer correlated products: each costs a triple T plus 2 broadcasts;
  - remove the 2 x 2d outer masks [u], [w], each a jointly hidden random R;
  - add 2 Beaver triples, one per outer Freivalds check;
  - online: add he_outer's HE wire, commitments and check; remove SPDZ's 2d outer openings per outer.
The ZKPoPKs on sent ciphertexts are reported separately, at the model price and at the scholar's executable Stern
price (235,113,860,648 bits per proof at N = 8192), and are NOT in total_payload_bits, as in the scholar's rows.

    python3 inventory_he_outer.py > inventory_he_outer.out.json
"""
import json
import sys

import he_matvec as HM
import he_outer as HO
import scholar_preprocessing as SP

STERN_BITS_PER_PROOF = 235113860648        # scholar_zkpopk_results.json, N8192_count_only.compact_proof_bits

def he_outer_row(d):
    base = SP.inventory(d, "he_mpc")
    ho = HO.counts(d, SP.N)
    hm = HM.counts(d, SP.N)
    outer_products = 2 * d * d
    prep = (base["preprocessing_payload_bits"]
            - outer_products * (SP.T + 2 * SP.BROADCAST)
            - 2 * 2 * d * SP.R
            + 2 * SP.T)
    online = base["online_bits"] + (ho["he_wire"] + ho["spdz_wire"] - ho["replaces_spdz_outer_wire"]) * SP.KBITS
    zk = hm["zkpopk_proofs"] + ho["zkpopk_proofs"]
    return dict(d=d, fork="he_mpc_outer", outer_products=0, scalar_triples=base["scalar_triples"] - outer_products + 2,
                jointly_hidden_random_fields=base["jointly_hidden_random_fields"] - 4 * d,
                preprocessing_payload_bits=prep, online_bits=online, total_payload_bits=prep + online,
                he_outer_ciphertexts=dict(sent=ho["cts_sent"], returned=ho["cts_returned"]),
                zkpopk_proofs=zk, zkpopk_bits_model=hm["zkpopk_bits"] + ho["zkpopk_bits"],
                zkpopk_bits_stern=zk * STERN_BITS_PER_PROOF)

def main():
    saved = {(r["d"], r["fork"]): r for r in json.load(open("scholar_preprocessing_results.json"))["rows"]}
    rows, control = [], True
    for d in (64, 1024, 4096):
        for f in ("mpc", "he_mpc", "fhe_a", "fhe_b"):
            r = SP.inventory(d, f)
            same = r == saved[(d, f)]
            control &= same
            rows.append(dict(d=d, fork=f, total_payload_bits=r["total_payload_bits"],
                             preprocessing_payload_bits=r["preprocessing_payload_bits"],
                             online_bits=r["online_bits"], equals_scholar_saved=same))
        rows.append(he_outer_row(d))
    print(json.dumps(dict(control_scholar_rows_unchanged=control, rows=rows), indent=1))
    if not control:
        sys.exit(1)

if __name__ == "__main__":
    main()
