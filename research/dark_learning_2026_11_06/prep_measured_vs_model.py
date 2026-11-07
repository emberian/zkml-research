"""Real MASCOT preprocessing (native/darkprep over MP-SPDZ, three processes on 127.0.0.1) against the Astra scholar's
count model (scholar_preprocessing.py, inventory_he_outer.he_outer_row), row by row, for the MPC fork with both HE
helpers at the steady state (x, y input; weights stay shared), d = 64, 1024, 4096.

    python3 prep_measured_vs_model.py [darkprep_measurements.json] > prep_measured_vs_model.out.json

Measured unit prices: total bytes sent by all three parties for one object kind alone (MP-SPDZ's own "Data sent"
counter, 1 MB = 1e6 bytes), divided by the number of objects. Measured totals: the full step programs. The control
is additivity: counts x measured unit prices must reproduce the measured full-step totals.
"""
import json
import sys

import inventory_he_outer as IHO
import scholar_preprocessing as SP
import step_counts

K = SP.KBITS
OWNER_MSG = 3 * SP.NPARTY * K          # each custodian sends the owner its plain (a_i, b_i, c_i): not in MP-SPDZ's counter

def units(meas):
    u = meas["units"]
    per = lambda a: sum(u[a]["sent_bytes"]) * 8 / u[a]["objects"]
    ar = per("ar100000")
    chain = per("lp400")
    return dict(input=per("in100000") + OWNER_MSG, random=ar, triple=per("tri100000"), bit=per("tr1x60x1000"),
                power_product=(chain - ar) / 254, chain=chain)

def model_rows(d):
    """The he_mpc_outer row's preprocessing, decomposed in the scholar's unit prices; asserts it sums to the row."""
    P = step_counts.params(d)
    ss = [P["S1"], P["S1"], P["S2"], P["S3"]]
    ks = [P["K1"], P["K1"], P["K2"], P["K3"]]
    mul = d * (sum(2 * (s - 1) for s in ss) + 1)
    beaver = mul + 3 * d + 2                  # online products + 3 Freivalds inner products + 2 outer checks
    rows = dict(input=(2 * d, SP.I), random=(4 * d, SP.R), triple=(beaver, SP.T),
                power_product=(254 * d, SP.T + 2 * SP.BROADCAST), bit=(d * sum(k + SP.spdz.KAPPA for k in ks), SP.BIT))
    total = sum(c * u for c, u in rows.values())
    assert total == IHO.he_outer_row(d)["preprocessing_payload_bits"], (total, IHO.he_outer_row(d))
    return rows, total

def main():
    meas = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "darkprep_measurements.json"))
    U = units(meas)
    full = {64: meas["runs"]["d64s_th1"], 1024: meas["runs"]["d1024s_th1"], 4096: meas["runs"]["d4096s_th1"]}
    out = dict(unit_prices_bits={k: dict(model=m, measured=round(U[k])) for k, m in
                                 (("input", SP.I), ("random", SP.R), ("triple", SP.T),
                                  ("power_product", SP.T + 2 * SP.BROADCAST), ("bit", SP.BIT))},
               tables={})
    for d, run in full.items():
        rows, mtotal = model_rows(d)
        tab = []
        for k, (c, mu) in rows.items():
            tab.append(dict(row=k, count=c, model_bits=c * mu, measured_bits=round(c * U[k]), ratio=round(c * U[k] / (c * mu), 3)))
        measured_sum = sum(r["measured_bits"] for r in tab)
        run_bits = run["total_sent_bits"] + 2 * d * OWNER_MSG
        out["tables"][d] = dict(rows=tab, model_total_bits=mtotal, units_times_counts_bits=measured_sum,
                                full_run_bits=run_bits, full_run_over_model=round(run_bits / mtotal, 3),
                                additivity=round(measured_sum / run_bits, 4), wall_s_1thread=run["wall_s"],
                                per_party_sent_bytes=[p["sent_bytes"] for p in run["parties"]])
    # The scholar's formula at the backend's actual parameters: MP-SPDZ uses tau = 3 (N_AMPLIFY) and SoftSpokenOT
    # with k = 2, i.e. lambda / k = 64 bits per extended OT instead of lambda = 128.
    v = meas["variants"]
    tri4 = sum(v["tau4_tri100000"]["sent_bytes"]) * 8 / v["tau4_tri100000"]["objects"]
    out["triple_formula_at_backend_parameters"] = {
        f"tau{tau}": dict(formula=formula_triple(tau, 64), measured=round(m), over_formula=round(m / formula_triple(tau, 64), 3))
        for tau, m in ((3, U["triple"]), (4, tri4))}
    out["tau4_full_runs"] = {d: dict(bits=v[f"tau4_d{d}s"]["total_sent_bits"] + 2 * d * OWNER_MSG,
                                     over_model=round((v[f"tau4_d{d}s"]["total_sent_bits"] + 2 * d * OWNER_MSG) / model_rows(d)[1], 3))
                             for d in (64, 4096)}
    out["d4096_variants_bits"] = {k: v[k]["total_sent_bits"] for k in ("d4096s_th4_tls", "d4096s_th5_softspoken4")}
    print(json.dumps(out, indent=1))

def formula_triple(tau, lam):
    n, k = SP.NPARTY, K
    return n * (n - 1) * (tau * lam * k + (tau + 5) * k * k) + 5 * n * (n - 1) * k + 2 * SP.BROADCAST

if __name__ == "__main__":
    main()
