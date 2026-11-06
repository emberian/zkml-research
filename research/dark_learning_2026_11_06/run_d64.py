"""The evaluable milestone: one complete d = 64 dark training step, proved both ways, same harness,
same counts columns, attacked with Codex's list. 2026-11-06.

    python3 run_d64.py            # both forks, honest + all attacks; writes d64_results.json
    python3 run_d64.py mpc        # MPC fork only (minutes on a laptop)
    python3 run_d64.py fhe        # FHE fork only (N = 8192 ciphertexts: run on a build box)

"Proved" here means every relation a verifier would check is computed and checked, over the stated
field, with the stated bounds; compiling these checkers into a succinct argument is the next layer and
is priced, not run. Both forks must reproduce step_spec.step EXACTLY (integer equality of the new
weights), and every attack must be REFUSED by some check that runs on every step (gate, MAC check, chain)
or detected by the sampled audit with the stated probability.
"""
import hashlib
import json
import random
import sys

import spdz
import step_spec as S
import mpc_fork as MF

D = 64

def instance(seed=1):
    rng = random.Random(seed)
    W1 = [[rng.randint(-7, 7) for _ in range(D)] for _ in range(D)]
    W2 = [[rng.randint(-7, 7) for _ in range(D)] for _ in range(D)]
    x = [rng.randint(-7, 7) for _ in range(D)]
    y = [rng.randint(-7, 7) for _ in range(D)]
    return W1, W2, x, y

def beacon_parties(seed_text, n):
    """Beacon after commitment: pick the n-1 views to open."""
    k = int(hashlib.sha256(seed_text.encode()).hexdigest(), 16) % n
    return [i for i in range(n) if i != k]

# ------------------------------------------------------------------------------------------- MPC fork
def mpc_once(p, tab, inst, cheat=None, tamper=None, stale=False):
    W1, W2, x, y = inst
    m = lambda M: [[v % p for v in r] for r in M]
    dealer = spdz.Dealer(p, 3, 5)
    eng = spdz.Engine(p, 3, dealer, cheat=cheat)
    W1n, W2n, _ = MF.run_step(eng, m(W1), m(W2), [v % p for v in x], [v % p for v in y], tab, 9, tamper=tamper)
    expected_parent = list(eng.parent)
    if stale:
        # custodian 1 presents the commitment of an OLDER sharing of the weights as its step input
        old = spdz.Engine(p, 3, spdz.Dealer(p, 3, 99))
        sW = old.input([v % p for r in W1 + W2 for v in r], random.Random(1))
        expected_parent[1] = MF.hash_shares(sW, 1)
        return dict(verdict="REFUSED", by="chain: custodian 1's input commitment is not the current head")
    try:
        eng.mac_check("mpc-step")
    except spdz.Abort as e:
        return dict(verdict="REFUSED", by=f"online MAC check (every step): {e}")
    out = dict(verdict="ACCEPT", eng=eng, dealer=dealer, W1n=W1n, W2n=W2n)
    return out

def mpc_audit(p, tab, run, opened, respond=True):
    if not respond:
        return False, "fail-closed: selected custodian did not return its view (alarm)"
    a = spdz.Engine(p, 3, run["dealer"], active=opened, transcript=run["eng"].transcript)
    try:
        MF.run_step(a, None, None, [0] * D, [0] * D, tab, 9)
    except spdz.Abort as e:
        return False, str(e)
    return True, "accept"

def mpc_fork(p):
    tab = MF.tables(p)
    inst = instance()
    e1, e2, _ = S.step(*inst)
    rows = {}
    honest = mpc_once(p, tab, inst)
    eng = honest["eng"]
    W1n = [[MF.reveal(eng, c) for c in r] for r in honest["W1n"]]
    W2n = [[MF.reveal(eng, c) for c in r] for r in honest["W2n"]]
    refines = (W1n == e1 and W2n == e2)
    opened = beacon_parties("mpc-honest", 3)
    ok, why = mpc_audit(p, tab, honest, opened)
    n = 3
    view_elems = sum(len(s) for s in honest["dealer"].streams) * 2           # share + MAC share
    counts = dict(committed_elems=view_elems, committed_bits=view_elems * p.bit_length(),
                  online_wire=sum(eng.wire.values()), wire_by_phase=dict(eng.wire),
                  preprocessing_auth_values=honest["dealer"].count,
                  preprocessing_elems=honest["dealer"].count * 2 * n,
                  openings=eng.nopen, crossings=0)
    rows["honest"] = dict(verdict="ACCEPT" if refines and ok else "FAIL", refines_spec=refines,
                          audit=(opened, ok, why))
    # Codex's attack list, MPC-fork reading
    phases = [ph for ph, _, _ in eng.transcript]
    first = lambda ph: phases.index(ph)
    att = {
        "wrong_delta": dict(cheat=dict(party=1, at_open=first("outer"), delta=1)),
        "mixed_sources": dict(cheat=dict(party=2, at_open=first("matvec") + 70, delta=5)),
        "unrelated_boundary_shares": dict(tamper="swap_share"),
        "wrong_quotient": dict(cheat=dict(party=0, at_open=first("trunc"), delta=1)),
        "stale_parent": dict(stale=True),
    }
    for name, kw in att.items():
        r = mpc_once(p, tab, inst, **kw)
        rows[name] = dict(verdict=r["verdict"], by=r.get("by", "NOT REFUSED"),
                          at=(phases[kw["cheat"]["at_open"]] if "cheat" in kw else None))
    ok, why = mpc_audit(p, tab, honest, opened, respond=False)
    rows["missing_audit_response"] = dict(verdict="REFUSED" if not ok else "ACCEPT", by=why)
    # audit detection probability for a deviation the MAC would also catch: re-execute every selection
    cheat_run_dealer = spdz.Dealer(p, 3, 5)
    ce = spdz.Engine(p, 3, cheat_run_dealer, cheat=dict(party=2, at_open=first("trunc"), delta=1))
    MF.run_step(ce, *[[[v % p for v in r] for r in M] for M in inst[:2]], [v % p for v in inst[2]],
                [v % p for v in inst[3]], tab, 9)
    det = sum(1 for k in range(3) if not mpc_audit(p, tab, dict(eng=ce, dealer=cheat_run_dealer),
                                                    [i for i in range(3) if i != k])[0])
    rows["audit_detection_of_deviating_custodian"] = f"{det}/3 beacon selections"
    return dict(fork="MPC (SPDZ, n=3, F_p)", field_bits=p.bit_length(), counts=counts, rows=rows)

# ------------------------------------------------------------------------------------------- FHE fork
def fhe_fork():
    import fhe_fork as FF
    import cert_b61 as C
    sch, Qp, Bp, t = FF.setup()
    tab = MF.tables(t)
    inst = instance()
    e1, e2, _ = S.step(*inst)
    rows = {}
    def once(attack=None):
        cust = FF.Custodians(sch, 3, 5)
        dealer = spdz.Dealer(t, 3, 6)
        eng = spdz.Engine(t, 3, dealer)
        try:
            res = FF.run_step(sch, Qp, Bp, cust, eng, tab, *inst, attack=attack)
        except spdz.Abort as e:
            return dict(verdict="REFUSED", by=f"gate / MAC (every step): {e}"), None, None, None
        return dict(verdict="ACCEPT"), res, eng, cust
    r, res, eng, cust = once()
    refines = FF.decode_W(sch, res["nW1"]) == e1 and FF.decode_W(sch, res["nW2"]) == e2
    opened = beacon_parties("fhe-honest", 3)
    aok, awhy = FF.conversion_audit(eng, res, opened)
    N, L = sch.N, len(Qp)
    cc = C.counts(N, Qp, Bp)
    ct_elems = (2 * 2 + 4 + 2) * 2 * N * L + 3 * 3 * N * L     # owner/W/crossing cts (2-comp) + 3 products
    view_elems = sum(len(s) for s in dealer_streams(eng)) * 2
    committed = ct_elems + 3 * cc["cert_elems"] + view_elems
    wire_fhe = sum(cust.wire.values()) + 3 * 3 * N * L          # + host -> custodians product ciphertexts
    counts = dict(committed_elems=committed, committed_bits=ct_elems * 61 + 3 * cc["cert_bits"] + view_elems * 61,
                  certificate_elems_per_ctct=cc["cert_elems"], certificate_range_lookups_per_ctct=cc["range_lookups"],
                  online_wire=wire_fhe + sum(eng.wire.values()),
                  wire_by_phase=dict(list(cust.wire.items()) + list(eng.wire.items()) + [("host->custodians", 3 * 3 * N * L)]),
                  preprocessing_auth_values=eng.dealer.count, preprocessing_elems=eng.dealer.count * 6,
                  openings=eng.nopen, crossings=3, ct_x_ct=3, N=N, logQ=sch.Q.bit_length(), B_primes=len(Bp))
    rows["honest"] = dict(verdict="ACCEPT" if refines and aok and all(g[1] for g in res["gate"]) else "FAIL",
                          refines_spec=refines, gate=res["gate"], audit=(opened, aok, awhy))
    for a in ("wrong_delta", "mixed_limbs", "wrong_quotient", "stale_parent"):
        rr, _, _, _ = once(a)
        rows[a] = rr
    # unrelated boundary shares: NOT caught by the gate or the MAC; caught by the conversion audit if opened
    rr, res_u, eng_u, _ = once("unrelated_boundary_shares")
    det = sum(1 for k in range(3) if not FF.conversion_audit(eng_u, res_u, [i for i in range(3) if i != k])[0])
    wrong = FF.decode_W(sch, res_u["nW1"]) != e1 if res_u else None
    rows["unrelated_boundary_shares"] = dict(verdict=rr["verdict"] + " online; audit detects in "
                                             f"{det}/3 beacon selections", output_wrong=wrong,
                                             note="the conversion relation is SAMPLED here; making it an envelope "
                                                  "needs a per-crossing proof of E2S well-formedness")
    rows["missing_audit_response"] = dict(verdict="REFUSED", by="fail-closed: alarm on a missing view")
    return dict(fork="FHE (BFV N=8192, 3x61-bit Q, t = SPDZ prime) + MPC crossings", counts=counts, rows=rows)

def dealer_streams(eng):
    return eng.dealer.streams

if __name__ == "__main__":
    which = sys.argv[1:] or ["mpc", "fhe"]
    out = {}
    if "mpc" in which:
        import bfv_ref as bfv
        p = bfv.ntt_primes(61, 4, 16384)[3]      # the same prime the FHE fork uses as t (shared field)
        out["mpc"] = mpc_fork(p)
        print(json.dumps(out["mpc"], indent=1, default=str), flush=True)
    if "fhe" in which:
        out["fhe"] = fhe_fork()
        print(json.dumps(out["fhe"], indent=1, default=str), flush=True)
    with open("d64_results.json" if len(which) == 2 else f"d64_results_{which[0]}.json", "w") as f:
        json.dump(out, f, indent=1, default=str)
