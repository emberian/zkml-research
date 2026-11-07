"""The handover proof's soundness, term by term (union bound), beside cosnark_soundness.py's per-step table.

    python3 handover_soundness.py [PROFILE] [d]       (default: ledger 4096; prints EXT = 1 and EXT = 2)
    python3 handover_soundness.py ledger-x2 4096 ledger-x2d ledger-x2de   (each profile as set, EXT from it)

|F| = p^EXT, the challenge field. Terms (the same standard ones as cosnark_soundness.py):
  - W_old(r) = W_new(r) at one point r per matrix: both sides are multilinear in 2 log2 d variables, so a wrong
    new commitment survives with probability 2 log2(d) / |F| per matrix (Schwartz-Zippel);
  - evaluation consistency is exact once proximity holds (it is a linear identity at opened columns);
  - PCS proximity per commitment (old W1, W2 in their second life; new W1, W2 fresh): n / |F| with n = BLOW W
    codeword points; the column test (3/4)^T_COLS per commitment;
  - the Ligero among all custodians: proximity n_L / |F| (n_L = 4 (K_L + T_HIDE)), linear and quadratic 1 / |F|
    each, columns (3/4)^T_OPEN.
Cut E (DEFER, handover.prove_defer), a pending head:
  - the old W1, W2 are opened ONCE (one life) and evaluated twice (at r, and at the head's r_k): proximity once per
    commitment, the column test once per evaluation ((3/4)^T each; proof.md section 21 (2));
  - the new W1, W2 are NOT opened here (their PCS terms are the next opening's); old W(r) = cN is exact, and cN =
    new W(r) is checked exactly at the next opening, so Schwartz-Zippel at r stays one term per matrix;
  - the carries: old c1p, c2p (second life) and new cN1, cN2 (first life), each proximity and columns;
  - the discharge old W(r_k) = c_kp is an exact identity at a point fixed before step k's child could be chosen; its
    Schwartz-Zippel term is step k's rank-1 term (cosnark_soundness.py), not the handover's.
Not in the table: Merkle binding (computational), Fiat-Shamir grinding (a factor of about Q hash queries)."""
import math
import sys

import cosnark as CS
import cosnark_ext as X
import cosnark_zk as ZK
import handover as HO
import proofwire as PW


def terms(prof, d, ext=None):
    PW.set_profile(prof)
    if ext is not None:
        X.EXT = ext
        if ext == 2:
            CS.NMASK = 4
    ext = X.EXT
    p = PW.he_field()
    F = p ** ext
    ld = d.bit_length() - 1
    out = []
    for k in HO.KINDS:
        out.append((f"Schwartz-Zippel {k}: old(r) = new(r), 2 log2 d = {2 * ld} variables", 2 * ld / F))
    if ZK.DEFER:
        sh = HO._dshapes(p, d, True)
        nev = {}
        for key, _ in HO._devals({k: [] for k in HO.KINDS}, {k: [] for k in HO.KINDS}):
            nev[key] = nev.get(key, 0) + 1
        for key, s in sorted(sh.items()):
            if key not in nev:
                continue                       # the new W: opened by the next step, not here
            out.append((f"PCS proximity {key[0]} {key[1]} (n = {len(s.pts)})", len(s.pts) / F))
            out.append((f"PCS columns {key[0]} {key[1]} ({nev[key]} evaluation(s))", nev[key] * 0.75 ** CS.T_COLS))
    else:
        for (side, k), s in sorted(HO._shapes(p, d).items()):
            out.append((f"PCS proximity {side} {k} (n = {len(s.pts)})", len(s.pts) / F))
            out.append((f"PCS columns {side} {k}", 0.75 ** CS.T_COLS))
    nl = 4 * (ZK.K_L + ZK.T_HIDE)
    out.append((f"Ligero proximity (n = {nl})", nl / F))
    out.append(("Ligero linear", 1 / F))
    out.append(("Ligero quadratic", 1 / F))
    out.append(("Ligero columns", 0.75 ** ZK.T_OPEN))
    return out


if __name__ == "__main__":
    prof = sys.argv[1] if len(sys.argv) > 1 else "ledger"
    d = int(sys.argv[2]) if len(sys.argv) > 2 else 4096
    if len(sys.argv) > 3 or "-x2" in prof:
        for pf in [prof] + sys.argv[3:]:
            t = terms(pf, d)
            tot = sum(x for _, x in t)
            print(f"{pf} (EXT = {X.EXT}, DEFER = {ZK.DEFER}): handover 2^{math.log2(tot):.1f}")
            for n, x in t:
                print(f"    {n:60s} 2^{math.log2(x):.1f}")
        sys.exit(0)
    for ext in (1, 2):
        t = terms(prof, d, ext)
        tot = sum(x for _, x in t)
        print(f"EXT = {ext}: handover 2^{math.log2(tot):.1f}")
        for n, x in t:
            print(f"    {n:60s} 2^{math.log2(x):.1f}")
