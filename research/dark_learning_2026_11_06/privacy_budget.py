"""The million-step privacy budget of the MPC fork, every term computed (gen 5, item 3).

    python3 privacy_budget.py [d] [steps] [N L F_bits]     # default 4096 1000000 16384 4 175 (ledger profile)

Terms (statistical distance between the real view of a coalition of up to n - 1 custodians and a simulated one, summed
over the run; union bound):
  he_stat     HE returns, ring smudging: sum over returns of N B / (2F + 1) (keygen_ceremony.distances, decision doc §21)
  he_rlwe     HE returns, the c1 component: (returns) x Adv_RLWE, Adv_RLWE <= 2^-128 (the estimator gives 2^213 core-SVP)
  trunc       SPDZ truncation masking (spdz.Engine.trunc): it opens c = x + 2^K + r with r uniform in [0, 2^(K+KAPPA)),
              and the simulator opens 2^K + r. SD = |x| / 2^(K+KAPPA) < 2^-KAPPA per truncation; the step truncates z1,
              z2, e (K = 13, 13, 8) and b g1 (K = 13): 4 d per step.
  mac         the batched MAC check passes a wrong opening with probability at most 2/p (rho cancellation, then
              guessing alpha). Only a passing forgery lets an abort depend on secret data, so this bounds the abort
              leakage statistically. Under Fiat-Shamir grinding of 2^g hashes the rho part becomes 2^g/p.
  aborts      each recorded abort can leak at most one bit if a forgery succeeded; without forgery the abort decision is
              a function of the adversary's own deviations only. Carried as the named k-abort term, not a distance.
  prep_*      the MASCOT preprocessing backend's terms, from the gen-5 preprocessing lane's measured configuration
              (notes/dark-learning-gen5/preprocessing.md §5; MP-SPDZ v0.4.4): combine (privacy of the triples:
              2^-k(tau-2)/2 per triple at tau >= 4 by the MASCOT proof, k = log2 p; 2^-k/2 at the released tau = 3),
              sacrifice (an incorrect triple passes: 1/|F| per triple), authentication (log|F| - 2 log log|F| bits per
              batch of ~1000), the owner's a b = c input check (1/|F| per input). Objects per step at steady state
              (W carried, not re-input): 2^14.97 at d = 64, 2^21.12 at d = 4096 (that lane's count).
Perfect (zero) terms: input masking, auth_plain, lookup openings, Beaver openings (uniform masks in F_p), the HE outer
commitments (hashes of uniformly masked shares), the collaborative proof within two lives (exact Ligero hiding,
§16/§19), the key ceremony's commit-reveal (its selective-abort factor (k+1) multiplies, §21).
Not in this file: quantum attacks on RLWE.

Gen 6 (`python3 privacy_budget.py gen6 [steps]`): the deployed run, GEN6 program, ledger-x2de + RS proofs, public
genesis (W_0 public by design, so no owner input of W), M = 52 release once at the end. Object counts per step and for
the release are the gen-6 preprocessing lane's (`darkprep plan` with the run's flags, notes/dark-learning-gen6/prep.md
§10-11): per step 4,482,247 triple-equivalents (2^22.10) incl. the proof section, 16,384 truncations, 8,192 owner
inputs; release 63,446,882 (2^25.92), 213,980 truncations. Backends: MASCOT tau = 5 (combine, sacrifice, auth, owner
check), or LowGear S = 60 (drowning <= 8192 / (1 + 3 2^60) per drowned ciphertext, TopGear ZK 2^-S per proof,
sacrifice 1/p), whose RLWE parameters must be at N >= 16,384 for 128 bits (prep lane: N = 8,192 at a 312-bit q is
about 90 bits). The collaborative proof adds no distance within its life counts (exact Ligero hiding; one life per W
under cut E).
"""
import json
import math
import sys

import bfv_ref as bfv
import keygen_ceremony as K

TRUNCS = ((13, "z1"), (13, "z2"), (8, "e"), (13, "bg"))   # (K, wire) per element, as mpc_fork.run_step
PREP_OBJECTS_LOG2 = {64: 14.97, 4096: 21.12}               # MASCOT triples (bits and powers included) per step


def prep_combine_bits(k, tau):
    """Statistical bits per triple of MASCOT's combine step (preprocessing lane, from the MASCOT proof)."""
    return k / 2 if tau <= 3 else k * (tau - 2) / 2


def log2(x):
    return round(math.log2(x), 2) if x > 0 else float("-inf")


def budget(d=4096, steps=10**6, N=16384, L=4, F_bits=175, kappa=40, mac_ext=1, exact_trunc=False, rlwe_bits=128,
           tau=None):
    """tau None: the ideal dealer (no preprocessing terms); else MASCOT with that amplification. mac_ext: the degree
    of the field the MAC check, the sacrifice and the authentication run in (1 = F_p, 2 = F_p^2)."""
    pr = bfv.ntt_primes(61, L + 1, 2 * N)
    p = pr[L]
    he = K.distances(d, N, L, F_bits, steps)
    he_stat_step = 2.0 ** he["log2_stat_per_step"]
    he_rlwe_step = he["returns"] * 2.0 ** -rlwe_bits
    if exact_trunc:
        trunc_step = 0.0
    else:
        # largest |x| per wire is below 2^K; SD per truncation |x| / 2^(K + kappa) < 2^-kappa
        trunc_step = sum(d * 2.0 ** -kappa for _K, _w in TRUNCS)
        for Kb, _w in TRUNCS:
            assert (1 << (Kb + kappa)) + (1 << (Kb + 1)) < p, f"kappa {kappa} wraps the field at K = {Kb}"
    mac_step = 2.0 / float(p) ** mac_ext
    terms = dict(he_stat=he_stat_step, he_rlwe=he_rlwe_step, trunc=trunc_step, mac=mac_step)
    if tau is not None:
        k = math.log2(p) * mac_ext
        objs = 2.0 ** PREP_OBJECTS_LOG2[d]
        terms["prep_combine"] = objs * 2.0 ** -prep_combine_bits(math.log2(p), tau)
        terms["prep_sacrifice"] = objs * 2.0 ** -k
        terms["prep_auth"] = (objs / 1000) * 2.0 ** -(k - 2 * math.log2(k))
        terms["prep_owner_check"] = (len(TRUNCS) * 0 + 2 * d) * 2.0 ** -k
    run = {k: min(1.0, v * steps) for k, v in terms.items()}
    total = min(1.0, sum(v * steps for v in terms.values()))
    return dict(d=d, steps=steps, N=N, L=L, F_bits=F_bits, p=p, kappa=kappa, mac_field_degree=mac_ext, tau=tau,
                exact_trunc=exact_trunc, truncations_per_step=0 if exact_trunc else len(TRUNCS) * d,
                log2_per_step={k: log2(v) for k, v in terms.items()},
                log2_run={k: log2(v) for k, v in run.items()},
                log2_run_total=log2(total),
                dominant=max(run, key=run.get),
                kappa_max_in_field=min(int(math.log2(p - (1 << (Kb + 1)))) - Kb for Kb, _ in TRUNCS))


GEN6_TRUNCS = ((19, "z1"), (19, "z2"), (8, "e"), (19, "bg"))     # GEN6: shifts 11/7/8, bounds 2^19/2^8/2^19
GEN6_STEP = dict(objs=4_482_247, truncs=16_384, owner_inputs=8_192, lg_batches=54.7, lg_drowned=13_132)
XT_OBJ_FACTOR = {False: 1.0978, True: 1.081}   # measured +9.78% per step (darkprep plan), +8.1% for the release
GEN6_RELEASE = dict(objs=63_446_882, truncs=213_980, owner_inputs=0, lg_batches=775, lg_drowned=185_880)


def gen6_terms(c, backend, p, kappa=40, S=60, xt=False):
    """One step's (or the release's) distance terms for the deployed gen-6 run. xt: exact truncation (genesis flag
    "XT", notes/dark-learning-gen6/xtrunc.md): masks uniform on [0, p), so the opened values are perfectly hidden and
    the trunc term is 0; XT adds 9.7% triple-equivalents (61 bits plus a 22-product r < p check per mask)."""
    k = math.log2(p)
    if xt:
        c = dict(c, objs=c["objs"] * XT_OBJ_FACTOR[c is GEN6_RELEASE or c.get("_release", False)])
    t = dict(trunc=0.0 if xt else c["truncs"] * 2.0 ** -kappa, mac=2.0 / p)
    if backend == "mascot5":
        t["prep_combine"] = c["objs"] * 2.0 ** -prep_combine_bits(k, 5)
        t["prep_sacrifice"] = c["objs"] * 2.0 ** -k
        t["prep_auth"] = (c["objs"] / 1000) * 2.0 ** -(k - 2 * math.log2(k))
        t["prep_owner_check"] = c["owner_inputs"] * 2.0 ** -k
    elif backend == "lowgear":
        t["prep_drowning"] = c["lg_drowned"] * 8192 / (1 + 3 * 2.0 ** S)
        t["prep_zk"] = 3 * c["lg_batches"] * 2.0 ** -S
        t["prep_sacrifice"] = c["objs"] * 2.0 ** -k
    return t


def gen6(steps=2000, N=16384, L=4, F_bits=175, d=4096, kappa=40, xt=False):
    for Kb, _w in GEN6_TRUNCS:
        assert (1 << (Kb + kappa)) + (1 << (Kb + 1)) < 2 ** 61, f"kappa {kappa} wraps the field at K = {Kb}"
    pr = bfv.ntt_primes(61, L + 1, 2 * N)
    p = pr[L]
    he = K.distances(d, N, L, F_bits, steps)
    out = {}
    for backend in ("mascot5", "lowgear"):
        st = gen6_terms(GEN6_STEP, backend, p, kappa, xt=xt)
        st["he_stat"] = 2.0 ** he["log2_stat_per_step"]
        st["he_rlwe"] = he["returns"] * 2.0 ** -128
        rel = gen6_terms(GEN6_RELEASE, backend, p, kappa, xt=xt)
        run = {k: min(1.0, v * steps + rel.get(k, 0.0)) for k, v in st.items()}
        total = min(1.0, sum(v * steps for v in st.values()) + sum(rel.values()))
        out[backend] = dict(steps=steps, d=d, p=p, kappa=kappa, exact_trunc=xt,
                            log2_per_step={k: log2(v) for k, v in st.items()},
                            log2_release={k: log2(v) for k, v in rel.items()},
                            log2_run={k: log2(v) for k, v in run.items()},
                            log2_run_total=log2(total), dominant=max(run, key=run.get))
    return out


def main():
    if sys.argv[1:2] == ["gen6"]:
        steps = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
        xt = "--xt" in sys.argv
        out = gen6(steps, xt=xt)
        for b, v in out.items():
            print(f"gen6{' XT' if xt else ''} {b:8s} {steps} steps + release: total 2^{v['log2_run_total']:>7}  dominant {v['dominant']}"
                  f"\n  per step {v['log2_per_step']}\n  release  {v['log2_release']}")
        json.dump(out, open(f"privacy_budget_gen6_{steps}{'_xt' if xt else ''}.json", "w"), indent=1)
        return
    a = [int(x) for x in sys.argv[1:]]
    d = a[0] if a else 4096
    steps = a[1] if len(a) > 1 else 10**6
    N, L, F = (a[2], a[3], a[4]) if len(a) > 4 else (16384, 4, 175)
    rows = {
        "ideal dealer, as built (KAPPA = 40, MACs in F_p)": budget(d, steps, N, L, F),
        "MASCOT as released (tau = 3), as built": budget(d, steps, N, L, F, tau=3),
        "MASCOT tau = 4, as built": budget(d, steps, N, L, F, tau=4),
    }
    km = rows["ideal dealer, as built (KAPPA = 40, MACs in F_p)"]["kappa_max_in_field"]
    rows["MASCOT tau = 4, KAPPA at the field's limit"] = budget(d, steps, N, L, F, kappa=km, tau=4)
    rows["MASCOT tau = 4, exact truncation"] = budget(d, steps, N, L, F, exact_trunc=True, tau=4)
    rows["MASCOT tau = 5, exact truncation, F_p^2 checks"] = budget(d, steps, N, L, F, exact_trunc=True, mac_ext=2,
                                                                   tau=5)
    rows["ideal dealer, exact truncation, F_p^2 MACs"] = budget(d, steps, N, L, F, exact_trunc=True, mac_ext=2)
    for k, v in rows.items():
        print(f"{k:48s} total 2^{v['log2_run_total']:>7}  dominant {v['dominant']:14s} run terms {v['log2_run']}")
    json.dump(rows, open(f"privacy_budget_d{d}_N{N}_L{L}_F{F}.json", "w"), indent=1)


if __name__ == "__main__":
    main()
