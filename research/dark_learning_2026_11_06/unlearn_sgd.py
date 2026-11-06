"""The SGD case for initiative 16: what is exact, what is only bounded, and what the bound is worth.

2026-11-06. Multinomial logistic regression on optdigits (x / 16 and a bias, 65 features, 10 classes), mini-batch SGD
with L2 weight decay, float64. The schedule is committed and public: in epoch e the record positions are ordered by
H(seed, e, position) and cut into consecutive batches of B0 slots; every batch is normalised by B0 (fixed), so
deleting record d empties ONE slot per epoch and leaves every other batch unchanged.

The comparator (named, as the program demands): the prescribed learner on D with d's slot empty ("null-record
replacement"). Three deletions are measured against it:
  exact replay     restart from the checkpoint before d's first step and replay the suffix without d. Bit-identical
                   to the comparator (checked on the float bits). Cost: the replayed steps; its certificate is a FULL
                   proof of those steps (Astra DL12: never a sampled one).
  bound only       do nothing and certify eps = sum over d's steps t of rho^(T-1-t) * gamma, with
                   rho = 1 - eta*lam (the update map is rho-Lipschitz because eta*(lam + L) <= 1, L = 65/2 (public: ||x||^2 <= 65)
                   bounding the multinomial Hessian) and gamma = eta * sqrt(2) * ||x_d|| / B0 (one removed summand).
                   Lean: traj_gap / sgd_delete_bound. "Doing nothing" satisfies it: eps is the whole claim.
  forget by        keep training on D \\ {d} for K more epochs; eps shrinks by rho per step (C23: contraction is
  contraction      forgetting, and costs utility).
And the host term: if audits are SAMPLED, a host can re-inject d's gradient; the landed displacement bound caps the
expected injected deviation before the first alarm (D/q pathwise per round, 2B/q in envelope form). Measured here
against the attack that re-injects on every round.
"""
import hashlib
import math
import random

import unlearn_c18 as U

C = U.NCLASS
D = 65

def feats(r):
    return [v / 16.0 for v in r[:64]] + [1.0]

def schedule(n, epochs, B0, seed):
    sched = []
    for e in range(epochs):
        order = sorted(range(n), key=lambda j: hashlib.sha256(f"{seed}:{e}:{j}".encode()).digest())
        sched += [order[i:i + B0] for i in range(0, n, B0)]
    return sched

def grad_sample(W, x, y):
    z = [sum(W[c][i] * x[i] for i in range(D)) for c in range(C)]
    m = max(z)
    ez = [math.exp(v - m) for v in z]
    s = sum(ez)
    p = [v / s for v in ez]
    p[y] -= 1.0
    return p      # gradient = p (outer) x

def step(W, batch, X, Y, eta, lam, B0, null=frozenset(), extra=None):
    G = [[0.0] * D for _ in range(C)]
    for j in batch:
        if j in null:
            continue
        x = X[j]
        g = grad_sample(W, x, Y[j])
        for c in range(C):
            gc = g[c]
            if gc:
                Gc = G[c]
                for i in range(D):
                    Gc[i] += gc * x[i]
    if extra is not None:                       # a covert re-injection (attack)
        for c in range(C):
            for i in range(D):
                G[c][i] += extra[c][i]
    return [[W[c][i] - eta * (G[c][i] / B0 + lam * W[c][i]) for i in range(D)] for c in range(C)]

def dist(W1, W2):
    return math.sqrt(sum((a - b) ** 2 for r1, r2 in zip(W1, W2) for a, b in zip(r1, r2)))

def train(X, Y, sched, eta, lam, B0, null=frozenset(), W0=None, start=0, keep=False):
    W = W0 or [[0.0] * D for _ in range(C)]
    ck = [W] if keep else None
    for t in range(start, len(sched)):
        W = step(W, sched[t], X, Y, eta, lam, B0, null)
        if keep:
            ck.append(W)
    return W, ck

def acc(W, rows):
    ok = 0
    for r in rows:
        x = feats(r)
        z = [sum(W[c][i] * x[i] for i in range(D)) for c in range(C)]
        ok += max(range(C), key=lambda c: z[c]) == r[64]
    return ok

def bound(uses, T, rho, gamma):
    return sum(rho ** (T - 1 - t) * gamma for t in uses if t < T)

def run(RESULTS, epochs=5, more=3, B0=32, lam=0.05, seed=16, n_del=4, trials=40, p_audit=0.05):
    tra, tes = U.load("optdigits.tra"), U.load("optdigits.tes")
    X = [feats(r) for r in tra]
    Y = [r[64] for r in tra]
    n = len(tra)
    Lmax = 65 / 2.0      # PUBLIC bound: ||x||^2 <= 64 * 1 + 1 for x/16 in [0,1] plus the bias (Codex round 2: not the
                         # data's maximum, which a deleted record could set)
    assert max(sum(v * v for v in x) for x in X) / 2.0 <= Lmax
    eta = 1.0 / (lam + Lmax)
    rho = 1.0 - eta * lam
    sched = schedule(n, epochs + more, B0, seed)
    T = epochs * (len(sched) // (epochs + more))
    print(f"[sgd] n = {n}, B0 = {B0}, lam = {lam}, L = {Lmax:.3f}, eta = {eta:.5f}, rho = {rho:.6f}, "
          f"T = {T} steps ({epochs} epochs) + {len(sched) - T} continuation steps")
    W_full, ck = train(X, Y, sched[:T], eta, lam, B0, keep=True)
    a_full = acc(W_full, tes)
    print(f"[sgd] trained on D: test accuracy {a_full}/{len(tes)}")
    rng = random.Random(seed)
    rows = []
    ok = True
    for d in rng.sample(range(n), n_del):
        null = frozenset([d])
        uses = [t for t, b in enumerate(sched) if d in b]
        gamma = eta * math.sqrt(2) * math.sqrt(sum(v * v for v in X[d])) / B0
        W_cmp, ck_cmp = train(X, Y, sched[:T], eta, lam, B0, null=null, keep=True)
        # exact replay from the checkpoint before d's first step
        t0 = min(uses)
        W_rep, _ = train(X, Y, sched[:T], eta, lam, B0, null=null, W0=ck[t0], start=t0)
        bit_identical = W_rep == W_cmp
        measured = dist(W_full, W_cmp)
        eps = bound(uses, T, rho, gamma)
        # forgetting by contraction: both continue on D \ {d}
        cont = []
        Wa, Wb = W_full, W_cmp
        per_epoch = len(sched) // (epochs + more)
        for k in range(1, more + 1):
            seg = sched[T + (k - 1) * per_epoch:T + k * per_epoch]
            Wa, _ = train(X, Y, seg, eta, lam, B0, null=null, W0=Wa)
            Wb, _ = train(X, Y, seg, eta, lam, B0, null=null, W0=Wb)
            Tk = T + k * per_epoch
            cont.append(dict(extra_epochs=k, measured=dist(Wa, Wb), bound=bound([u for u in uses if u < T], Tk, rho, gamma)))
        row = dict(record=d, steps_using_d=[u for u in uses if u < T], first_use=t0, replayed_steps=T - t0,
                   exact_replay_bit_identical=bit_identical, measured_distance=measured, certified_bound=eps,
                   bound_holds=measured <= eps, continuation=cont)
        ok &= bit_identical and measured <= eps and all(c["measured"] <= c["bound"] for c in cont)
        rows.append(row)
        print(f"[sgd] d = {d}: replay {T - t0}/{T} steps, bit-identical {bit_identical}; ||W - W_cmp|| = "
              f"{measured:.3e} <= eps = {eps:.3e}: {measured <= eps}; after {more} more epochs: "
              f"{cont[-1]['measured']:.3e} <= {cont[-1]['bound']:.3e}")
    # the host term: re-inject d's gradient on every round after the deletion, audited with probability p
    d = rows[0]["record"]
    null = frozenset([d])
    per_epoch = len(sched) // (epochs + more)
    W_cmp_T = train(X, Y, sched[:T], eta, lam, B0, null=null)[0]
    arng = random.Random(seed + 1)
    finals, maxgap = [], 0.0
    for _ in range(trials):
        Wa = Wb = W_cmp_T                    # the deletion was honest at T; the host re-injects afterwards
        t = T
        while t < len(sched):
            g = grad_sample(Wa, X[d], Y[d])
            extra = [[g[c] * X[d][i] for i in range(D)] for c in range(C)]
            maxgap = max(maxgap, eta * math.sqrt(sum(v * v for row_ in extra for v in row_)) / B0)
            Wa = step(Wa, sched[t], X, Y, eta, lam, B0, null, extra=extra)
            Wb = step(Wb, sched[t], X, Y, eta, lam, B0, null)
            t += 1
            if arng.random() < p_audit:      # the audit fires on this corrupt round and the checker is exact
                break
        finals.append(dist(Wa, Wb))
    mean_dev = sum(finals) / len(finals)
    # displacement_bound_of_gap with an A PRIORI per-round gap (Codex round 1: not the maximum observed in the
    # trials): the re-injected term is eta/B0 * ||(p - e_y) x_d^T|| <= eta * sqrt(2) * ||x_d|| / B0, and q = p_audit
    D_apriori = eta * math.sqrt(2) * math.sqrt(sum(v * v for v in X[d])) / B0
    assert maxgap <= D_apriori
    host_bound = D_apriori / p_audit
    print(f"[sgd] host re-injects d's gradient every round, audit rate {p_audit}: mean deviation at stop "
          f"{mean_dev:.3e} over {trials} trials <= D/q = {host_bound:.3e}: {mean_dev <= host_bound}")
    ok &= mean_dev <= host_bound
    RESULTS["sgd"] = dict(n=n, B0=B0, lam=lam, eta=eta, rho=rho, L=Lmax, T=T, epochs=epochs,
                          continuation_epochs=more, test_accuracy=a_full, test_size=len(tes), deletions=rows,
                          host_reinjection=dict(p_audit=p_audit, trials=trials, mean_deviation_at_stop=mean_dev,
                                                displacement_bound_D_over_q=host_bound, a_priori_round_gap=D_apriori,
                                                max_observed_round_gap=maxgap),
                          all_hold=ok)
    return ok
