"""The mind's release: the only output that leaves custody, with the collaborative ZK proof that it was computed from
the weights committed at the ledger head (gen 6; policy by the train lane).

2026-11-07. Policy (train lane): M public test examples (MNIST t10k 0..M-1), images X (d x M) and labels public. Released:
(M, C), C = the number of examples the model classifies correctly; never scores or predictions. Per example t:
    z1 = W1 x_t                      LOCAL on shares (x public)
    u1 = trunc(z1, S1, K1)
    h  = SIG[u1 - T_LO]              (the lookup gate, one table)
    z2_c = W2[c] . h  for c < ncls   (Beaver products; only the class rows of W2)
    o_c = trunc(z2_c, S1, K1)
    q_k = trunc(o_l - o_k - 1, KC, KC) for k != l      (-1 iff o_l <= o_k, else 0; s = K = KC)
    ok_t = prod_{k != l} (1 + q_k)   (Beaver products, stage by stage over t)
    C = sum_t ok_t                   the ONE opening ("release")
The proof is the collaborative ZK middle (cosnark_gates_zk) over this program's record, with external vectors
    W1, W2   the ledger head's commitments, CARRIED at their second life (the last step's spine used the first);
    z1, h    committed fresh (d M each);
and the IO constraints z1[j, t] = sum_k W1[j, k] X[k, t] (public X: linear), h = the lookup's output form, and every
use of W2's class rows and of h through their external atoms. The verifier replays the program symbolically against
the public transcript with its own X and labels, so the constraint system is the verifier's. Transcript label
"release-zk"; context = (model, epoch, head step).
"""
import cosnark_gates as G
import cosnark_gates_zk as GZ
import cosnark_zk as ZK
import cosnark as CS
import spdz

KC = 10


def sig_table(p, t_lo):
    import step_spec as S
    return spdz.interpolate([S.sig(u + t_lo) % p for u in range(256)], p)


def run_release(eng, W1, W2, X, labels, prog, ncls=10, kc=KC):
    """The release program on a RecEngine (live: W1, W2 are the head's share matrices; symbolic: None). X: d x M
    public (mod p), labels: M ints < ncls. Returns (C, the external vectors z1 and h as shares)."""
    p = eng.p
    eng.lb = prog.lb
    eng.rs = getattr(prog, "rs", False)
    d, M = len(X), len(X[0])
    z = lambda: {}
    W1f = [W1[j][k] for j in range(d) for k in range(d)] if W1 else [z() for _ in range(d * d)]
    W2f = [W2[c][k] for c in range(ncls) for k in range(d)] if W2 else [z() for _ in range(ncls * d)]
    W1v = eng.rec_in("W1", W1f)
    W2v = eng.rec_in("W2", W2f)
    # z1 = W1 X, local; bound to its committed external vector by a linear IO constraint per entry
    z1 = []
    for j in range(d):
        for t in range(M):
            sh = eng.lin([(X[k][t], W1v[j * d + k]) for k in range(d)])
            a = eng._atom("ext", ("z1", j * M + t), None)
            eng.ext[("z1", j * M + t)] = a
            f = {a: 1}
            for k in range(d):
                if X[k][t] % p:
                    (w,) = W1v[j * d + k].form
                    f[w] = (f.get(w, 0) - X[k][t]) % p
            eng.cons.append((f, 0, 0, "io"))
            z1.append(G.mk(dict(sh), {a: 1}))
    tab = (sig_table(p, prog.t_lo),)
    u1 = [eng.trunc(v, prog.s1, prog.k1, rc=prog.rc_of("z1", kc)) for v in z1]
    if getattr(prog, "rs", False) and prog.lb:
        # L (proof.md 23): h by the bit circuit in the MPC, not the masked powers
        h = eng.lookup_bits(prog.t_lo, prog.s1)
    else:
        h = [eng.lookup2(u, -prog.t_lo % p, tab, 255)[0] for u in u1]
    eng.rec_out("h", h)
    hb = [G.mk(dict(x), {eng.ext[("h", k)]: 1}) for k, x in enumerate(h)]
    # batch-friendly order (the custodians run each stage as one vector operation): every class-row product, then
    # every score truncation, then every comparison, then the products of the comparisons stage by stage
    prods = [[[eng.mul(W2v[c * d + k], hb[k * M + t]) for k in range(d)] for t in range(M)] for c in range(ncls)]
    o = [[eng.trunc(eng.lin([(1, x) for x in prods[c][t]]), prog.s1, prog.k1, rc=prog.rc_of("score", kc))
          for t in range(M)] for c in range(ncls)]
    fs = []
    for t in range(M):
        l = labels[t]
        qs = [eng.trunc(eng.lin([(1, o[l][t]), (-1, o[k][t])], -1), kc, kc, rc=prog.rc_of("compare", kc))
              for k in range(ncls) if k != l]
        fs.append([eng.cadd(1, q) for q in qs])
    oks = [f[0] for f in fs]
    for j in range(1, ncls - 1):
        oks = [eng.mul(oks[t], fs[t][j]) for t in range(M)]
    C = eng.open(eng.lin([(1, x) for x in oks]), "release")
    if prog.rc:
        G.append_range(eng)
    if prog.lb:
        G.append_lookup(eng, prog.t_lo, prog.s1)
    return C, dict(z1=[dict(x) for x in z1], h=[dict(x) for x in h])


def io_spec(p, d, M):
    """The release's external vectors: the head's W1, W2 (carried, second life, the spine's d x d shape) and z1, h."""
    sh = ZK.shapes(p, d, True)
    lens = dict(W1=d * d, W2=d * d, z1=GZ.plen(d * M), h=GZ.plen(d * M))
    return GZ.IO(lens, ("W1", "W2"), "release-zk", shapes={"W1": sh["W1"], "W2": sh["W2"]})


def replay(p, public, X, labels, prog, ncls=10, kc=KC):
    sym = G.RecEngine(p, 3, None, symbolic=True, transcript=[("open", {}, v) for v in public])
    run_release(sym, None, None, X, labels, prog, ncls, kc)
    return sym


def prove(live, sym, head_wires, z1h, head_coms, ctx, io, deferred=None):
    """head_wires: the head's W1, W2 share vectors (flat d^2); z1h: run_release's z1, h share vectors. deferred (cut
    E): the last step's stats["deferred"], whose claims the release discharges."""
    wires = dict(W1=head_wires["W1"], W2=head_wires["W2"], z1=z1h["z1"], h=z1h["h"])
    return GZ.prove_middle_zk(live, sym, wires, head_coms, context=ctx, io=io, deferred=deferred)


def plain_scores(W1, W2, X, prog, ncls=10):
    """The class scores o (ncls x M) over the integers (floor truncations, exact while the bounds hold)."""
    import step_spec as S
    d, M = len(X), len(X[0])
    out = []
    for t in range(M):
        z1 = [sum(W1[j][k] * X[k][t] for k in range(d)) for j in range(d)]
        h = [S.sig(z >> prog.s1) for z in z1]
        out.append([(sum(W2[c][k] * h[k] for k in range(d))) >> prog.s1 for c in range(ncls)])
    return [[out[t][c] for t in range(M)] for c in range(ncls)]


def plain_count(W1, W2, X, labels, prog, ncls=10, kc=KC):
    """The plaintext twin: the same count over the integers."""
    o = plain_scores(W1, W2, X, prog, ncls)
    C = 0
    for t in range(len(labels)):
        o_ = [o[c][t] for c in range(ncls)]
        l = labels[t]
        C += all((o_[l] - o_[k] - 1) >> kc == 0 for k in range(ncls) if k != l)
    return C
