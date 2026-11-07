"""Custody handover (gen 5, item 4): resharing the weights to a new committee, and the proof that the new committee's
commitment holds the same weights, chained into the ledger.

2026-11-07. Spec: the Veil model /Users/ember/dev/veil-pilot/VeilPilot/CustodyHandover.lean (resharing with the
both-periods corruption rule: inside the handover window a held custodian counts against BOTH committees' n - 1
budget; senders erase their subshares with their share; n-of-n blocks on one crash). Design: handover note §2e
(notes/dark-learning-handover-2721.md): a handover is one more step type in the same chain.

Resharing. Old custodian i splits its share s_i of each weight matrix into n_new uniform subshares sub_ij (summing to
s_i), sends sub_ij to new custodian j and erases s_i and its subshares; new custodian j holds s'_j = sum_i sub_ij.
The new committee then authenticates s' under its own MAC key (auth_plain with its own preprocessing).

The handover proof. The old committee's commitment of W (the ledger head's child roots, a hiding share-tuple PCS) and
the new committee's fresh commitment are evaluated at one Fiat-Shamir point r (after both roots are fixed), and a
collaborative zero-knowledge Ligero among all n_old + n_new custodians proves, on HIDDEN values:
  - evaluation consistency of the old row combination u_old at the old commitment's opened columns,
  - the same for u_new at the new commitment's opened columns,
  - <u_old - u_new, b(r)> = 0, i.e. W_old(r) = W_new(r): Schwartz-Zippel on the MLE, error 2 log2(d) / p.
No evaluation value is revealed (the old and new rows are hidden rows; the columns are uniform within each
commitment's lives). Lives: the old commitment was opened once in its step (child) and is opened a second time here,
never as a parent again; the new commitment is opened here and once more as the next step's parent. So LIVES = 2
suffices; the third life the handover note §2e anticipated is not needed because the old child is not reused.
Each u row of the old commitment is shared among the old custodians only (zero shares for the new ones), and vice
versa; Ligero's hiding values are drawn by every custodian. Under the both-periods rule a coalition holds at most
n_old - 1 old and n_new - 1 new custodians, so every hidden row keeps one honest share.

Wire format of a HANDOVER PROOF (encode/decode; the ledger takes these bytes, never a Python object), proofwire's
conventions (big-endian, field element 8 bytes and < p, hash 32 bytes, column index u32 < its domain, no length
prefixes, no trailing bytes):
  header   magic b"DLHAND01" | d u16 | n_old u8 | n_new u8   (must equal what the ledger supplies)
  body     old_roots {W1, W2}: n_old hashes each | new_roots: n_new each | eval_roots: n_old + n_new |
           mask_roots: n_old + n_new | prox_old {W1, W2}: n_old rows of W each |
           cols_old {W1, W2}: (T_COLS indices < BLOW W, n_old x T_COLS x (R elements, path)) each |
           prox_new, cols_new likewise with n_new |
           ligero: cozk messages for one group of 4 ceil(W / K_L) hidden rows (proofwire.ligero_schema)
where each matrix commitment (2 log2 d variables) has C = d columns, R = d + NMASK rows, W = d + HIDE, BLOW W points;
schema() gives every length as a function of (d, n_old, n_new, PARAMS).
"""
import os
import struct

import cosnark as CS
import cosnark_ext as X
import cosnark_zk as ZK
import cozk as Z
import proofwire as PW
from cosnark import Transcript, eqv

KINDS = ("W1", "W2")


def reshare(old_shares, n_new, p, rng):
    """old_shares[i] = custodian i's share vector. Returns (sub[i][j], new_shares[j])."""
    sub = []
    for s in old_shares:
        parts = [[rng.randrange(p) for _ in s] for _ in range(n_new - 1)]
        parts.append([(v - sum(c)) % p for v, c in zip(s, zip(*parts))] if parts else list(s))
        sub.append(parts)
    new = [[sum(sub[i][j][k] for i in range(len(old_shares))) % p for k in range(len(old_shares[0]))]
           for j in range(n_new)]
    return sub, new


def _keys():
    return [("old", k) for k in KINDS] + [("new", k) for k in KINDS]


def context_digest(model, epoch_old, epoch_new, after_step, old_set, new_set):
    return ("handover", model, epoch_old, epoch_new, after_step, tuple(old_set), tuple(new_set))


def _schedule(tr, p, d):
    """Per matrix: one point r of length 2 log2 d, in F_{p^EXT} (one transcript call of EXT 2 log2 d draws); the
    evaluation list is (old k, r), (new k, r) per k."""
    ld = d.bit_length() - 1
    evals = []
    for k in KINDS:
        r = X.chal(tr, p, 2 * ld)
        evals += [(("old", k), r), (("new", k), r)]
    return evals


def _rows(sh, evals):
    """Each evaluation's u rows, component-major: EXT blocks of ceil(W / K_L) rows (cosnark_zk.row_layout)."""
    rows, nxt = [], 0
    for key, _ in evals:
        nr = -(-sh[key].W // ZK.K_L)
        rows.append(list(range(nxt, nxt + X.EXT * nr)))
        nxt += X.EXT * nr
    return rows, nxt


def _constraints(p, sh, evals, cols, urows):
    """Every check is an identity over F_{p^EXT}, emitted as EXT F_p constraints, component 0 first (cosnark_zk's
    evar / ecell / eadder; EXT = 1: the base system, byte for byte)."""
    lin, labels = [], []
    cur = ["?"]
    E = X.EXT
    add = ZK.eadder(p, lin, labels, cur)
    def U(e, c):
        nr = -(-sh[evals[e][0]].W // ZK.K_L)
        return ZK.ecell([(urows[e][k * nr + c // ZK.K_L], c % ZK.K_L) for k in range(E)])
    for e, (key, pt) in enumerate(evals):
        s = sh[key]
        a = s.eval_weights_e(pt)
        J, csum = cols[key]
        cur[0] = f"PCS evaluation consistency ({key[0]} {key[1]})"
        for jj, j in enumerate(J):
            x, xs, forms = s.pts[j], 1, []
            for c in range(s.W):
                forms.append(ZK.evar(p, U(e, c), (xs,)))
                xs = xs * x % p
            add(*forms, rhs=X.dot(a, [(v,) for v in csum[jj]], p))
    for q, k in enumerate(KINDS):
        eo, en = 2 * q, 2 * q + 1
        pt = evals[eo][1]
        s = sh[("old", k)]
        b = X.eqv(pt[:s.mc], p)
        cur[0] = f"handover: old {k}(r) = new {k}(r)"
        forms = []
        for c in range(s.C):
            forms.append(ZK.evar(p, U(eo, c), b[c]))
            forms.append(ZK.evar(p, U(en, c), X.neg(b[c], p)))
        add(*forms)
    return lin, labels


def prove(p, d, old_coms, new_coms, ctx, seed=("handover",), deferred=None, carry_src=None):
    """old_coms/new_coms: {"W1": ZKPCS, "W2": ZKPCS} held by the old / new committee (the old ones carried from the
    last step's child). Returns (proof, stats). Raises cosnark.LifeExhausted on a third opening of an old commitment.
    Cut E (ZK.DEFER): deferred = the head step's stats["deferred"] (None when the head is final); see prove_defer."""
    if ZK.DEFER:
        return prove_defer(p, d, old_coms, new_coms, ctx, seed, deferred, carry_src)
    assert deferred is None and carry_src is None
    n_old, n_new = len(old_coms["W1"].ext), len(new_coms["W1"].ext)
    n = n_old + n_new
    com = {("old", k): old_coms[k] for k in KINDS}
    com.update({("new", k): new_coms[k] for k in KINDS})
    for k in KINDS:
        old_coms[k].base = old_coms[k].block          # the old child's second life
        new_coms[k].base = 0                           # the new commitment's first life
    tr = Transcript("handover")
    tr.absorb("ctx", ctx)
    for key in _keys():
        tr.absorb(repr(key), com[key].roots)
    evals = _schedule(tr, p, d)
    urows, nrows = _rows(com, evals)
    L = Z.Prover(Z.Params(p, ZK.K_L, ZK.T_HIDE, ZK.T_OPEN), n, (seed, ctx))
    for e, (key, pt) in enumerate(evals):
        c = com[key]
        a = c.eval_weights_e(pt)
        own = [c.row_combo_e(i, a) for i in range(len(c.ext))]
        zero = [[0] * c.W for _ in range(X.EXT)]
        shares = own + [zero] * n_new if key[0] == "old" else [zero] * n_old + own
        for kk in range(X.EXT):
            for s0 in range(0, c.W, ZK.K_L):
                L.add_row([u[kk][s0:s0 + ZK.K_L] for u in shares])
    eval_roots = L.commit()
    mask_roots = L.commit_masks()
    tr.absorb("lig-evals", eval_roots, mask_roots)
    old_part = {key[1]: com[key] for key in _keys() if key[0] == "old"}
    new_part = {key[1]: com[key] for key in _keys() if key[0] == "new"}
    _, prox_o, cols_o = CS.pcs_prove(old_part, [], tr, n_old, p)
    _, prox_n, cols_n = CS.pcs_prove(new_part, [], tr, n_new, p)
    cols = {}
    for side, cc, part, nn in (("old", cols_o, old_part, n_old), ("new", cols_n, new_part, n_new)):
        for k in KINDS:
            J, per = cc[k]
            cols[(side, k)] = (J, [[sum(per[i][jj][0][r] for i in range(nn)) % p for r in range(part[k].R)]
                                   for jj in range(len(J))])
    lin, labels = _constraints(p, com, evals, cols, urows)
    lig = L.prove(tr, lin, [])
    proof = dict(old_roots={k: old_coms[k].roots for k in KINDS}, new_roots={k: new_coms[k].roots for k in KINDS},
                 eval_roots=eval_roots, mask_roots=mask_roots,
                 prox_old={k: prox_o[k][1] for k in KINDS}, prox_new={k: prox_n[k][1] for k in KINDS},
                 cols_old={k: cols_o[k] for k in KINDS}, cols_new={k: cols_n[k] for k in KINDS}, ligero=lig)
    stats = dict(hidden_rows=nrows, lin_constraints=len(lin), ligero_wire=L.wire,
                 first_violated=ZK.first_violated(p, L.rows, lin, [], labels))
    return proof, stats


def verify(p, d, n_old, n_new, ctx, old_roots, proof, deferred=None, out=None):
    """Public data only: the ledger supplies ctx and old_roots (its head's parent roots); the proof names the new roots,
    which the ledger records as the next parent when this accepts. Cut E: deferred = the head's pending claims from the
    ledger (proofwire.deferred_of), out receives the new head's (see verify_defer)."""
    if ZK.DEFER:
        return verify_defer(p, d, n_old, n_new, ctx, old_roots, proof, deferred, out)
    if deferred is not None:
        return False, "handover: a pending head outside cut E"
    if proof.get("old_roots") != old_roots:
        return False, "handover: old roots are not the ledger head's"
    new_roots = proof["new_roots"]
    ld = d.bit_length() - 1
    sh = {}
    for side in ("old", "new"):
        for k in KINDS:
            base = (CS.NMASK // CS.LIVES) if side == "old" else 0
            sh[(side, k)] = ZK.PubShape(p, 2 * ld, CS.HIDE, CS.NMASK, base)
    roots = {("old", k): old_roots[k] for k in KINDS}
    roots.update({("new", k): new_roots[k] for k in KINDS})
    if any(len(roots[("old", k)]) != n_old or len(roots[("new", k)]) != n_new for k in KINDS):
        return False, "handover: wrong committee sizes"
    tr = Transcript("handover")
    tr.absorb("ctx", ctx)
    for key in _keys():
        tr.absorb(repr(key), roots[key])
    evals = _schedule(tr, p, d)
    urows, nrows = _rows(sh, evals)
    tr.absorb("lig-evals", proof["eval_roots"], proof["mask_roots"])
    for side, nn, pr, pc in (("old", n_old, proof["prox_old"], proof["cols_old"]),
                             ("new", n_new, proof["prox_new"], proof["cols_new"])):
        part = {k: sh[(side, k)] for k in KINDS}
        ok, why = CS.pcs_verify(part, {k: roots[(side, k)] for k in KINDS}, [], [],
                                {k: (None, pr[k]) for k in KINDS}, pc, tr, nn, p)
        if not ok:
            return False, f"handover ({side} committee): {why}"
    cols = {}
    for side, nn, pc in (("old", n_old, proof["cols_old"]), ("new", n_new, proof["cols_new"])):
        for k in KINDS:
            J, per = pc[k]
            cols[(side, k)] = (J, [[sum(per[i][jj][0][r] for i in range(nn)) % p for r in range(sh[(side, k)].R)]
                                   for jj in range(len(J))])
    lin, _ = _constraints(p, sh, evals, cols, urows)
    ok, why = Z.verify(Z.Params(p, ZK.K_L, ZK.T_HIDE, ZK.T_OPEN), n_old + n_new, [proof["eval_roots"]], [nrows],
                       proof["mask_roots"], lin, [], proof["ligero"], tr)
    return ok, (why if not ok else "accept")


# ----------------------------------------------------------------------------------------------- wire format
MAGIC = b"DLHAND01"


def _shapes(p, d):
    ld = d.bit_length() - 1
    return {(side, k): ZK.PubShape(p, 2 * ld, CS.HIDE, CS.NMASK, (CS.NMASK // CS.LIVES) if side == "old" else 0)
            for side in ("old", "new") for k in KINDS}


def schema(p, d, n_old, n_new, pending=False):
    """The handover proof's byte schema: every length a function of (d, n_old, n_new, PARAMS); under cut E also of
    whether the head is pending (from the ledger)."""
    if ZK.DEFER:
        return schema_defer(p, d, n_old, n_new, pending)
    sh = _shapes(p, d)
    nrows = 4 * X.EXT * (-(-sh[("old", "W1")].W // ZK.K_L))
    ro, po, co = PW.pcs_schema(n_old, {k: sh[("old", k)] for k in KINDS})
    rn, pn, cn = PW.pcs_schema(n_new, {k: sh[("new", k)] for k in KINDS})
    n = n_old + n_new
    return ("dict", [("old_roots", ro), ("new_roots", rn), ("eval_roots", PW.L_(n, PW.HH)),
                     ("mask_roots", PW.L_(n, PW.HH)), ("prox_old", po), ("cols_old", co), ("prox_new", pn),
                     ("cols_new", cn), ("ligero", PW.ligero_schema(n, [nrows]))])


def _sizes_ok(d, n_old, n_new):
    return d >= 2 and d & (d - 1) == 0 and d < 1 << 16 and 1 <= n_old <= 255 and 1 <= n_new <= 255


def _magic():
    return MAGIC_E if ZK.DEFER else MAGIC


def encode(p, d, proof):
    n_old, n_new = len(proof["old_roots"]["W1"]), len(proof["new_roots"]["W1"])
    assert _sizes_ok(d, n_old, n_new)
    w = PW.W(p)
    w.b += _magic() + struct.pack(">HBB", d, n_old, n_new)
    PW.walk(w, schema(p, d, n_old, n_new, "c1p" in proof["old_roots"]), PW._plain(proof))
    return bytes(w.b)


def decode(p, blob, d, n_old, n_new, pending=False):
    """d, n_old, n_new (and, under cut E, whether the head is pending) come from the ledger. Raises
    proofwire.ParseError on any deviation from the schema."""
    if not _sizes_ok(d, n_old, n_new):
        raise PW.ParseError("committee sizes or width out of range")
    r = PW.R(p, blob)
    if r.take(8) != _magic():
        raise PW.ParseError("bad magic")
    if struct.unpack(">HBB", r.take(4)) != (d, n_old, n_new):
        raise PW.ParseError("width or committee sizes differ from the ledger's")
    proof = PW.walk(r, schema(p, d, n_old, n_new, pending))
    r.end()
    return proof


def verify_bytes(p, d, n_old, n_new, ctx, old_roots, blob, deferred=None, out=None):
    """The untrusted-input verifier: (ok, why, new_roots). Parsing fails closed before any verification. Cut E:
    deferred = the head's pending claims (proofwire.deferred_of(Ledger.pending)); out receives the new head's."""
    try:
        proof = decode(p, blob, d, n_old, n_new, deferred is not None)
    except PW.ParseError as e:
        return False, f"parse: {e}", None
    except Exception as e:                       # anything else in parsing is a refusal, never a crash
        return False, f"parse: {type(e).__name__}", None
    ok, why = verify(p, d, n_old, n_new, ctx, old_roots, proof, deferred, out)
    return ok, why, (proof["new_roots"] if ok else None)


# ----------------------------------------------------------------------------------------------- cut E (DEFER)
# Under cut E (proof.md sections 21-22) a W has one life and a step does not open its child: the ledger's head is
# "pending" with points r_k and carries c_k (= W_head(r_k), committed by the old committee, second life left). The
# handover then
#   - opens the old head's W1, W2 ONCE (one life, base 0) and evaluates each twice: at the handover point r, and, when
#     the head is pending, at r_k against the old carries c1p, c2p (their second life): the head's DISCHARGE;
#   - does NOT open the new committee's W1, W2: their roots are absorbed before r, and the new committee commits
#     carries cN1, cN2 = new W(r) (each new custodian its own share's evaluation, two lives) after r and before the
#     Ligero's and the PCS columns' challenges; the proof shows old W(r) = cN;
#   - leaves the new head pending: points {"W1": r_1, "W2": r_2}, carry roots {"c1p": cN1, "c2p": cN2}, exactly a
#     step's pending (proofwire.pending_json), which the next step (its parent opening), the release or a closing
#     proof discharges: new W(r) = cN.
# Soundness: new W is fixed (roots absorbed) before r, cN before every challenge its constraints use, so old W(r) =
# cN = new W(r) at a point neither committee chose: 2 log2(d) / |F| per matrix, as before, with the second half
# checked where new W is next opened.
MAGIC_E = b"DLHAND02"


def _dkeys(pending):
    """Absorb order before r: old W, the old carries (pending head), new W."""
    return [("old", k) for k in KINDS] + ([("old", c) for c in ZK.CARRY_IN] if pending else []) + \
        [("new", k) for k in KINDS]


def _dshapes(p, d, pending):
    ld = d.bit_length() - 1
    sh = {(side, k): ZK.w_shape(p, 2 * ld) for side in ("old", "new") for k in KINDS}
    if pending:
        sh.update({("old", c): ZK.carry_shape(p, True) for c in ZK.CARRY_IN})
    sh.update({("new", c): ZK.carry_shape(p, False) for c in ZK.CARRY})
    return sh


def _devals(rpts, dpts):
    """Pairs (W evaluation, carry evaluation): per matrix (old k at r, new carry cN at the zero point), then, for a
    pending head, per matrix (old k at r_k, old carry c_kp at the zero point)."""
    cpt = [X.zero()] * ZK.carry_m()
    ev = []
    for q, k in enumerate(KINDS):
        ev += [(("old", k), rpts[k]), (("new", ZK.CARRY[q]), cpt)]
    if dpts is not None:
        for q, k in enumerate(KINDS):
            ev += [(("old", k), list(dpts[k])), (("old", ZK.CARRY_IN[q]), cpt)]
    return ev


def _dpoints(tr, p, d):
    return {key[1]: pt for key, pt in _schedule(tr, p, d)[::2]}


def _dconstraints(p, sh, evals, cols, urows):
    """PCS consistency of every evaluation at its commitment's opened columns, then per pair W(pt) = carry: the
    handover's old W(r) = cN, and the discharge's old W(r_k) = c_kp (cosnark_zk.close_constraints' form)."""
    lin, labels, cur = [], [], ["?"]
    E = X.EXT
    add = ZK.eadder(p, lin, labels, cur)
    def U(e, c):
        nr = -(-sh[evals[e][0]].W // ZK.K_L)
        return ZK.ecell([(urows[e][k * nr + c // ZK.K_L], c % ZK.K_L) for k in range(E)])
    for e, (key, pt) in enumerate(evals):
        s = sh[key]
        a = s.eval_weights_e(pt)
        J, csum = cols[key]
        cur[0] = f"PCS evaluation consistency ({key[0]} {key[1]})"
        for jj, j in enumerate(J):
            x, xs, forms = s.pts[j], 1, []
            for c in range(s.W):
                forms.append(ZK.evar(p, U(e, c), (xs,)))
                xs = xs * x % p
            add(*forms, rhs=X.dot(a, [(v,) for v in csum[jj]], p))
    for i in range(len(evals) // 2):
        ew, ec = 2 * i, 2 * i + 1
        (wk, pt), (ck, _) = evals[ew], evals[ec]
        s = sh[wk]
        b = X.eqv(pt[:s.mc], p)
        Yf = [dict() for _ in range(E)]
        for c in range(s.C):
            f_ = ZK.evar(p, U(ew, c), b[c])
            for kk in range(E):
                for key, v in f_[kk].items():
                    Yf[kk][key] = (Yf[kk].get(key, 0) + v) % p
        Cf = ZK.evar(p, ZK.ecell([U(ec, k2)[0].popitem()[0] for k2 in range(E)]), X.neg(X.one(), p))
        cur[0] = (f"handover: old {wk[1]}(r) = new carry {ck[1]}" if ck[0] == "new"
                  else f"handover discharge: old {wk[1]}(r_k) = {ck[1]}")
        add(Yf, Cf)
    return lin, labels


def _sum_cols(cc, part, nn, p):
    out = {}
    for k in part:
        J, per = cc[k]
        out[k] = (J, [[sum(per[i][jj][0][r] for i in range(nn)) % p for r in range(part[k].R)] for jj in range(len(J))])
    return out


def prove_defer(p, d, old_coms, new_coms, ctx, seed, deferred, carry_src=None):
    """Cut E's handover (see the section head). old_coms: the head's W (one life, unopened); new_coms: the new
    committee's W (ZK.w_pcs, one life, NOT opened here); deferred: the head step's stats["deferred"] (points r_k,
    carries c1p/c2p held by the old committee) or None for a final head. carry_src (TEST ONLY, refusal row (i)): the
    commitments whose evaluations the new committee commits as cN (default new_coms). Returns (proof, stats);
    stats["deferred"] is the new head's (points, carries {"c1p": cN1, "c2p": cN2}) for the next step's prover."""
    n_old, n_new = len(old_coms["W1"].ext), len(new_coms["W1"].ext)
    n, E = n_old + n_new, X.EXT
    pending = deferred is not None
    com = {("old", k): old_coms[k] for k in KINDS}
    com.update({("new", k): new_coms[k] for k in KINDS})
    for k in KINDS:
        old_coms[k].base = 0                           # the head's single life
    if pending:
        for c in ZK.CARRY_IN:
            cc = deferred["carries"][c]
            cc.base = cc.block                         # the old carry's second life
            com[("old", c)] = cc
    tr = Transcript("handover")
    tr.absorb("ctx", ctx)
    for key in _dkeys(pending):
        tr.absorb(repr(key), com[key].roots)
    rpts = _dpoints(tr, p, d)
    # the new committee's carries cN = new W(r): each new custodian commits its own share's evaluation
    src = carry_src or new_coms
    for q, k in enumerate(KINDS):
        s, r = src[k], rpts[k]
        a, b = s.eval_weights_e(r), X.eqv(r[:s.mc], p)
        ys = [X.dot([tuple(u[kk][cc] for kk in range(E)) for cc in range(s.C)], b, p)
              for u in (s.row_combo_e(j, a) for j in range(n_new))]
        shares = [list(X.pad(y)) + [0] * ((1 << ZK.carry_m()) - E) for y in ys]
        cn = ZK.CARRY[q]
        com[("new", cn)] = ZK.ZKPCS(p, shares, cn, hide=CS.LIVES * CS.T_COLS, nmask=CS.LIVES * E, lives=CS.LIVES)
    tr.absorb("carry", com[("new", "c1")].roots, com[("new", "c2")].roots)
    evals = _devals(rpts, deferred["points"] if pending else None)
    urows, nrows = _rows(com, evals)
    L = Z.Prover(Z.Params(p, ZK.K_L, ZK.T_HIDE, ZK.T_OPEN), n, (seed, ctx))
    for e, (key, pt) in enumerate(evals):
        c = com[key]
        a = c.eval_weights_e(pt)
        own = [c.row_combo_e(i, a) for i in range(len(c.ext))]
        zero = [[0] * c.W for _ in range(E)]
        shares = own + [zero] * n_new if key[0] == "old" else [zero] * n_old + own
        for kk in range(E):
            for s0 in range(0, c.W, ZK.K_L):
                L.add_row([u[kk][s0:s0 + ZK.K_L] for u in shares])
    eval_roots = L.commit()
    mask_roots = L.commit_masks()
    tr.absorb("lig-evals", eval_roots, mask_roots)
    old_part = {key[1]: com[key] for key in com if key[0] == "old"}
    new_part = {c: com[("new", c)] for c in ZK.CARRY}
    _, prox_o, cols_o = CS.pcs_prove(old_part, [], tr, n_old, p)
    _, prox_n, cols_n = CS.pcs_prove(new_part, [], tr, n_new, p)
    cols = {("old", k): v for k, v in _sum_cols(cols_o, old_part, n_old, p).items()}
    cols.update({("new", k): v for k, v in _sum_cols(cols_n, new_part, n_new, p).items()})
    lin, labels = _dconstraints(p, com, evals, cols, urows)
    lig = L.prove(tr, lin, [])
    proof = dict(old_roots={k: old_part[k].roots for k in sorted(old_part)},
                 new_roots={k: new_coms[k].roots for k in KINDS},
                 carry_roots={c: new_part[c].roots for c in ZK.CARRY},
                 eval_roots=eval_roots, mask_roots=mask_roots,
                 prox_old={k: prox_o[k][1] for k in sorted(prox_o)}, cols_old={k: cols_o[k] for k in sorted(cols_o)},
                 prox_new={k: prox_n[k][1] for k in ZK.CARRY}, cols_new={k: cols_n[k] for k in ZK.CARRY},
                 ligero=lig)
    stats = dict(hidden_rows=nrows, lin_constraints=len(lin), ligero_wire=L.wire,
                 first_violated=ZK.first_violated(p, L.rows, lin, [], labels),
                 deferred=dict(points=dict(rpts), carries={"c1p": new_part["c1"], "c2p": new_part["c2"]}))
    return proof, stats


def verify_defer(p, d, n_old, n_new, ctx, old_roots, proof, deferred, out=None):
    """Public data only. old_roots: the ledger head's W roots; deferred: its pending claims (proofwire.deferred_of;
    None for a final head). On acceptance out (if given) receives the new head's pending claims: points {"W1",
    "W2"} and carry_roots {"c1p", "c2p"} (proofwire.pending_json's input)."""
    pending = deferred is not None
    sh = _dshapes(p, d, pending)
    want = sorted(KINDS + (ZK.CARRY_IN if pending else ()))
    if sorted(proof.get("old_roots", {})) != want:
        return False, "handover: the proof names the wrong old commitments for this head"
    if any(proof["old_roots"][k] != old_roots[k] for k in KINDS):
        return False, "handover: old roots are not the ledger head's"
    if pending and any(proof["old_roots"][c] != deferred["carry_roots"][c] for c in ZK.CARRY_IN):
        return False, "handover: the old carries are not the head's pending carries"
    roots = {("old", k): v for k, v in proof["old_roots"].items()}
    roots.update({("new", k): proof["new_roots"][k] for k in KINDS})
    roots.update({("new", c): proof["carry_roots"][c] for c in ZK.CARRY})
    if any(len(v) != (n_old if key[0] == "old" else n_new) for key, v in roots.items()):
        return False, "handover: wrong committee sizes"
    tr = Transcript("handover")
    tr.absorb("ctx", ctx)
    for key in _dkeys(pending):
        tr.absorb(repr(key), roots[key])
    rpts = _dpoints(tr, p, d)
    tr.absorb("carry", roots[("new", "c1")], roots[("new", "c2")])
    evals = _devals(rpts, deferred["points"] if pending else None)
    urows, nrows = _rows(sh, evals)
    tr.absorb("lig-evals", proof["eval_roots"], proof["mask_roots"])
    old_names = [k for _, k in sh if _ == "old"]
    parts = (("old", n_old, old_names, proof["prox_old"], proof["cols_old"]),
             ("new", n_new, list(ZK.CARRY), proof["prox_new"], proof["cols_new"]))
    cols = {}
    for side, nn, names, pr, pc in parts:
        part = {k: sh[(side, k)] for k in names}
        ok, why = CS.pcs_verify(part, {k: roots[(side, k)] for k in names}, [], [], {k: (None, pr[k]) for k in names},
                                pc, tr, nn, p)
        if not ok:
            return False, f"handover ({side} committee): {why}"
        cols.update({(side, k): v for k, v in _sum_cols(pc, part, nn, p).items()})
    lin, _ = _dconstraints(p, sh, evals, cols, urows)
    ok, why = Z.verify(Z.Params(p, ZK.K_L, ZK.T_HIDE, ZK.T_OPEN), n_old + n_new, [proof["eval_roots"]], [nrows],
                       proof["mask_roots"], lin, [], proof["ligero"], tr)
    if not ok:
        return False, why
    if out is not None:
        out.update(points=dict(rpts), carry_roots={"c1p": proof["carry_roots"]["c1"], "c2p": proof["carry_roots"]["c2"]})
    return True, "accept"


def schema_defer(p, d, n_old, n_new, pending):
    sh = _dshapes(p, d, pending)
    old = {k: s for (side, k), s in sh.items() if side == "old"}
    carries = {c: sh[("new", c)] for c in ZK.CARRY}
    ro, po, co = PW.pcs_schema(n_old, old)
    rc, pn, cn = PW.pcs_schema(n_new, carries)
    nrows = sum(X.EXT * -(-sh[key].W // ZK.K_L) for key, _ in _devals({k: [] for k in KINDS},
                                                                       {k: [] for k in KINDS} if pending else None))
    n = n_old + n_new
    return ("dict", [("old_roots", ro), ("new_roots", ("dict", [(k, PW.L_(n_new, PW.HH)) for k in KINDS])),
                     ("carry_roots", rc), ("eval_roots", PW.L_(n, PW.HH)), ("mask_roots", PW.L_(n, PW.HH)),
                     ("prox_old", po), ("cols_old", co), ("prox_new", pn), ("cols_new", cn),
                     ("ligero", PW.ligero_schema(n, [nrows]))])
