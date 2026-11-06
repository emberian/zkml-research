"""The custodied variant of C18 (initiative 16): the statistics are dark, the deletion is still checkable.

2026-11-06. Composes with the dark-learning harness's custody path: the statistics A, B live as SPDZ shares with
MACs (spdz.py, imported unmodified, over a 256-bit prime field q). The records are the host's (public features),
so every insert and delete is a PUBLIC-coefficient update: party 0 adds -m*c to its share, every party adds
-alpha_i*m*c to its MAC share. Zero communication, zero triples (the program's public-coefficient corner).

Two checks, for two audiences:
  * a STRANGER, from commitments alone. Each custodian publishes a Pedersen vector commitment to its share,
    C_i = prod_k g_k^{s_ik} * h^{rho_i} in a 2048-bit Schnorr group of 256-bit prime order q (the SPDZ field), so
    prod_i C_i = Com(S; rho). A deletion of record r with multiplicity m must satisfy
        prod_i C_i'  ==  prod_i C_i * Com(m * contrib(r); 0)^(-1),
    which the stranger checks from the public record and the published commitments, never seeing S. The log legs
    (positions, tombstones, Count = 0) are the host-visible ones, shared code (unlearn_c18.check_delete_log).
  * the CUSTODIANS, against a deviating custodian: a zero test. Fiat-Shamir coins r_k hash the commitments and the
    request (the witness enters the point); the custodians open v = sum_k r_k (S'_k - S_k + m c_k), which is 0 for
    an honest update, and run the SPDZ MAC check. A custodian that changed its share differently opens v != 0;
    one that also lies at the opening fails the MAC check.
The share-to-commitment link (Codex round 2: without it a coalition can publish commitments that do not commit to
the shares it holds, and the stranger's arithmetic is about a fiction) is closed by the SPDZ MAC check lifted to the
exponent. The commitment randomness rho is itself an authenticated shared value, committed under h. Each custodian
also publishes D_i, the same vector commitment to its MAC shares, and A_i = g0^{alpha_i} once at setup. To check,
X = prod C_i; each custodian publishes E_i = X^{alpha_i} with a Chaum-Pedersen proof that log_g0 A_i = log_X E_i;
anyone verifies prod D_i == prod E_i. Honest: prod D_i = Com(alpha S; alpha rho) = X^alpha. A coalition whose
commitments are off by e must offset its MAC commitments by alpha e without knowing alpha (one custodian honest):
it passes with probability 1/q. After a deletion every D_i moves by Com(m c)^(-alpha_i), which custodian i computes.
What is still not built: a release FROM custody (an MPC solve, priced); Pedersen binding is discrete-log, so not
post-quantum (a lattice commitment is the PQ replacement with the same homomorphic and MAC-in-exponent checks).
"""
import hashlib
import json
import os
import random

import spdz
import unlearn_c18 as U

HERE = os.path.dirname(os.path.abspath(__file__))
GROUP_FILE = os.path.join(HERE, "unlearn_custody_group.json")

def _hint(tag, k, bits):
    out, i = b"", 0
    while len(out) * 8 < bits:
        out += hashlib.sha256(f"unlearn-ped-v1:{tag}:{k}:{i}".encode()).digest()
        i += 1
    return int.from_bytes(out, "big") >> (len(out) * 8 - bits)

def _is_prime(n, rounds=24):
    if n < 2:
        return False
    for sp in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % sp == 0:
            return n == sp
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    rng = random.Random(n)
    for _ in range(rounds):
        a = rng.randrange(2, n - 2)
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

def group():
    """Nothing-up-my-sleeve Schnorr group: q = first prime >= hash-derived 256-bit odd; p = k q + 1, the first prime
    with k >= a hash-derived 1792-bit even start. Cached in unlearn_custody_group.json and re-checked on load."""
    if os.path.exists(GROUP_FILE):
        g = json.load(open(GROUP_FILE))
        p, q = int(g["p"], 16), int(g["q"], 16)
        assert _is_prime(q) and _is_prime(p) and (p - 1) % q == 0 and p.bit_length() == 2048
        return p, q
    q = _hint("q", 0, 256) | (1 << 255) | 1
    while not _is_prime(q):
        q += 2
    k = (_hint("k", 0, 1792) | (1 << 1791)) & ~1
    while True:
        p = k * q + 1
        if p.bit_length() == 2048 and _is_prime(p, 2) and _is_prime(p):
            break
        k += 2
    json.dump(dict(p=hex(p), q=hex(q), how=group.__doc__), open(GROUP_FILE, "w"), indent=1)
    return p, q

class Pedersen:
    def __init__(self, nvec):
        self.p, self.q = group()
        cof = (self.p - 1) // self.q
        self.g = [pow(_hint("g", k, 2048) % self.p, cof, self.p) for k in range(nvec)]
        self.h = pow(_hint("h", 0, 2048) % self.p, cof, self.p)
        assert all(x != 1 for x in self.g) and self.h != 1
        self.pows = 0

    def com(self, vec, rho):
        acc = pow(self.h, rho % self.q, self.p)
        for gk, v in zip(self.g, vec):
            if v % self.q:
                acc = acc * pow(gk, v % self.q, self.p) % self.p
                self.pows += 1
        return acc

    def com_small(self, sparse):
        """prod g_k^{v_k} for small nonnegative or negative v (the public contribution): returns the group element."""
        acc = 1
        for k, v in sparse:
            e = pow(self.g[k], abs(v), self.p)
            acc = acc * (e if v > 0 else pow(e, -1, self.p)) % self.p
            self.pows += 1
        return acc

def flat(S):
    A, B = S
    return [v for row in A for v in row] + [v for row in B for v in row]

def contrib_sparse(phi, r, m):
    f, y = phi(r), r[64]
    D = len(f)
    out = []
    for i in range(D):
        for j in range(D):
            if f[i] * f[j]:
                out.append((i * D + j, m * f[i] * f[j]))
    for i in range(D):
        if f[i]:
            out.append((D * D + i * U.NCLASS + y, m * f[i]))
    return out

class Custody:
    """n custodians holding SPDZ shares of the flattened statistics, plus their published commitments."""
    def __init__(self, S, n=3, seed=16, ped=None):
        self.ped = ped
        self.q = ped.q
        self.n = n
        self.dealer = spdz.Dealer(self.q, n, seed)
        self.vals = [dict(enumerate(self.dealer.auth(v, "stat"))) for v in flat(S)]          # custody entry: an ideal authenticated input
        rng = random.Random(seed + 7)
        self.rho = dict(enumerate(self.dealer.auth(rng.randrange(self.q), "rho")))          # authenticated randomness
        self.C = [ped.com([sh[i][0] for sh in self.vals], self.rho[i][0]) for i in range(n)]
        self.Dm = [ped.com([sh[i][1] for sh in self.vals], self.rho[i][1]) for i in range(n)]
        self.g0 = ped.g[-1]
        self.nonce = [hashlib.sha256(f"custodian-nonce:{seed}:{i}".encode()).hexdigest() for i in range(n)]
        self.A = [pow(self.g0, a, ped.p) for a in self.dealer.alpha_sh]

    def joint(self):
        acc = 1
        for c in self.C:
            acc = acc * c % self.ped.p
        return acc

    def delete_local(self, sparse, deviate=None):
        """Public-coefficient update: party 0's share -= v, every MAC share -= alpha_i v. Returns (old, new).
        deviate = (j, sparse2): custodian j moves its own share by -sparse2 instead of the public rule
        (its MAC share follows the public rule: it cannot fix the MAC without alpha)."""
        q, a = self.q, self.dealer.alpha_sh
        old = self.vals
        new = [dict(v) for v in old]
        for k, v in sparse:
            for i in range(self.n):
                s, mac = new[k][i]
                new[k][i] = ((s - v) % q if i == 0 else s, (mac - a[i] * v) % q)
        if deviate:
            j, sp2 = deviate
            cm = dict(sparse)
            for k, v2 in sp2:
                s, mac = new[k][j]
                new[k][j] = ((s - v2 + (cm.get(k, 0) if j == 0 else 0)) % q, mac)
        U.CNT.add("custody_local_updates", len(sparse) * self.n)
        return old, new

def dleq_prove(ped, g0, X, a, tag):
    k = int.from_bytes(hashlib.sha256(repr(("dleq-nonce", tag, a)).encode()).digest(), "big") % ped.q
    t1, t2 = pow(g0, k, ped.p), pow(X, k, ped.p)
    A, E = pow(g0, a, ped.p), pow(X, a, ped.p)
    c = int.from_bytes(hashlib.sha256(repr(("dleq", g0, X, A, E, t1, t2)).encode()).digest(), "big") % ped.q
    return E, (t1, t2, (k + c * a) % ped.q)

def dleq_verify(ped, g0, X, A, E, pf):
    t1, t2, z = pf
    c = int.from_bytes(hashlib.sha256(repr(("dleq", g0, X, A, E, t1, t2)).encode()).digest(), "big") % ped.q
    ped.pows += 4
    return pow(g0, z, ped.p) == t1 * pow(A, c, ped.p) % ped.p and pow(X, z, ped.p) == t2 * pow(E, c, ped.p) % ped.p

def exponent_mac_check(ped, cust, C, Dm, tag):
    """Anyone: prod Dm_i == prod_i (prod_j C_j)^{alpha_i}, each factor with a Chaum-Pedersen proof."""
    X = 1
    for c in C:
        X = X * c % ped.p
    lhs, rhs = 1, 1
    for i in range(cust.n):
        E, pf = dleq_prove(ped, cust.g0, X, cust.dealer.alpha_sh[i], (tag, i))      # custodian i
        if not dleq_verify(ped, cust.g0, X, cust.A[i], E, pf):
            return False
        rhs = rhs * E % ped.p
        lhs = lhs * Dm[i] % ped.p
    return lhs == rhs

def zero_coins(cust, new, coins_seed, legacy=False):
    """The zero test's coins. Fixed (Codex round 2): every custodian first hash-commits to its updated (share, MAC)
    vector and the coins hash those commitments, so no custodian can pick its deviation after seeing the coins.
    legacy=True: coins from the public commitments and the request only (predictable before the update)."""
    if legacy:
        seed = hashlib.sha256(coins_seed).digest()
    else:
        hc = [hashlib.sha256(repr((i, [new[k][i] for k in range(len(new))], cust.nonce[i])).encode()).digest()
              for i in range(cust.n)]
        seed = hashlib.sha256(coins_seed + b"".join(hc)).digest()
    rng = random.Random(seed)
    return [rng.randrange(1, cust.q) for _ in range(len(new))]

def zero_test(cust, old, new, sparse, coins_seed, lie=None, legacy=False):
    """Open v = sum r_k (S'_k - S_k + c_k) and MAC-check it. lie = (party, delta): that party shifts its opened share."""
    q = cust.q
    eng = spdz.Engine(q, cust.n, cust.dealer, cheat=({"party": lie[0], "at_open": 0, "delta": lie[1]} if lie else None))
    cmap = dict(sparse)
    coins = zero_coins(cust, new, coins_seed, legacy)
    U.CNT.add("zero_test_hash_commitments", 0 if legacy else cust.n)
    terms = []
    v = {i: (0, 0) for i in range(cust.n)}
    for k in range(len(new)):
        r = coins[k]
        diff = {i: ((new[k][i][0] - old[k][i][0]) % q, (new[k][i][1] - old[k][i][1]) % q) for i in range(cust.n)}
        v = {i: ((v[i][0] + r * diff[i][0]) % q, (v[i][1] + r * diff[i][1]) % q) for i in range(cust.n)}
        if k in cmap:
            v = eng.cadd(r * cmap[k] % q, v)
    try:
        opened = eng.open(v, "zero-test")
        if opened != 0:
            return False, f"zero test: opened {opened % 1000}... != 0 (a custodian's share update is not the public one)", eng
        eng.mac_check(coins_seed.hex())
    except spdz.Abort as e:
        return False, f"zero test: {e}", eng
    return True, "ok", eng

def stranger_check(ped, C_old, C_new_parts, sparse):
    """From commitments alone: prod C_i' == C * Com(contrib)^-1."""
    joint = 1
    for c in C_new_parts:
        joint = joint * c % ped.p
    X = ped.com_small(sparse)
    return joint == C_old * pow(X, -1, ped.p) % ped.p

def run(RESULTS, n_del=4, seed=16):
    tra = U.load("optdigits.tra")
    phi = U.Phi("ident-bias-v1")
    lam = 1
    gen = U.Genesis(phi, lam, dict(dataset="UCI optdigits", files=U.OPTDIGITS))
    host = U.Host(gen)
    rng = random.Random(seed)
    dup = tra[rng.randrange(len(tra))]
    stream = list(tra)
    stream.insert(rng.randrange(len(stream)), dup)
    for r in stream:                                        # the host's log; stats enter custody below
        cert, st = host.insert(r)
        host.commit(cert, st)
    D = phi.D
    ped = Pedersen(D * D + D * U.NCLASS + 1)               # the last generator is g0 for the alpha commitments
    cust = Custody(host.S, seed=seed, ped=ped)
    entry_pows = ped.pows
    p0 = ped.pows
    link_entry = exponent_mac_check(ped, cust, cust.C, cust.Dm, "entry")
    link_pows = ped.pows - p0
    # K5/K6: a coalition publishes commitments that do not commit to its shares (off by e = -contrib(d) at entry)
    dkey = U.content_key(dup)
    e_sparse = contrib_sparse(phi, dup, 1)
    off = pow(ped.com_small(e_sparse), -1, ped.p)
    C_bad = [cust.C[0], cust.C[1] * off % ped.p] + cust.C[2:]
    k5 = not exponent_mac_check(ped, cust, C_bad, cust.Dm, "k5")
    Dm_bad = [cust.Dm[0], cust.Dm[1] * pow(off, cust.dealer.alpha_sh[1], ped.p) % ped.p] + cust.Dm[2:]
    k6 = not exponent_mac_check(ped, cust, C_bad, Dm_bad, "k6")
    print(f"[custody] share-to-commitment link (MAC in the exponent) at entry: {link_entry} ({link_pows} exponentiations)")
    print(f"  {'REFUSED' if k5 else 'ACCEPTED'}  K5 a custodian's commitment does not commit to its share (off by contrib(d))")
    print(f"  {'REFUSED' if k6 else 'ACCEPTED'}  K6 ... and it offsets its MAC commitment by alpha_1 * e (it does not know alpha)")
    ok_link = link_entry and k5 and k6
    print(f"[custody] {cust.n} custodians, SPDZ over a {cust.q.bit_length()}-bit field; {len(cust.vals)} shared "
          f"statistics; per-custodian Pedersen commitments ({entry_pows} exponentiations at custody entry)")
    keys = [U.content_key(dup)] + [U.content_key(r) for r in rng.sample([r for r in tra if r != dup], n_del - 1)]
    rows, ok = [], True
    for c in keys:
        cert, st = host.delete(c)
        lok, lwhy, _ = U.check_delete_log(host.head["log_root"], host.head["log_len"], cert)
        m = len(cert["positions"])
        sparse = contrib_sparse(phi, cert["record"], m)
        C_old = cust.joint()
        old, new = cust.delete_local(sparse)
        D0 = pow(ped.com_small(sparse), -1, ped.p)
        C_new = [cust.C[0] * D0 % ped.p] + cust.C[1:]
        Dm_new = [cust.Dm[i] * pow(D0, cust.dealer.alpha_sh[i], ped.p) % ped.p for i in range(cust.n)]
        p0 = ped.pows
        s_ok = stranger_check(ped, C_old, C_new, sparse)
        stranger_pows = ped.pows - p0
        coins = hashlib.sha256(repr((C_old, C_new, c)).encode()).digest()
        z_ok, z_why, eng = zero_test(cust, old, new, sparse, coins)
        p1 = ped.pows
        l_ok = exponent_mac_check(ped, cust, C_new, Dm_new, coins.hex())
        link_pows_del = ped.pows - p1
        ok &= lok and s_ok and z_ok and l_ok
        rows.append(dict(multiplicity=m, log_legs=lok, stranger_check=s_ok, custodian_zero_test=z_ok,
                         link_check=l_ok, link_check_exponentiations=link_pows_del,
                         local_updates_per_party=len(sparse), stranger_small_exponentiations=stranger_pows,
                         wire_elements=sum(eng.wire.values())))
        # attacks against THIS deletion, before it is committed
        if c == keys[1]:
            other = contrib_sparse(phi, host.records[keys[2]], 1)
            att = []
            att.append(("K1 commitments unchanged (deletion claimed, nothing subtracted)",
                        not stranger_check(ped, C_old, cust.C, sparse)))
            D2 = pow(ped.com_small(other), -1, ped.p)
            att.append(("K2 commitment subtracts a different record",
                        not stranger_check(ped, C_old, [cust.C[0] * D2 % ped.p] + cust.C[1:], sparse)))
            o2, n2 = cust.delete_local(sparse, deviate=(1, other))
            zk, zw, _ = zero_test(cust, o2, n2, sparse, coins)
            att.append(("K3 custodian 1 updates its share with a different record (honest commitment published)",
                        not zk and "opened" in zw))
            # K4: same deviation, and custodian 1 shifts its opened share so that v opens to 0
            _, _, e_probe = zero_test(cust, o2, n2, sparse, coins)
            v_bad = e_probe.transcript[0][2]
            zk4, zw4, _ = zero_test(cust, o2, n2, sparse, coins, lie=(1, (-v_bad) % cust.q))
            # K4 is NOT a refusal: lying at the opening back to the honest value is MAC-consistent, because the
            # MAC shares followed the public rule. What custody can ever open is the AUTHENTICATED value, which is the
            # honest one; a raw-share deviation is a future lie that the MAC check catches unless it restores that
            # value (Codex round 2). Expected outcome: accepted, and the opened value is the honest 0.
            att.append(("K4 ... and lies at the opening back to 0: ACCEPTED as expected (the authenticated value is "
                        "the honest one; the raw share is not what any opening can use)", zk4))
            # K7 (Codex round 2): custodian 1 keeps part of d's contribution in its share with an error e chosen
            # orthogonal to the coins; its MAC shares follow the public rule, so the opened value and MAC both pass
            # when the coins are predictable (legacy), and fail once the coins hash the committed updated shares
            rl = zero_coins(cust, new, coins, legacy=True)
            k1, k2 = sparse[0][0], sparse[1][0]
            o7, n7 = cust.delete_local(sparse)
            for kk, ev in ((k1, rl[k2]), (k2, -rl[k1] % cust.q)):
                s_, m_ = n7[kk][1]
                n7[kk][1] = ((s_ + ev) % cust.q, m_)
            legacy_ok, _, _ = zero_test(cust, o7, n7, sparse, coins, legacy=True)
            fixed_ok, fixed_why, _ = zero_test(cust, o7, n7, sparse, coins)
            att.append(("K7 an error orthogonal to predictable coins: ACCEPTED by the legacy zero test (falsifier bites)",
                        legacy_ok))
            att.append(("K7 ... refused once the coins hash the custodians' committed updated shares (a custodian that "
                        "does not lie at the opening)", not fixed_ok))
            for name, as_expected in att:
                print(f"  {'AS EXPECTED' if as_expected else 'UNEXPECTED'}  {name}")
            ok &= all(r for _, r in att)
            RESULTS.setdefault("custody", {})["attacks"] = [dict(attack=a, outcome_as_expected=r) for a, r in att]
        cust.vals = new
        cust.C, cust.Dm = C_new, Dm_new
        host.commit(cert, st)
    # the dark state equals the never-trained statistics: reconstruct once (an audit opening, here only to check)
    S_rec = [sum(v[i][0] for i in range(cust.n)) % cust.q for v in cust.vals]
    S_rec = [x - cust.q if x > cust.q // 2 else x for x in S_rec]
    exact = S_rec == flat(host.S)
    print(f"[custody] {len(keys)} deletions: log legs, stranger check and custodian zero test all pass: {ok}; "
          f"reconstructed dark state == host-visible fold over the remaining records: {exact}")
    ok &= exact and ok_link
    RESULTS.setdefault("custody", {}).update(dict(
        link_entry=link_entry, link_entry_exponentiations=link_pows, K5_refused=k5, K6_refused=k6,
        custodians=cust.n, field_bits=cust.q.bit_length(), group_bits=ped.p.bit_length(), shared_values=len(cust.vals),
        entry_exponentiations=entry_pows, deletions=rows, dark_state_exact=exact, all_ok=ok,
        not_built=["release from custody (MPC solve)", "post-quantum commitment"]))
    return ok
