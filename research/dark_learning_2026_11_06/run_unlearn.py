"""Initiative 16 milestone: train, commit, delete, certify, attack. Counts only.

    python3 run_unlearn.py [c18] [c19] [sgd] [custody]      (default: all; writes unlearn_results.json)

C18 on optdigits (3,823 train records + 1 duplicate, 1,797 test). Every attack is a mutation of an honest
certificate and must be REFUSED by the named check; the run fails otherwise.
"""
import copy
import json
import random
import sys

import unlearn_c18 as U

RESULTS = {}

def snap(label):
    return dict(U.CNT)

def delta(before):
    return {k: U.CNT.get(k, 0) - before.get(k, 0) for k in U.CNT if U.CNT.get(k, 0) != before.get(k, 0)}

def choose_lam(phi, tra):
    """lam chosen on a split of the TRAIN file only (first 3,000 fit, last 823 validate)."""
    fit, val = tra[:3000], tra[3000:]
    S = U.fold(fit, phi)
    scores = {}
    for lam in (1, 4, 16, 64, 256):
        N, den = U.solve(S, lam)
        scores[lam] = U.accuracy(N, phi, val)
    best = max(scores, key=lambda l: (scores[l], -l))
    return best, scores

def expect_refused(name, led, cert, needle, table):
    led2 = copy.deepcopy(led)
    ok, why = led2.accept(cert)
    good = (not ok) and needle in why
    table.append(dict(attack=name, accepted=ok, reason=why, refused_by_expected_check=good))
    print(f"  {'REFUSED' if not ok else 'ACCEPTED'}  {name}: {why}")
    return good

def run_c18(phi=None, label="c18", n_delete=9, seed=16):
    tra, tes = U.load("optdigits.tra"), U.load("optdigits.tes")
    phi = phi or U.Phi("ident-bias-v1")
    lam = 1
    lam_scores = None
    print(f"[{label}] D = {phi.D}; lam = {lam} PINNED a priori (a lam chosen on deletable records would depend on "
          f"them: Codex round 1; no data-dependent sweep is run: Codex round 2)")
    gen = U.Genesis(phi, lam, dict(dataset="UCI optdigits", files=U.OPTDIGITS))
    host, led = U.Host(gen), U.Ledger(gen)
    rng = random.Random(seed)
    dup = tra[rng.randrange(len(tra))]
    stream = list(tra)
    stream.insert(rng.randrange(len(stream)), dup)          # one record submitted twice
    per = {}
    # ---- training: every insert is a certified event the verifier replays from genesis
    vtrain = {}
    for k, r in enumerate(stream):
        cert, st = host.insert(r)
        b = snap("ins")                                      # verifier-side counts only
        ok, why = led.accept(cert)
        assert ok, why
        host.commit(cert, st)
        for kk, vv in delta(b).items():
            vtrain[kk] = vtrain.get(kk, 0) + vv
        if k == len(stream) - 1:
            per["insert"] = delta(b)
    per["training_total_verifier"] = vtrain
    cert, st = host.release()
    b = snap("rel")
    ok, why = led.accept(cert)
    assert ok, why
    host.commit(cert, st)
    per["release"] = delta(b)
    model0 = cert["new_head"]["model"]
    acc0 = U.accuracy(cert["N"], phi, tes)
    print(f"[{label}] trained on {len(stream)} records; test accuracy {acc0}/{len(tes)}; delta bits "
          f"{cert['delta'].bit_length()}")
    # ---- deletions: the duplicate (two copies) and n_delete others, by content key
    keys = [U.content_key(dup)]
    others = rng.sample([r for r in tra if r != dup], n_delete)
    keys += [U.content_key(r) for r in others]
    deleted_rows = [dup, dup] + others
    pre_delete = (copy.deepcopy(host), copy.deepcopy(led))
    for i, c in enumerate(keys):
        cert, st = host.delete(c)
        b = snap("del")
        ok, why = led.accept(cert)
        assert ok, why
        host.commit(cert, st)
        per.setdefault("delete_m%d" % len(cert["positions"]), delta(b))
        if i == 0:
            s_ok, s_why = led.serve(model0)
            assert not s_ok
    b = snap("rel2")
    cert, st = host.release()
    ok, why = led.accept(cert)
    assert ok, why
    host.commit(cert, st)
    acc1 = U.accuracy(cert["N"], phi, tes)
    # ---- exactness: trained-then-deleted vs never-trained, byte for byte
    remaining = list(stream)
    for r in deleted_rows:
        remaining.remove(r)
    S_never = U.fold(remaining, phi)
    N2, d2 = U.solve(S_never, lam)
    never_stats = U.stats_commit(S_never)
    never_model = U.model_commit(never_stats, lam, N2, d2)
    exact_stats = led.head["stats"] == never_stats
    exact_model = led.head["model"] == never_model
    tombs = sum(v == U.tomb(j) for j, v in enumerate(host.values))
    absent = all(sum(v == c for v in host.values) == 0 for c in keys)
    print(f"[{label}] deleted {len(keys)} keys ({len(deleted_rows)} records); test accuracy {acc1}/{len(tes)}")
    print(f"[{label}] EXACT: stats commitment equal to never-trained: {exact_stats}; model commitment equal: "
          f"{exact_model}; log differs by {tombs} tombstones (accountability); every key absent: {absent}")
    assert exact_stats and exact_model and absent
    s_old, _ = led.serve(model0)
    s_new, _ = led.serve(led.head["model"])
    assert not s_old and s_new
    # ---- attacks against the deletion of the duplicate and of one other record
    host0, led0 = pre_delete
    table = []
    good = True
    c_dup, c_one = keys[0], keys[1]
    r_one = others[0]
    c_two = keys[2]
    honest, st = host0.delete(c_one)
    # A1 fake deletion that keeps the record
    a = copy.deepcopy(honest); a["new_head"]["stats"] = led0.head["stats"]
    good &= expect_refused("A1a keep the record in the statistics (log tombstoned)", led0, a, "'stats'", table)
    a = copy.deepcopy(honest); a["positions"], a["paths"] = [], []
    good &= expect_refused("A1b keep the record in the log (no position tombstoned)", led0, a, "positions empty", table)
    a = copy.deepcopy(honest); a["log_after"] = host0.values; a["new_head"]["log_root"] = led0.head["log_root"]
    good &= expect_refused("A1c claim deletion with the log unchanged", led0, a, "", table)
    # A2 deletion that removes a different record
    other_pos = host0.values.index(c_two)
    a = copy.deepcopy(honest); a["positions"] = [other_pos]; a["paths"] = [U.path_of(host0.values, other_pos)]
    good &= expect_refused("A2a tombstone a different record's position", led0, a, "does not open", table)
    a = copy.deepcopy(honest); a["record"] = host0.records[c_two]
    good &= expect_refused("A2b present a different record's bytes for the key", led0, a, "do not hash", table)
    a = copy.deepcopy(honest)
    S_bad = U.copy_stats(led0.S); U.add_contrib(S_bad, phi(host0.records[c_two]), host0.records[c_two][64], sign=-1, count=False)
    a["new_head"]["stats"] = U.stats_commit(S_bad)
    good &= expect_refused("A2c tombstone the right leaf, subtract a different record", led0, a, "'stats'", table)
    # A3 a state trained on d that claims not
    led1, host1 = copy.deepcopy(led0), copy.deepcopy(host0)
    ok, _ = led1.accept(honest); host1.commit(honest, st)
    assert ok
    N_old, d_old = U.solve(host0.S, lam)
    rel = dict(kind="release", parent=U.head_hash(led1.head), N=N_old, delta=d_old,
               new_head=dict(led1.head, parent=U.head_hash(led1.head), seq=led1.head["seq"] + 1,
                             model=U.model_commit(led1.head["stats"], lam, N_old, d_old)))
    good &= expect_refused("A3a release the model trained on d after its deletion", led1, rel, "!= delta B", table)
    s_ok, s_why = led1.serve(model0)
    table.append(dict(attack="A3b serve the pre-deletion model after deletion (C20)", accepted=s_ok, reason=s_why,
                      refused_by_expected_check=not s_ok))
    print(f"  {'REFUSED' if not s_ok else 'ACCEPTED'}  A3b serve the pre-deletion model after deletion (C20): {s_why}")
    good &= not s_ok
    # unlogged training: an insert whose statistics also carry d
    h2 = copy.deepcopy(host1)
    newrec = tes[0]
    ins, _ = h2.insert(newrec)
    S_bad = U.copy_stats(host1.S)
    U.add_contrib(S_bad, phi(newrec), newrec[64], count=False)
    U.add_contrib(S_bad, phi(r_one), r_one[64], count=False)
    ins["new_head"]["stats"] = U.stats_commit(S_bad)
    good &= expect_refused("A3c re-train on d silently inside a later insert", led1, ins, "'stats'", table)
    # A4 the C18 falsifier: a duplicate deleted once
    hd = copy.deepcopy(host0)
    a, _ = hd.delete(c_dup)
    assert len(a["positions"]) == 2
    j0 = a["positions"][0]
    vals = list(hd.values); vals[j0] = U.tomb(j0)
    S_bad = U.copy_stats(led0.S); U.add_contrib(S_bad, phi(dup), dup[64], sign=-1, count=False)
    a["positions"], a["paths"], a["log_after"] = [j0], [U.path_of(hd.values, j0)], vals
    a["new_head"]["log_root"], a["new_head"]["stats"] = U.bag(U.build_peaks(vals)), U.stats_commit(S_bad)
    good &= expect_refused("A4 duplicate deleted once (C18 falsifier 1)", led0, a, "Count(key) = 1", table)
    # A5 phi changed after accumulation
    a = copy.deepcopy(honest)
    f2 = [2 * v for v in phi(r_one)]
    S_bad = U.copy_stats(led0.S); U.add_contrib(S_bad, f2, r_one[64], sign=-1, count=False)
    a["new_head"]["stats"] = U.stats_commit(S_bad)
    good &= expect_refused("A5a subtract with a changed feature map (C18 falsifier 2)", led0, a, "'stats'", table)
    a = copy.deepcopy(honest); a["new_head"]["genesis"] = U.H("genesis", "another phi")
    good &= expect_refused("A5b a head under a different genesis (phi, lam)", led0, a, "does not extend", table)
    # A6 singular system: without lam > 0 the release is not unique
    zero_cols = [i for i in range(phi.D) if all(led.S[0][i][j] == 0 for j in range(phi.D))]
    lam0 = None
    if zero_cols:
        # at lam = 0 the zero rows of A leave those rows of N free: two different models pass the release check
        A0, B0 = led.S
        keep = [i for i in range(phi.D) if i not in zero_cols]
        Nk, dk = U.solve(([[A0[i][j] for j in keep] for i in keep], [B0[i] for i in keep]), 0)
        Na = [[0] * U.NCLASS for _ in range(phi.D)]
        for t, i in enumerate(keep):
            Na[i] = Nk[t]
        Nb = [row[:] for row in Na]
        Nb[zero_cols[0]] = [dk] * U.NCLASS                  # weight 1 on an always-zero pixel, every class
        Na, da = U.canonical(Na, dk)
        Nb, db = U.canonical(Nb, dk)
        both = U.check_release(led.S, 0, Na, da)[0] and U.check_release(led.S, 0, Nb, db)[0]
        lam0 = dict(zero_feature_columns=zero_cols, two_distinct_models_pass_at_lam0=both and Na != Nb)
        print(f"  [falsifier bites] lam = 0: two distinct canonical models pass (lam I + A) N = delta B: {both and Na != Nb}")
        good &= bool(both and Na != Nb)
    # with lam pinned, a second encoding of the model is refused, and lam <= 0 cannot be pinned
    try:
        U.Genesis(phi, 0, {})
        lam0_refused = False
    except AssertionError:
        lam0_refused = True
    table.append(dict(attack="A6a genesis with lam = 0 (C18 falsifier 3, singular system)", accepted=not lam0_refused,
                      reason="Genesis refuses lam <= 0" if lam0_refused else "accepted", refused_by_expected_check=lam0_refused,
                      lam0_nonuniqueness=lam0))
    print(f"  {'REFUSED' if lam0_refused else 'ACCEPTED'}  A6a genesis with lam = 0; zero feature columns in A: {zero_cols}")
    good &= lam0_refused
    N1, d1 = U.solve(led1.S, lam)
    a = dict(kind="release", parent=U.head_hash(led1.head), N=[[2 * v for v in row] for row in N1], delta=2 * d1,
             new_head=dict(led1.head, parent=U.head_hash(led1.head), seq=led1.head["seq"] + 1,
                           model=U.model_commit(led1.head["stats"], lam, [[2 * v for v in row] for row in N1], 2 * d1)))
    good &= expect_refused("A6b a second encoding of the same model (non-canonical)", led1, a, "canonical", table)
    # A7 stale parent: replay the honest deletion after it was accepted
    good &= expect_refused("A7 replay the deletion against the next head (stale parent)", led1, honest, "parent", table)
    # A8 omission or substitution in the absence leg
    a = copy.deepcopy(honest); a["log_after"] = a["log_after"][:-1]
    good &= expect_refused("A8a drop one leaf from the whole-log opening", led0, a, "rebuild", table)
    a = copy.deepcopy(honest); la = list(a["log_after"]); la[5] = U.tomb(5); a["log_after"] = la
    good &= expect_refused("A8b substitute one leaf in the whole-log opening", led0, a, "rebuild", table)
    # A9 equivocation: a second, different child of the same parent after the first is accepted
    other, _ = host0.delete(c_two)
    good &= expect_refused("A9 a second child of the same parent (fork)", led1, other, "parent", table)
    # A10 delete a record that was never inserted
    ghost = tes[1]
    gk = U.content_key(ghost)
    a = copy.deepcopy(honest); a["key"], a["record"] = gk, ghost
    good &= expect_refused("A10 delete a record that was never inserted", led0, a, "does not open", table)
    # A11 (Codex round 1) a release whose N carries an extra row: the deleted record smuggled into the model commitment
    N1, d1 = U.solve(led1.S, lam)
    Nx = [row[:] for row in N1] + [list(r_one[:U.NCLASS])]
    a = dict(kind="release", parent=U.head_hash(led1.head), N=Nx, delta=d1,
             new_head=dict(led1.head, parent=U.head_hash(led1.head), seq=led1.head["seq"] + 1,
                           model=U.model_commit(led1.head["stats"], lam, Nx, d1)))
    good &= expect_refused("A11 release with an extra row carrying the deleted record (Codex r1)", led1, a, "D x 10", table)
    # A13 (Codex round 2) a head with an extra field carrying the deleted record
    a = copy.deepcopy(honest); a["new_head"]["payload"] = list(r_one)
    good &= expect_refused("A13 a head with an extra field carrying the deleted record (Codex r2)", led0, a, "fields other", table)
    # A12 a record with a trailing payload element (its content key ignores the payload)
    a = copy.deepcopy(honest); a["record"] = tuple(r_one) + (99,)
    good &= expect_refused("A12 a record with a trailing payload element", led0, a, "not a 64-feature", table)
    print(f"[{label}] attacks: {sum(t['refused_by_expected_check'] for t in table)}/{len(table)} refused by the expected check")
    RESULTS[label] = dict(
        D=phi.D, lam=lam, lam_validation=lam_scores, records=len(stream), duplicate_inserted=True,
        test_accuracy_before=acc0, test_accuracy_after=acc1, test_size=len(tes), keys_deleted=len(keys),
        records_deleted=len(deleted_rows), exact_stats_equal_never_trained=exact_stats,
        exact_model_equal_never_trained=exact_model, tombstones=tombs, every_key_absent=absent,
        per_certificate_counts=per, attacks=table, all_attacks_refused=good,
        verifier_holds=dict(stats_integers=phi.D * phi.D + phi.D * U.NCLASS, head_fields=7),
        absence_leg_bytes=32 * len(stream))
    return good

def main(argv):
    which = argv or ["c18", "c19", "sgd", "custody"]
    ok = True
    if "c18" in which:
        ok &= run_c18()
    if "c19" in which:
        import unlearn_c19
        ok &= unlearn_c19.run(RESULTS, run_c18)
    if "sgd" in which:
        import unlearn_sgd
        ok &= unlearn_sgd.run(RESULTS)
    if "custody" in which:
        import unlearn_custody
        ok &= unlearn_custody.run(RESULTS)
    out = "unlearn_results.json" if not argv else "unlearn_results_%s.json" % "_".join(which)
    with open(out, "w") as f:
        json.dump(RESULTS, f, indent=1, default=lambda o: o.hex() if isinstance(o, bytes) else str(o))
    print("UNLEARN", "PASS" if ok else "FAIL")
    return ok

if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1:]) else 1)
