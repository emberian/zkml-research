#!/usr/bin/env python3
"""Erasure and handover checks of a deployed dl-custodian handover, from the Mac over ssh (handover lane).

    check_handover.py RUN.json OUT [--self] [--tools HOST=DL_HAND ...] [--profile ledger-sq] [--no-relaunch]

RUN.json is the deploy lane's run config (native/deploy/run.py). The layout is
ROOT/NAME/seatI for the old seats and ROOT/NAME/newJ for the new ones, each with D/, tls/ and <name>.cmd.
Every seat dir is read only, except for the relaunch.
- Rotation (default): the old seats' D/handover_P<I>.json; the new seats' D/join_P<J>.json, D/ledger_P<J>.jsonl
  and D/handover_e<E>.bin.
- --self: the seats' D/self_handover_P<I>.json and D/ledger_P<I>.jsonl.

Per old seat, rotation:
- the memory scan before erasure (control) and after;
- the disk scan before (control) and after;
- the pre-handover decryption (control) and the post-erasure one;
- the state files gone, checked by the report and by a remote stat of every secret file;
- the restarted seat: `dl-hand restart-seat` on its box, with its own argv;
- a relaunch of the exact `serve` command line and of its --resume variant, each of which must exit non-zero
  before it can sign anything (no TLS key).

Per new seat: the MAC check under its own key, its own decryption (control), the same proof digest as every old
seat, and its replica's rotation record. Natively, on its box: `dl-hand verify-rotation`, which also checks that a
one-byte flip is refused. All three replicas must be equal up to the rotation.

Exits 0 when every check holds. Writes OUT/checks.json and OUT/measure.json. The replay with
`proofwire.py replay` is a separate job (`replay.sh`, written to OUT).
"""
import hashlib, json, os, shlex, subprocess, sys, time

def sh(host, cmd, check=True, timeout=None):
    r = subprocess.run(["ssh", "-o", "BatchMode=yes", host, cmd], text=True, capture_output=True, timeout=timeout)
    if check and r.returncode != 0:
        raise SystemExit(f"[{host}] {cmd}\n{r.stdout}\n{r.stderr}")
    return r

def fetch(host, path, local):
    r = subprocess.run(["scp", "-q", f"{host}:{path}", local], capture_output=True, text=True)
    return r.returncode == 0

def cmd_argv(cmdline):
    """'cd DIR && ENV CMD' (run.py's <name>.cmd) -> (dir, env, the command tokens, dl-custodian's argv)."""
    toks = shlex.split(cmdline)
    assert toks[0] == "cd" and toks[2] == "&&", cmdline
    d, rest = toks[1], toks[3:]
    k = next(i for i, t in enumerate(rest) if t.endswith("/dl-custodian"))
    env = [t for t in rest[:k] if "=" in t and not t.startswith("-") and t.split("=")[0].isupper()]
    return d, env, rest, rest[k + 1:]

def main():
    a = sys.argv[1:]
    cfg = json.load(open(a[0]))
    out = a[1]
    self_mode = "--self" in a
    relaunch = "--no-relaunch" not in a
    prof = a[a.index("--profile") + 1] if "--profile" in a else "ledger"
    tools = {}
    if "--tools" in a:
        for t in a[a.index("--tools") + 1:]:
            if "=" not in t or t.startswith("--"):
                break
            h, p = t.split("=", 1)
            tools[h] = p
    os.makedirs(out, exist_ok=True)
    name = cfg["name"]
    N, L, F, d = cfg["prof"]
    olds = [(i, s["host"], f"{s['root']}/{name}/seat{i}") for i, s in enumerate(cfg["seats"])]
    news = [] if self_mode else [(j, s["host"], f"{s['root']}/{name}/new{j}") for j, s in enumerate(cfg["handover"]["new_seats"])]
    checks = []
    def ck(who, what, ok, detail=None):
        checks.append({"seat": who, "check": what, "ok": bool(ok), "detail": detail})
        print(f"{'ok  ' if ok else 'FAIL'} [{who}] {what}" + (f"  ({detail})" if detail is not None and not ok else ""), flush=True)
    # ---- reports
    rep_old, rep_new = {}, {}
    for i, h, sd in olds:
        lp = os.path.join(out, f"old{i}.json")
        fn = f"self_handover_P{i}.json" if self_mode else f"handover_P{i}.json"
        got = fetch(h, f"{sd}/D/{fn}", lp)
        v = json.load(open(lp)) if got else {"error": "no report"}
        rep_old[i] = v
        fetch(h, f"{sd}/serve{i}.cmd", os.path.join(out, f"serve{i}.cmd"))
        fetch(h, f"{sd}/serve{i}.mon", os.path.join(out, f"serve{i}.mon"))
        fetch(h, f"{sd}/serve{i}.log", os.path.join(out, f"serve{i}.log"))
    for j, h, sd in news:
        lp = os.path.join(out, f"join{j}.json")
        v = json.load(open(lp)) if fetch(h, f"{sd}/D/join_P{j}.json", lp) else {"error": "no report"}
        rep_new[j] = v
        fetch(h, f"{sd}/D/ledger_P{j}.jsonl", os.path.join(out, f"ledger_new{j}.jsonl"))
        fetch(h, f"{sd}/new{j}.cmd", os.path.join(out, f"new{j}.cmd"))
        fetch(h, f"{sd}/new{j}.mon", os.path.join(out, f"new{j}.mon"))
    if self_mode:
        for i, h, sd in olds:
            fetch(h, f"{sd}/D/ledger_P{i}.jsonl", os.path.join(out, f"ledger_seat{i}.jsonl"))
    # ---- per old seat (the old role in --self)
    digests = []
    for i, h, sd in olds:
        v = rep_old[i]
        who = f"old {i} @ {h}"
        o = v.get("old_role", v) if self_mode else v
        ck(who, "report present, no error", "error" not in v, v.get("error"))
        if "error" in v:
            continue
        digests.append(o.get("proof_sha256"))
        sb, sa = o.get("scan_before_erasure", {}), o.get("scan_after_erasure", {})
        ck(who, "memory scan ran (Linux /proc)", sb.get("available") is True and sa.get("available") is True)
        ck(who, "memory scan before erasure finds the material (control)", sb.get("hits", 0) > 0, sb.get("hits"))
        ck(who, "memory scan after erasure finds none of it", sa.get("hits") == 0, sa.get("hits_by_kind"))
        db, da = o.get("disk_scan_before_erasure", {}), o.get("disk_scan_after_erasure", {})
        ck(who, "disk scan before erasure finds the material in the state files (control)", db.get("hits", 0) > 0, db.get("hit_files"))
        ck(who, "disk scan after erasure finds none of it", da.get("hits") == 0 and da.get("unreadable") == [] and "hits" in da,
           {"hit_files": da.get("hit_files"), "unreadable": da.get("unreadable")})
        ck(who, "the zeroizing allocator was active", (o.get("allocator_wiped_bytes") or 0) > 0)
        ck(who, "no state file left, no wipe error", o.get("state_files_left") == [] and o.get("file_wipe_errors") == [],
           [o.get("state_files_left"), o.get("file_wipe_errors")])
        if not self_mode:
            ck(who, "decrypts its pre-handover ciphertext while it holds the key (control)",
               o.get("pre_handover_decrypts") is True and o.get("decrypts_captured_before_erasure") is True)
            ck(who, "cannot decrypt it after erasure (same process)", o.get("decrypts_captured_after_erasure") is False)
    # ---- the restarted old seats (rotation: the process has exited)
    if not self_mode:
        for i, h, sd in olds:
            who = f"old {i} @ {h}"
            if "error" in rep_old[i]:
                continue
            alive = sh(h, f"kill -0 $(cat {sd}/serve{i}.pid) 2>/dev/null && echo alive || echo exited", check=False).stdout.strip()
            ck(who, "the old seat's process has exited", alive == "exited", alive)
            cmdline = open(os.path.join(out, f"serve{i}.cmd")).read().strip()
            sdir, env, toks, argv = cmd_argv(cmdline)
            tool = tools.get(h)
            work = os.path.dirname(tool.rstrip("/")).rsplit("/", 2)[0] + f"/checks/{name}/old{i}" if tool else None
            if tool:
                sh(h, f"mkdir -p {work}")
                hp = f"{work}/handover_P{i}.json"
                subprocess.run(["scp", "-q", os.path.join(out, f"old{i}.json"), f"{h}:{hp}"], check=True)
                jps = []
                for j in range(len(news)):
                    subprocess.run(["scp", "-q", os.path.join(out, f"join{j}.json"), f"{h}:{work}/join_P{j}.json"], check=True)
                    jps.append(f"{work}/join_P{j}.json")
                r = sh(h, f"nice -n 15 {tool} restart-seat {work}/restart.json {hp} {' '.join(jps)} -- {shlex.join(argv)}", check=False)
                rs = json.loads(r.stdout) if r.returncode == 0 else {"error": r.stderr[-2000:]}
                json.dump(rs, open(os.path.join(out, f"restart{i}.json"), "w"), indent=1)
                ck(who, "restarted: no TLS key, checkpoint, carry, tape or owner-message file of steps 0..K on disk",
                   "error" not in rs and all(f["present"] is False for f in rs["files"]), [f["path"] for f in rs.get("files", []) if f.get("present")] or rs.get("error"))
                ck(who, "restarted: loads no TLS key, no share and no tape entry",
                   rs.get("tls_key_loaded") is False and rs.get("share_entries_loaded") == 0 and rs.get("tape_entries_loaded") == 0)
                att = rs.get("decryption_attempts", [])
                ck(who, "restarted: decrypts neither its old ciphertext nor any new seat's (each target found)",
                   len(att) == 1 + len(news) and all(t["found"] and t["decrypted"] is False for t in att), att)
            # every --erase-extra file (e.g. the retired key's MP-SPDZ MAC-key files) is gone from its box
            ee = [argv[k + 1] for k, t in enumerate(argv[:-1]) if t == "--erase-extra"]
            if ee:
                r = sh(h, "for f in " + " ".join(shlex.quote(x) for x in ee) + "; do for g in $f; do test -e \"$g\" && echo \"LEFT $g\"; done; done; true", check=False)
                left = [l[5:] for l in r.stdout.splitlines() if l.startswith("LEFT ")]
                ck(who, f"the {len(ee)} --erase-extra paths (retired MP-SPDZ key files) are gone", left == [], left)
            if relaunch:
                for variant, extra in [("serve", ""), ("serve --resume", " --resume")]:
                    pidf = f"{sdir}/relaunch{i}{'-resume' if extra else ''}.pid"
                    logf = f"{sdir}/relaunch{i}{'-resume' if extra else ''}.log"
                    inner = " ".join(shlex.quote(t) for t in toks) + extra
                    t0 = time.time()
                    r = sh(h, f"cd {shlex.quote(sdir)} && ( timeout 300 env {' '.join(env)} {inner} > {logf} 2>&1 < /dev/null & echo $! > {pidf}; wait $!; echo EXIT $? ); tail -c 600 {logf}", check=False, timeout=400)
                    dt = time.time() - t0
                    lines = r.stdout.splitlines()
                    code = next((int(l.split()[1]) for l in lines if l.startswith("EXIT ")), None)
                    tail = "\n".join(l for l in lines if not l.startswith("EXIT "))
                    # it must stop, non-zero and before its timeout, at one of its own erased secret inputs: the TLS key
                    # (no handshake can be signed), the checkpoint, or the step's tape (no share can be contributed)
                    secret = [f"tls_{i}.key", "own TLS key", f"ckpt_P{i}.bin", f"carry_P{i}.bin"] + \
                             [argv[k + 1].split("{")[0] for k, t in enumerate(argv[:-1]) if t in ("--tapes", "--tape")]
                    missing = [x for x in secret if x in tail]
                    ok = code not in (0, 124, None) and bool(missing) and ("No such file" in tail or "own TLS key" in tail)
                    ck(who, f"relaunch of the same `{variant}` command exits non-zero at a missing erased secret (TLS key, checkpoint or tape)", ok,
                       {"exit": code, "seconds": round(dt, 1), "tail": tail[-300:]})
    # ---- new seats
    epoch = None
    for j, h, sd in news:
        v = rep_new[j]
        who = f"new {j} @ {h}"
        ck(who, "join report present, no error", "error" not in v, v.get("error"))
        if "error" in v:
            continue
        r = v["report"]
        epoch = v.get("epoch")
        digests.append(r.get("proof_sha256"))
        ck(who, "MAC check under its own new key passes", r.get("mac_check") == "ok")
        ck(who, "its MAC key share is nonzero", r.get("alpha_differs_from_zero") is True)
        ck(who, "decrypts its own ciphertext under the new key (control)", r.get("decrypts_own_ct") is True)
        recs = [json.loads(l) for l in open(os.path.join(out, f"ledger_new{j}.jsonl"))]
        rot = [x for x in recs if x["kind"] == "rotate"]
        ck(who, "its ledger replica holds one rotation, to epoch E", len(rot) == 1 and rot[0]["epoch"] == epoch, [x.get("epoch") for x in rot])
        tool = tools.get(h)
        if tool and rot:
            work = os.path.dirname(tool.rstrip("/")).rsplit("/", 2)[0] + f"/checks/{name}/new{j}"
            sh(h, f"mkdir -p {work}")
            rr = sh(h, f"nice -n 15 {tool} verify-rotation {work} {sd}/D/ledger_P{j}.jsonl {sd}/D/handover_e{epoch}.bin {N} {L} {F} {d} {prof}", check=False)
            try:
                vr = json.loads(rr.stdout)
            except Exception:
                vr = {"error": rr.stderr[-2000:]}
            json.dump(vr, open(os.path.join(out, f"verify_rotation{j}.json"), "w"), indent=1)
            ck(who, "native re-verification of the rotation from handover_e<E>.bin accepts; sha256 equals the record's",
               vr.get("accepted") is True and vr.get("proof_sha256_matches_record") is True, vr.get("error"))
            ck(who, "a one-byte-flipped copy of the proof is refused (negative control)", vr.get("flipped_byte_refused") is True, vr.get("flipped_error"))
    if news:
        pref = []
        for j, _, _ in news:
            ls = open(os.path.join(out, f"ledger_new{j}.jsonl")).read().splitlines()
            k = next((n for n, l in enumerate(ls) if json.loads(l)["kind"] == "rotate"), len(ls))
            pref.append(hashlib.sha256("\n".join(ls[:k + 1]).encode()).hexdigest())
        ck("ledger", "the three new replicas are equal through the rotation", len(set(pref)) == 1, pref)
    ck("all", "every seat holds the same handover proof (sha256)", len(digests) == len(olds) + len(news) and len(set(digests)) == 1 and None not in digests, digests)
    if self_mode:
        for i, h, sd in olds:
            v = rep_old[i]
            if "error" in v:
                continue
            nr = v["new_role"]
            ck(f"seat {i} @ {h}", "new role: MAC check under the new key passes", nr.get("mac_check") == "ok")
            ck(f"seat {i} @ {h}", "new role: the kept HE key decrypts its own ciphertext", nr.get("decrypts_own_ct") is True)
            recs = [json.loads(l) for l in open(os.path.join(out, f"ledger_seat{i}.jsonl"))]
            rot = [x for x in recs if x["kind"] == "rotate"]
            g = recs[0]
            ck(f"seat {i} @ {h}", "its replica rotated to the same custodian set at epoch + 1",
               len(rot) >= 1 and rot[-1]["custodians"] == g["custodians"] and rot[-1]["epoch"] == v.get("epoch"))
            tool = tools.get(h)
            if tool and rot:
                work = os.path.dirname(tool.rstrip("/")).rsplit("/", 2)[0] + f"/checks/{name}/seat{i}"
                sh(h, f"mkdir -p {work}")
                rr = sh(h, f"nice -n 15 {tool} verify-rotation {work} {sd}/D/ledger_P{i}.jsonl {sd}/D/handover_e{v.get('epoch')}.bin {N} {L} {F} {d} {prof}", check=False)
                try:
                    vr = json.loads(rr.stdout)
                except Exception:
                    vr = {"error": rr.stderr[-2000:]}
                json.dump(vr, open(os.path.join(out, f"verify_rotation_seat{i}.json"), "w"), indent=1)
                ck(f"seat {i} @ {h}", "native re-verification accepts; one-byte flip refused",
                   vr.get("accepted") is True and vr.get("flipped_byte_refused") is True and vr.get("proof_sha256_matches_record") is True, vr.get("error"))
    # ---- measurements
    def mon_peak(p):
        try:
            rows = [l.split() for l in open(p) if l.strip()]
            return {"rss_peak_mb": max(int(r[1]) for r in rows) / 1024, "cgroup_peak_mb": max(int(r[3]) for r in rows) / 2**20}
        except Exception:
            return None
    meas = {"old": {}, "new": {}}
    for i, h, _ in olds:
        o = rep_old[i].get("old_role", rep_old[i]) if self_mode else rep_old[i]
        meas["old"][i] = {"host": h, **{k: o.get(k) for k in ["reshare_seconds", "prove_seconds", "erase_seconds", "seconds", "peak_rss_mb", "bytes_sent_per_peer"]},
                          "disk_scan_seconds": [o.get("disk_scan_before_erasure", {}).get("seconds"), o.get("disk_scan_after_erasure", {}).get("seconds")],
                          "memory_scan": {k: o.get(k, {}).get("bytes") for k in ["scan_before_erasure", "scan_after_erasure"]},
                          "sampler": mon_peak(os.path.join(out, f"serve{i}.mon"))}
        if self_mode:
            nr = rep_old[i].get("new_role", {})
            meas["new"][i] = {"host": h, **{k: nr.get(k) for k in ["reshare_seconds", "commit_seconds", "prove_seconds", "auth_seconds", "seconds", "proof_bytes", "peak_rss_mb", "bytes_sent_per_peer_mesh6"]}}
    for j, h, _ in news:
        r = rep_new[j].get("report", {})
        meas["new"][j] = {"host": h, **{k: r.get(k) for k in ["ceremony_seconds", "reshare_seconds", "commit_seconds", "prove_seconds", "auth_seconds", "seconds", "proof_bytes", "peak_rss_mb",
                                                              "bytes_sent_per_peer_mesh6", "bytes_sent_per_peer_mesh3_ceremony", "bytes_sent_per_peer_mesh3_total"]},
                          "sampler": mon_peak(os.path.join(out, f"new{j}.mon"))}
    json.dump(meas, open(os.path.join(out, "measure.json"), "w"), indent=1)
    allok = all(c["ok"] for c in checks)
    json.dump({"run": name, "mode": "self" if self_mode else "rotation", "all_ok": allok, "checks": checks}, open(os.path.join(out, "checks.json"), "w"), indent=1)
    print("ALL CHECKS", "PASS" if allok else "FAIL", f"({sum(c['ok'] for c in checks)}/{len(checks)})")
    sys.exit(0 if allok else 1)

if __name__ == "__main__":
    main()
