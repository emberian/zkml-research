#!/usr/bin/env python3
"""The deployment run orchestrator, driven from the Mac over ssh.

    run.py RUN.json setup     each seat makes its own TLS identity in its own run dir (keys never leave the box);
                              only certificates are gathered and handed out; cfg files are copied
    run.py RUN.json check     ports free / reachable, disk, loads
    run.py RUN.json launch    records loads, starts the owner then the three custodians, one PID file each, and a
                              per-process sampler (RSS, cgroup memory, load) with its own PID file
    run.py RUN.json status    alive or exited, the last line of each log
    run.py RUN.json collect   pulls every step_*.json / serve_*.json / sampler log into OUT/<name>/ and writes
                              summary.json (per step: wall, bytes per link, CPU and peak RSS per party, proof sizes)
    run.py RUN.json stop      stops every process of this run by its PID file (and only that)
    run.py RUN.json resume    after a pause: relaunch with --resume for the steps left (owner included)

RUN.json:
  name, out (local results dir), prof [N, L, F, d], gate, program, steps, flags [extra serve flags],
  genesis_cfg (local file, copied to each seat as genesis.json), owner_cfg (local file -> owner's cfg.json; its
  "data" is a path on the owner's box), custodian ("dl-custodian" or "darkstep"),
  seats: [{host, root, bin, scope, addr, tapes, owner_msgs, env}], owner: {host, root, bin, scope, addr}
Each seat's dir is ROOT/NAME/seatI; the owner's is ROOT/NAME/owner. Paths in tapes/owner_msgs may use {k}.
"""
import json, os, shlex, subprocess, sys, time

def sh(host, cmd, check=True, capture=True):
    r = subprocess.run(["ssh", "-o", "BatchMode=yes", host, cmd], text=True,
                       stdout=subprocess.PIPE if capture else None, stderr=subprocess.STDOUT if capture else None)
    if check and r.returncode != 0:
        raise SystemExit(f"[{host}] {cmd}\n{r.stdout}")
    return (r.stdout or "").strip()

def seat_dir(cfg, s, i):
    return f"{s['root']}/{cfg['name']}/seat{i}"

def owner_dir(cfg):
    return f"{cfg['owner']['root']}/{cfg['name']}/owner"

def scp_from(host, path, local):
    subprocess.run(["scp", "-q", f"{host}:{path}", local], check=True)

def scp_to(local, host, path):
    subprocess.run(["scp", "-q", local, f"{host}:{path}"], check=True)

def setup(cfg):
    loc = os.path.join(cfg["out"], cfg["name"], "certs")
    os.makedirs(loc, exist_ok=True)
    who = [(str(i), s, seat_dir(cfg, s, i)) for i, s in enumerate(cfg["seats"])] + [("owner", cfg["owner"], owner_dir(cfg))]
    for seat, s, d in who:
        sh(s["host"], f"mkdir -p {d}/tls {d}/D && {s['bin']}/darkstep tls-keygen {seat} {d}/tls")
        scp_from(s["host"], f"{d}/tls/cert_{seat}.der", loc)
    for seat, s, d in who:
        for c in ["0", "1", "2", "owner"]:
            if c != seat:
                scp_to(os.path.join(loc, f"cert_{c}.der"), s["host"], f"{d}/tls/")
        if seat != "owner" and cfg.get("genesis_cfg"):
            scp_to(cfg["genesis_cfg"], s["host"], f"{d}/genesis.json")
    if cfg.get("owner_cfg"):
        scp_to(cfg["owner_cfg"], cfg["owner"]["host"], f"{owner_dir(cfg)}/cfg.json")
    ho = cfg.get("handover")
    if ho:
        # the new committee: its own identities; cert_0..2 are ITS certificates; the six-party mesh's cert6_0..5 are
        # the old committee's then the new one's; the owner gets the new certificates for its second session
        nloc = os.path.join(loc, "new")
        os.makedirs(nloc, exist_ok=True)
        news = [(str(j), s, new_dir(cfg, s, j)) for j, s in enumerate(ho["new_seats"])]
        for seat, s, d in news:
            sh(s["host"], f"mkdir -p {d}/tls {d}/D && {s['bin']}/darkstep tls-keygen {seat} {d}/tls")
            scp_from(s["host"], f"{d}/tls/cert_{seat}.der", nloc)
        six = os.path.join(loc, "tls6")
        os.makedirs(six, exist_ok=True)
        for j in range(3):
            subprocess.run(["cp", os.path.join(loc, f"cert_{j}.der"), os.path.join(six, f"cert6_{j}.der")], check=True)
            subprocess.run(["cp", os.path.join(nloc, f"cert_{j}.der"), os.path.join(six, f"cert6_{3 + j}.der")], check=True)
        for seat, s, d in news:
            for c in ["0", "1", "2"]:
                if c != seat:
                    scp_to(os.path.join(nloc, f"cert_{c}.der"), s["host"], f"{d}/tls/")
            scp_to(os.path.join(loc, "cert_owner.der"), s["host"], f"{d}/tls/")
            if cfg.get("genesis_cfg"):
                scp_to(cfg["genesis_cfg"], s["host"], f"{d}/genesis.json")
        for seat, s, d in [(str(i), s, seat_dir(cfg, s, i)) for i, s in enumerate(cfg["seats"])] + news:
            sh(s["host"], f"mkdir -p {d}/tls6")
            for j in range(6):
                scp_to(os.path.join(six, f"cert6_{j}.der"), s["host"], f"{d}/tls6/")
        od = owner_dir(cfg)
        sh(cfg["owner"]["host"], f"mkdir -p {od}/tls-next")
        for j in range(3):
            scp_to(os.path.join(nloc, f"cert_{j}.der"), cfg["owner"]["host"], f"{od}/tls-next/")
    print("setup: identities made per seat; certificates distributed")

def new_dir(cfg, s, j):
    return f"{s['root']}/{cfg['name']}/new{j}"

def loads(cfg):
    hosts = sorted({s["host"] for s in cfg["seats"]} | {cfg["owner"]["host"]})
    out = {}
    for h in hosts:
        out[h] = sh(h, "cat /proc/loadavg; ps -eo pcpu,rss,comm --sort=-pcpu | head -8", check=False)
    return out

def check(cfg):
    for i, s in enumerate(cfg["seats"]):
        print(f"seat {i} {s['host']}:", sh(s["host"], f"df -h {s['root']} | tail -1; cat /proc/loadavg", check=False))
    for name, a in [("owner", cfg["owner"]["addr"])] + [(f"seat{i}", s["addr"]) for i, s in enumerate(cfg["seats"][:2])]:
        h, p = a.rsplit(":", 1)
        busy = subprocess.run(["nc", "-z", "-G", "3", h, p], capture_output=True).returncode == 0
        print(f"{name} {a}: {'IN USE (something listens)' if busy else 'free'}")

SAMPLER = r'''p=$(cat {pidf}); cg=/sys/fs/cgroup$(cut -d: -f3 /proc/$p/cgroup 2>/dev/null | head -1)
while kill -0 $p 2>/dev/null; do
  r=$(awk '/VmRSS/{{print $2}}' /proc/$p/status 2>/dev/null); c=$(cat $cg/memory.current 2>/dev/null); k=$(cat $cg/memory.peak 2>/dev/null)
  echo "$(date +%s) ${{r:-0}} ${{c:-0}} ${{k:-0}} $(cut -d' ' -f1 /proc/loadavg)"; sleep 5
done'''

def start(host, d, name, cmd, env=""):
    pidf = f"{d}/{name}.pid"
    # no "cd && cmd &": that backgrounds a subshell, whose PID would land in the file and which holds ssh open
    # the exact command line, for a later check that relaunches it (e.g. an old seat after its handover)
    sh(host, f"cat > {d}/{name}.cmd << 'EOF_CMD'\ncd {d} && {env} {cmd}\nEOF_CMD")
    sh(host, f"cd {d} || exit 1; {env} nohup {cmd} > {d}/{name}.log 2>&1 < /dev/null & echo $! > {pidf}")
    start_sampler(host, d, name)

def start_sampler(host, d, name):
    samp = SAMPLER.format(pidf=f"{d}/{name}.pid")
    sh(host, f"cd {d} || exit 1; nohup sh -c {shlex.quote(samp)} > {d}/{name}.mon 2>&1 < /dev/null & echo $! > {d}/{name}.mon.pid")

def disk_gate(cfg):
    """Stop before launch if any box would fall under its free-space line by the run's end. Projected per seat: its
    checkpoint, carry and latest bundle (fixed), plus every bundle on the archive seat (steps x bundle_bytes)."""
    d = cfg["prof"][3]
    fixed = 2 * 8 * 2 * d * d * 2 + int(cfg.get("bundle_bytes", 251e6)) * 2   # ckpt + shares (test) + carry ~ bundles
    need = {}
    for i, s in enumerate(cfg["seats"]):
        b = fixed + (cfg["steps"] * int(cfg.get("bundle_bytes", 251e6)) if s.get("archive") else 0)
        key = (s["host"], s["root"])
        need[key] = need.get(key, 0) + b
    ok = True
    report = []
    for (h, root), b in need.items():
        line = next((s.get("disk_line_gb", 30) for s in cfg["seats"] if s["host"] == h), 30)
        avail = int(sh(h, f"df -Pk {root} | tail -1 | awk '{{print $4}}'")) * 1024
        after = (avail - b) / 2**30
        report.append({"host": h, "root": root, "avail_gb": round(avail / 2**30, 1), "projected_gb": round(b / 2**30, 1), "after_gb": round(after, 1), "line_gb": line})
        ok &= after >= line
    print(json.dumps(report))
    if not ok:
        raise SystemExit("disk gate: a box would fall under its line; not launching (tell the coordinator)")
    return report

def launch(cfg, seats_only=False):
    N, L, F, d = cfg["prof"]
    gate = disk_gate(cfg)
    os.makedirs(os.path.join(cfg["out"], cfg["name"]), exist_ok=True)
    json.dump({"utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "disk": gate, "loads": loads(cfg)},
              open(os.path.join(cfg["out"], cfg["name"], "loads_start.json"), "w"), indent=1)
    o = cfg["owner"]
    od = owner_dir(cfg)
    ocmd = f"nice -n 15 {o.get('scope', '')} {o['bin']}/dl-owner --listen {o['addr']} --tls {od}/tls --t {cfg['t']} --d {d} " + \
           (f"--train {od}/cfg.json" + (" --public-genesis" if cfg.get("genesis_cfg") else "") if cfg.get("owner_cfg") else f"--test-public {o['test_public']}") + \
           (f" --next-tls {od}/tls-next" if cfg.get("handover") else "") + \
           (f" --next-tls {od}/tls" * cfg.get("owner_repeat", 0))
    if not seats_only:
        start(o["host"], od, "owner", ocmd)
    addrs = " ".join(s["addr"] for s in cfg["seats"])
    exe = cfg.get("custodian", "dl-custodian")
    for i, s in enumerate(cfg["seats"]):
        sd = seat_dir(cfg, s, i)
        args = f"serve {i} {N} {L} {F} {d} {sd}/D {addrs} --tls {sd}/tls --owner {o['addr']} --steps {cfg['steps']} " \
               f"--gate {cfg['gate']} --program {cfg['program']} " + (f"--tape {s['tape']} " if s.get("tape") else f"--tapes {s['tapes']} ") + \
               (f"--owner-msgs {s['owner_msgs']} " if s.get("owner_msgs") else "")
        if cfg.get("genesis_cfg"):
            args += f"--genesis-cfg {sd}/genesis.json "
        args += " ".join(cfg.get("flags", []))
        args += f" --consumed-log {s['root']}/consumed.jsonl"
        if s.get("archive"):
            args += f" --proof-archive {sd}/archive"
        if s.get("listen"):
            args += f" --listen {s['listen']}"
        if s.get("extra"):
            args += " " + " ".join(s["extra"])
        ho = cfg.get("handover")
        if ho:
            args += f" --handover-at {ho['at']} --mesh6 {ho['mesh6']} --tls6 {sd}/tls6"
        start(s["host"], sd, f"serve{i}", f"nice -n 15 {s.get('scope', '')} {s['bin']}/{exe} {args}", env=s.get("env", ""))
    ho = cfg.get("handover")
    if ho:
        naddrs = " ".join(s["addr"] for s in ho["new_seats"])
        for j, s in enumerate(ho["new_seats"]):
            nd = new_dir(cfg, s, j)
            args = f"join {j} {N} {L} {F} {d} {nd}/D {naddrs} --tls {nd}/tls --owner {o['addr']} --steps {ho['steps_after']} " \
                   f"--after-step {ho['at']} --gate {cfg['gate']} --program {cfg['program']} --tapes {s['tapes']} " \
                   f"--owner-msgs {s['owner_msgs']} --handover-tape {s['handover_tape']} --mesh6 {ho['mesh6']} --tls6 {nd}/tls6 "
            if cfg.get("genesis_cfg"):
                args += f"--genesis-cfg {nd}/genesis.json "
            args += " ".join(ho.get("flags", []))
            args += f" --consumed-log {s['root']}/consumed.jsonl"
            if s.get("archive"):
                args += f" --proof-archive {nd}/archive"
            start(s["host"], nd, f"new{j}", f"nice -n 15 {s.get('scope', '')} {s['bin']}/dl-custodian {args}", env=s.get("env", ""))
    print("launched; status with: run.py RUN.json status")

def procs(cfg):
    yield cfg["owner"]["host"], owner_dir(cfg), "owner"
    for i, s in enumerate(cfg["seats"]):
        yield s["host"], seat_dir(cfg, s, i), f"serve{i}"
    for j, s in enumerate((cfg.get("handover") or {}).get("new_seats", [])):
        yield s["host"], new_dir(cfg, s, j), f"new{j}"

def status(cfg):
    for h, d, n in procs(cfg):
        print(f"{n} [{h}]:", sh(h, f"if kill -0 $(cat {d}/{n}.pid) 2>/dev/null; then echo -n 'alive: '; else echo -n 'exited: '; fi; "
                                   f"tail -1 {d}/{n}.log; tail -1 {d}/{n}.mon", check=False))

def stop(cfg):
    for h, d, n in procs(cfg):
        for f in [f"{d}/{n}.pid", f"{d}/{n}.mon.pid"]:
            print(h, f, sh(h, f"test -f {f} && (kill $(cat {f}) 2>/dev/null && echo stopped || echo 'not running')", check=False))

def collect(cfg):
    loc = os.path.join(cfg["out"], cfg["name"])
    for h, d, n in procs(cfg):
        os.makedirs(os.path.join(loc, n), exist_ok=True)
        subprocess.run(f"scp -q {h}:{d}/{n}.log {h}:{d}/{n}.mon {os.path.join(loc, n)}/", shell=True)
        if n != "owner":
            subprocess.run(f"scp -q '{h}:{d}/D/*.json' {os.path.join(loc, n)}/", shell=True)
    steps = {}
    party = {}
    proofs = {}
    names = [(f"serve{i}", f"P{i}") for i in range(3)] + [(f"new{j}", f"N{j}") for j in range(len((cfg.get("handover") or {}).get("new_seats", [])))]
    for dname, key in names:
        pd = os.path.join(loc, dname)
        for f in sorted(os.listdir(pd)):
            if f.startswith("step_") and f.endswith(".json"):
                r = json.load(open(os.path.join(pd, f)))
                steps.setdefault(r["step"], {})[key] = r
            if f.startswith("proof_") and f.endswith(".json") and f[6:-5].split("_")[0].isdigit():
                r = json.load(open(os.path.join(pd, f)))
                proofs.setdefault(r["serve_step"], {})[key] = r
            if f.startswith("serve_P") or f.startswith("handover_P") or f.startswith("join_P") or f.startswith("self_handover_P") or f.startswith("release_P"):
                party.setdefault(key, {})[f.split("_P")[0]] = json.load(open(os.path.join(pd, f)))
        mon = os.path.join(pd, f"{dname}.mon")
        if os.path.exists(mon):
            rows = [l.split() for l in open(mon) if len(l.split()) == 5]
            if rows:
                party.setdefault(key, {})["sampled_peak_rss_kb"] = max(int(r[1]) for r in rows)
                party[key]["sampled_cgroup_peak_bytes"] = max(int(r[3]) for r in rows)
                party[key]["load1_range"] = [min(float(r[4]) for r in rows), max(float(r[4]) for r in rows)]
    table = []
    for k in sorted(steps):
        row = {"step": k}
        for key, r in sorted(steps[k].items()):
            a = (r.get("after_step") or {}) if isinstance(r.get("after_step"), dict) else {}
            pr = proofs.get(k, {}).get(key) or a
            row[key] = {"verdict": r.get("verdict"), "step_s": r.get("step_seconds"), "cpu_s": r.get("cpu_seconds"),
                        "peak_rss_kb": r.get("peak_rss_kb"), "transcript": (r.get("transcript") or "")[:16],
                        "bytes_to": {j: v["total"] for j, v in (r.get("bytes_sent_to") or {}).items()},
                        "proof_s": pr.get("proof_seconds"), "proof_bytes": pr.get("proof_bytes"), "verify_s": pr.get("verify_seconds"),
                        "proof_elements_sent": pr.get("proof_field_elements_sent"), "after_step_s": r.get("after_step_seconds"),
                        "waited_for_proof_s": a.get("waited_for_previous_proof_seconds"),
                        "proof_bytes_to": {j: v["proof"] for j, v in (r.get("after_step_bytes_to") or {}).items()}}
        ts = {v["transcript"] for kk, v in row.items() if kk != "step"}
        row["one_transcript"] = len(ts) == 1
        table.append(row)
    json.dump({"steps": table, "parties": party}, open(os.path.join(loc, "summary.json"), "w"), indent=1)
    for row in table:
        print(json.dumps(row))
    print(json.dumps(party))

def resume(cfg):
    """After a pause (custodian 0's --pause-utc window; all three checkpointed and exited 3): relaunch the owner and
    the three custodians with --resume for the steps that are left. The logs of the earlier part are kept."""
    s0 = cfg["seats"][0]
    sd = seat_dir(cfg, s0, 0)
    rep = json.loads(sh(s0["host"], f"cat {sd}/D/serve_P0.json"))
    done = rep["next_step"]
    left = cfg["steps"] - done
    if left <= 0:
        raise SystemExit("nothing left to run")
    for h, d, n in procs(cfg):
        sh(h, f"cd {d} && for f in {n}.log {n}.mon; do test -f $f && mv $f $f.part{done}; done; true")
    c = dict(cfg, steps=left, flags=cfg.get("flags", []) + ["--resume"])
    print(f"resuming at step {done}, {left} steps left")
    launch(c)

if __name__ == "__main__":
    cfg = json.load(open(sys.argv[1]))
    if sys.argv[2] == "launch-seats":
        launch(cfg, seats_only=True)
        sys.exit(0)
    {"setup": setup, "check": check, "gate": disk_gate, "resume": resume, "launch": launch, "status": status, "stop": stop, "collect": collect}[sys.argv[2]](cfg)
