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
    run.py RUN.json stop      stops every process of this run by its PID file (and only that), the nightly pauser too
    run.py RUN.json resume    after a pause: relaunch with --resume for the steps left (owner included)
    run.py RUN.json redo      after an XT redo (every custodian exited 5 at step k, notes/dark-learning-gen6/xtrunc.md):
                              wait for step k's fresh preprocessing (each seat's xt_redo_tapes), then resume step k
                              alone on it; `drive` does this itself and then resumes the steps left
    run.py RUN.json plan      the disk plan: per filesystem, what the run still writes and what is left above its line
                              (also for each N in cfg "plan_steps"); `gate` (and every launch) refuses a config that
                              would end under a line; `drive` rechecks every disk_poll_s and pauses the committee
                              (each seat's DIR/PAUSE, serve --pause-file) until the boxes are back above their lines

RUN.json:
  name, out (local results dir), prof [N, L, F, d], gate, program, steps, flags [extra serve flags],
  genesis_cfg (local file, copied to each seat as genesis.json), owner_cfg (local file -> owner's cfg.json; its
  "data" is a path on the owner's box), custodian ("dl-custodian" or "darkstep"),
  seats: [{host, root, bin, scope, addr, tapes, owner_msgs, env}], owner: {host, root, bin, scope, addr}
Each seat's dir is ROOT/NAME/seatI; the owner's is ROOT/NAME/owner. Paths in tapes/owner_msgs may use {k}.
  Exact truncation (flag --xt): each seat (and each handover new_seat) may carry xt_redo_tapes and
  xt_redo_owner_msgs, patterns with {k} (the redone step) and optionally {r} (the redo count of the run): the
  fresh one-step chunk a redo of step k consumes (prep makes it on demand, under the seat's same MAC key).
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
    if cfg.get("vault"):
        # each seat's file key in its box's keyring (the uid's persistent keyring), its TLS key sealed under it
        for i, s in enumerate(cfg["seats"]):
            nxt = " --with-next" if "--self-handover-tape" in s.get("extra", []) else ""
            print(sh(s["host"], f"{s['bin']}/dl-custodian vault-init {i} {seat_dir(cfg, s, i)}/tls --epoch 0{nxt}"))
        for j, s in enumerate((cfg.get("handover") or {}).get("new_seats", [])):
            print(sh(s["host"], f"{s['bin']}/dl-custodian vault-init {j} {new_dir(cfg, s, j)}/tls --epoch 1"))
    print("setup: identities made per seat; certificates distributed")

def consumed_log(s):
    """The box's single-use registry: ROOT/consumed.jsonl, one per box. A seat may name another ("consumed_log") only
    for public-seed test-dealer tapes (a memory measurement), never for real preprocessing."""
    return s.get("consumed_log", f"{s['root']}/consumed.jsonl")

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

# Measured sizes (bytes) behind the disk plan; a run's cfg "disk" overrides any of them.
#   bundle: one step's proof bundle under ledger-x2de + RS (reh: 47,466,293-47,475,509; ledger-x2: ~76 MB)
#   handover_bundle: handover_e1.bin (reh: 27,552,248); release_bundle: the release's (run10c: 260,069,187)
#   state: a process's dir without its archive (ckpt 536,870,996 + carry 288,873,140 + latest bundle + join/ledger/
#     logs: reh 0.875-0.903 GB), plus 4 KB of ledger, step json and sampler log per step
#   tape: one sealed step file (run13-c0: 151,581,665 + 196,660 owner msg); handover_tape: 33,554,448 entries
#     (24 + 17 n, sealed + 36); release_tape: run13-rel (2,672,137,730)
#   lookahead: how many step files per process prep holds ahead of the run (spent ones are wiped: --wipe-spent)
DISK = {"bundle": 47.5e6, "handover_bundle": 27.6e6, "release_bundle": 260.1e6, "state": 0.95e9, "per_step": 4096,
        "tape": 151.8e6, "handover_tape": 570.4e6, "release_tape": 2672.2e6, "lookahead": 20}

def total_steps(cfg):
    ho = cfg.get("handover")
    return cfg["steps"] + (ho["steps_after"] if ho else 0)

def has_release(cfg):
    ho = cfg.get("handover")
    return (ho or {}).get("release") == "deferred" or "--release" in ((ho or {}).get("flags") or cfg.get("flags", []))

def prep_dir(s):
    """The box's preprocessing dir: the tape pattern up to its /chunks/."""
    t = s.get("tapes") or s.get("tape") or s["root"]
    return t.split("/chunks/")[0] + "/chunks" if "/chunks/" in t else s["root"]

def mount_of(h, path):
    # the nearest existing ancestor's filesystem (a chunk dir may not exist yet)
    return sh(h, f"p={shlex.quote(path)}; while [ ! -e \"$p\" ]; do p=$(dirname \"$p\"); done; df -Pk \"$p\" | tail -1 | awk '{{print $6, $4}}'")

def disk_need(cfg, done=0):
    """Bytes each filesystem still takes from step `done` to the run's end, keyed by (host, mount point). Per process:
    its state dir and its tapes ahead (lookahead step files, its handover and release tapes when not made yet); the
    archive seat (one per committee) adds every remaining bundle, the handover's and the release's. Conservative: an
    old seat's dir is kept after its erasure, and a tape already on disk is counted as ahead."""
    k = dict(DISK, **cfg.get("disk", {}))
    n_all = total_steps(cfg)
    left = max(0, n_all - done)
    ho = cfg.get("handover")
    at = ho["at"] if ho else None
    procs_ = [(s, seat_dir(cfg, s, i), False) for i, s in enumerate(cfg["seats"])] + \
             [(s, new_dir(cfg, s, j), True) for j, s in enumerate((ho or {}).get("new_seats", []))]
    need, lines, avail, items = {}, {}, {}, {}
    def add(h, path, b, what, line):
        mp, av = mount_of(h, path).split()
        key = (h, mp)
        need[key] = need.get(key, 0) + b
        avail[key] = int(av) * 1024
        lines[key] = max(lines.get(key, 0), line)
        items.setdefault(key, {})
        items[key][what] = items[key].get(what, 0) + b
    for s, d, new in procs_:
        h, line = s["host"], s.get("disk_line_gb", 30)
        # this process's steps still to run
        mine = (n_all - at - 1 if new else (at + 1 if ho else n_all))
        first = (at + 1 if new else 0)
        todo = max(0, min(mine, first + mine - done))
        add(h, s["root"], k["state"] + k["per_step"] * todo, "state", line)
        add(h, prep_dir(s), k["tape"] * min(todo, k["lookahead"]), "tapes ahead", line)
        last = new or not ho
        if new and s.get("handover_tape") and done <= at and sh(h, f"test -e {s['handover_tape']} && echo y || echo n", check=False) == "n":
            add(h, prep_dir(s), k["handover_tape"], "handover tape", line)
        rel = next((x for a, x in zip(s.get("extra", []), s.get("extra", [])[1:]) if a == "--release-tape"), None)
        if last and has_release(cfg) and rel and sh(h, f"test -e {rel} && echo y || echo n", check=False) == "n":
            add(h, prep_dir(s), k["release_tape"], "release tape", line)
        if s.get("archive"):
            b = k["bundle"] * todo
            if new or not ho:
                b += k["release_bundle"] if has_release(cfg) else 0
            if new:
                b += k["handover_bundle"] if done <= at else 0
            add(h, s["root"], b, "archive", line)
    out = []
    for key, b in need.items():
        out.append({"host": key[0], "mount": key[1], "avail_gb": round(avail[key] / 2**30, 1), "projected_gb": round(b / 2**30, 1),
                    "after_gb": round((avail[key] - b) / 2**30, 1), "line_gb": lines[key],
                    "items_gb": {w: round(v / 2**30, 2) for w, v in items[key].items()}})
    return out

def disk_gate(cfg, done=0):
    """Stop before launch if any filesystem would fall under its free-space line by the run's end (disk_need)."""
    report = disk_need(cfg, done)
    print(json.dumps(report))
    if any(r["after_gb"] < r["line_gb"] for r in report):
        raise SystemExit("disk gate: a box would fall under its line; not launching (tell the coordinator)")
    return report

def plan(cfg):
    """The disk plan without launching: the projection for this config, and for each N in cfg "plan_steps"."""
    print(json.dumps({"steps": total_steps(cfg), "boxes": disk_need(cfg)}, indent=1))
    for n in cfg.get("plan_steps", []):
        c = json.loads(json.dumps(cfg))
        ho = c.get("handover")
        if ho:
            # the handover at the same fraction of the run
            at = max(0, min(n - 2, round(ho["at"] * n / total_steps(cfg))))
            ho["at"], c["steps"], ho["steps_after"] = at, at + 1, n - at - 1
        else:
            c["steps"] = n
        print(json.dumps({"steps": n, "boxes": disk_need(c)}, indent=1))

def start_nightly(cfg):
    """cfg "nightly": {"host", "stop": "HHMMSS", "cont": "HHMMSS"} (forge: 100000-105830): nightly.sh on that box,
    run there (not from the Mac, which may sleep), SIGSTOPs every process of this run on it by PID file at stop and
    SIGCONTs them at cont, every day; its own PID file ROOT/NAME/nightly.pid. Peers wait on their receives meanwhile
    (serve --timeout must exceed the window: 7200 s)."""
    nt = cfg.get("nightly")
    if not nt:
        return
    h = nt["host"]
    s = next(s for s in cfg["seats"] + (cfg.get("handover") or {}).get("new_seats", []) if s["host"] == h)
    d = f"{s['root']}/{cfg['name']}"
    if sh(h, f"test -f {d}/nightly.pid && kill -0 $(cat {d}/nightly.pid) 2>/dev/null && echo y || echo n", check=False) == "y":
        return
    pfs = [f"{dd}/{n}{x}" for hh, dd, n in procs(cfg) if hh == h for x in (".pid", ".mon.pid")]
    sh(h, f"mkdir -p {d}")
    scp_to(os.path.join(os.path.dirname(os.path.abspath(__file__)), "nightly.sh"), h, f"{d}/nightly.sh")
    sh(h, f"cd {d} && nohup bash {d}/nightly.sh {d}/nightly.log {nt['stop']} {nt['cont']} {' '.join(pfs)} > /dev/null 2>&1 < /dev/null & echo $! > {d}/nightly.pid")
    print(f"nightly pause on {h}: {nt['stop']}-{nt['cont']} UTC over {len(pfs)} PID files")

def pause_file(d):
    return f"{d}/PAUSE"

def launch(cfg, seats_only=False, with_new=True):
    N, L, F, d = cfg["prof"]
    gate = disk_gate(cfg)
    os.makedirs(os.path.join(cfg["out"], cfg["name"]), exist_ok=True)
    json.dump({"utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "disk": gate, "loads": loads(cfg)},
              open(os.path.join(cfg["out"], cfg["name"], "loads_start.json"), "w"), indent=1)
    o = cfg["owner"]
    od = owner_dir(cfg)
    ocmd = owner_cmd(cfg, f"{od}/tls", ([f"{od}/tls-next"] if cfg.get("handover") else []) + [f"{od}/tls"] * cfg.get("owner_repeat", 0))
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
        args += f" --consumed-log {consumed_log(s)}"
        if cfg.get("vault"):
            args += " --vault"
        if s.get("archive"):
            args += f" --proof-archive {sd}/archive"
        args += f" --pause-file {pause_file(sd)}"
        if s.get("listen"):
            args += f" --listen {s['listen']}"
        if s.get("extra"):
            args += " " + " ".join(s["extra"])
        ho = cfg.get("handover")
        if ho:
            args += f" --handover-at {ho['at']} --mesh6 {ho['mesh6']} --tls6 {sd}/tls6"
        start(s["host"], sd, f"serve{i}", f"nice -n 15 {s.get('scope', '')} {s['bin']}/{exe} {args}", env=s.get("env", ""))
    if cfg.get("handover") and with_new and cfg["handover"].get("launch_new", "at_start") == "at_start":
        launch_new(cfg)
    start_nightly(cfg)
    print("launched; status with: run.py RUN.json status")

def new_args(cfg, s, j):
    a = ""
    if cfg.get("genesis_cfg"):
        a += f"--genesis-cfg {new_dir(cfg, s, j)}/genesis.json "
    a += " ".join(cfg["handover"].get("flags", []))
    a += f" --consumed-log {consumed_log(s)}"
    if cfg.get("vault"):
        a += " --vault"
    if s.get("archive"):
        a += f" --proof-archive {new_dir(cfg, s, j)}/archive"
    a += f" --pause-file {pause_file(new_dir(cfg, s, j))}"
    if s.get("extra"):
        a += " " + " ".join(s["extra"])
    return a

def launch_new(cfg):
    """The new committee's join processes (they wait for the old seats on the six-party mesh after step `at`)."""
    N, L, F, d = cfg["prof"]
    o = cfg["owner"]
    ho = cfg.get("handover")
    if ho:
        naddrs = " ".join(s["addr"] for s in ho["new_seats"])
        for j, s in enumerate(ho["new_seats"]):
            nd = new_dir(cfg, s, j)
            args = f"join {j} {N} {L} {F} {d} {nd}/D {naddrs} --tls {nd}/tls --owner {o['addr']} --steps {ho['steps_after']} " \
                   f"--after-step {ho['at']} --gate {cfg['gate']} --program {cfg['program']} --tapes {s['tapes']} " \
                   f"--owner-msgs {s['owner_msgs']} --handover-tape {s['handover_tape']} --mesh6 {ho['mesh6']} --tls6 {nd}/tls6 "
            args += new_args(cfg, s, j)
            start(s["host"], nd, f"new{j}", f"nice -n 15 {s.get('scope', '')} {s['bin']}/dl-custodian {args}", env=s.get("env", ""))

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
    nt = cfg.get("nightly")
    if nt:
        s = next(s for s in cfg["seats"] + (cfg.get("handover") or {}).get("new_seats", []) if s["host"] == nt["host"])
        f = f"{s['root']}/{cfg['name']}/nightly.pid"
        print(nt["host"], f, sh(nt["host"], f"test -f {f} && (kill $(cat {f}) 2>/dev/null && echo stopped || echo 'not running')", check=False))
    for h, d, n in procs(cfg):
        for f in [f"{d}/{n}.pid", f"{d}/{n}.mon.pid"]:
            # SIGCONT after the TERM: a process the nightly pause stopped would otherwise hold the signal
            print(h, f, sh(h, f"test -f {f} && (kill $(cat {f}) 2>/dev/null && {{ kill -CONT $(cat {f}) 2>/dev/null; echo stopped; }} || echo 'not running')", check=False))

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

def alive(host, d, n):
    return sh(host, f"test -f {d}/{n}.pid && kill -0 $(cat {d}/{n}.pid) 2>/dev/null && echo yes || echo no", check=False) == "yes"

def phase(cfg):
    """"old" until the new committee has taken over (its join processes were started), then "new"."""
    ho = cfg.get("handover")
    if not ho:
        return "old"
    s = ho["new_seats"][0]
    return "new" if sh(s["host"], f"test -f {new_dir(cfg, s, 0)}/new0.pid && echo y || echo n", check=False) == "y" else "old"

def owner_cmd(cfg, tls, nxt):
    o, d = cfg["owner"], cfg["prof"][3]
    return f"nice -n 15 {o.get('scope', '')} {o['bin']}/dl-owner --listen {o['addr']} --tls {tls} --t {cfg['t']} --d {d} " + \
        (f"--train {owner_dir(cfg)}/cfg.json" + (" --public-genesis" if cfg.get("genesis_cfg") else "") if cfg.get("owner_cfg") else f"--test-public {o['test_public']}") + \
        "".join(f" --next-tls {x}" for x in nxt)

def resume(cfg):
    """After a pause (the committee's custodian 0 voted for its --pause-utc window; all three checkpointed and exited
    3): relaunch the owner and the active committee's custodians with --resume for the steps that are left. Before
    the handover that is the old committee (the new one is left alone: it is started by launch_new); after it, the
    new committee's seats come back as `serve --resume` in their own dirs, and the owner serves only them. The
    logs of the earlier part are kept (NAME.log.part<step>)."""
    if phase(cfg) == "new" and all(not alive(s["host"], new_dir(cfg, s, j), f"new{j}") for j, s in enumerate(cfg["handover"]["new_seats"])):
        return resume_new(cfg)
    s0 = cfg["seats"][0]
    sd = seat_dir(cfg, s0, 0)
    rep = json.loads(sh(s0["host"], f"cat {sd}/D/serve_P0.json"))
    done = rep["next_step"]
    left = cfg["steps"] - done
    if left <= 0:
        # every step ran: what can be left is the release (it failed after the last checkpoint); --steps 0 runs it
        # alone from the checkpoint, on the release's own tape (single use: a claimed one is refused)
        rel = sh(s0["host"], f"cat {sd}/D/release_P0.json 2>/dev/null || echo null", check=False)
        if cfg.get("handover") or "--release" not in cfg.get("flags", []) or (rel != "null" and '"error"' not in rel):
            raise SystemExit("nothing left to run")
        left = 0
    for h, d, n in procs(cfg):
        if not n.startswith("new"):
            sh(h, f"cd {d} && for f in {n}.log {n}.mon; do test -f $f && mv $f $f.part{done}; done; true")
    c = dict(cfg, steps=left, flags=cfg.get("flags", []) + ["--resume"])
    print(f"resuming at step {done}, {left} steps left" + (" (the release alone)" if left == 0 else ""))
    launch(c, with_new=False)

def resume_new(cfg, redo=None):
    """redo = (k, r): step k alone on each new seat's xt_redo_tapes (XT redo r of the run)."""
    N, L, F, d = cfg["prof"]
    ho = cfg["handover"]
    s0 = ho["new_seats"][0]
    rep = json.loads(sh(s0["host"], f"cat {new_dir(cfg, s0, 0)}/D/serve_P0.json"))
    done = rep["next_step"]
    left = ho["at"] + 1 + ho["steps_after"] - done
    extra = ""
    if redo:
        left = 1
    elif left <= 0:
        # every step ran; a deferred release (handover "release": "deferred") runs alone from the checkpoint once
        # its own tapes are made (--steps 0 --release; single use: a claimed tape is refused)
        if ho.get("release") != "deferred" or release_done(cfg):
            raise SystemExit("nothing left to run")
        if not release_ready(cfg):
            raise SystemExit("the release's tapes are not complete yet")
        left, extra = 0, " --release"
    o, od = cfg["owner"], owner_dir(cfg)
    # the owner's identity with the new committee's certificates only (its key stays on its box)
    sh(o["host"], f"mkdir -p {od}/tls-new && cp {od}/tls/tls_owner.key {od}/tls/cert_owner.der {od}/tls-next/cert_*.der {od}/tls-new/")
    for h, dd, n in procs(cfg):
        if n == "owner" or n.startswith("new"):
            sh(h, f"cd {dd} && for f in {n}.log {n}.mon; do test -f $f && mv $f $f.part{done}; done; true")
    start(o["host"], od, "owner", owner_cmd(cfg, f"{od}/tls-new", []))
    naddrs = " ".join(s["addr"] for s in ho["new_seats"])
    for j, s in enumerate(ho["new_seats"]):
        nd = new_dir(cfg, s, j)
        tp, om = (redo_paths(s, redo) if redo else (s["tapes"], s["owner_msgs"]))
        args = f"serve {j} {N} {L} {F} {d} {nd}/D {naddrs} --tls {nd}/tls --owner {o['addr']} --steps {left} " \
               f"--gate {cfg['gate']} --program {cfg['program']} --tapes {tp} --owner-msgs {om} " + new_args(cfg, s, j) + " --resume" + extra
        start(s["host"], nd, f"new{j}", f"nice -n 15 {s.get('scope', '')} {s['bin']}/dl-custodian {args}", env=s.get("env", ""))
    start_nightly(cfg)
    print(f"new committee resuming at step {done}, {left} steps left" + (" (the release alone)" if extra else ""))

def redo_paths(s, redo):
    """A seat's tape and owner-message patterns for the XT redo (k, r): {r} filled, {k} left for serve."""
    k, r = redo
    if not s.get("xt_redo_tapes"):
        raise SystemExit("an XT redo needs each seat's xt_redo_tapes (and xt_redo_owner_msgs) in the config")
    return (s["xt_redo_tapes"].replace("{r}", str(r)), s.get("xt_redo_owner_msgs", s["owner_msgs"]).replace("{r}", str(r)))

def redo_seats(cfg):
    """The active committee's seats as (seat, index, dir)."""
    if phase(cfg) == "new":
        return [(s, j, new_dir(cfg, s, j)) for j, s in enumerate(cfg["handover"]["new_seats"])]
    return [(s, i, seat_dir(cfg, s, i)) for i, s in enumerate(cfg["seats"])]

def redo_state(cfg):
    """OUT/NAME/xt_redo.json: {"count": redos launched so far, "pending": step k of the segment in flight or null}."""
    p = os.path.join(cfg["out"], cfg["name"], "xt_redo.json")
    return json.load(open(p)) if os.path.exists(p) else {"count": 0, "pending": None}

def save_redo_state(cfg, st):
    p = os.path.join(cfg["out"], cfg["name"], "xt_redo.json")
    os.makedirs(os.path.dirname(p), exist_ok=True)
    json.dump(st, open(p + ".tmp", "w"))
    os.replace(p + ".tmp", p)

def redo_ready(cfg, k, r):
    """Every active seat's fresh one-step chunk for the redo of step k exists: its tape and owner message, and for
    a prep chunk (CHUNK/step-J/tape_I.bin) its chunk-P<I>.json, which darkprep writes last."""
    for s, i, _ in redo_seats(cfg):
        tp, om = redo_paths(s, (k, r))
        tp, om = tp.replace("{k}", str(k)), om.replace("{k}", str(k))
        cj = f"{os.path.dirname(os.path.dirname(tp))}/chunk-P{i}.json"
        test = f"test -f {tp} && test -f {om}" + (f" && test -f {cj}" if os.path.basename(os.path.dirname(tp)).startswith("step-") else "")
        if sh(s["host"], f"{test} && echo y || echo n", check=False) != "y":
            return False
    return True

def redo(cfg, wait_s=None):
    """After every custodian of the active committee exited 5 (an XT redo, step k; the checkpoint is at step k - 1
    and the MAC key is kept): wait until step k's fresh preprocessing is on every seat, then resume step k alone on
    it (serve --resume --steps 1 --tapes <xt_redo_tapes>). The steps after it are resumed as usual once it ends."""
    seats = redo_seats(cfg)
    reps = [json.loads(sh(s["host"], f"cat {d}/D/serve_P{i}.json")) for s, i, d in seats]
    if not all(x.get("exit") == 5 for x in reps):
        raise SystemExit("not an XT redo: " + json.dumps([x.get("exit") for x in reps]))
    k = reps[0]["next_step"]
    st = redo_state(cfg)
    r = st["count"]
    while not redo_ready(cfg, k, r):
        if wait_s is None:
            raise SystemExit(f"the XT redo of step {k} waits for its fresh preprocessing (xt_redo_tapes, redo {r})")
        time.sleep(wait_s)
    st = {"count": r + 1, "pending": k}
    save_redo_state(cfg, st)
    for h, d, n in procs(cfg):
        sh(h, f"cd {d} && for f in {n}.log {n}.mon; do test -f $f && mv $f $f.redo{k}; done; true")
    if phase(cfg) == "new":
        resume_new(cfg, redo=(k, r))
    else:
        c = dict(cfg, steps=1, flags=cfg.get("flags", []) + ["--resume"],
                 seats=[dict(s, tape=None, tapes=redo_paths(s, (k, r))[0], owner_msgs=redo_paths(s, (k, r))[1]) for s in cfg["seats"]])
        launch(c, with_new=False)
    print(f"XT redo {r}: step {k} resumed alone on its fresh preprocessing")
    return k

def release_tape(s):
    x = s.get("extra", [])
    return next((b for a, b in zip(x, x[1:]) if a == "--release-tape"), None)

def release_ready(cfg):
    """Every new seat's release chunk is complete: its chunk-P<I>.json (prep writes it last) beside step-0."""
    for j, s in enumerate(cfg["handover"]["new_seats"]):
        t = release_tape(s)
        cd = os.path.dirname(os.path.dirname(t))
        if sh(s["host"], f"test -f {cd}/chunk-P{j}.json && test -f {t} && echo y || echo n", check=False) != "y":
            return False
    return True

def release_done(cfg):
    s = cfg["handover"]["new_seats"][0]
    r = sh(s["host"], f"cat {new_dir(cfg, s, 0)}/D/release_P0.json 2>/dev/null || echo null", check=False)
    return r != "null" and '"error"' not in r

def in_window(w, now=None):
    a, b = [int(x[:2]) * 60 + int(x[3:]) for x in w.split("-")]
    t = now if now is not None else time.gmtime()
    m = t.tm_hour * 60 + t.tm_min
    return a <= m < b if a <= b else (m >= a or m < b)

def drive(cfg):
    """The whole run, unattended, from the Mac: launch; start the new committee once the old one has finished step
    at - 1 (handover.launch_new "deferred"; "at_start" starts it with the old one); after a pause, wait out the
    window and resume (either committee); stop everything by PID file on any other exit; collect at the end.
    Events go to OUT/NAME/drive.log. Stop it by its own PID file (drive.pid beside the log)."""
    loc = os.path.join(cfg["out"], cfg["name"])
    os.makedirs(loc, exist_ok=True)
    log = open(os.path.join(loc, "drive.log"), "a")
    def ev(m):
        line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} {m}"
        print(line, file=log, flush=True)
        print(line, flush=True)
    win = next((cfg["flags"][k + 1] for k, x in enumerate(cfg.get("flags", [])) if x == "--pause-utc"), None)
    ho = cfg.get("handover")
    s0 = cfg["seats"][0]
    def active():
        if phase(cfg) == "new":
            return [(s["host"], new_dir(cfg, s, j), j) for j, s in enumerate(ho["new_seats"])]
        return [(s["host"], seat_dir(cfg, s, i), i) for i, s in enumerate(cfg["seats"])]
    def done_steps():
        h, d, _ = active()[0]
        last = sh(h, f"ls {d}/D 2>/dev/null | sed -n 's/^step_\\([0-9]*\\)_P0.json$/\\1/p' | sort -n | tail -1", check=False)
        return int(last) + 1 if last.isdigit() else (ho["at"] + 1 if phase(cfg) == "new" else 0)
    def disk_low():
        # the remaining run against every filesystem's line: low means it would end under its line
        try:
            low = [r for r in disk_need(cfg, done_steps()) if r["after_gb"] < r["line_gb"]]
        except SystemExit as e:
            ev(f"disk check failed: {e}")
            return False
        if low:
            ev("disk low: " + json.dumps(low))
        return bool(low)
    next_disk = 0.0
    if sh(s0["host"], f"test -f {seat_dir(cfg, s0, 0)}/serve0.pid && echo y || echo n", check=False) == "n":
        launch(cfg)
        ev("launched")
    else:
        ev("attached to a launched run")
    while True:
        time.sleep(cfg.get("drive_poll_s", 60))
        try:
            ph = phase(cfg)
            if ph == "old":
                if ho and ho.get("launch_new") == "deferred":
                    at = ho["at"]
                    sd = seat_dir(cfg, s0, 0)
                    if at == 0 or sh(s0["host"], f"test -f {sd}/D/step_{at - 1}_P0.json && echo y || echo n", check=False) == "y":
                        launch_new(cfg)
                        ev(f"new committee started (old committee past step {at - 1})")
                        continue
                seats = [(s["host"], seat_dir(cfg, s, i), f"serve{i}", i) for i, s in enumerate(cfg["seats"])]
            else:
                seats = [(s["host"], new_dir(cfg, s, j), f"new{j}", j) for j, s in enumerate(ho["new_seats"])]
            live = [alive(h, d, n) for h, d, n, _ in seats]
            if any(live):
                if time.time() >= next_disk:
                    next_disk = time.time() + cfg.get("disk_poll_s", 600)
                    if disk_low():
                        # every live seat of the committee asks for the pause at the next step boundary
                        for h, d, _ in active():
                            sh(h, f"touch {pause_file(d)}", check=False)
                        ev("pause files set: the committee checkpoints at the next boundary and waits for disk")
                continue
            reps = [json.loads(sh(h, f"cat {d}/D/serve_P{i}.json 2>/dev/null || echo null", check=False) or "null") for h, d, n, i in seats]
            if ph == "old" and ho:
                # the old committee's normal end is the handover: then the new committee carries on
                hand = [sh(h, f"cat {d}/D/handover_P{i}.json 2>/dev/null || echo null", check=False) for h, d, n, i in seats]
                if all(x != "null" and '"error"' not in x for x in hand):
                    ev("old committee handed over and exited")
                    continue
            if all(r and r.get("exit") == 5 for r in reps):
                k = reps[0]["next_step"]
                ev(f"XT redo at step {k} ({ph} committee): a wrap-zone opening, public and data-independent; the key is "
                   f"kept; waiting for step {k}'s fresh preprocessing")
                redo(cfg, wait_s=cfg.get("disk_poll_s", 600))
                ev(f"XT redo: step {k} launched alone on its fresh preprocessing")
                continue
            st = redo_state(cfg)
            if st["pending"] is not None and all(r and r.get("exit") == 0 for r in reps):
                k = st["pending"]
                save_redo_state(cfg, dict(st, pending=None))
                try:
                    resume(cfg)
                    ev(f"XT redo of step {k} done; the steps after it resumed")
                    continue
                except SystemExit as e:
                    ev(f"XT redo of step {k} done; {e}")
            if all(r and r.get("paused") for r in reps):
                ev(f"paused at step {reps[0]['next_step']} ({ph} committee)")
                while win and in_window(win):
                    time.sleep(60)
                while any(sh(h, f"test -e {pause_file(d)} && echo y || echo n", check=False) == "y" for h, d, _ in active()):
                    if not disk_low():
                        for h, d, _ in active():
                            sh(h, f"rm -f {pause_file(d)}", check=False)
                        ev("disk back above every line: pause files removed")
                        break
                    time.sleep(cfg.get("disk_poll_s", 600))
                resume(cfg)
                ev("resumed")
                continue
            if all(r and r.get("exit") == 0 for r in reps) and (ph == "new" or not ho):
                if ho and ho.get("release") == "deferred" and not release_done(cfg):
                    ev(f"steps done at step {reps[0]['next_step']}; the release waits for its tapes")
                    while not release_ready(cfg):
                        time.sleep(cfg.get("disk_poll_s", 600))
                    resume_new(cfg)
                    ev("the release's tapes are complete: the release launched alone from the checkpoint")
                    continue
                ev(f"run ended at step {reps[0]['next_step']}")
                break
            ev(f"stopped unexpectedly ({ph} committee): " + json.dumps([r and {k: r.get(k) for k in ("next_step", "exit", "paused")} for r in reps]))
            stop(cfg)
            break
        except SystemExit as e:
            ev(f"driver error: {e}")
            continue
    collect(cfg)
    ev("collected")

if __name__ == "__main__":
    cfg = json.load(open(sys.argv[1]))
    if sys.argv[2] == "launch-seats":
        launch(cfg, seats_only=True)
        sys.exit(0)
    {"setup": setup, "check": check, "gate": disk_gate, "plan": plan, "resume": resume, "redo": redo, "launch": launch, "launch-new": launch_new, "drive": drive, "status": status, "stop": stop, "collect": collect}[sys.argv[2]](cfg)
