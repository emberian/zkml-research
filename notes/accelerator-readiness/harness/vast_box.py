"""One vast.ai box at a time for the accelerator-readiness paid runs (initiative 17), under ember's rules
(2026-11-06): the key is read from ~/.vast-key inside this process only (never printed, never on a command
line, never in a file we write); one box at a time; a hard spend cap and a wall-clock watchdog per box; the
instance is DESTROYED as soon as its run ends and its absence is verified through the API; every rental is
logged in VAST-LEDGER.md; refuse when total spend would exceed $25.

    python3 vast_box.py offers --gpu "H100 SXM" [--n 8]
    python3 vast_box.py run --offer ID --label NAME --bundle TAR [--bundle TAR ...] --cmd 'bash ...; bash ...'
                            --max-hours H --max-usd X --out DIR [--image IMG] [--disk GB]
    python3 vast_box.py cpu-offers [--cores 16 --ram-gb 24 --mbit 500 --tb-up 0.6 --tb-down 1.2 --hours 24]
    python3 vast_box.py hold --offer ID --label NAME --max-hours H --max-usd X --out DIR [--alias A] [--disk GB]
                             (a box held for hours: OUT/ssh.json + OUT/ssh_config; touch OUT/RELEASE to destroy it)
    python3 vast_box.py list                         (our instances; should be empty between runs)
    python3 vast_box.py destroy --id N               (manual; verifies absence)

`run` is meant to be started detached with a PID file (nohup ... & echo $! > vast-run.pid). It writes its
progress to stdout; SIGTERM or any error still destroys the instance (finally + signal handler).
"""
import argparse
import datetime as dt
import json
import pathlib
import re
import shlex
import signal
import subprocess
import sys
import time
import urllib.parse
import urllib.request

HERE = pathlib.Path(__file__).resolve().parent
LEDGER = HERE.parent / "VAST-LEDGER.md"
API = "https://console.vast.ai/api/v0"
TOTAL_CAP = 25.0
# offers whose host rejected the account and per-instance ssh key on every attempt (2026-11-06: B200 Oregon,
# accel-b200-mma-01 and -02). Never rent these again.
BLACKLIST = {50255943}
SSH_KEY = pathlib.Path.home() / ".ssh" / "id_ed25519"      # its .pub is the account's registered key
KNOWN = pathlib.Path.home() / ".cache" / "accel-ready" / "vast_known_hosts"
DEFAULT_IMAGE = "nvidia/cuda:12.9.1-devel-ubuntu24.04"


def _key():
    return (pathlib.Path.home() / ".vast-key").read_text().strip()


def api(method, path, body=None, timeout=60):
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(API + path, data=data, method=method,
                                 headers={"Authorization": "Bearer " + _key(), "Content-Type": "application/json"})
    for attempt in range(5):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                txt = r.read().decode()
                return json.loads(txt) if txt else {}
        except urllib.error.HTTPError as e:
            msg = e.read().decode()[:300]
            if e.code in (429, 500, 502, 503) and attempt < 4:
                time.sleep(5 * (attempt + 1))
                continue
            raise RuntimeError(f"vast {method} {path}: HTTP {e.code} {msg}") from None
        except urllib.error.URLError:
            if attempt < 4:
                time.sleep(5 * (attempt + 1))
                continue
            raise


def now():
    return dt.datetime.now(dt.timezone.utc)


def log(*a):
    print(now().strftime("%H:%M:%SZ"), *a, flush=True)


def credit():
    return float(api("GET", "/users/current/").get("credit", 0.0))


def ledger_spent():
    if not LEDGER.exists():
        return 0.0
    tot = 0.0
    for line in LEDGER.read_text().splitlines():
        m = re.match(r"\|\s*end\s*\|.*?\|\s*\$([0-9.]+)\s*\|", line)
        if m:
            tot += float(m.group(1))
    return tot


def ledger(row):
    if not LEDGER.exists():
        LEDGER.write_text(
            "# vast.ai rental ledger (initiative 17)\n\n"
            "Rules (ember, 2026-11-06): $27 credit; stop at $25 total; one box at a time; spend cap and wall watchdog\n"
            "per box; destroy at run end and verify absence via the API. Rows are written by `harness/vast_box.py`.\n"
            "`cost` on an end row is the credit drop measured through the API (billing can lag a few minutes; the\n"
            "rate x elapsed estimate is beside it).\n\n"
            "| event | utc | instance | offer / type | $/h | label | cost | detail |\n|---|---|---|---|---|---|---|---|\n")
    with open(LEDGER, "a") as f:
        f.write("| " + " | ".join(str(c).replace("|", "/") for c in row) + " |\n")


def offers(a):
    q = {"gpu_name": {"eq": a.gpu}, "num_gpus": {"eq": 1}, "rentable": {"eq": True}, "type": "on-demand",
         "order": [["dph_total", "asc"]], "limit": 50}
    d = api("GET", "/bundles/?q=" + urllib.parse.quote(json.dumps(q)))
    for o in d.get("offers", [])[: a.n]:
        print(o["id"], f"${o['dph_total']:.3f}/h", o.get("gpu_name"), f"cpu {o.get('cpu_cores_effective', 0):.0f}",
              f"ram {o.get('cpu_ram', 0) / 1024:.0f}G", f"disk {o.get('disk_space', 0):.0f}G",
              f"down {o.get('inet_down', 0):.0f}Mb", f"rel {o.get('reliability2', 0):.3f}",
              f"cuda {o.get('cuda_max_good')}", o.get("geolocation"), o.get("cpu_name"))


def cpu_offers(a):
    """On-demand offers for a CPU seat (any GPU), ranked by the total for a run: hours x rate + TB out x the host's
    upload price + TB in x its download price (hosts bill each direction per GB)."""
    q = {"cpu_cores_effective": {"gte": a.cores}, "cpu_ram": {"gte": a.ram_gb * 1024}, "inet_up": {"gte": a.mbit},
         "inet_down": {"gte": a.mbit}, "rentable": {"eq": True}, "rented": {"eq": False}, "type": "on-demand",
         "order": [["dph_total", "asc"]], "limit": 400}
    rows = []
    for o in api("GET", "/bundles/?q=" + urllib.parse.quote(json.dumps(q))).get("offers", []):
        up, dn = 1000 * (o.get("inet_up_cost") or 0), 1000 * (o.get("inet_down_cost") or 0)
        rows.append((a.hours * o["dph_total"] + a.tb_up * up + a.tb_down * dn, up, dn, o))
    for tot, up, dn, o in sorted(rows, key=lambda r: r[0])[: a.n]:
        print(f"${tot:6.2f}", o["id"], f"${o['dph_total']:.3f}/h", f"cpu {o.get('cpu_cores_effective', 0):.0f}",
              f"ram {o.get('cpu_ram', 0) / 1024:.0f}G", f"up {o.get('inet_up', 0):.0f} dn {o.get('inet_down', 0):.0f} Mb",
              f"$/TB up {up:.1f} dn {dn:.1f}", f"static {o.get('static_ip')}", f"rel {o.get('reliability2', 0):.3f}",
              o.get("geolocation"), o.get("cpu_name"))


def instances():
    return api("GET", "/instances/?owner=me").get("instances", [])


def destroy(iid):
    """Destroy and verify absence (or a terminal state) through the API. Returns True when verified gone."""
    for attempt in range(10):
        try:
            api("DELETE", f"/instances/{iid}/")
        except RuntimeError as e:
            log("destroy call:", e)
        time.sleep(10)
        live = [i for i in instances() if i.get("id") == iid]
        if not live:
            log(f"instance {iid} verified absent")
            return True
        log(f"instance {iid} still listed: {live[0].get('actual_status')} / {live[0].get('cur_state')}")
    return False


def ssh_base(host, port):
    KNOWN.parent.mkdir(parents=True, exist_ok=True)
    return ["-i", str(SSH_KEY), "-p", str(port), "-o", "StrictHostKeyChecking=accept-new",
            "-o", f"UserKnownHostsFile={KNOWN}", "-o", "ConnectTimeout=20", "-o", "ServerAliveInterval=30",
            "-o", "BatchMode=yes"]


def ssh(host, port, cmd, timeout=600):
    return subprocess.run(["ssh"] + ssh_base(host, port) + [f"root@{host}", cmd], capture_output=True, text=True,
                          timeout=timeout)


def rent(a):
    """The rules before any rental, then create it, attach our key and write the ledger's start row."""
    # one box of OURS at a time; other lanes (dark-learning's custodian CPU box) may hold their own on the account
    ours = [i for i in instances() if str(i.get("label") or "").startswith("accel-")]
    if ours:
        sys.exit(f"an accel-* instance already exists: one box at a time ({[i.get('id') for i in ours]})")
    if a.offer in BLACKLIST:
        sys.exit(f"offer {a.offer} is blacklisted (ssh never answered)")
    spent = ledger_spent()
    if spent + a.max_usd > TOTAL_CAP:
        sys.exit(f"refused: ledger spend ${spent:.2f} + this cap ${a.max_usd:.2f} > ${TOTAL_CAP:.2f}")
    c0 = credit()
    # the account-wide cap: ember's $27.70 credit with a stop at $25 spent, whoever on the account spent it
    if (27.70 - c0) + a.max_usd > TOTAL_CAP:
        sys.exit(f"refused: account spend ${27.70 - c0:.2f} + this cap ${a.max_usd:.2f} > ${TOTAL_CAP:.2f}")
    offer = api("GET", "/bundles/?q=" + urllib.parse.quote(json.dumps({"ask_contract_id": {"eq": a.offer}})))["offers"]
    if not offer:
        sys.exit(f"offer {a.offer} not available")
    o = offer[0]
    rate = float(o["dph_total"])
    hours = min(a.max_hours, a.max_usd / rate)
    log(f"offer {a.offer}: {o['gpu_name']} ${rate:.3f}/h; watchdog {hours * 60:.0f} min (cap ${a.max_usd:.2f}); credit ${c0:.2f}")
    body = {"client_id": "me", "image": a.image, "disk": a.disk, "runtype": "ssh_direct ssh_proxy",
            "label": a.label, "onstart": "touch /root/onstart.ok"}
    r = api("PUT", f"/asks/{a.offer}/", body)
    iid = r.get("new_contract")
    if not iid:
        sys.exit(f"create failed: {str(r)[:300]}")
    t0 = now()
    try:   # attach the key to this instance too (the account key alone did not reach a B200 host, 2026-11-06)
        api("POST", f"/instances/{iid}/ssh/", {"ssh_key": SSH_KEY.with_suffix(".pub").read_text().strip()})
    except Exception as e:
        log("attach ssh key:", str(e)[:160])
    global KNOWN
    KNOWN = KNOWN.parent / f"vast_known_hosts.{iid}"     # fresh per instance: proxy host:port pairs get reused
    ledger(["start", t0.strftime("%Y-%m-%d %H:%MZ"), iid, f"{a.offer} {o['gpu_name']}", f"{rate:.3f}", a.label, "",
            f"cap ${a.max_usd:.2f}, watchdog {hours * 60:.0f} min, image {a.image}, credit before ${c0:.2f}"])
    return iid, o, rate, hours, c0, t0


def wait_ssh(iid, a, state, deadline, t0):
    """Wait for the instance to run and accept our key; raise (the caller destroys) on a boot error, a boot timeout or
    a host that refuses ssh for longer than --ssh-timeout once running."""
    host = port = None
    while time.time() < deadline and time.time() - t0.timestamp() < a.boot_timeout:
        inst = api("GET", f"/instances/{iid}/").get("instances") or {}
        st = inst.get("actual_status")
        if st == "running" and inst.get("ssh_host"):
            state.setdefault("running_since", time.time())
            cands = [(inst["ssh_host"], inst["ssh_port"])]
            try:
                hp = (inst.get("ports") or {}).get("22/tcp") or []
                if inst.get("public_ipaddr") and hp:
                    cands.append((inst["public_ipaddr"].strip(), int(hp[0]["HostPort"])))
            except Exception:
                pass
            ok = False
            for h, pt in cands:
                r = ssh(h, pt, "true", 60)
                if r.returncode == 0:
                    host, port, ok = h, pt, True
                    break
                log(f"ssh {h}:{pt} rc {r.returncode}: {r.stderr.strip()[-160:]}")
            if ok:
                break
            if time.time() - state["running_since"] > a.ssh_timeout:
                state["reason"] = "ssh_unreachable"
                raise RuntimeError("running but ssh unreachable")
        msg = (inst.get("status_msg") or "").strip()
        log("boot:", st, msg[:100])
        bad = any(w in msg.lower() for w in ("no space left", "error response", "failed to", "unauthorized"))
        state["bad_boot"] = state.get("bad_boot", 0) + 1 if bad else 0
        if state["bad_boot"] >= 4:
            state["reason"] = "host_boot_error: " + msg[:80]
            raise RuntimeError("host cannot start the image")
        time.sleep(20)
    else:
        state["reason"] = "boot_timeout"
        raise RuntimeError("instance did not become reachable")
    return host, port


def close(iid, o, rate, a, c0, t0, state):
    """Destroy, verify absence, write the ledger's end row (credit drop measured through the API)."""
    gone = destroy(iid)
    t1 = now()
    time.sleep(30)
    c1 = credit()
    est = rate * (t1 - t0).total_seconds() / 3600
    ledger(["end", t1.strftime("%Y-%m-%d %H:%MZ"), iid, f"{a.offer} {o['gpu_name']}", f"{rate:.3f}", a.label,
            f"${max(c0 - c1, 0):.2f}",
            f"est ${est:.2f} over {(t1 - t0).total_seconds() / 60:.1f} min; destroyed+verified {gone}; "
            f"reason {state['reason'] or 'ok'}; credit after ${c1:.2f}"])
    log(f"END instance {iid}: verified gone {gone}; est ${est:.2f}; credit ${c0:.2f} -> ${c1:.2f}")
    if not gone:
        log("!!! INSTANCE NOT VERIFIED GONE: destroy by hand and tell ember")
        sys.exit(2)


def hold(a):
    """A box held for hours (a custodian seat): rent it, write its ssh details to OUT/ssh.json and an ssh config block
    (Host --alias) to OUT/ssh_config, then watch it. It is destroyed (and its absence verified) at the first of: the
    wall clock (--max-hours, or --max-usd / rate), the spend cap measured as the credit drop through the API (billed
    bandwidth included) or as rate x elapsed, the file OUT/RELEASE (touch it to give the box back), SIGTERM / SIGINT,
    or the instance leaving the running state. Start it detached with a PID file (nohup ... & echo $! > hold.pid)."""
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "RELEASE").unlink(missing_ok=True)
    iid, o, rate, hours, c0, t0 = rent(a)
    state = {"rc": None, "reason": None}

    def on_term(sig, frm):
        raise KeyboardInterrupt(f"signal {sig}")
    signal.signal(signal.SIGTERM, on_term)
    deadline = time.time() + hours * 3600
    try:
        host, port = wait_ssh(iid, a, state, deadline, t0)
        inst = api("GET", f"/instances/{iid}/").get("instances") or {}
        info = {"instance": iid, "offer": a.offer, "host": host, "port": port, "user": "root",
                "public_ip": (inst.get("public_ipaddr") or "").strip(), "rate_usd_h": rate,
                "geolocation": o.get("geolocation"), "cpu": o.get("cpu_name"), "cores": o.get("cpu_cores_effective"),
                "ram_mb": o.get("cpu_ram"), "inet_up_usd_tb": 1000 * (o.get("inet_up_cost") or 0),
                "inet_down_usd_tb": 1000 * (o.get("inet_down_cost") or 0), "ports": inst.get("ports"),
                "known_hosts": str(KNOWN), "deadline_utc": dt.datetime.fromtimestamp(deadline, dt.timezone.utc).isoformat(),
                "max_usd": a.max_usd, "credit_before": c0}
        (out / "ssh.json").write_text(json.dumps(info, indent=1) + "\n")
        (out / "ssh_config").write_text(
            f"Host {a.alias}\n\tHostname {host}\n\tPort {port}\n\tUser root\n\tIdentityFile {SSH_KEY}\n"
            f"\tIdentitiesOnly yes\n\tUserKnownHostsFile {KNOWN}\n\tStrictHostKeyChecking yes\n"
            f"\tServerAliveInterval 30\n\tServerAliveCountMax 6\n")
        log(f"HELD: ssh root@{host} -p {port} (alias {a.alias} in {out / 'ssh_config'}) up after "
            f"{(now() - t0).total_seconds():.0f} s; destroyed at {info['deadline_utc']} at the latest")
        last_credit = 0.0
        while True:
            if (out / "RELEASE").exists():
                state["reason"] = "released"
                break
            if time.time() > deadline:
                state["reason"] = "watchdog"
                break
            est = rate * (time.time() - t0.timestamp()) / 3600
            if est >= a.max_usd:
                state["reason"] = f"spend cap (estimate ${est:.2f})"
                break
            if time.time() - last_credit > 300:
                last_credit = time.time()
                try:
                    drop = c0 - credit()
                    if drop >= a.max_usd:
                        state["reason"] = f"spend cap (credit drop ${drop:.2f})"
                        break
                    st = (api("GET", f"/instances/{iid}/").get("instances") or {}).get("actual_status")
                    log(f"held: {st}; credit drop ${drop:.2f}, estimate ${est:.2f} of ${a.max_usd:.2f}")
                    if st not in ("running", None):
                        state["reason"] = f"instance {st}"
                        break
                except Exception as e:
                    log("watch:", str(e)[:200])
            time.sleep(20)
        state["rc"] = 0
    except BaseException as e:
        state["reason"] = state["reason"] or repr(e)[:200]
        log("ERROR / interrupt:", state["reason"])
    finally:
        log("releasing:", state["reason"])
        close(iid, o, rate, a, c0, t0, state)


def run(a):
    iid, o, rate, hours, c0, t0 = rent(a)
    state = {"rc": None, "reason": None}

    def on_term(sig, frm):
        raise KeyboardInterrupt(f"signal {sig}")
    signal.signal(signal.SIGTERM, on_term)
    deadline = time.time() + hours * 3600
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    try:
        host, port = wait_ssh(iid, a, state, deadline, t0)
        log(f"ssh root@{host} -p {port} up after {(now() - t0).total_seconds():.0f} s")
        prep = ("set -e; (command -v python3 >/dev/null && python3 -c 'import venv, ensurepip' 2>/dev/null) || "
                "(apt-get update -qq && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq python3 python3-venv "
                "python3-pip curl git ca-certificates >/dev/null); mkdir -p /root/run; nvidia-smi -L")
        r = ssh(host, port, prep, 900)
        log("prep rc", r.returncode, r.stdout.strip()[-300:], r.stderr.strip()[-300:])
        for b in a.bundle:
            subprocess.run(["scp"] + ["-P" if x == "-p" else x for x in ssh_base(host, port)] +
                           [b, f"root@{host}:/root/run/"], check=True, capture_output=True, timeout=600)
        untar = "; ".join(f"tar xzf /root/run/{pathlib.Path(b).name} -C /root/run" for b in a.bundle)
        # shlex.quote, not json.dumps: inside double quotes the launching shell expanded the job's own $? (every
        # step's RC printed as 0, accel-h100-all-02). The & must cover only the job (an `a && b &` chain backgrounds the untar too, with ssh's stdout open)
        job = (f"cd /root/run && {untar} && {{ nohup setsid bash -c {shlex.quote(a.cmd)} > /root/run/job.log 2>&1 "
               f"< /dev/null & echo $! > /root/run/job.pid; }}; sleep 1; cat /root/run/job.pid")
        r = ssh(host, port, job, 300)
        log("job started, remote pid", r.stdout.strip(), r.stderr.strip()[-200:])
        last = ""
        while True:
            if time.time() > deadline:
                state["reason"] = "watchdog"
                log("WATCHDOG: wall/spend cap reached; collecting partial results")
                ssh(host, port, "kill -TERM -- -$(cat /root/run/job.pid) 2>/dev/null; true", 60)
                break
            r = ssh(host, port, "kill -0 $(cat /root/run/job.pid) 2>/dev/null && echo RUNNING || echo DONE; "
                                "tail -n 3 /root/run/job.log", 120)
            lines = r.stdout.strip().splitlines()
            if lines and lines[1:] and "\n".join(lines[1:]) != last:
                last = "\n".join(lines[1:])
                log("job:", last.replace("\n", " / ")[-400:])
            if lines and lines[0] == "DONE":
                break
            time.sleep(30)
        r = ssh(host, port, "cd /root && tar czf /root/run/results.tgz accel-results run/job.log 2>/dev/null; "
                            "ls -la /root/run/results.tgz", 300)
        subprocess.run(["scp"] + ["-P" if x == "-p" else x for x in ssh_base(host, port)] +
                       [f"root@{host}:/root/run/results.tgz", str(out / "results.tgz")], capture_output=True, timeout=600)
        if (out / "results.tgz").exists():
            subprocess.run(["tar", "xzf", str(out / "results.tgz"), "-C", str(out)])
            log("results in", out)
        state["rc"] = 0
    except BaseException as e:
        state["reason"] = state["reason"] or repr(e)[:200]
        log("ERROR / interrupt:", state["reason"])
    finally:
        close(iid, o, rate, a, c0, t0, state)

def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("offers"); p.add_argument("--gpu", required=True); p.add_argument("--n", type=int, default=8)
    sub.add_parser("list")
    p = sub.add_parser("destroy"); p.add_argument("--id", type=int, required=True)
    p = sub.add_parser("hold")
    p.add_argument("--offer", type=int, required=True)
    p.add_argument("--label", required=True)
    p.add_argument("--alias", default="vast-held")
    p.add_argument("--max-hours", type=float, required=True)
    p.add_argument("--max-usd", type=float, required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--image", default=DEFAULT_IMAGE)
    p.add_argument("--disk", type=int, default=60)
    p.add_argument("--boot-timeout", type=int, default=1200)
    p.add_argument("--ssh-timeout", type=int, default=300)
    p = sub.add_parser("cpu-offers")
    p.add_argument("--cores", type=float, default=16); p.add_argument("--ram-gb", type=float, default=24)
    p.add_argument("--mbit", type=float, default=500); p.add_argument("--tb-up", type=float, default=0.6)
    p.add_argument("--tb-down", type=float, default=1.2); p.add_argument("--hours", type=float, default=24)
    p.add_argument("--n", type=int, default=20)
    p = sub.add_parser("run")
    p.add_argument("--offer", type=int, required=True)
    p.add_argument("--label", required=True)
    p.add_argument("--bundle", action="append", required=True)
    p.add_argument("--cmd", required=True)
    p.add_argument("--max-hours", type=float, required=True)
    p.add_argument("--max-usd", type=float, required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--image", default=DEFAULT_IMAGE)
    p.add_argument("--disk", type=int, default=60)
    p.add_argument("--boot-timeout", type=int, default=1200)
    p.add_argument("--ssh-timeout", type=int, default=300)
    a = ap.parse_args()
    if a.cmd == "offers":
        offers(a)
    elif a.cmd == "list":
        for i in instances():
            print(i.get("id"), i.get("gpu_name"), i.get("actual_status"), i.get("dph_total"), i.get("label"))
    elif a.cmd == "hold":
        hold(a)
    elif a.cmd == "cpu-offers":
        cpu_offers(a)
    elif a.cmd == "destroy":
        print("verified gone" if destroy(a.id) else "NOT verified gone")
    else:
        run(a)


if __name__ == "__main__":
    main()
