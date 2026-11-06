"""One vast.ai box at a time for the accelerator-readiness paid runs (initiative 17), under ember's rules
(2026-11-06): the key is read from ~/.vast-key inside this process only (never printed, never on a command
line, never in a file we write); one box at a time; a hard spend cap and a wall-clock watchdog per box; the
instance is DESTROYED as soon as its run ends and its absence is verified through the API; every rental is
logged in VAST-LEDGER.md; refuse when total spend would exceed $25.

    python3 vast_box.py offers --gpu "H100 SXM" [--n 8]
    python3 vast_box.py run --offer ID --label NAME --bundle TAR [--bundle TAR ...] --cmd 'bash ...; bash ...'
                            --max-hours H --max-usd X --out DIR [--image IMG] [--disk GB]
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


def run(a):
    if instances():
        sys.exit("an instance already exists on the account: one box at a time (vast_box.py list)")
    spent = ledger_spent()
    if spent + a.max_usd > TOTAL_CAP:
        sys.exit(f"refused: ledger spend ${spent:.2f} + this cap ${a.max_usd:.2f} > ${TOTAL_CAP:.2f}")
    c0 = credit()
    offer = api("GET", "/bundles/?q=" + urllib.parse.quote(json.dumps({"id": {"eq": a.offer}})))["offers"]
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
    ledger(["start", t0.strftime("%Y-%m-%d %H:%MZ"), iid, f"{a.offer} {o['gpu_name']}", f"{rate:.3f}", a.label, "",
            f"cap ${a.max_usd:.2f}, watchdog {hours * 60:.0f} min, image {a.image}, credit before ${c0:.2f}"])
    state = {"rc": None, "reason": None}

    def on_term(sig, frm):
        raise KeyboardInterrupt(f"signal {sig}")
    signal.signal(signal.SIGTERM, on_term)
    deadline = time.time() + hours * 3600
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    try:
        host = port = None
        while time.time() < deadline and time.time() - t0.timestamp() < a.boot_timeout:
            inst = api("GET", f"/instances/{iid}/").get("instances") or {}
            st = inst.get("actual_status")
            if st == "running" and inst.get("ssh_host"):
                host, port = inst["ssh_host"], inst["ssh_port"]
                if ssh(host, port, "true", 60).returncode == 0:
                    break
            log("boot:", st, inst.get("status_msg", "")[:80] if inst.get("status_msg") else "")
            time.sleep(20)
        else:
            state["reason"] = "boot_timeout"
            raise RuntimeError("instance did not become reachable")
        log(f"ssh root@{host} -p {port} up after {(now() - t0).total_seconds():.0f} s")
        prep = ("set -e; (command -v python3 >/dev/null && python3 -c 'import venv' 2>/dev/null) || "
                "(apt-get update -qq && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq python3 python3-venv "
                "python3-pip curl git ca-certificates >/dev/null); mkdir -p /root/run; nvidia-smi -L")
        r = ssh(host, port, prep, 900)
        log("prep rc", r.returncode, r.stdout.strip()[-300:], r.stderr.strip()[-300:])
        for b in a.bundle:
            subprocess.run(["scp"] + ["-P" if x == "-p" else x for x in ssh_base(host, port)] +
                           [b, f"root@{host}:/root/run/"], check=True, capture_output=True, timeout=600)
        untar = "; ".join(f"tar xzf /root/run/{pathlib.Path(b).name} -C /root/run" for b in a.bundle)
        job = (f"cd /root/run && {untar} && nohup setsid bash -c {json.dumps(a.cmd)} > /root/run/job.log 2>&1 "
               f"< /dev/null & echo $! > /root/run/job.pid; sleep 1; cat /root/run/job.pid")
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


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("offers"); p.add_argument("--gpu", required=True); p.add_argument("--n", type=int, default=8)
    sub.add_parser("list")
    p = sub.add_parser("destroy"); p.add_argument("--id", type=int, required=True)
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
    a = ap.parse_args()
    if a.cmd == "offers":
        offers(a)
    elif a.cmd == "list":
        for i in instances():
            print(i.get("id"), i.get("gpu_name"), i.get("actual_status"), i.get("dph_total"), i.get("label"))
    elif a.cmd == "destroy":
        print("verified gone" if destroy(a.id) else "NOT verified gone")
    else:
        run(a)


if __name__ == "__main__":
    main()
