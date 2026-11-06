"""One Cloud TPU VM session: create (spot v5e), push a bundle, run it under a timeout, pull results, delete.

    python3 gcp_run.py --name tpuperf-s1 --zone us-central1-a --wall 3600 -- <command run on the VM in ~/b>

Bundle = tpuperf/ + run_profile.py (this directory). Results: results/gcp/<name>/. Deletion is guaranteed
three ways: a finally block, a detached reaper that deletes at --wall + 600 s (PID in .reaper-<name>.pid,
stopped by that PID only), and a post-delete `tpu-vm list` check. Every VM gets a ledger row.
"""
import argparse
import datetime as dt
import json
import os
import pathlib
import re
import signal
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
LEDGER = HERE / "GCP-LEDGER.md"
PROJECT = "gen-lang-client-0657209111"
RATE = {"v5litepod-1": (1, 0.359329), "v5litepod-4": (4, 0.359329), "v5litepod-8": (8, 0.359329),
        "v6e-1": (1, 0.671112)}
VERSION = {"v5litepod": "v2-alpha-tpuv5-lite", "v6e": "v2-alpha-tpuv6e"}
CAP_STOP = 17.0
G = ["gcloud", "--project", PROJECT, "compute", "tpus", "tpu-vm"]


def sh(cmd, timeout=None, check=False):
    print("+", " ".join(cmd)[:300], flush=True)
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    out = (r.stdout + r.stderr).strip()
    if out:
        print(out[-3000:], flush=True)
    if check and r.returncode:
        raise RuntimeError(f"rc={r.returncode}: {out[-500:]}")
    return r.returncode, out


def spent():
    tot = 0.0
    for line in LEDGER.read_text().splitlines():
        cells = [c.strip() for c in line.split("|")]
        if len(cells) > 9 and re.fullmatch(r"\d+\.\d+", cells[8] or ""):
            tot += float(cells[8])
    return tot


def ledger(row):
    with open(LEDGER, "a") as f:
        f.write("| " + " | ".join(str(c) for c in row) + " |\n")


def exists(name, zone):
    rc, out = sh(G + ["list", "--zone", zone, "--format=value(name)"], timeout=120)
    return name in out.split()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--name", required=True)
    ap.add_argument("--zones", nargs="*", default=["us-east1-c", "us-central1-a", "us-east5-b", "us-south1-a", "us-west1-c",
                    "us-west4-a", "europe-west4-b"],
                    help="tried in order until a spot create succeeds (one VM at a time)")
    ap.add_argument("--network", default="tpuperf-net")
    ap.add_argument("--type", default="v5litepod-1")
    ap.add_argument("--wall", type=int, default=3600)
    ap.add_argument("--jax", default="0.12.0.1")
    ap.add_argument("--root", default=str(HERE), help="directory to bundle (its whole tree)")
    ap.add_argument("--pull", nargs="*", default=["results.json", "run.log"], help="files under ~/b to fetch")
    ap.add_argument("cmd", nargs=argparse.REMAINDER)
    a = ap.parse_args()
    cmd = " ".join(a.cmd[1:] if a.cmd and a.cmd[0] == "--" else a.cmd) or "python3 run_profile.py"
    chips, rate = RATE[a.type]
    already = spent()
    worst = already + chips * rate * (a.wall + 900) / 3600
    if worst > CAP_STOP:
        sys.exit(f"refusing: spent {already:.2f} + worst case {worst - already:.2f} would pass ${CAP_STOP}")
    _, lst = sh(G + ["list", "--zone", "-", "--format=value(name)"], timeout=180)
    if any(l.strip() and not l.startswith(("ERROR", "WARNING", "Listed")) for l in lst.splitlines()):
        sys.exit(f"refusing: a TPU VM already exists: {lst}")
    out = HERE / "results" / "gcp" / a.name
    out.mkdir(parents=True, exist_ok=True)
    t0 = dt.datetime.now(dt.timezone.utc)
    deadline = time.time() + a.wall
    # detached reaper: deletes the VM after wall + 600 s no matter what happens to this process
    a.zone = a.zones[0]
    kill_all = "; ".join(" ".join(G + ["delete", a.name, "--zone", z, "--quiet"]) for z in a.zones)
    reaper = subprocess.Popen(["sh", "-c", f"sleep {a.wall + 600}; {kill_all}"],
                              stdout=open(out / "reaper.log", "w"), stderr=subprocess.STDOUT, start_new_session=True)
    pidf = HERE / f".reaper-{a.name}.pid"
    pidf.write_text(str(reaper.pid))
    outcome = "?"
    created = False
    try:
        vt = VERSION["v6e" if a.type.startswith("v6e") else "v5litepod"]
        tried = []
        for z in a.zones:
            a.zone = z
            region = z.rsplit("-", 1)[0]
            subnet = "tpuperf-usw4" if region == "us-west4" else f"tpuperf-{region}"
            rc, o = sh(G + ["create", a.name, "--zone", z, "--accelerator-type", a.type, "--version", vt, "--spot",
                             "--network", a.network, "--subnetwork", subnet], timeout=900)
            created = rc == 0 or exists(a.name, z)
            if created:
                break
            reason = "capacity" if "capacity" in o.lower() else (o.strip().splitlines()[-1][:60] if o.strip() else "?")
            tried.append(f"{z}:{reason}")
            if time.time() > deadline - 1200:
                break
        if not created:
            outcome = "create failed: " + "; ".join(tried)[:300]
            return
        outcome = "created in " + a.zone + (" after " + ", ".join(tried) if tried else "")
        ssh = G + ["ssh", a.name, "--zone", a.zone, "--command"]
        scp = G + ["scp", "--zone", a.zone]
        tar = out / "bundle.tgz"
        subprocess.run(["tar", "czf", str(tar), "--exclude", "__pycache__", "."], cwd=a.root, check=True)
        sh(scp + [str(tar), f"{a.name}:bundle.tgz"], timeout=600, check=True)
        # The image's python is 3.10 (no venv module); JAX >= 0.7 needs 3.11+. uv brings its own 3.12.
        # /tmp/tp is the measurement env (pinned jax); the bundle's session script uses $HOME/b/py.
        setup = (f"mkdir -p b && tar xzf bundle.tgz -C b && (curl -LsSf https://astral.sh/uv/install.sh | sh) >/dev/null 2>&1; "
                 f"export PATH=$HOME/.local/bin:$PATH; uv venv -p 3.12 /tmp/tp 2>&1 | tail -2 && "
                 f"uv pip install -q -p /tmp/tp/bin/python 'jax[tpu]=={a.jax}' numpy 2>&1 | tail -3; "
                 "printf '#!/bin/sh\\nexec /tmp/tp/bin/python \"$@\"\\n' > b/py && chmod +x b/py; b/py -c 'import jax, sys; print(sys.version.split()[0], jax.__version__, jax.devices())'")
        sh(ssh + [setup], timeout=900, check=True)
        left = int(deadline - time.time()) - 120
        run = (f"export PATH=$HOME/.local/bin:$PATH; cd b && ACCEL_RESULTS=$HOME/b/results.json timeout {left} {cmd} > run.log 2>&1; "
               "echo RC=$?; tail -n 40 run.log")
        rc, o = sh(ssh + [run], timeout=left + 60)
        (out / "ssh-tail.txt").write_text(o)
        for f in a.pull:
            (out / f).parent.mkdir(parents=True, exist_ok=True)
            sh(scp + [f"{a.name}:b/{f}", str(out / f)], timeout=300)
        m = re.search(r"RC=(\d+)", o)
        outcome += f"; rc {m.group(1) if m else '?'}"
        if not m and "preempt" in o.lower():
            outcome = "PREEMPTED"
    except Exception as e:
        outcome = f"error: {repr(e)[:150]}"
        if created and not exists(a.name, a.zone):
            outcome = "PREEMPTED or vanished: " + outcome
    finally:
        if created or exists(a.name, a.zone):
            sh(G + ["delete", a.name, "--zone", a.zone, "--quiet"], timeout=900)
        gone = not exists(a.name, a.zone)
        t1 = dt.datetime.now(dt.timezone.utc)
        hours = (t1 - t0).total_seconds() / 3600
        cost = chips * rate * hours if created else 0.0
        if gone:
            try:
                os.kill(int(pidf.read_text()), signal.SIGTERM)  # our own reaper, by its PID file
                pidf.unlink()
            except Exception:
                pass
        ledger([a.name, a.zone, a.type, "spot", t0.strftime("%H:%M:%S"), t1.strftime("%H:%M:%S"), f"{hours:.3f}",
                f"{cost:.3f}", outcome + ("" if gone else " / DELETE NOT CONFIRMED, reaper armed"), f"{already + cost:.3f}"])
        print(json.dumps(dict(name=a.name, outcome=outcome, gone=gone, hours=hours, cost=cost, cumulative=already + cost)))


if __name__ == "__main__":
    main()
