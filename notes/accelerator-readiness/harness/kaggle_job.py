"""One Kaggle job per experiment for the accelerator-readiness lane (initiative 17), following
/Users/ember/swarm/kaggle.md: private script kernel, one unique id per experiment, platform timeout plus an
internal watchdog, hardware verified inside the job, /kaggle/working kept to results + a bounded log,
a ledger row per submission, TPU serialized through a lock file.

    python3 kaggle_job.py stage   --id SLUG --acc t4|tpu --entry REL.py [--args ...] --files F... [--root DIR]
                                  [--watchdog S] [--internet]
    python3 kaggle_job.py submit  --id SLUG --timeout S [--holder NAME]       (push + ledger row)
    python3 kaggle_job.py status  --id SLUG
    python3 kaggle_job.py harvest --id SLUG --out DIR                          (results + manifest + log)

Staging dir: STAGE_ROOT/SLUG (outside every repo). The bundle is a base64 tar of the named files only,
embedded in run.py; inside the job it unpacks under /tmp/accel/SLUG and the entry runs with cwd there.
The entry must write its measurements to the path in env ACCEL_RESULTS (a JSON file); run.py writes
manifest.json (source hash, versions, hardware, elapsed, rc) and log.txt (last 200 KB) beside it.
Never prints or reads the Kaggle token: the CLI reads ~/.kaggle/access_token itself.
"""
import argparse
import base64
import datetime as dt
import hashlib
import io
import json
import os
import pathlib
import re
import subprocess
import sys
import tarfile

HERE = pathlib.Path(__file__).resolve().parent
LEDGER = HERE.parent / "KAGGLE-LEDGER.md"
TPU_LOCK = HERE.parent / "TPU-LOCK"
STAGE_ROOT = pathlib.Path(os.environ.get("ACCEL_STAGE_ROOT", "/Users/ember/.cache/accel-ready/kaggle-stage"))
KAGGLE = ["uvx", "--from", "kaggle", "--with", "six", "kaggle"]
OWNER = "emberian64"
ACC = {"t4": "NvidiaTeslaT4", "tpu": "TpuV5E8"}

RUNNER = r'''
import base64, hashlib, json, os, pathlib, platform, subprocess, sys, tarfile, threading, time
T0 = time.time()
OUT = pathlib.Path("/kaggle/working")
WORK = pathlib.Path("/tmp/accel") / SLUG
WORK.mkdir(parents=True, exist_ok=True)
manifest = {"slug": SLUG, "acc": ACC, "source_sha256": SOURCE_SHA, "entry": ENTRY, "args": ARGS,
            "watchdog_s": WATCHDOG, "python": sys.version, "platform": platform.platform()}
def dump():
    manifest["elapsed_s"] = round(time.time() - T0, 1)
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=1))
def sh(cmd, t=60):
    try:
        r = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=t)
        return (r.stdout + r.stderr).strip()
    except Exception as e:
        return "ERR " + repr(e)
# hardware first: a job that asked for an accelerator and got CPU must fail loudly
if ACC == "t4":
    manifest["nvidia_smi"] = sh("nvidia-smi --query-gpu=name,memory.total,driver_version,compute_cap --format=csv,noheader")
    manifest["nvcc"] = sh("nvcc --version | tail -2; ls -d /usr/local/cuda*")
    ok = "T4" in manifest["nvidia_smi"] or os.environ.get("ACCEL_ANY_GPU") == "1"
else:
    manifest["jax"] = sh(sys.executable + " -c \"import jax; print(jax.__version__, jax.default_backend(), jax.device_count(), [d.device_kind for d in jax.devices()][:1])\"", 300)
    ok = " tpu " in (" " + manifest["jax"] + " ")
manifest["hardware_ok"] = ok
dump()
if not ok:
    print("HARDWARE CHECK FAILED", manifest, flush=True)
    sys.exit(3)
(WORK / "bundle.tar.gz").write_bytes(base64.b64decode(PAYLOAD))
with tarfile.open(WORK / "bundle.tar.gz") as f:
    f.extractall(WORK, filter="data")
env = dict(os.environ, ACCEL_RESULTS=str(OUT / "results.json"), ACCEL_DEVICE=ACC, PYTHONUNBUFFERED="1")
log = open(WORK / "log.txt", "w")
p = subprocess.Popen([sys.executable, "-u", ENTRY] + ARGS, cwd=WORK, env=env, stdout=subprocess.PIPE,
                     stderr=subprocess.STDOUT, text=True)
last = [time.time()]
def pump():
    for line in p.stdout:
        last[0] = time.time()
        sys.stdout.write(line); sys.stdout.flush()
        log.write(line); log.flush()
th = threading.Thread(target=pump, daemon=True); th.start()
reason = None
while p.poll() is None:
    time.sleep(2)
    if time.time() - T0 > WATCHDOG:
        reason = "watchdog_wall"
    elif time.time() - last[0] > STALL:
        reason = "watchdog_no_output"
    if reason:
        p.kill(); break
p.wait(); th.join(5); log.close()
manifest["rc"] = p.returncode
manifest["killed"] = reason
data = (WORK / "log.txt").read_bytes()
(OUT / "log.txt").write_bytes(data[-200000:])
dump()
print("ACCEL_JOB_DONE rc=%s killed=%s elapsed=%.1f" % (p.returncode, reason, time.time() - T0), flush=True)
sys.exit(0 if p.returncode == 0 else 4)
'''


def title_of(slug):
    return " ".join(w.capitalize() for w in slug.split("-"))


def stage(a):
    root = pathlib.Path(a.root).resolve()
    files = sorted(set(a.files) | {a.entry})
    buf = io.BytesIO()
    h = hashlib.sha256()
    with tarfile.open(fileobj=buf, mode="w:gz") as tf:
        for rel in files:
            p = root / rel
            data = p.read_bytes()
            h.update(rel.encode() + b"\0" + data + b"\0")
            ti = tarfile.TarInfo(rel)
            ti.size = len(data)
            ti.mtime = 0
            tf.addfile(ti, io.BytesIO(data))
    sha = h.hexdigest()
    out = STAGE_ROOT / a.id
    out.mkdir(parents=True, exist_ok=True)
    for old in out.iterdir():
        old.unlink()
    head = "".join(f"{k} = {v!r}\n" for k, v in dict(
        SLUG=a.id, ACC=a.acc, SOURCE_SHA=sha, ENTRY=a.entry, ARGS=a.args or [], WATCHDOG=a.watchdog,
        STALL=a.stall, PAYLOAD=base64.b64encode(buf.getvalue()).decode()).items())
    (out / "run.py").write_text(head + RUNNER)
    meta = {"id": f"{OWNER}/{a.id}", "title": title_of(a.id), "code_file": "run.py", "language": "python",
            "kernel_type": "script", "is_private": True, "enable_gpu": a.acc == "t4", "enable_tpu": a.acc == "tpu",
            "enable_internet": bool(a.internet), "dataset_sources": [], "competition_sources": [],
            "kernel_sources": [], "model_sources": []}
    (out / "kernel-metadata.json").write_text(json.dumps(meta, indent=2) + "\n")
    (out / "stage.json").write_text(json.dumps({"files": files, "sha": sha, "acc": a.acc, "entry": a.entry,
                                                "args": a.args or [], "watchdog": a.watchdog}, indent=1))
    print(out, sha, sum(1 for _ in files), "files", (out / "run.py").stat().st_size, "bytes")


def ledger_rows():
    return LEDGER.read_text() if LEDGER.exists() else ""


def append_ledger(cells):
    with open(LEDGER, "a") as f:
        f.write("| " + " | ".join(str(c).replace("|", "/") for c in cells) + " |\n")


def submit(a):
    out = STAGE_ROOT / a.id
    st = json.loads((out / "stage.json").read_text())
    if f"`{a.id}`" in ledger_rows() and not a.reuse_harvested:
        sys.exit(f"{a.id} already in the ledger: one id per experiment (harvest, then pass --reuse-harvested)")
    if st["acc"] == "tpu":
        try:
            fd = os.open(TPU_LOCK, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        except FileExistsError:
            sys.exit("TPU-LOCK held: " + TPU_LOCK.read_text().strip())
        os.write(fd, f"{a.holder} {a.id} {dt.datetime.now(dt.timezone.utc).isoformat()}\n".encode())
        os.close(fd)
    cmd = KAGGLE + ["kernels", "push", "-p", str(out), "--accelerator", ACC[st["acc"]], "--timeout", str(a.timeout)]
    t = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d %H:%MZ")
    r = subprocess.run(cmd, capture_output=True, text=True)
    txt = (r.stdout + r.stderr).strip()
    print(txt)
    m = re.search(r"version (\d+)", txt, re.I)
    ver = m.group(1) if m else "?"
    if r.returncode != 0 and st["acc"] == "tpu":
        TPU_LOCK.unlink()
    shown = " ".join(c if c != str(out) else "STAGE/" + a.id for c in cmd[6:])
    append_ledger([t, f"`{a.id}`", ver, st["acc"], st["sha"][:16], f"`{st['entry']} {' '.join(st['args'])}`",
                   f"`kaggle {shown}`", a.holder, "submitted" if r.returncode == 0 else "push-failed rc=%d" % r.returncode,
                   "", ""])


def status(a):
    r = subprocess.run(KAGGLE + ["kernels", "status", f"{OWNER}/{a.id}"], capture_output=True, text=True)
    print((r.stdout + r.stderr).strip())
    return r.stdout + r.stderr


def harvest(a):
    s = status(a)
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    for pat in ("^results[.]json$", "^manifest[.]json$", "^log[.]txt$"):
        subprocess.run(KAGGLE + ["kernels", "output", f"{OWNER}/{a.id}", "-p", str(out), "--force",
                                 "--file-pattern", pat], capture_output=True, text=True)
    got = {p.name: p.stat().st_size for p in out.iterdir()}
    print("harvested", got)
    man = json.loads((out / "manifest.json").read_text()) if (out / "manifest.json").exists() else {}
    terminal = any(w in s.lower() for w in ("complete", "error", "cancel"))
    st = json.loads((STAGE_ROOT / a.id / "stage.json").read_text()) if (STAGE_ROOT / a.id / "stage.json").exists() else {}
    if terminal and st.get("acc") == "tpu" and TPU_LOCK.exists() and a.id in TPU_LOCK.read_text():
        TPU_LOCK.unlink()
        print("TPU-LOCK released")
    if terminal:
        append_ledger([dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d %H:%MZ"), f"`{a.id}`", "harvest", st.get("acc", "?"),
                       man.get("source_sha256", "?")[:16], "", "", a.holder,
                       re.sub(r"\s+", " ", s.strip().split("has status")[-1])[:40],
                       f"elapsed {man.get('elapsed_s', '?')} s, rc {man.get('rc', '?')}, hw_ok {man.get('hardware_ok', '?')}",
                       ", ".join(f"{k} {v}" for k, v in sorted(got.items()))])


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("stage")
    s.add_argument("--id", required=True)
    s.add_argument("--acc", choices=["t4", "tpu"], required=True)
    s.add_argument("--entry", required=True)
    s.add_argument("--args", nargs="*")
    s.add_argument("--files", nargs="*", default=[])
    s.add_argument("--root", default=".")
    s.add_argument("--watchdog", type=int, default=1200)
    s.add_argument("--stall", type=int, default=600)
    s.add_argument("--internet", action="store_true")
    for name in ("submit", "status", "harvest"):
        p = sub.add_parser(name)
        p.add_argument("--id", required=True)
        p.add_argument("--holder", default="accel-ready")
        if name == "submit":
            p.add_argument("--timeout", type=int, required=True)
            p.add_argument("--reuse-harvested", action="store_true")
        if name == "harvest":
            p.add_argument("--out", required=True)
    a = ap.parse_args()
    if a.cmd == "stage" and not re.fullmatch(r"[a-z0-9-]{5,50}", a.id):
        sys.exit("id: lowercase, digits, dashes, 5-50 chars")
    {"stage": stage, "submit": submit, "status": status, "harvest": harvest}[a.cmd](a)


if __name__ == "__main__":
    main()
