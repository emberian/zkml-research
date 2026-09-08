#!/usr/bin/env python3
"""Retain one command's output, elapsed time and process resource usage."""
import datetime, json, pathlib, resource, subprocess, sys, time

root = pathlib.Path(__file__).resolve().parent
label, *command = sys.argv[1:]
if not label or not command or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-_" for c in label):
    raise SystemExit("usage: run_command.py LABEL COMMAND ARG...")
record_path = root / "results" / (label + ".command.json")
record = {"command": command, "cwd": str(root), "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
with record_path.open("x") as f:
    json.dump(record, f, indent=2)
started = time.monotonic()
with (root / "results" / (label + ".stdout")).open("xb") as stdout, (root / "results" / (label + ".stderr")).open("xb") as stderr:
    process = subprocess.Popen(command, cwd=root, stdout=stdout, stderr=stderr)
    record["pid"] = process.pid
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    code = process.wait()
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
record.update(returncode=code, elapsed_seconds=time.monotonic()-started,
              finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              user_seconds=usage.ru_utime, system_seconds=usage.ru_stime,
              max_rss_bytes=usage.ru_maxrss if sys.platform == "darwin" else usage.ru_maxrss*1024)
record_path.write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record), flush=True)
raise SystemExit(code)
