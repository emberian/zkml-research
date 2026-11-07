"""Sweep driver for native/darktrain: runs configs (JSON objects, one per line or a Python list) through the binary
in parallel and appends one summary line per run to the output JSONL (the full curve under "curve").

    python3 -I train_sweep.py BINARY CONFIGS.jsonl OUT.jsonl JOBS [THREADS_PER_JOB]
"""
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


def run(binary, cfg, threads):
    env = dict(os.environ, RAYON_NUM_THREADS=str(threads))
    out = subprocess.run([binary, "float" if cfg.pop("_float", False) else "run", json.dumps(cfg)],
                         capture_output=True, text=True, env=env)
    lines = [json.loads(l) for l in out.stdout.splitlines() if l.strip()]
    if out.returncode != 0 or not lines or "summary" not in lines[-1]:
        return dict(cfg=cfg, error=out.stderr[-2000:])
    s = lines[-1]
    s["curve"] = lines[:-1]
    return s


def main():
    binary, cfgs, outp, jobs = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    threads = int(sys.argv[5]) if len(sys.argv) > 5 else 2
    with open(cfgs) as f:
        todo = [json.loads(l) for l in f if l.strip()]
    with ThreadPoolExecutor(jobs) as ex, open(outp, "a") as out:
        for r in ex.map(lambda c: run(binary, c, threads), todo):
            out.write(json.dumps(r) + "\n")
            out.flush()


if __name__ == "__main__":
    main()
