#!/usr/bin/env python3
"""The run of record's config for run.py, for either third box.

    record.py LAYOUT --steps N --handover-at K --chunks NAME [--chunk-steps S] [--third HOST,IP,ROOT] > RUN.json

LAYOUT:
  hbox    forge (seat 0) + bb2 (seat 1) + hbox (seat 2; swarm-build, SWARM_MEM_MAX=16G, /othersys, disk line 30 GB;
          nothing is written to hbox's root fs)
  wired   forge + bb2 + a wired third box (--third HOST,IP,ROOT; the default is a placeholder that run.py's gate
          and check refuse, so a config cannot launch before ember names the box)
One custodian per machine in each committee: the new committee is three new processes, one on each of the same three
boxes, with their own TLS identities, their own MP-SPDZ key (prep's handover chunk) and their own HE ceremony.

What it pins (the posture of the run; change it here, not by hand in the JSON):
- profile ledger-x2de with RS by default (F_{p^2} challenges, cuts D and E, one masked zero test per truncation; the genesis record carries "EXT": 2 and Ledger::open refuses another);
- every tape single-use (the box registry), checked against the profile before step 0, waited for (--tape-wait)
  when prep runs behind, wiped once spent (--wipe-spent);
- pipelined proofs on their own mesh per committee; every bundle archived on one seat per committee (--archive-on, forge
  by default; latest only elsewhere); the disk plan (run.py plan / gate / drive's disk pause) against every box's line;
- forge's nightly 10:00-11:00 UTC: custodian 0 votes the pause, run.py drive resumes after the window;
- the handover after step K (the new committee started by drive after step K - 1, launch_new "deferred");
- the release at the end, from the release's own tape on each box (loaded after the steps' tape is freed);
- every state file (checkpoint, carry, TLS key) sealed under the epoch's file key (darkhand::vault), destroyed at
  the erasure.
Chunk paths follow the prep lane's layout ROOT/chunks/NAME-P<I>/step-<j>/{tape_I.bin,owner-msg-P<I>.bin} with
--chunk-steps S steps per chunk dir: NAME-c<c>-P<I> for the old committee's chunk c (from step 0) and NAME-n-c<c>-P<I>
for the new committee's (from step K + 1);
the handover tapes NAME-ho-P<I>/step-0/tape_I.bin and the release tapes NAME-rel-P<I>/step-0/tape_I.bin.
"""
import argparse, json, sys

GEN = "/Users/ember/dev/zkml-research/research/dark_learning_2026_11_06/train_genesis_gen6.json"
OUT = "/private/tmp/claude-501/-Users-ember-dev-aidev/78fef112-a52f-425f-8503-f3fa24ff087c/scratchpad/dl-gen5/deploy2/runs"

FORGE = {"host": "dregg-forge", "ip": "178.105.4.114", "root": "/srv/lanes/dl-gen6-deploy", "prep": "/srv/lanes/dl-gen6-prep",
         "scope": "systemd-run --scope -p MemoryMax=12G", "env": "DS_THREADS=16"}
BB2 = {"host": "bb2", "ip": "2.31.77.40", "root": "/home/build/lanes/dl-gen6-deploy", "prep": "/home/build/lanes/dl-gen6-prep",
       "scope": "systemd-run --user --scope -p MemoryMax=16G", "env": "DS_THREADS=16"}
HBOX = {"host": "hbox", "ip": None, "root": "/othersys/lanes/dl-gen6-deploy", "prep": "/othersys/lanes/dl-gen6-prep",
        "scope": "env SWARM_MEM_MAX=16G swarm-build", "env": "DS_THREADS=16", "disk_line_gb": 30}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("layout", choices=["hbox", "wired", "dev"], help="dev: forge + bb2 + bb2, a rehearsal (two seats on one box: not a deployment)")
    ap.add_argument("--no-release", action="store_true", help="end without the release (a rehearsal while the release does not fit)")
    ap.add_argument("--steps", type=int, required=True, help="N, the run's steps")
    ap.add_argument("--handover-at", type=int, required=True, help="K: the rotation after step K")
    ap.add_argument("--chunks", required=True, help="the prep lane's chunk name for this run")
    ap.add_argument("--chunk-steps", type=int, default=2)
    ap.add_argument("--prep-max-ready", type=int, default=9, help="prep's `darkprep produce --max-ready R`: at most R finished "
                    "chunks wait, one more is being made, so a process has at most (R + 1) x chunk-steps step files ahead "
                    "(the disk plan's lookahead)")
    ap.add_argument("--third", default="NEWBOX,0.0.0.0,/srv/lanes/dl-gen6-deploy", help="HOST,IP,ROOT of the wired third box")
    ap.add_argument("--name", default="record")
    ap.add_argument("--archive-on", default="dregg-forge", help="the box whose seat keeps every bundle (one seat per committee); "
                    "forge by default: at ~47.5 MB a step, 2,000 steps are ~89 GiB, which only forge holds above its line (run.py plan)")
    ap.add_argument("--profile", default="ledger-x2de", help="the proof profile (the coordinator's: ledger-x2de with the program flag RS)")
    ap.add_argument("--no-rs", action="store_true", help="without the program flag RS (its tapes differ: K + 1 - s bits per truncation)")
    ap.add_argument("--key-dir", default=None, help="the old committee's MP-SPDZ runtime dir name in prep's ROOT (e.g. wired: "
                    "ROOT/wired<I>/mpspdz); its p-61 MAC-key and secrets files are erased at the handover and the dir scanned")
    ap.add_argument("--key-hash", default="519717d82129ff48ce3a78ec360a737b5b3d8a5f", help="the p-61 Mascot-Secrets file's parameter hash")
    a = ap.parse_args()
    if not 0 <= a.handover_at < a.steps - 1:
        sys.exit("the handover must leave the new committee at least one step")
    if a.layout == "hbox":
        third = HBOX
        # hbox is behind NAT: it only dials (--nat 2 in every three-party mesh, --nat6 2,5 in the six-party one,
        # where old seat 2's loopback address takes new seat 2's dial on the same box)
    elif a.layout == "dev":
        third = dict(BB2)
    else:
        h, ip, root = a.third.split(",")
        third = {"host": h, "ip": ip, "root": root, "prep": root.replace("dl-gen6-deploy", "dl-gen6-prep"),
                 "scope": "systemd-run --scope -p MemoryMax=16G", "env": "DS_THREADS=16"}
    boxes = [FORGE, BB2, third]
    ip = lambda b: b["ip"] or "0.0.0.0"
    base = 28600
    pp = lambda b, k: f"{ip(b)}:{base + k}"
    mesh_old, mesh_new = [pp(b, i) for i, b in enumerate(boxes)], [pp(b, 20 + i) for i, b in enumerate(boxes)]
    proof_old, proof_new = ",".join(pp(b, 10 + i) for i, b in enumerate(boxes)), ",".join(pp(b, 30 + i) for i, b in enumerate(boxes))
    six = [pp(b, 40 + i) for i, b in enumerate(boxes)] + [pp(b, 43 + i) for i, b in enumerate(boxes)]
    if a.layout == "hbox":
        six[2] = f"127.0.0.1:{base + 42}"
    mesh6 = ",".join(six)
    # --ret-round: the switched returns rounded to their noise bits (run7 through hbox: 0.59 of the bytes; run13: the
    # rounded step proved and accepted at d = 4096, and its release's C equals the plaintext twin's)
    common = ["--ret-primes", "2", "--ret-round", "--prove", "--profile", a.profile] + ([] if a.no_rs else ["--rs"]) + [ "--wipe-spent", "--tape-wait", "7200",
              "--pause-utc", "10:00-11:00", "--timeout", "3600", "--pipeline-proofs"] + \
             (["--nat", "2", "--nat6", "2,5"] if a.layout == "hbox" else [])
    def bin_(b):
        return f"{b['root']}/ws-target-run/release"
    def seat(b, i, new):
        # the new committee's chunks count from step K + 1 again (--chunk-first): their own name
        c = f"{b['prep']}/chunks/{a.chunks}{'-n' if new else ''}-c{{c}}-P{i}/step-{{j}}"
        s = {"host": b["host"], "root": b["root"], "bin": bin_(b), "scope": b["scope"], "env": b["env"],
             "addr": (mesh_new if new else mesh_old)[i],
             "tapes": f"{c}/tape_{i}.bin", "owner_msgs": f"{c}/owner-msg-P{i}.bin",
             "extra": ["--proof-mesh", proof_new if new else proof_old]}
        if b.get("disk_line_gb"):
            s["disk_line_gb"] = b["disk_line_gb"]
        if b["host"] == a.archive_on and i == [x["host"] for x in boxes].index(a.archive_on):
            s["archive"] = True
        if new:
            s["handover_tape"] = f"{b['prep']}/chunks/{a.chunks}-ho-P{i}/step-0/tape_{i}.bin"
            if not a.no_release:
                s["extra"] += ["--release-data", f"{b['root']}/data/mnist",
                               "--release-tape", f"{b['prep']}/chunks/{a.chunks}-rel-P{i}/step-0/tape_{i}.bin"]
        elif a.key_dir:
            k = f"{b['prep']}/{a.key_dir}{i}/mpspdz"
            s["extra"] += ["--erase-extra", f"{k}/Player-Data/Mascot-Secrets-p-61-{a.key_hash}-P{i}-3",
                           "--erase-extra", f"{k}/Player-Data/3-p-61/Player-MAC-Keys-p-P{i}", "--scan-extra", k]
        return s
    cfg = {
        "name": a.name, "out": OUT, "prof": [16384, 4, 175, 4096], "t": 2305843009210515457, "gate": 309, "program": "gen6",
        "steps": a.handover_at + 1,
        "flags": common + ["--chunk-steps", str(a.chunk_steps)],
        "genesis_cfg": GEN, "owner_cfg": f"{OUT}/owner_cfg_bb2.json",
        "seats": [seat(b, i, False) for i, b in enumerate(boxes)],
        "owner": {"host": "bb2", "root": BB2["root"], "bin": bin_(BB2), "scope": "systemd-run --user --scope -p MemoryMax=8G",
                  "addr": f"{BB2['ip']}:{base + 9}"},
        "handover": {"at": a.handover_at, "steps_after": a.steps - a.handover_at - 1, "mesh6": mesh6, "launch_new": "deferred",
                     "new_seats": [seat(b, i, True) for i, b in enumerate(boxes)],
                     "flags": common + ["--chunk-steps", str(a.chunk_steps), "--chunk-first", str(a.handover_at + 1)] + ([] if a.no_release else ["--release"])},
        "drive_poll_s": 60,
        "disk": {"lookahead": (a.prep_max_ready + 1) * a.chunk_steps},
        "vault": True,
    }
    json.dump(cfg, sys.stdout, indent=1)
    print()

if __name__ == "__main__":
    main()
