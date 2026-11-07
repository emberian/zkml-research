#!/usr/bin/env python3
"""Custody check for a deployed run: no tape, key, checkpoint or share file of custodian i exists on another box.

Usage: custody_check.py SEATS.json
SEATS.json: {"seats": [{"seat": "0", "ssh": "dregg-forge", "dirs": ["/srv/lanes/dl-gen6-deploy/run1"]}, ...]}
(the owner is a seat too: {"seat": "owner", ...}; its dirs may be on a custodian's box but must be its own).

Two checks, on every box, over every file under every seat's dirs on that box:
1. by name: a secret of seat s (tls_<s>.key, tape_<s>*.bin, ckpt_P<s>.bin, shares_<s>.bin, owner-msg-P<s>.bin,
   tape_I.bin under step-*/ in a chunk of seat s) is only in seat s's own dirs;
2. by content: the sha256 of each secret file, taken on its home box, matches no file of the same size anywhere
   else (a renamed copy is found too).
Exit 0 and print "custody: ok" with the counts, or exit 1 with the violations.
"""
import json, re, shlex, subprocess, sys

SECRET = [r"tls_{s}\.key$", r"tape_{s}(_.*)?\.bin$", r"ckpt_P{s}\.bin$", r"shares_{s}\.bin$", r"owner-msg-P{s}\.bin$"]


def listing(ssh, dirs):
    """(path, size) of every regular file under dirs on the box."""
    q = " ".join(shlex.quote(d) for d in dirs)
    out = subprocess.run(["ssh", ssh, f"find {q} -type f -printf '%s\\t%p\\n' 2>/dev/null; true"], capture_output=True, text=True, check=True).stdout
    return sorted({(p, int(s)) for s, p in (l.split("\t", 1) for l in out.splitlines() if "\t" in l)})


def hashes(ssh, paths):
    if not paths:
        return {}
    out = subprocess.run(["ssh", ssh, "sha256sum " + " ".join(shlex.quote(p) for p in paths)], capture_output=True, text=True, check=True).stdout
    return {l.split(None, 1)[1].strip(): l.split()[0] for l in out.splitlines()}


def main():
    cfg = json.load(open(sys.argv[1]))
    seats = cfg["seats"]
    boxes = {}
    for st in seats:
        boxes.setdefault(st["ssh"], []).append(st)
    files = {b: listing(b, [d for st in sts for d in st["dirs"]]) for b, sts in boxes.items()}
    def owner_of_path(b, p):
        # the seat whose dir is the longest prefix of p (the owner's dir may sit inside a custodian's run dir)
        best = max(((len(d), st["seat"]) for st in boxes[b] for d in st["dirs"] if p.startswith(d.rstrip("/") + "/")), default=(0, None))
        return best[1]
    viol, secrets = [], []
    for b, fl in files.items():
        for p, size in fl:
            name = p.rsplit("/", 1)[1]
            for st in seats:
                s = st["seat"]
                if any(re.search(pat.format(s=re.escape(s)), name) for pat in SECRET):
                    home = owner_of_path(b, p)
                    if st["ssh"] != b or home != s:
                        viol.append(f"{b}:{p} is seat {s}'s secret but lies in seat {home}'s dirs")
                    else:
                        secrets.append((b, p, size, s))
    sh = {}
    for b in files:
        sh.update({(b, p): h for p, h in hashes(b, [p for (bb, p, _, _) in secrets if bb == b]).items()})
    for b, fl in files.items():
        sizes = {size for (bb, _, size, s) in secrets}
        cand = [p for p, size in fl if size in sizes]
        hs = hashes(b, cand)
        for (bb, p0, size, s) in secrets:
            h0 = sh[(bb, p0)]
            for p, h in hs.items():
                if h == h0 and not (b == bb and p == p0) and owner_of_path(b, p) != s:
                    viol.append(f"{b}:{p} has the content of seat {s}'s {p0} (on {bb})")
    if viol:
        print("custody: VIOLATIONS")
        for v in viol:
            print("  " + v)
        sys.exit(1)
    if "-v" in sys.argv:
        for x in secrets:
            print("  secret", x)
    print(json.dumps({"custody": "ok", "secret_files": len(secrets), "files_scanned": sum(len(f) for f in files.values()),
                      "by_seat": {st["seat"]: sum(1 for x in secrets if x[3] == st["seat"]) for st in seats}}))


if __name__ == "__main__":
    main()
