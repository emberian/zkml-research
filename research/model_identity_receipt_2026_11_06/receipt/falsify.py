#!/usr/bin/env python3
"""The receipt's falsifiers: altered copies of an honest receipt, each of which mir-verify must refuse.

usage: falsify.py RECEIPT MIR_VERIFY [--negative NEG.json] [--eval-key PEM]
                  [--strict-receipt S.json --recomputer PK]
RECEIPT must be accepted with its own evaluator key trusted. Altered copies must be refused. With --eval-key the
colluding-evaluator cases run too: the evaluator re-signs an altered receipt, and what must stop it is the graph's
structure or a recomputer's signature. --strict-receipt is a receipt whose two required edges are signed by the
recomputer key PK; it must pass --strict, and its altered copies must not. Exit 0 iff everything is as expected.
"""
import argparse, copy, hashlib, json, os, subprocess, sys, tempfile

a = argparse.ArgumentParser()
a.add_argument("receipt"); a.add_argument("mir_verify")
a.add_argument("--negative"); a.add_argument("--eval-key")
a.add_argument("--strict-receipt"); a.add_argument("--recomputer")
args = a.parse_args()
V = args.mir_verify
COMPONENTS = ["integers", "flashprove-config", "tokenizer", "adapter", "system-prompt", "tools"]
sha = lambda s: hashlib.sha256(s.encode()).hexdigest()
other = sha("another")

def run(r, cid=None, trust=None, extra=()):
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
        json.dump(r, f)
    p = subprocess.run([V, "check", f.name, "--cid", cid or r["commitment_id"], "--trust", trust or r["eval"]["public_key"],
                        "--fp-verdict", "yes", *extra], capture_output=True, text=True)
    os.unlink(f.name)
    return p.returncode, [l.strip()[3:].strip() for l in p.stdout.splitlines() if l.startswith("  NO ")] or [p.stderr.strip()[:90]]

def node(r, kind):
    return next(n for n in r["graph"]["nodes"] if n["kind"] == kind)

def redeploy(r):
    by = {n["kind"]: n["digest"] for n in r["graph"]["nodes"]}
    node(r, "deployment")["digest"] = sha("mir13/deployment/v1\n" + "".join(f"{k}\t{by[k]}\n" for k in COMPONENTS))

def resign(r):
    with tempfile.TemporaryDirectory() as d:
        j, b = os.path.join(d, "r.json"), os.path.join(d, "f.bin")
        json.dump(r, open(j, "w"))
        if subprocess.run([V, "fields", j, b]).returncode != 0:
            return r
        sig = subprocess.run(["openssl", "pkeyutl", "-sign", "-inkey", args.eval_key, "-rawin", "-in", b],
                             capture_output=True, check=True).stdout.hex()
    r["eval"]["signature"] = sig
    return r

ok = True
def expect(label, want_accept, rc, why):
    global ok
    good = (rc == 0) == want_accept
    ok &= good
    print(f"{'ACCEPT' if rc == 0 else 'REFUSE'}{'' if good else ' (UNEXPECTED)'}  {label}" + ("" if rc == 0 else f"  -- {'; '.join(why)}"))

honest = json.load(open(args.receipt))
expect("honest receipt", True, *run(honest))

def alt(label, f, collude=False, **kw):
    r = copy.deepcopy(honest); f(r)
    if collude: r = resign(r)
    expect(label + (" [evaluator re-signs]" if collude else ""), False, *run(r, **kw))

def swap_cid(r): r["commitment_id"] = other; node(r, "flashprove-commitment")["digest"] = other
def other_ckpt(r): r["rootset"] = other; node(r, "integers")["digest"] = other; redeploy(r)
def adapter(r): node(r, "adapter")["digest"] = sha("a LoRA adapter"); redeploy(r)
def sysprompt(r): node(r, "system-prompt")["digest"] = sha("You are a pirate."); redeploy(r)
def scores(r): r["eval"]["scores"] = "MMLU-Pro 99.9"
alt("swapped commitment ID (receipt and graph both)", swap_cid)
alt("evaluation presented for a different checkpoint (other root set)", other_ckpt)
alt("provenance graph with a different adapter hash", adapter)
alt("provenance graph with a different system prompt", sysprompt)
alt("scores changed after signing", scores)
alt("graph names another commitment than the receipt", lambda r: node(r, "flashprove-commitment").update(digest=other))
alt("deployment digest not its components'", lambda r: node(r, "deployment").update(digest=other))
alt("evaluated node changed to meta-bf16", lambda r: r["eval"].update(node="meta-bf16"))
alt("hollow commitment: the proof was checked against another ID", lambda r: None, cid=other)
alt("evaluator key not trusted by the client", lambda r: None, trust=sha("k"))
alt("strict mode with E3 only published", lambda r: None, extra=("--strict",))
if args.eval_key:
    alt("evaluated node meta-bf16", lambda r: r["eval"].update(node="meta-bf16"), collude=True)
    alt("evaluated node wsums (a digest, not a model)", lambda r: r["eval"].update(node="wsums"), collude=True)
    alt("a second integers node aliasing the bf16 model",
        lambda r: r["graph"]["nodes"].insert(0, {"id": "alias", "kind": "integers", "digest": node(r, "base")["digest"]}), collude=True)
    alt("duplicate node id", lambda r: r["graph"]["nodes"].append(dict(node(r, "base"))), collude=True)
    alt("edge to a node that does not exist", lambda r: r["graph"]["edges"].append(
        {"src": "ghost", "dst": "integers", "rel": "quantizes", "rule": "x", "basis": {"kind": "published", "source": "x"}}), collude=True)
    alt("no edges at all (E2 and E3 missing)", lambda r: r["graph"].update(edges=[]), collude=True)
    alt("a non-hex digest", lambda r: node(r, "tools").update(digest="z" * 64), collude=True)
if args.negative:
    neg = json.load(open(args.negative))
    expect("signed evaluation of Meta's bf16 model presented for the 4-bit commitment", False, *run(neg))
if args.strict_receipt:
    s = json.load(open(args.strict_receipt))
    expect("strict receipt, both edges recomputed by a trusted key", True, *run(s, extra=("--strict", "--recomputer", args.recomputer)))
    expect("strict receipt, recomputer not trusted", False, *run(s, extra=("--strict", "--recomputer", sha("r"))))
    t = copy.deepcopy(s); node(t, "gguf-files")["digest"] = other; t["files_digest"] = other
    t = resign(t) if args.eval_key else t
    expect("strict receipt, file digest changed, recomputer signatures kept" + (" [evaluator re-signs]" if args.eval_key else ""),
           False, *run(t, extra=("--strict", "--recomputer", args.recomputer)))
print("falsifiers: all as expected" if ok else "falsifiers: SOMETHING WAS NOT AS EXPECTED")
sys.exit(0 if ok else 1)
