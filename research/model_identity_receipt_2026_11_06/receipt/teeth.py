#!/usr/bin/env python3
"""G14: corruption teeth for mir-stream on FlashProve's synthetic oracle shards.

usage: teeth.py MIR_STREAM ORACLE_DIR BASE_MANIFEST WORKDIR
1. flip the sign bit of one stored F32 weight of blk.10.ffn_down_exps: its raw and integer digests, its root and the
   root set change, and no other tensor's root does;
2. swap routed experts 0 and 1 of blk.10.ffn_up_exps: the two slice roots trade places, the tensor root changes;
3. e_res 12 instead of 11: only token_embd's root changes.
"""
import json, os, shutil, subprocess, sys

binp, odir, basem, work = sys.argv[1:5]
base = json.load(open(basem))
shards = [os.path.join(odir, f"oracle-0000{i}-of-00002.gguf") for i in (1, 2)]

def layout():
    out = {}
    for s in shards:
        for line in subprocess.run([binp, "layout", s], capture_output=True, text=True, check=True).stdout.splitlines():
            name, typ, rest = line.split(" ", 2)
            dims, off, n = rest.rsplit(" ", 2)
            out[name] = (s, typ, json.loads(dims), int(off), int(n))
    return out

def run(tag, files, eres=11):
    out = os.path.join(work, tag)
    subprocess.run([binp, "local", "--eres", str(eres), "--out", out, *files], capture_output=True, check=True)
    return json.load(open(os.path.join(out, "manifest-v2.json")))

def roots(m):
    return {t["name"]: t for t in m["tensors"]}

def copy_with(tag, edit):
    d = os.path.join(work, tag + "-shards"); os.makedirs(d, exist_ok=True)
    files = []
    for s in shards:
        t = os.path.join(d, os.path.basename(s)); shutil.copyfile(s, t); files.append(t)
    edit({os.path.basename(s): t for s, t in zip(shards, files)})
    return files

L = layout(); B = roots(base); ok = True

def check(what, cond):
    global ok
    print(("ok   " if cond else "FAIL ") + what); ok &= cond

# 1
name = "blk.10.ffn_down_exps.weight"; s, typ, dims, off, n = L[name]; assert typ == "F32"
def flip(m):
    p = m[os.path.basename(s)]
    with open(p, "r+b") as f:
        f.seek(off + 4 * 5 + 3); b = f.read(1); f.seek(off + 4 * 5 + 3); f.write(bytes([b[0] ^ 0x80]))
R = roots(run("flip", copy_with("flip", flip)))
check("flip: raw digest changes", R[name]["raw_sha256"] != B[name]["raw_sha256"])
check("flip: integer digest changes", R[name]["int_sha256"] != B[name]["int_sha256"])
check("flip: tensor root changes", R[name]["root"] != B[name]["root"])
check("flip: no other tensor root changes", all(R[k]["root"] == B[k]["root"] for k in B if k != name))

# 2
name = "blk.10.ffn_up_exps.weight"; s, typ, dims, off, n = L[name]; per = n // dims[2]
def swap(m):
    p = m[os.path.basename(s)]
    with open(p, "r+b") as f:
        f.seek(off); a = f.read(per); b = f.read(per); f.seek(off); f.write(b + a)
R = roots(run("swap", copy_with("swap", swap)))
check("swap: slice roots trade places", R[name]["slice_roots"] == B[name]["slice_roots"][::-1] and
      B[name]["slice_roots"][0] != B[name]["slice_roots"][1])
check("swap: tensor root changes", R[name]["root"] != B[name]["root"])

# 3
M12 = run("eres12", shards, eres=12); R = roots(M12)
check("e_res: token_embd root changes", R["token_embd.weight"]["root"] != B["token_embd.weight"]["root"])
check("e_res: no other root changes", all(R[k]["root"] == B[k]["root"] for k in B if k != "token_embd.weight"))
check("e_res: root set changes", M12["rootset"] != base["rootset"])
sys.exit(0 if ok else 1)
