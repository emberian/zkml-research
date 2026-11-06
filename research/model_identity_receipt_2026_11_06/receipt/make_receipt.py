#!/usr/bin/env python3
"""Assemble a model-identity receipt (mir13/receipt/v1) from a mir-stream manifest and FlashProve's published values,
have mir-verify print the fields to sign, sign them with an Ed25519 key through openssl, and write the receipt.

usage: make_receipt.py --manifest M.json --expected EXPECTED.txt --weights-sha WEIGHTS.sha256 --key KEY.pem
                       --mir-verify BIN --out RECEIPT.json [--eval-node NODE] [--benchmark TEXT] [--scores TEXT]
                       [--evaluator NAME]

Stdlib only. The graph below is Llama 4 Maverick UD-Q4_K_XL's; every digest comes from the manifest, from FlashProve's
expected.txt / weights.sha256, or is the SHA-256 of the text shown.
"""
import argparse, hashlib, json, subprocess, sys, tempfile, os

def sha(text): return hashlib.sha256(text.encode()).hexdigest()

def expected_values(path):
    out = {}
    for line in open(path):
        h, name = line.split()
        out[name] = h
    return out

def raw_pubkey(pem):
    der = subprocess.run(["openssl", "pkey", "-in", pem, "-pubout", "-outform", "DER"], capture_output=True, check=True).stdout
    return der[-32:].hex()

def sign(pem, data_path):
    return subprocess.run(["openssl", "pkeyutl", "-sign", "-inkey", pem, "-rawin", "-in", data_path],
                          capture_output=True, check=True).stdout.hex()

COMPONENTS = ["integers", "flashprove-config", "tokenizer", "adapter", "system-prompt", "tools"]

def deployment_digest(nodes):
    by = {n["kind"]: n["digest"] for n in nodes}
    return sha("mir13/deployment/v1\n" + "".join(f"{k}\t{by[k]}\n" for k in COMPONENTS))

def build(m, exp, weights_sha_text, args):
    files_digest = hashlib.sha256(weights_sha_text.encode()).hexdigest()
    ours = "".join(f"{f['sha256']}  {f['name']}\n" for f in m["files"])
    if ours != weights_sha_text:
        msg = "the streamed file digests differ from the published list"
        if args.require_match:
            sys.exit("make_receipt: " + msg)
        print("note: " + msg, file=sys.stderr)
    fp_rel = "FlashProve 0.16.0-rc.26 @ 9e2bdd8ff5bf9c62f18263d7dac189b0400b260c"
    nodes = [
        {"id": "meta-bf16", "kind": "base",
         "digest": sha("hf:meta-llama/Llama-4-Maverick-17B-128E-Instruct@73d14711bcc77c16df3470856949c3764056b617")},
        {"id": "gguf", "kind": "gguf-files", "digest": files_digest},
        {"id": "integers", "kind": "integers", "digest": m["rootset"]},
        {"id": "wsums", "kind": "wsums", "digest": m["wsums_sha256"]},
        {"id": "commitment", "kind": "flashprove-commitment", "digest": exp["commitment-id"]},
        {"id": "fp-config", "kind": "flashprove-config", "digest": exp["config/KL.bin"]},
        {"id": "fp-key", "kind": "flashprove-key-file", "digest": exp["ivk/key.bin"]},
        {"id": "fp-release", "kind": "prover-release", "digest": sha(fp_rel)},
        {"id": "tokenizer", "kind": "tokenizer", "digest": m["files"][0]["sha256"]},
        {"id": "adapter", "kind": "adapter", "digest": sha(args.adapter)},
        {"id": "system-prompt", "kind": "system-prompt", "digest": sha(args.system_prompt)},
        {"id": "tools", "kind": "tools", "digest": sha(args.tools)},
    ]
    nodes.append({"id": "deployment", "kind": "deployment", "digest": deployment_digest(nodes)})
    pub = lambda s: {"kind": "published", "source": s}
    rer = lambda s: {"kind": "rerunnable", "how": s}
    edges = [
        {"src": "meta-bf16", "dst": "gguf", "rel": "quantizes",
         "rule": "unsloth UD-Q4_K_XL dynamic 4-bit quantization, rev 41032e5471dd6ea5b349062d978626215d6c5bba",
         "basis": pub("unsloth model card tag base_model:quantized:meta-llama/Llama-4-Maverick-17B-128E-Instruct")},
        {"src": "gguf", "dst": "integers", "rel": "converts",
         "rule": "FlashProve docs/model.md section 11 at e_res 10; registry v2 roots per ROOTS-V2.md",
         "basis": rer("mir-stream remote --eres 10 (stream/); gates.sh G11-G13")},
        {"src": "integers", "dst": "wsums", "rel": "digest-of",
         "rule": "SHA-256 of wsums.txt as weight_sums/ writes it",
         "basis": rer("mir-stream; equals FlashProve examples/maverick/expected.txt (gate G12)")},
        {"src": "gguf", "dst": "commitment", "rel": "commits",
         "rule": "cp_commit -public-weights, examples/maverick/public-seed.bin, e_res 10, fitted KL.bin",
         "basis": pub("FlashProve examples/maverick/expected.txt and README reproduction record (one H100, 330 GB host memory)")},
        {"src": "fp-config", "dst": "commitment", "rel": "digest-of", "rule": "R4.11: the ID hashes the configuration",
         "basis": pub("FlashProve examples/maverick/expected.txt")},
        {"src": "fp-key", "dst": "commitment", "rel": "digest-of",
         "rule": "R4.11: the ID hashes the anchor root and OOD answers held in key.bin",
         "basis": pub("FlashProve examples/maverick/expected.txt")},
    ]
    return {
        "format": "mir13/receipt/v1",
        "commitment_id": exp["commitment-id"],
        "rootset": m["rootset"],
        "wsums_sha256": m["wsums_sha256"],
        "files_digest": files_digest,
        "graph": {"nodes": nodes, "edges": edges},
        "eval": {"evaluator": args.evaluator, "public_key": raw_pubkey(args.key), "node": args.eval_node,
                 "benchmark": args.benchmark, "scores": args.scores, "signature": ""},
        "stream": {"tensors": len(m["tensors"]), "experts": len(m["experts"]), "eres": m["eres"],
                   "files_match_expected": m.get("files_match_expected")},
    }

def sign_edges(r, args, d):
    """Sign, as recomputer, every edge whose relation is in --recompute (the signer re-ran it)."""
    if not args.recomputer_key:
        return
    pk = raw_pubkey(args.recomputer_key)
    tmp = os.path.join(d, "edges.json")
    json.dump(r, open(tmp, "w"))
    for i, e in enumerate(r["graph"]["edges"]):
        if e["rel"] in args.recompute.split(","):
            out = os.path.join(d, f"e{i}.bin")
            subprocess.run([args.mir_verify, "edge-fields", tmp, str(i), out], check=True)
            e["basis"] = {"kind": "recomputed", "signer": pk, "signature": sign(args.recomputer_key, out)}

def main():
    a = argparse.ArgumentParser()
    for k in ["--manifest", "--expected", "--weights-sha", "--key", "--mir-verify", "--out"]:
        a.add_argument(k, required=True)
    a.add_argument("--eval-node", default="deployment")
    a.add_argument("--adapter", default="none")
    a.add_argument("--tools", default="none")
    a.add_argument("--require-match", action="store_true")
    a.add_argument("--recomputer-key")
    a.add_argument("--recompute", default="converts")
    a.add_argument("--evaluator", default="demonstration key of the mir13 lane: no lab has signed an evaluation of this checkpoint")
    a.add_argument("--benchmark", default="none run: this record signs the identity fields only")
    a.add_argument("--scores", default="none")
    a.add_argument("--system-prompt", default="")
    args = a.parse_args()
    m = json.load(open(args.manifest))
    r = build(m, expected_values(args.expected), open(args.weights_sha).read(), args)
    with tempfile.TemporaryDirectory() as d:
        sign_edges(r, args, d)
        unsigned = os.path.join(d, "r.json"); fields = os.path.join(d, "f.bin")
        json.dump(r, open(unsigned, "w"), indent=1)
        subprocess.run([args.mir_verify, "fields", unsigned, fields], check=True)
        r["eval"]["signature"] = sign(args.key, fields)
    json.dump(r, open(args.out, "w"), indent=1)
    print(args.out)

if __name__ == "__main__":
    main()
