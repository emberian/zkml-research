#!/usr/bin/env python3
"""Tiny scry.io MCP client (no MCP config needed). Key: ~/.scry-key or $SCRY_API_KEY.
  scry.py sql '<ONE SELECT ... LIMIT n>'            # SCRY_MAX_SECONDS env sets the deadline (default 120)
  scry.py call <tool> '<json args>'                 # e.g. call schema '{"relation":"openalex.works"}'
Relations: openalex.works (hasAllTokens(search_text_lc,[...])), openalex.cited_by, academic.catalog,
academic.papers (hasToken(text,'tok')), hackernews.items, github.documents, forums.posts. eprint is NOT here."""
import sys, os, json, urllib.request
key = os.environ.get("SCRY_API_KEY") or open(os.path.expanduser("~/.scry-key")).read().strip()
MAXS = os.environ.get("SCRY_MAX_SECONDS", "120")
def rpc(method, params, timeout=600):
    body = json.dumps({"jsonrpc":"2.0","id":1,"method":method,"params":params}).encode()
    req = urllib.request.Request("https://mcp.scry.io", data=body, headers={
        "Authorization": f"Bearer {key}", "Content-Type": "application/json",
        "Accept": "application/json, text/event-stream", "x-scry-admission": "patient", "x-scry-max-seconds": MAXS})
    with urllib.request.urlopen(req, timeout=timeout) as r: raw = r.read().decode()
    for line in raw.splitlines():
        if line.startswith("data:"): raw = line[5:].strip(); break
    d = json.loads(raw)
    if "error" in d: print("ERR", d["error"]); sys.exit(1)
    return d["result"]
cmd = sys.argv[1]
if cmd == "sql":
    res = rpc("tools/call", {"name":"sql","arguments":{"sql":sys.argv[2], **(json.loads(sys.argv[3]) if len(sys.argv)>3 else {})}})
elif cmd == "call":
    res = rpc("tools/call", {"name":sys.argv[2],"arguments":json.loads(sys.argv[3]) if len(sys.argv)>3 else {}})
else: print(__doc__); sys.exit(2)
for b in res.get("content", []):
    if b.get("type") == "text": print(b["text"])
if res.get("isError"): print("[isError=true]")
