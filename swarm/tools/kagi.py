#!/usr/bin/env python3
"""Kagi Search API v1. Usage: kagi.py "<query>" [limit]. Key: $KAGI_API_KEY or ~/dev/allgame/.env"""
import sys, os, json, re, html, urllib.request
key = os.environ.get("KAGI_API_KEY")
if not key:
    for line in open(os.path.expanduser("~/dev/allgame/.env")):
        if line.startswith("KAGI_API_KEY="): key = line.split("=",1)[1].strip().strip('"').strip("'")
q = sys.argv[1]; limit = int(sys.argv[2]) if len(sys.argv) > 2 else 10
req = urllib.request.Request("https://kagi.com/api/v1/search", data=json.dumps({"query": q}).encode(),
    headers={"Authorization": f"Bearer {key}", "Content-Type": "application/json"})
with urllib.request.urlopen(req, timeout=30) as r: data = json.load(r)
clean = lambda t: html.unescape(re.sub(r"</?strong>", "", t or "")).strip()
items = (data.get("data") or {}).get("search") or []
print(f"[{len(items)} results for: {q}]")
for it in items[:limit]:
    print(f"\n** {clean(it.get('title'))}\n{it.get('url')}\n{clean(it.get('snippet'))[:400]}")
