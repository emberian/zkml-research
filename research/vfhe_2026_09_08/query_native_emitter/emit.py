#!/usr/bin/env python3
"""Emit the unchanged query witness using the selected Lean-generated native plan."""
from pathlib import Path
import argparse,hashlib,json,subprocess
P=Path(__file__).resolve().parent

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('new_out_dir',type=Path);ap.add_argument('public_rows_json',type=Path)
 a=ap.parse_args();out=a.new_out_dir.resolve();rows=a.public_rows_json.resolve()
 if out.exists():ap.error('output directory must be new')
 if not rows.is_file():ap.error('public rows must exist')
 pins=json.loads((P/'SOURCE_PINS.json').read_text())
 for name,digest in pins['files'].items():
  if sha(P/name)!=digest:raise SystemExit('selected native producer file changed: '+name)
 for name,digest in pins['frozen_query_sources'].items():
  if sha(Path(name))!=digest:raise SystemExit('frozen query source changed: '+name)
 cmd=[str(P/'native/target/release/lean-query-witness'),str(P/'program/witness_plan.json'),str(P/'program/template_ir2.json'),str(rows),str(out)]
 raise SystemExit(subprocess.run(cmd).returncode)
if __name__=='__main__':main()
