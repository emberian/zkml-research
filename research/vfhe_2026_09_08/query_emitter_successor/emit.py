#!/usr/bin/env python3
"""Opt-in cached producer, with the frozen query template and new output only."""
from pathlib import Path
import argparse,hashlib,json,subprocess
P=Path(__file__).resolve().parent
FROZEN=P.parent/'query_arithmetic'

def main():
 ap=argparse.ArgumentParser()
 ap.add_argument('out_dir',type=Path)
 ap.add_argument('public_rows_json',type=Path)
 args=ap.parse_args()
 out=args.out_dir.resolve();rows=args.public_rows_json.resolve()
 if out.exists():ap.error('out_dir must be new; existing outputs are preserved')
 if not rows.is_file():ap.error('public_rows_json must exist')
 pins=json.loads((FROZEN/'source_pins.json').read_text())
 for name,digest in pins['sources'].items():
  if hashlib.sha256((FROZEN/name).read_bytes()).hexdigest()!=digest:
   raise SystemExit('frozen query source changed: '+name)
 own=json.loads((P/'SOURCE_PINS.json').read_text())
 for name,digest in own['sources'].items():
  if hashlib.sha256((P/name).read_bytes()).hexdigest()!=digest:
   raise SystemExit('successor source changed: '+name)
 if not (P/'build/Compiler/BfvQueryWitnessFast.olean').exists():
  raise SystemExit('run the documented one-module build before emission')
 cmd=['lake','env','bash','-c','LEAN_PATH="$1/build:$LEAN_PATH" lean --root="$1" --run "$1/EmitBfvQueryFast.lean" "$2" "$3"','emit',str(P),str(out),str(rows)]
 raise SystemExit(subprocess.run(cmd,cwd='/Users/ember/dev/minidregg').returncode)

if __name__=='__main__':main()
