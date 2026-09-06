#!/usr/bin/env python3
"""Pin actual Lean axiom reports across the four source-word namespaces."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent;mods=['FheShoupWord','FheBarrettWord','FheRnsModularAccumulation','FheRnsSourceWord'];reports=[]
for p in sorted(ROOT.glob('build-*.json')):
 for item in json.loads(p.read_text()):
  if item['exit_code']==0 and item['command'][-1].endswith('/FheModularAxiomReport.lean'):reports.append(item)
assert reports
messages=re.findall(r"'Minidregg\.Compiler\.\w+\.\w+' (?:does not depend on any axioms|depends on axioms: \[[^\]]*\])",reports[-1]['stdout']);assert len(messages)==38
pins={m.split("'")[1]:m for m in messages};(ROOT/'axiom-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
for mod in mods:
 p=ROOT/'Compiler'/f'{mod}.lean';s=p.read_text().split('\n-- AXIOM PINS')[0].rstrip()+'\n';names=re.findall(r'^theorem (\w+)',s,re.M);s+='\n-- AXIOM PINS: actual checked print output.\n'
 for name in names:
  fq='Minidregg.Compiler.'+mod+'.'+name;s+='\n/-- info: '+pins[fq]+' -/\n#guard_msgs in\n#print axioms '+fq+'\n'
 p.write_text(s)
print('Pinned 38 declarations across four source-word modules.')
