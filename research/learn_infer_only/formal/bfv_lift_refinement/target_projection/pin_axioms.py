#!/usr/bin/env python3
"""Pin actual printed axiom reports; never invent the expected axiom list."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
mods=['FheTargetProjection','FheTargetProjectionLayout','FheTargetProjectionEmit','FheTargetProjectionVerifier','FheTargetProjectionWitness']
reports=[]
for p in ROOT.glob('build-*.json'):
 for item in json.loads(p.read_text()):
  if item['exit_code']==0 and item['command'][-1].endswith('/FheTargetProjectionAxiomReport.lean'):reports.append(item)
assert reports
messages=re.findall(r"'Minidregg\.Compiler\.FheTargetProjection\.\w+' (?:does not depend on any axioms|depends on axioms: \[[^\]]*\])",reports[-1]['stdout'])
assert len(messages)==22
pins={m.split("'")[1].rsplit('.',1)[1]:m for m in messages}
(ROOT/'axiom-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
for mod in mods:
 p=ROOT/'Compiler'/f'{mod}.lean';s=p.read_text().split('\n-- AXIOM PINS')[0].rstrip()+'\n';names=re.findall(r'^theorem (\w+)',s,re.M)
 s+='\n-- AXIOM PINS: actual checked print output.\n'
 for name in names:s+='\n/-- info: '+pins[name]+' -/\n#guard_msgs in\n#print axioms Minidregg.Compiler.FheTargetProjection.'+name+'\n'
 p.write_text(s)
print('Pinned22 declarations across5 library modules.')
