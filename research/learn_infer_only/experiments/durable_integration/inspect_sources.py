#!/usr/bin/env python3
"""Supplement kernel pins with a source census and a red-tested token scan."""
from pathlib import Path
import hashlib, json, re, sys

root = Path(__file__).resolve().parents[2]
base = root/'formal/durable_integration/Assurance'
slash = chr(92)
pattern = slash+'b(sorry|admit)'+slash+'b|^axiom'+slash+'s'
controls = {x: bool(re.search(pattern, x, re.M))
            for x in ['sorry', 'admit', 'axiom bogus : False']}
assert all(controls.values())
result = dict(command=[sys.executable, str(Path(__file__).resolve())],
              theorem_pattern='^theorem ', pin_pattern='^#guard_msgs',
              forbidden_pattern=pattern, forbidden_positive_controls=controls, files=[])
for path in sorted(base.glob('*.lean')):
    source = path.read_text()
    theorems = len(re.findall(result['theorem_pattern'], source, re.M))
    pins = len(re.findall(result['pin_pattern'], source, re.M))
    forbidden = re.findall(pattern, source, re.M)
    result['files'].append(dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                                theorems=theorems, pins=pins, forbidden_matches=forbidden))
    assert theorems == pins and not forbidden
(Path(__file__).parent/'results/source_inventory.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
