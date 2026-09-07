#!/usr/bin/env python3
"""Regression controls for the imported-admission-identifier census defect."""
from pathlib import Path
import hashlib
import json
import check_all_formal as checker

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / 'formal/durable_integration/window_frame/Assurance/CiphertextWindowFrameWitness.lean'
source = SOURCE.read_text()
good = checker.census(source)
assert good['pin_count'] == 14 and good['admit_identifier_tokens']
assert not good['forbidden_constructs']

def rejected(label, changed):
    assert changed != source
    try:
        checker.census(changed)
    except ValueError as exc:
        return {'label': label, 'refused': True, 'reason': str(exc)}
    raise AssertionError(f'census accepted {label}')

controls = [
    rejected('proof placeholder tactic', source.replace('by decide +kernel', 'by admit', 1)),
    rejected('sorry proof placeholder', source.replace('by decide +kernel', 'by sorry', 1)),
    rejected('untrusted native proof shortcut', source.replace('by decide +kernel', 'by native_decide', 1)),
    rejected('unguarded axiom print', source + '\n#print axioms mixed_subject\n'),
    rejected('missing theorem axiom guard', source.replace('#guard_msgs in #print axioms classifications', '-- removed guard', 1)),
]
result = {
    'scope': 'Lexical regression controls; the integration separately elaborates every exact axiom guard in Lean.',
    'source': str(SOURCE),
    'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    'checker_sha256': hashlib.sha256(Path(checker.__file__).read_bytes()).hexdigest(),
    'imported_admission_identifier_accepted': True,
    'positive_pins': good['pin_count'],
    'negative_controls': controls,
}
print(json.dumps(result, indent=2))
