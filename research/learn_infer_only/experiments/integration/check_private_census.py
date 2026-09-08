#!/usr/bin/env python3
"""Check private-name census against exact full-UD source and corruptions."""
import hashlib
import json
from pathlib import Path
import check_all_formal as checker

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[2] / 'proof_frontier/2026-09-08/formal/full_ud/src/Selvage/FullUDTeeth.lean'
text = SOURCE.read_text()
module = 'Selvage.FullUDTeeth'
result = checker.census(text, module)
assert result['theorem_count'] == result['pin_count'] == 6
assert sum(d['private'] for d in result['qualified_declarations']) == 3
controls = []
for label, changed, target in [
    ('wrong module identity', text, 'Selvage.WrongModule'),
    ('public declaration with private print', text.replace('private theorem affine_mem', 'theorem affine_mem'), module),
    ('private declaration with public print', text.replace('_private.Selvage.FullUDTeeth.0.Minidregg.Selvage.FullUDTeeth.affine_mem', 'Minidregg.Selvage.FullUDTeeth.affine_mem'), module),
    ('unrelated declaration name', text.replace("FullUDTeeth.affine_mem'", "FullUDTeeth.unrelated'"), module),
    ('missing private guard', text.replace('#print axioms affine_mem', '#check affine_mem'), module),
]:
    try:
        checker.census(changed, target)
    except ValueError as exc:
        controls.append(dict(label=label, refused=True, reason=str(exc)))
    else:
        raise AssertionError(label)
print(json.dumps(dict(scope='Lexical census regression; exact Lean guards remain independently compiled.',
    source=str(SOURCE), source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    checker_sha256=hashlib.sha256(Path(checker.__file__).read_bytes()).hexdigest(),
    positive_pins=result['pin_count'], private_pins=3, negative_controls=controls), indent=2))
