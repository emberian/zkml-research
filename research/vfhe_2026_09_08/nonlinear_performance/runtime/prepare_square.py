#!/usr/bin/env python3
"""Apply the shared source-preserving whole-row migration to saved square profiles."""
from pathlib import Path
import json
import os
import sys
from common import ROOT, command, save, sha

BASE = ROOT.parent.parent
REPAIR = BASE.parent / 'proof_frontier/2026-09-08/ir2_verifier_bridge/air_pcs_join/whole_domain/repair_template.py'


def main():
    out = ROOT.parent / 'templates'
    out.mkdir()
    baseline = json.loads((BASE / 'proved_journal/live_nonlinear/PIPELINE.json').read_text())
    result = {'migration': str(REPAIR), 'migration_sha256': sha(REPAIR), 'profiles': {}}
    for kind in ('extension', 'tensor', 'rescale'):
        result['profiles'][kind] = []
        for index, old in enumerate(baseline['profiles'][kind]):
            dest = out / kind / str(index) / 'template_ir2.json'
            command(out, f'{kind}{index:02}', [sys.executable, REPAIR, old['template'], dest], 120, os.environ.copy())
            profile = dict(old, template=str(dest), template_sha256=sha(dest))
            record = json.loads(dest.with_suffix('.json.repair.json').read_text())
            assert record['source_sha256'] == old['template_sha256']
            assert record['normalized_polynomial_bodies_equal'] and record['all_other_constraints_and_metadata_equal']
            profile['source_template'] = old['template']
            profile['source_template_sha256'] = old['template_sha256']
            profile['whole_row_migration'] = str(dest.with_suffix('.json.repair.json'))
            result['profiles'][kind].append(profile)
    save(out / 'PROFILES.json', result)
    print(json.dumps({'profiles': sum(map(len, result['profiles'].values())), 'manifest': str(out / 'PROFILES.json')}, indent=2))


if __name__ == '__main__':
    main()
