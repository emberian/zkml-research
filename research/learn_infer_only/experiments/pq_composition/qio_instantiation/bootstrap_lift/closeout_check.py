#!/usr/bin/env python3
"""Verify frozen proof/review provenance and closeout links, without replaying others' tools."""
import hashlib
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent
REVIEW=HERE.parents[2]/'adversarial_review'/'pq_bootstrap'


def main():
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    expected={
        HERE/'BOOTSTRAP_LIFT.md':'ec9f721f2402d31a49a9fd4ee14f978b4cf7474429600710347dc555fe0d9792',
        HERE/'POINTWISE_CORRECTNESS.md':'c63e299a31a33617888814d5b4f371cf0f1e25541b4ebaa061e9bc84340d81f2',
        HERE.parent/'INSTANTIATION.md':'163ebdcc5e376441b4a146b6964aba60002c3c55952cfb1e17d0c363478109fd',
        REVIEW/'REPORT.md':'7809d588814e987b5bc05a165f681601229bcdc098b75c7508255ad4898642e7',
        REVIEW/'results.json':'64d819f1970cd96b261a16b5923525e380f3ec390e2c7c8a02fb321304acc7ea',
        REVIEW/'review_manifest.json':'d5901811297c56475327856855c98c63eb027fbd3f51c33c04e4f8e59f964298',
        HERE.parent.parent/'base_fe_audit'/'BASE_FE_AUDIT.md':'3e49e259abbe3ca72da5528b96ca8080b96a3589a442e6b3a38ea66841c60d2d',
    }
    for path,digest in expected.items():
        assert sha(path)==digest,(str(path),sha(path),digest)
    results=json.loads((REVIEW/'results.json').read_text())
    assert results['all_review_inputs_unchanged']
    for path,digest in results['input_hashes_after'].items():
        assert sha(Path(path))==digest,path
    closeout=HERE/'CLOSEOUT.md'
    prose=re.sub(r'```.*?```','',closeout.read_text(),flags=re.S)
    prose=re.sub(r'`[^`]*`','',prose)
    links=[x for x in re.findall(r'\]\(([^)]+)\)',prose) if not x.startswith('https://')]
    assert all((HERE/x).is_file() for x in links),links
    result={'label':'EXECUTED','scope':__doc__,'closeout_sha256':sha(closeout),
            'script_sha256':sha(Path(__file__)),
            'frozen_proof_source_and_review_files_checked':len(expected),
            'review_input_hashes_rechecked':len(results['input_hashes_after']),
            'closeout_local_links_checked':len(links),
            'expected_hashes':{str(p):h for p,h in expected.items()},
            'additional_queries':0,'external_or_frozen_writes':0}
    (HERE/'closeout_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
