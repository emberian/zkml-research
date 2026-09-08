"""Copy one completed public fixture for the standalone verifier; no proving."""
import argparse
import hashlib
import json
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('template',type=Path)
parser.add_argument('case',type=Path)
parser.add_argument('proof',type=Path)
parser.add_argument('output',type=Path)
parser.add_argument('--rows',type=Path,help='Explicit public row export (default CASE/public_rows.json)')
args=parser.parse_args()
sources={'template.json':args.template,'public_rows.json':args.rows or args.case/'public_rows.json','proof.bin':args.proof}
args.output.mkdir(parents=True,exist_ok=False)
files={}
for name,path in sources.items():
    assert 'private' not in path.resolve().parts
    data=path.read_bytes()
    (args.output/name).write_bytes(data)
    files[name]={'source':str(path.resolve()),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
manifest={'claim':'SOURCE public proof/input transport fixture; acceptance must come from the verifier',
  'backend':'FixedPublicPreprocessing (shared proved_operation/backend adapter)','public_table_id':11,'files':files,
  'scope':'Exact public coefficient rows under the supplied application-approved Lean template. Ciphertext decoding/provenance and learner authorization are outside this browser wrapper.'}
(args.output/'fixture.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest,indent=2))
