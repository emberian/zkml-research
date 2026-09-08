"""Copy the completed public statement/proof; no new prover or private reads."""
import hashlib
import json
from pathlib import Path

here=Path(__file__).resolve().parent
source=here.parent/'new_constructions/scaled'
inventory=json.loads((source/'public_artifacts.json').read_text())
dest=here/'fixtures/matvec4096'
dest.mkdir(parents=True,exist_ok=False)
files={}
for name,original in [('statement.bin','paired_001/statement.bin'),('proof.bin','paired_001/fused.proof')]:
    data=(source/original).read_bytes()
    row={'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
    assert row==inventory[original], original
    (dest/name).write_bytes(data)
    files[name]={**row,'source':str(source/original)}
manifest={'claim':'SOURCE exact completed public ring-matvec bundle; acceptance must come from the verifier',
  'degree':4096,'matrix_rows':64,'matrix_columns':8192,'files':files,
  'source_revision':'matvecmul 00379074cad457367a86dde2ecee9d0f318a7e12 plus combined-matvec.patch',
  'source_patch_sha256':hashlib.sha256((source/'combined-matvec.patch').read_bytes()).hexdigest(),
  'scope':'Complete existing verifier with all three PCS openings, public caller matrix/input/expected output. WHIR ConjectureList; configured level100 is not certified security bits.'}
(dest/'fixture.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest,indent=2))

