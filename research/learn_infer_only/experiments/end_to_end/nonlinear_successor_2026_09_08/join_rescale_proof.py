"""Read-only hash and exact-digit join to the other lane's completed proof."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
OWNER=REPO/'research/vfhe_2026_09_08/proved_rescale_generic'
FORMAL=REPO/'research/vfhe_2026_09_08/arithmetic_rescale_generic'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def main():
 trace=read(HERE/'public_trace/basic.json');case=OWNER/'results/case001';operation=read(case/'operation.json');selection=read(case/'selection.json');rows=read(case/'public_rows.json');proof=read(OWNER/'results/proof001/proof.json');verify=read(OWNER/'results/verify001.stdout');reject=read(OWNER/'results/reject001.stdout')
 assert operation['source_descriptor_sha256']==sha(HERE/'public_trace/descriptor.json')
 assert operation['source_trace_sha256']==sha(HERE/'public_trace/basic.json')
 assert (case/'basic.json').read_bytes()==(HERE/'public_trace/basic.json').read_bytes()
 assert (case/'basic-000.ct').read_bytes()==(HERE/'public_trace/basic-000.ct').read_bytes()
 assert (case/'basic.dot.ct').read_bytes()==(HERE/'public_trace/basic.dot.ct').read_bytes()
 assert len(selection)==len(rows)==32 and len({(x['component'],x['coefficient']) for x in selection})==32
 matched=0
 for row_id,(position,row) in enumerate(zip(selection,rows)):
  assert len(row)==88 and row[0]==row_id
  expected=[row_id];c=position['component'];i=position['coefficient']
  for name,limbs,digits in [('product_extended_power_basis',9,7),('output_power_basis',4,6)]:
   for limb in range(limbs):
    value=trace[name][c][limb][i];ds=[(value>>(9*d))&511 for d in range(digits)];assert sum(v<<(9*d) for d,v in enumerate(ds))==value
    expected.extend(ds);matched+=1
  assert row==expected
 assert proof['verified'] and verify['verified'] and not reject['verified'] and reject['changed_output_rejected']
 assert all(read(OWNER/f'results/{name}.command.json')['returncode']==0 for name in ['prove001','verify001','reject001'])
 assert sha(OWNER/'results/proof001/proof.bin')==proof['proof_sha256']==verify['proof_sha256']==reject['proof_sha256']
 assert sha(FORMAL/'artifacts/template_ir2.json')==proof['template_sha256']
 paths=[HERE/'REPORT.md',HERE/'RESULT.json',HERE/'public_trace/descriptor.json',HERE/'public_trace/basic.json',HERE/'public_trace/basic-000.ct',HERE/'public_trace/native_scaler_constants.json',case/'operation.json',case/'public_rows.json',case/'selection.json',OWNER/'results/proof001/proof.json',OWNER/'results/proof001/proof.bin',OWNER/'results/verify001.stdout',OWNER/'results/reject001.stdout',OWNER/'results/prove001.command.json',OWNER/'results/verify001.command.json',OWNER/'results/reject001.command.json',FORMAL/'artifacts/template_ir2.json',FORMAL/'artifacts/emission.json']
 result={'status':'saved proof joined by independent public hash/digit checks; no proof rerun, FHE or private reads','selected_positions':32,'total_positions':24576,'exact_joined_residues':matched,'output_residue_equations':128,'fresh_verification_record_passed':True,'changed_output_record_rejected':True,'proof_bytes':proof['proof_bytes'],'proof_seconds':proof['prove_ns']/1e9,'fresh_verify_seconds':verify['verify_ns']/1e9,'owner_runtime_raw_ciphertext_residue_checks':operation['all_captured_output_coefficients_checked_against_raw_ciphertext'],'owner_runtime_check_attribution':'Saved exporter operation.json; this join independently checked complete ciphertext-copy bytes and selected tuple/trace residues, not the NTT inverse implementation','scope':'32 selected exact native directed9-to4 rescale positions; no whole ciphertext square, extension, convolution, rotations, encoder or FIFO proof','sha256':{str(p.relative_to(REPO)):sha(p) for p in paths}}
 (HERE/'RESCALE_PROOF_JOIN.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
if __name__=='__main__':main()
