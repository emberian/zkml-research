"""Final public metadata/cost packaging; no model, crypto, or private-file read."""
import collections,gzip,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_bytes())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
def main():
 reports=ROOT/'reports/run001';run=load(ROOT/'run.command.json');start=load(ROOT/'run_started.json')
 assert run['returncode']==0
 summary=collections.defaultdict(lambda:{'count':0,'sum_ns':0});rows=[];pins={}
 files=['commands.jsonl.gz','verified_commands.jsonl.gz','independent_public_commands.jsonl','private_receive_commands.jsonl.gz']
 for name in files:
  p=reports/name;pins[name]=sha(p);raw=gzip.decompress(p.read_bytes()) if name.endswith('.gz') else p.read_bytes()
  for line in raw.splitlines():
   row=json.loads(line);assert row['exit_code']==0
   key=name+':'+row['role']+':'+row['command'][1];summary[key]['count']+=1;summary[key]['sum_ns']+=row['elapsed_ns']
   rows.append((name,row))
 public=[r for name,r in rows if name!='private_receive_commands.jsonl.gz']
 private=[r for name,r in rows if name=='private_receive_commands.jsonl.gz']
 assert len(public)==52 and all(r['command'][1]!='reader-decrypt' for r in public)
 assert len(private)==4 and sum(r['command'][1]=='reader-decrypt' for r in private)==2
 dump(ROOT/'crypto_costs.json',{'public_cli_rows':len(public),'public_decryptions':0,
      'later_private_receive_cli_rows':len(private),'later_decryptions':2,'by_component_role_command':dict(summary),
      'log_sha256':pins,'scope':'Actual logged subprocess intervals; overlap outer/model timing and persistent-worker meters.'})
 coordination={'actual_live_start_utc':start['started_utc'],'live_outer_wall_ns':run['wall_ns'],
               'live_start_source':'run_started.json','live_wall_source':'run.command.json',
               'TFHE_window_signal_utc_reported_by_worker':'2026-09-08T05:56:13.59Z',
               'TFHE_first_infer_block_closed_utc_reported_by_worker':'2026-09-08T05:56:47Z',
               'worker_reports_source':'collaboration messages from /root/emitted_runtime in this authorized run',
               'scope':'Dispatched on the actual Infer-window signal, but recorded start was after that block closed. Subsequent Learn overlap was explicitly accepted by the worker; no TFHE pause or delay was requested.'}
 dump(ROOT/'coordination.json',coordination)
 report=(ROOT/'REPORT.md').read_text()
 report=report.replace('one actual SmolLM3-3B model forward on two semantic-axis prompts, then one signed BFV Learn and two Infer events.',
                       'one actual SmolLM3-3B model forward on two semantic-axis prompts within the fixed Infer(q01), model-plus-Learn, Infer(q01) sequence.')
 report+='\n[EXECUTED/REPORTED timing scope] The recorded live start is 05:56:48 UTC. The TFHE worker reported its first Infer block closed at 05:56:47 UTC, so the attempt overlapped subsequent Learn work despite dispatch on its earlier window signal. The worker explicitly accepted that overlap; no pause was requested. coordination.json preserves both attributions.\n'
 report+='\n[EXECUTED independent public check] The separate reviewer checked the three-event hash/state chain, fixed q01, 33 stored public CAS blobs, all 52 retained public CLI rows with zero decryptions, and four later receive rows with exactly two redacted decryptions. The source/model/phase gate bindings agree. Private integer matches, model-forward result and output-change remain attributed to the author execution, not a second private audit. See ../../../../../adversarial_review/live_semantic_bfv/REPORT.md.\n'
 (ROOT/'REPORT.md').write_text(report)
 (ROOT/'STATUS.md').write_text('[EXECUTED] Complete: one frozen actual model forward (two axes), one Learn/two Infer, three public/verified transitions, service closure and independent keyless replay/storage checks before two private decryptions, both exact integer matches, and final independent public-evidence check. The selected output changed; its disclosure is explicit. Source/model/query/parent pins hold. See REPORT.md and manifest.json.\n\n[OPEN] Root owns collection and independent-review final seal. Full key, plaintext issuer, four bins per public route, same-account roles and pending authority outbox remain; this is no new utility estimate or no-master-read result.\n')
 (ROOT/'NEXT.md').write_text('[OPEN] Root may collect this completed one-attempt result and the independent review under experiments/adversarial_review/live_semantic_bfv/. Preserve the original draft, both prelaunch source revisions and all ignored runtime. Do not rerun model/BFV or acknowledge the intentionally pending authority outbox within this frozen result. Private correctness is author-executed; independent review checks source and public evidence only.\n')
 print(json.dumps({'ok':True,'public_cli_rows':len(public),'later_decryptions':2,'report_sha256':sha(ROOT/'REPORT.md'),
                   'coordination_sha256':sha(ROOT/'coordination.json')}))
if __name__=='__main__':main()
