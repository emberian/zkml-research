"""Summarize a completed one-attempt run from public evidence; no private read."""
import csv,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_bytes())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 reports=ROOT/'reports/run001';run=load(ROOT/'run.command.json');result=load(reports/'report.json')
 phase=load(reports/'public_phase.json');verification=load(reports/'public_verification.json');validation=load(reports/'validation.json')
 assert run['returncode']==0 and result['ok'] and verification['ok'] and validation['ok']
 assert run['source_snapshot_and_model_bytes_unchanged']
 assert len(run['phases'])==4 and all(p['returncode']==0 and p['process_group_absent'] for p in run['phases'])
 with (ROOT/'costs.csv').open('w') as f:
  writer=csv.writer(f);writer.writerow(['component','unit','value','source','scope'])
  for p in run['phases']:writer.writerow([p['phase'],'seconds',p['wall_ns']/1e9,'run.command.json','sequential phase subprocess wall; outer hash checks excluded'])
  writer.writerow(['total','seconds',run['wall_ns']/1e9,'run.command.json','outer wall includes source/model hashes; overlaps phase intervals'])
  for k in ['children_user_cpu_seconds','children_system_cpu_seconds','maximum_child_rss_bytes_macos']:
   writer.writerow([k,'bytes' if 'rss' in k else 'seconds',run[k],'run.command.json','child resource usage; peak is not summed resident memory'])
  for k,v in result['model_cost'].items():
   if isinstance(v,(int,float)):writer.writerow(['model:'+k,'count' if k=='model_parameter_count' else 'seconds',v,'reports/run001/report.json','actual source-model telemetry; overlapping intervals'])
 changed=str(result['output_changed_after_learning']).lower()
 lines=[
  '# One fresh semantic text through deferred verified BFV receipt',
  '',
  '[EXECUTED] The single frozen attempt completed one actual SmolLM3-3B model forward on two semantic-axis prompts, then one signed BFV Learn and two Infer events. Both durable received answers match the private direct integer references. This is one illustration, not a new utility estimate.',
  '',
  f'[EXECUTED] Output changed after Learn: **{changed}**. The query was fixed as q01 before tokenization and scoring; no result-dependent choice or repeat occurred. Under the fixed +1/127 one-hot mapping, this disclosed boolean determines whether the selected after-score is 0 or 16129. No selected-score confidentiality is claimed.',
  '',
  '[EXECUTED] The authority finalized all three events. The network verifier independently recomputed and durably stored each transition without decrypting. All host, authority, baseline-reader and verifier services closed before a separate keyless process recomputed all three events in an independent CAS and checked the actual durable public tables and stored bytes. Both registered Infer receipts remained pending throughout that public phase, with zero received answers and zero reader-decrypt calls.',
  '',
  '[EXECUTED] The passing public-verification artifact, exact phase hash and envelope hash gated a separate offline private process. It invoked the unchanged VerifiedReader.receive twice against the already registered and verified envelopes, then checked the saved raw logits/tie decisions, one-hot vector and direct integer dot product. Two verifying-reader decryptions and zero baseline decryptions are recorded. The authority stayed closed and its delivery outbox remains unacknowledged; the result is durable verified offline receipt.',
  '',
  f'[EXECUTED] Outer pipeline wall time was {run["wall_ns"]/1e9:.3f}s; the public driver including setup/model work took {phase["public_phase_wall_ns"]/1e9:.3f}s. Costs are in costs.csv and phase_commands.json. Intervals overlap where noted, machine load is shared, and this is not a cross-fixture speedup claim.',
  '',
  '[EXECUTED] Sources, model files, fixed query rows and parent manifests match their pins. The original live draft and initial successor source freeze remain preserved; source_revision.json records only prelaunch source/audit corrections with the same private text and prompts. One tokenizer/hash preparation, zero generated tokens, zero weight updates and no scoring retry were used.',
  '',
  '[EXECUTED] Read CONTRACT.md, freeze.json, reports/run001/public_phase.json, public_verification.json, report.json and validation.json for exact premises, commands and role boundaries. The private report and raw model outputs remain in ignored runtime. Public artifacts omit selected-feature binding fields; possible one-hot rows and hashes already belong to the public query dictionary.',
  '',
  '[OPEN] The semantic issuer is trusted and sees plaintext. The network verifier loads the full BFV reader secret during its public phase even though it performs no decryption then; the later independent public verifier is keyless. The full key remains after receipt. Public routing, four effective bins per route, same-account process/file boundaries and classical role signatures remain. There is no no-master-read, encrypted 3B cognition, OS-isolation, exactly-once physical delivery or end-to-end post-quantum claim.',
  '',
  '[EXECUTED] This seam made no web/Scry calls and ran no previously stopped task. Root owns shared ledgers and commits.',
  '']
 (ROOT/'REPORT.md').write_text('\n'.join(lines))
 (ROOT/'STATUS.md').write_text('[EXECUTED] The one frozen live-text attempt completed: one actual two-axis model forward, one Learn/two Infer, all three independent public transitions and durable storage checks, service shutdown before the gated two private decryptions, and both exact integer matches. Sources/model/query/parents remain pinned. See REPORT.md.\n\n[OPEN] Independent final public-evidence review and root collection remain; full-key/plaintext-issuer and output-boolean disclosure limits are explicit.\n')
 (ROOT/'NEXT.md').write_text('[OPEN] Complete independent final public-evidence review and seal the owned artifact manifest for root collection. Do not rerun the model or BFV workload. Authority outbox remains pending by design; do not describe offline receipt as acknowledged authority delivery. No new utility denominator or no-master-read claim.\n')
 print(json.dumps({'ok':True,'report_sha256':sha(ROOT/'REPORT.md'),'output_changed_after_learning':result['output_changed_after_learning']}))
if __name__=='__main__':main()
