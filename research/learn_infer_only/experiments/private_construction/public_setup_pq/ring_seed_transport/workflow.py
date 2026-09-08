#!/usr/bin/env python3
"""Run each actual actor command in a fresh macOS sandboxed process.

The orchestrator never opens recipient key/output payloads. It reads public
receipts and public artifacts only; private directories are mode0700.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import datetime

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'ring_transport'
sys.path.insert(0,str(BASE))
from transport import params,fixture,SparseBasis,Container,digest


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--profile',choices=['toy','candidate_full'],required=True)
    ap.add_argument('--run',required=True)
    a=ap.parse_args(); p=params(a.profile)
    rt=HERE/'.runtime'/a.run; public=rt/'public'; private=rt/'private'; results=HERE/'results'/a.run
    if rt.exists() or results.exists():raise ValueError('run name already exists; refusing to reuse artifacts')
    public.mkdir(parents=True); private.mkdir(mode=0o700); results.mkdir(parents=True)
    os.chmod(private,0o700)
    recipients=[]
    for i in range(p.recipients):
        folder=private/f'recipient_{i:02d}'; folder.mkdir(mode=0o700); os.chmod(folder,0o700); recipients.append(folder)
    roleprofiles={}
    for role in ['public']+[f'recipient_{i:02d}' for i in range(p.recipients)]:
        denied=[private] if role=='public' else [folder for folder in recipients if folder.name!=role]
        profile='(version 1)\n(allow default)\n(deny network*)\n'
        for folder in denied:profile+='(deny file-read* file-write* (subpath '+json.dumps(str(folder))+'))\n'
        path=results/f'{role}.sb'; path.write_text(profile); roleprofiles[role]=path
    # One cheap OS policy probe uses public canary bytes, never a secret key.
    canary=recipients[1]/'public_canary.txt'; canary.write_text('public test string\n'); os.chmod(canary,0o600)
    probe=[]
    for role in ['public','recipient_00']:
        command=['/usr/bin/sandbox-exec','-f',str(roleprofiles[role]),sys.executable,'-c',
                 'import sys; open(sys.argv[1],"rb").read()',str(canary)]
        run=subprocess.run(command,capture_output=True,text=True)
        probe.append({'role':role,'argv':command,'returncode':run.returncode,'stderr':run.stderr,'stdout':run.stdout})
        if run.returncode==0:raise RuntimeError('OS private-path denial probe unexpectedly succeeded')
    (results/'process_policy_probe.json').write_text(json.dumps(probe,indent=2)+'\n')
    commands=[]; start=time.perf_counter(); started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    sources=[HERE/'seed_transport.py',HERE/'workflow.py',HERE/'expansion/public_expander.py',BASE/'transport.py']
    before={str(path):digest(path) for path in sources}

    def actor(label,role,args):
        receipt=results/(label+'.json')
        command=['/usr/bin/sandbox-exec','-f',str(roleprofiles[role]),sys.executable,'-B',str(HERE/'seed_transport.py' if args[0] in ('init','register','finalize','encode') else BASE/'transport.py'),
                 '--receipt',str(receipt),*map(str,args)]
        began=time.perf_counter()
        run=subprocess.run(command,capture_output=True,text=True,cwd=public)
        wall=time.perf_counter()-began
        (results/(label+'.stdout.log')).write_text(run.stdout)
        (results/(label+'.stderr.log')).write_text(run.stderr)
        row={'label':label,'role':role,'argv':command,'returncode':run.returncode,'wall_seconds':wall,'receipt':str(receipt)}
        commands.append(row)
        if run.returncode:raise RuntimeError(f'actor {label} failed: {run.stderr} {run.stdout}')
        d=json.loads(receipt.read_text())
        if d['status']!='PASS':raise RuntimeError(f'actor {label} failed')
        private_reads=[x for x in d['artifact_reads'] if x['private']]
        if role=='public' and private_reads:raise RuntimeError('public actor read private artifact')
        if role!='public' and any(not Path(x['path']).is_relative_to(private/role) for x in private_reads):
            raise RuntimeError('recipient read another recipient artifact')
        print(json.dumps({'event':label,'role':role,'seconds':wall,'status':'PASS'}),flush=True)
        return d

    try:
        actor('init','public',['init','--profile',a.profile,'--out',public/'a.json'])
        for i in range(p.recipients):
            actor(f'register_{i:02d}',f'recipient_{i:02d}',[
                'register','--public-a',public/'a.json','--coordinate',i,
                '--key-out',recipients[i]/'key.ring','--registration-out',public/f'registration_{i:02d}.ring'])
        finalargs=['finalize','--public-a',public/'a.json','--registry-out',public/'registry.ring','--out',public/'public.json']
        for i in range(p.recipients):finalargs+=['--registration',public/f'registration_{i:02d}.ring']
        actor('finalize','public',finalargs)
        basis=SparseBasis(p.d,p.recipients,p.p); lifts=[]
        for step in range(3):
            x=fixture(p,step); lifts.append(basis.transform(x))
            ip=public/f'input_{step}.json'; ip.write_text(json.dumps(x)+'\n')
            actor(f'encode_{step}','public',['encode','--public',public/'public.json','--registry',public/'registry.ring','--input',ip,'--out',public/f'cipher_{step}.ring'])
        actor('signed','public',['combine','--term',2,public/'cipher_0.ring','--term',-1,public/'cipher_1.ring','--out',public/'signed.ring'])
        actor('window_0','public',['window','--add',public/'cipher_0.ring','--capacity',2,'--out',public/'window_0.ring'])
        actor('window_1','public',['window','--state',public/'window_0.ring','--add',public/'cipher_1.ring','--capacity',2,'--out',public/'window_1.ring'])
        actor('window_expiry','public',['window','--state',public/'window_1.ring','--add',public/'cipher_2.ring','--expire',public/'cipher_0.ring','--capacity',2,'--out',public/'window_2.ring'])
        # All recipients independently load only their own private key and read
        # the final expired window. Recipient0 additionally reads fresh/signed.
        for i in range(p.recipients):
            actor(f'decode_window_{i:02d}',f'recipient_{i:02d}',[
                'decode','--key',recipients[i]/'key.ring','--ciphertext',public/'window_2.ring',
                '--expected-lift',lifts[1][i]+lifts[2][i],'--out',recipients[i]/'window_output.json'])
        for step in range(3):
            actor(f'decode_fresh_{step}','recipient_00',['decode','--key',recipients[0]/'key.ring',
                '--ciphertext',public/f'cipher_{step}.ring','--expected-lift',lifts[step][0],
                '--out',recipients[0]/f'fresh_output_{step}.json'])
        actor('decode_signed','recipient_00',['decode','--key',recipients[0]/'key.ring','--ciphertext',public/'signed.ring',
            '--expected-lift',2*lifts[0][0]-lifts[1][0],'--out',recipients[0]/'signed_output.json'])
        # Cheap malformed-length check on a small public registration artifact.
        small=public/'registration_00.ring'; malformed=public/'malformed.ring'
        malformed.write_bytes(small.read_bytes()+b'\x00')
        rejected=False
        try:Container(malformed,'registration')
        except ValueError:rejected=True
        if not rejected:raise RuntimeError('trailing byte was accepted')
        public_artifacts={str(path):{'bytes':path.stat().st_size,'sha256':digest(path)} for path in sorted(public.iterdir()) if path.is_file()}
        # Private metadata only; no private file is opened by this orchestrator.
        private_metadata=[{'recipient':i,'path':str(folder/'key.ring'),'bytes':(folder/'key.ring').stat().st_size,
                          'mode':oct((folder/'key.ring').stat().st_mode & 0o777)} for i,folder in enumerate(recipients)]
        result={'status':'PASS','started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
                'elapsed_seconds':time.perf_counter()-start,'profile':a.profile,'parameters':p.__dict__,
                'commands':commands,'public_artifacts':public_artifacts,'private_metadata_only':private_metadata,
                'actual_recipient_rows_generated':p.recipients,'absent_recipient_rows_generated':0,
                'fresh_encodes':3,'designated_outputs_matched':p.recipients+4,'malformed_trailing_byte_rejected':True,
                'process_policy_denial_probes':2,'public_roles_private_artifact_reads':0,
                'source_sha256':before,'sources_unchanged':all(digest(Path(path))==h for path,h in before.items()),
                'orchestrator_private_payload_reads':0,'security_scope':'Conditional public-XOF instantiation, not ideal-uniform equivalence; saved artifact sandbox excludes host administration and escapes'}
    except Exception as exc:
        result={'status':'FAIL','error':f'{type(exc).__name__}: {exc}','commands':commands,'elapsed_seconds':time.perf_counter()-start}
    (results/'WORKFLOW.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'elapsed_seconds':result['elapsed_seconds'],'report':str(results/'WORKFLOW.json')}),flush=True)
    return 0 if result['status']=='PASS' and result['sources_unchanged'] else 1


if __name__=='__main__':raise SystemExit(main())
