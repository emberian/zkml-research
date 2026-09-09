from pathlib import Path
import hashlib,json,os,subprocess,sys,time
P=Path(__file__).resolve().parent
prior=json.loads((P.parent.parent/'rescale_native_emitter/results/emit_plan001_command.json').read_text())
env=dict(os.environ,LEAN_PATH=str(P/'build')+':'+str(P.parent.parent/'nonlinear_performance/formal/build')+':'+str(P.parent.parent/'basis_extension_successor/build')+':'+prior['LEAN_PATH']+':/Users/ember/dev/breadstuffs/metatheory/.lake/build/lib/lean')
name=sys.argv[1];number=len(list((P/'results').glob(name+'_*.json')))+1;log=P/'results'/f'{name}_{number:03d}.log';cmd=[prior['command'][0],'-o',f'build/Compiler/{name}.olean',f'Compiler/{name}.lean'];start=time.perf_counter()
with log.open('w') as f:p=subprocess.run(cmd,cwd=P,env=env,stdout=f,stderr=subprocess.STDOUT)
r={'command':cmd,'cwd':str(P),'LEAN_PATH':env['LEAN_PATH'],'seconds':time.perf_counter()-start,'exit':p.returncode,'source_sha256':hashlib.sha256((P/f'Compiler/{name}.lean').read_bytes()).hexdigest(),'log':str(log)}
(P/'results'/f'{name}_{number:03d}.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));print(log.read_text());raise SystemExit(p.returncode)
