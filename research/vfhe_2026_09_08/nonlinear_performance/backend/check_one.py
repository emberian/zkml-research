from pathlib import Path
import hashlib,json,os,subprocess,sys,time
root=Path(__file__).resolve().parent
prior=json.loads((root.parents[1]/'rescale_native_emitter/results/emit_plan001_command.json').read_text())
paths=[str(root/'build'),'/Users/ember/dev/breadstuffs/metatheory/.lake/build/lib/lean',prior['LEAN_PATH']]
env=dict(os.environ,LEAN_PATH=':'.join(paths));name=sys.argv[2] if len(sys.argv)>2 else 'IR2RangeLookupBridge';number=sys.argv[1]
cmd=[prior['command'][0],'-o',f'build/Compiler/{name}.olean',f'Compiler/{name}.lean'];start=time.perf_counter()
r=subprocess.run(cmd,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(root/'checks'/f'{number}.log').write_text(r.stdout)
(root/'checks'/f'{number}.json').write_text(json.dumps(dict(command=cmd,cwd=str(root),LEAN_PATH=env['LEAN_PATH'],seconds=time.perf_counter()-start,exit=r.returncode,source_sha256=hashlib.sha256((root/'Compiler'/f'{name}.lean').read_bytes()).hexdigest()),indent=2)+'\n')
print(r.returncode);print(r.stdout);sys.exit(r.returncode)
