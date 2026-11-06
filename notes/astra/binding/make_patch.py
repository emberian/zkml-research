from pathlib import Path
import difflib, hashlib, json, subprocess
base=Path(__file__).resolve().parent
root=Path('/Users/ember/dev/minidregg')
parts=[]
for p in sorted((base/'source/Selvage').glob('*.lean')):
 rel='Selvage/'+p.name
 old=base/'original'/rel
 before=old.read_text() if old.exists() else ''
 after=p.read_text()
 parts.append('diff --git a/'+rel+' b/'+rel+'\n')
 if not old.exists():parts.append('new file mode 100644\n')
 parts.extend(difflib.unified_diff(before.splitlines(keepends=True),after.splitlines(keepends=True),fromfile=('a/'+rel if old.exists() else '/dev/null'),tofile='b/'+rel))
patch=base.parent/'binding-term.patch';patch.write_text(''.join(parts))
cmd=['git','-C',str(root),'apply','--check',str(patch)]
r=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(base/'patch-apply-check.log').write_text('COMMAND '+repr(cmd)+'\n'+r.stdout+'\nEXIT '+str(r.returncode)+'\nPATCH_SHA256 '+hashlib.sha256(patch.read_bytes()).hexdigest()+'\n')
print(r.stdout);print('git apply --check exit',r.returncode)
raise SystemExit(r.returncode)
