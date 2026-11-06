from pathlib import Path
import hashlib, json, re
base=Path(__file__).resolve().parent

def no_comments(text):
    out=[];i=0;depth=0
    while i<len(text):
        if depth:
            if text[i:i+2]=='/-':depth+=1;i+=2
            elif text[i:i+2]=='-/':depth-=1;i+=2
            else:i+=1
        elif text[i:i+2]=='/-':depth=1;i+=2
        elif text[i:i+2]=='--':
            j=text.find('\n',i);i=len(text) if j<0 else j+1
        elif text[i]=='"':
            j=i+1
            while j<len(text):
                if text[j]=='\\':j+=2
                elif text[j]=='"':j+=1;break
                else:j+=1
            out.append(text[i:j]);i=j
        else:out.append(text[i]);i+=1
    assert depth==0,'Unclosed comment'
    return ''.join(out)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
summary={'checks':{},'source_hashes':{}}
for name in ['BindingGame','BindingBudget']:
 p=base/'source/Selvage'/(name+'.lean');text=p.read_text();code=no_comments(text)
 assert not re.search(r'\b(sorry|axiom|native_decide|implemented_by|unsafe|opaque)\b',code)
 theorem_count=len(re.findall(r'^theorem ',code,re.M))
 pin_count=len(re.findall(r'^#guard_msgs .*#print axioms ',code,re.M))
 assert theorem_count==pin_count,(name,theorem_count,pin_count)
 summary['checks'][name]={'theorems':theorem_count,'axiom_pins':pin_count,'forbidden_escapes':0}
 summary['source_hashes'][str(p.relative_to(base))]=sha(p)
for name in ['Commitment','AuditSampling','CollisionResistanceROM']:
 p=base/'source/Selvage'/(name+'.lean');old=base/'original/Selvage'/(name+'.lean')
 assert re.sub(r'\s+','',no_comments(p.read_text()))==re.sub(r'\s+','',no_comments(old.read_text())),name+' changes code'
 summary['checks'][name]='Comments only; executable tokens unchanged'
 summary['source_hashes'][str(p.relative_to(base))]=sha(p)
core=json.loads((base/'core-build-manifest.json').read_text())
adapter=json.loads((base/'adapter-build-manifest.json').read_text())
assert core['source_sha256']==sha(base/'source/Selvage/BindingGame.lean')==adapter['core_source_sha256']
assert adapter['adapter_sha256']==sha(base/'source/Selvage/BindingBudget.lean')
assert core['olean_sha256']==sha(base/'build/Selvage/BindingGame.olean')
for logfile in ['build-core.log','build-adapter.log','import-boundary.log','patch-apply-check.log']:
 s=(base/logfile).read_text();assert 'EXIT 0\n' in s,logfile
 summary['checks'][logfile]='PASS (scope described in binding-term-design.md)'
summary['patch_sha256']=sha(base.parent/'binding-term.patch')
summary['whole_project_build']='NOT RUN: local Selvage 4.30 oleans incompatible with pinned Lean/Mathlib 4.35; hbox integration required'
(base/'validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
