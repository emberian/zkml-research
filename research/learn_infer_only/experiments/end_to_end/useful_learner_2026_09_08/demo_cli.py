"""Use the real CLI to add a ninth intent from new text and query it."""
import json,shutil,subprocess,sys,time
from pathlib import Path
from learner import HERE,save
FIXTURE={'label':'account_access','teaching_texts':['I forgot the passcode for the banking app and cannot sign in.','Please help me reset my login password so I can access my account.'],'query':'I cannot log in because I no longer remember the code for the app.'}
def run(backend):
 source=HERE/'models'/backend
 if backend=='plain':
  target=HERE/'models/live_plain';target.mkdir();shutil.copyfile(source/'learner.json',target/'learner.json')
 else:target=source
 events=[]
 args=[['query',str(target),'--text',FIXTURE['query']]]
 args += [['teach',str(target),'--label',FIXTURE['label'],'--text',text] for text in FIXTURE['teaching_texts']]
 args += [['query',str(target),'--text',FIXTURE['query']],['status',str(target)]]
 for arguments in args:
  cmd=[sys.executable,'-B',str(HERE/'learner.py')]+arguments;t=time.perf_counter();p=subprocess.run(cmd,capture_output=True,text=True,timeout=60)
  event={'argv':cmd,'returncode':p.returncode,'elapsed_seconds':time.perf_counter()-t,'stdout':p.stdout,'stderr':p.stderr};events.append(event)
  save(HERE/f'cli_demo_{backend}.json',{'fixture':FIXTURE,'events':events})
  if p.returncode:raise RuntimeError(p.stderr)
 results=[json.loads(e['stdout']) for e in events]
 print(json.dumps({'backend':backend,'before':results[0]['label'],'after':results[3]['label'],'expected_new_label':FIXTURE['label'],'new_class_learned':results[3]['label']==FIXTURE['label'],'new_revision':results[-1]['revision']}))
if __name__=='__main__':
 save(HERE/'cli_demo_inputs.json',FIXTURE)
 run(sys.argv[1] if len(sys.argv)>1 else 'plain')
