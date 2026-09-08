"""Actual persistent-session extension from77 to78 learned intents."""
import json,shutil,subprocess,sys,time
from pathlib import Path
from learner import HERE,save
REQUESTS=[{'op':'query','text':'How do I submit a mortgage application for a new house?'},{'op':'teach','label':'loan_application','text':'I would like to apply for a mortgage to buy my first home.'},{'op':'teach','label':'loan_application','text':'Please explain the documents needed for a housing loan application.'},{'op':'query','text':'How do I submit a mortgage application for a new house?'},{'op':'status'}]
def main():
 backend=sys.argv[1]
 if backend=='plain':
  target=HERE/'models/full77_live_plain';target.mkdir();shutil.copyfile(HERE/'models/full77/learner.json',target/'learner.json')
 else:
  assert (HERE/'full77/encrypted_result.json').exists(),'Finish the encrypted benchmark first'
  target=HERE/'models/full77_bfv'
 save(HERE/'session_inputs.json',REQUESTS)
 argv=[sys.executable,'-B',str(HERE/'session.py'),str(target)];start=time.perf_counter()
 p=subprocess.run(argv,input=''.join(json.dumps(x)+'\n' for x in REQUESTS),text=True,capture_output=True,timeout=120)
 result={'argv':argv,'returncode':p.returncode,'elapsed_seconds':time.perf_counter()-start,'stdout':p.stdout,'stderr':p.stderr,'requests':REQUESTS};save(HERE/f'session_{backend}.json',result)
 assert p.returncode==0,p.stderr
 rows=[json.loads(x) for x in p.stdout.splitlines()];assert rows[0]['ready'] and all(x['ok'] for x in rows[1:])
 print(json.dumps({'backend':backend,'before':rows[1]['result']['label'],'after':rows[4]['result']['label'],'revision':rows[5]['result']['revision'],'classes':len(rows[5]['result']['classes'])}))
if __name__=='__main__':main()
