"""Teach a new travel-insurance class through the actual persistent interface."""
import json,shutil,subprocess,sys,time
from model import HERE,save
REQUESTS=[{'op':'query','text':'Where can I buy a policy covering medical care on my trip overseas?'},{'op':'teach','label':'travel_insurance','text':'I need travel insurance for an overseas holiday, including hospital treatment.'},{'op':'teach','label':'travel_insurance','text':'Does your travel policy cover medical emergencies while I am abroad?'},{'op':'query','text':'Where can I buy a policy covering medical care on my trip overseas?'},{'op':'status'}]
def main():
 backend=sys.argv[1];save(HERE/'live_inputs.json',REQUESTS)
 if backend=='plain':
  target=HERE/'models/live_plain';target.mkdir();shutil.copyfile(HERE/'models/plain/model.json',target/'model.json')
 else:
  assert (HERE/'encrypted_result.json').exists(),'Complete the fixed benchmark first'
  target=HERE/'models/bfv'
 argv=[sys.executable,'-B',str(HERE/'session.py'),str(target)];start=time.perf_counter();p=subprocess.run(argv,input=''.join(json.dumps(r)+'\n' for r in REQUESTS),capture_output=True,text=True,timeout=180)
 result={'argv':argv,'returncode':p.returncode,'elapsed_seconds':time.perf_counter()-start,'stdout':p.stdout,'stderr':p.stderr,'requests':REQUESTS};save(HERE/f'live_{backend}.json',result)
 assert p.returncode==0,p.stderr
 rows=[json.loads(x) for x in p.stdout.splitlines()];assert rows[0]['ready'] and all(r['ok'] for r in rows[1:]),rows
 print(json.dumps({'backend':backend,'before':rows[1]['result']['label'],'after':rows[4]['result']['label'],'new_class':'travel_insurance','revision':rows[5]['result']['revision']}))
if __name__=='__main__':main()
