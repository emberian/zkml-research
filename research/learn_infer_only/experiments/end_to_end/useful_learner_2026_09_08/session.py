#!/usr/bin/env python3
"""Keep the text encoder loaded while teaching and querying one model over JSONL."""
import argparse,contextlib,json,sys
from encoder import Encoder
from learner import Learner

def main():
 parser=argparse.ArgumentParser(description='Read teach/query/status JSON objects, one per line. One writer per model directory.')
 parser.add_argument('directory');args=parser.parse_args()
 encoder=Encoder();learner=Learner(args.directory)
 print(json.dumps({'ready':True,**learner.status()}),flush=True)
 for line in sys.stdin:
  if not line.strip():continue
  try:
   request=json.loads(line);op=request.get('op');learner=Learner(args.directory)
   expected={'status':{'op'},'query':{'op','text'},'teach':{'op','text','label'}}
   if op not in expected or set(request)!=expected[op]:raise ValueError('Use status, query with text, or teach with text and label')
   if op=='status':result=learner.status()
   else:
    with contextlib.redirect_stdout(sys.stderr):vector=encoder.encode([request['text']])[0]
    result=learner.teach_vector(request['label'],vector) if op=='teach' else learner.query_vector(vector)
   print(json.dumps({'ok':True,'op':op,'result':result}),flush=True)
  except Exception as error:
   print(json.dumps({'ok':False,'error':str(error)}),flush=True)
if __name__=='__main__':main()
