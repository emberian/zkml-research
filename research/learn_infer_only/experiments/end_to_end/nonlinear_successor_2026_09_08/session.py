#!/usr/bin/env python3
"""Persistent nonlinear text issuer plus cached public BFV host, JSONL interface."""
import argparse,contextlib,json,sys
from fast_model import FastModel
from model import Encoder,HERE,OLD,transform

def main():
 p=argparse.ArgumentParser(description='One teach/query/status JSON request per line; one writer per model directory.');p.add_argument('directory');a=p.parse_args();model=FastModel(a.directory);encoder=Encoder(cache=HERE/'feature_cache')
 def vector(text):
  old=OLD/'feature_cache'/(encoder.key(text)+'.json')
  if old.exists():return transform(json.loads(old.read_text())['vector'])
  with contextlib.redirect_stdout(sys.stderr):return transform(encoder.encode([text])[0])
 print(json.dumps({'ready':True,**model.status()}),flush=True)
 try:
  for line in sys.stdin:
   if not line.strip():continue
   try:
    request=json.loads(line);op=request.get('op');expected={'status':{'op'},'query':{'op','text'},'teach':{'op','text','label'}}
    if op not in expected or set(request)!=expected[op]:raise ValueError('Use status, query/text or teach/text/label')
    if op=='status':result=model.status()
    elif op=='teach':result=model.teach_vector(request['label'],vector(request['text']))
    else:result=model.query_vector(vector(request['text']))
    print(json.dumps({'ok':True,'op':op,'result':result}),flush=True)
   except Exception as error:
    print(json.dumps({'ok':False,'error':str(error)}),flush=True)
 finally:model.close()
if __name__=='__main__':main()
