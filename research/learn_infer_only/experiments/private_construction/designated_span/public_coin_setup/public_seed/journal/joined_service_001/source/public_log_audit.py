#!/usr/bin/env python3
"""Exact-field omission check for public protocol logs, not a leakage theorem."""
from pathlib import Path
import json

PRIVATE_FIELDS={'signed_score','sign','answer','decode_elapsed_ns'}

def check_public_logs(root):
 counts={'log_files':0,'json_records':0,'nested_stdout_documents':0,'public_bounds_metadata_fields':0}
 def walk(value):
  if isinstance(value,dict):
   bad=PRIVATE_FIELDS.intersection(value)
   if bad:raise ValueError('private scalar/decode field in public log: '+','.join(sorted(bad)))
   counts['public_bounds_metadata_fields']+='row_signed_score_bounds' in value
   command=value.get('command')
   if isinstance(command,list) and len(command)>1 and command[1]=='reader-decrypt':raise ValueError('private decoder command in public log')
   if value.get('private_output_omitted') is True:raise ValueError('private operation unexpectedly routed to public log')
   for key,item in value.items():
    if key in ['stdout','stderr'] and isinstance(item,str) and item.strip():
     # CLI stdout is a complete JSON document; unrelated stderr text is kept
     # as diagnostic data but is never treated as a parsed scalar object.
     try:decoded=json.loads(item)
     except json.JSONDecodeError:
      if key=='stdout':raise ValueError('non-JSON public CLI stdout')
     else:counts['nested_stdout_documents']+=1;walk(decoded)
    else:walk(item)
  elif isinstance(value,list):
   for item in value:walk(item)
 for path in sorted(Path(root).glob('*.jsonl')):
  counts['log_files']+=1
  for line in path.read_text().splitlines():
   if line.strip():walk(json.loads(line));counts['json_records']+=1
 return {'ok':True,'scope':'exact parsed public log fields and actual command names; no timing/security theorem','private_fields_absent':sorted(PRIVATE_FIELDS),'private_decoder_commands_absent':True,**counts}

if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);a=p.parse_args()
 print(json.dumps(check_public_logs(a.root)))
