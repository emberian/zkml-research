"""Public request policy and actual ciphertext transition recomputation."""
import copy
from common import *

ACTION_BASE=['schema','genesis','params_id','program_id','program_version','key_id','public_key_sha256','kind','route','request_id','nonce','parent_revision','parent_state','recipient']

def validate_action(action,authorization,g,cas):
 require(isinstance(action,dict),'actionObject');kind=action.get('kind')
 extra=['record_id','fresh_ct','feature_policy','range_assertion'] if kind=='Learn' else ['query_ct']
 require(kind in ['Learn','Infer'],'commandKind');exact_keys(action,ACTION_BASE+extra,'actionFields')
 require(action['schema']=='resident-action-v1','actionSchema')
 for k,v in identity_fields(g).items():require(action[k]==v,'identity:'+k)
 require(integer(action['route']) and action['route'] in g['routes'],'route')
 require(integer(action['parent_revision']) and action['parent_revision']>=0,'parentRevision')
 for k in ['request_id','nonce']:
  require(isinstance(action[k],str) and 0<len(action[k])<=128,'identifier:'+k)
 require(action['recipient']==g['recipient'],'recipient')
 if kind=='Learn':
  require(action['feature_policy']==g['feature_policy'] and action['range_assertion']==[-127,127],'issuerPolicy')
  require(isinstance(action['record_id'],str) and 0<len(action['record_id'])<=128,'recordId')
  payload=verify(authorization,g['issuer_vk'],'resident-issuer-v1');cas.get(action['fresh_ct'])
 else:
  payload=verify(authorization,g['command_vk'],'resident-query-authorization-v1');cas.get(action['query_ct'],'query')
  require({'query_ct':action['query_ct'],'route':action['route']} in g['query_policy'],'queryNotPreregistered')
 require(payload==action,'authorizationContext')
 return kind

def transition(state,action,g,cas):
 """Recompute from canonical current blobs; host and authority call independently."""
 validate_state(state,g,cas);new=copy.deepcopy(state);route=new['routes'][str(action['route'])]
 out=cas.fresh_output()
 if action['kind']=='Learn':
  entry={'record_id':action['record_id'],'ct_sha256':action['fresh_ct']}
  old=route['queue'][0] if len(route['queue'])==g['capacity'] else None
  cas.crypto.run('host-learn',acc=cas.get(route['acc_ct']),fresh=cas.get(entry['ct_sha256']),old=cas.get(old['ct_sha256']) if old else None,out=out)
  result=cas.finish_output(out);route['queue'].append(entry)
  if old:route['queue'].pop(0)
  route['acc_ct']=result;route['admissions']+=1
  delta={'kind':'Learn','route':action['route'],'fresh':entry,'expired':old,'acc_ct':result}
  proposal={'result_ct':result,'expired_ct':old['ct_sha256'] if old else None,'next_state':digest(new)}
 else:
  cas.crypto.run('host-infer',acc=cas.get(route['acc_ct']),query=cas.get(action['query_ct'],'query'),out=out)
  result=cas.finish_output(out)
  delta={'kind':'Infer','route':action['route'],'query_ct':action['query_ct'],'output_ct':result}
  proposal={'result_ct':result,'expired_ct':None,'next_state':digest(new)}
 return new,delta,proposal

def apply_delta(state,delta,g):
 new=copy.deepcopy(state);route=new['routes'][str(delta['route'])]
 if delta['kind']=='Learn':
  expected=route['queue'][0] if len(route['queue'])==g['capacity'] else None
  require(delta['expired']==expected,'replayExpiry')
  route['queue'].append(delta['fresh'])
  if expected:route['queue'].pop(0)
  route['acc_ct']=delta['acc_ct'];route['admissions']+=1
 else:require(delta['kind']=='Infer','replayKind')
 return new

def request_for(action,auth,proposal):return {'schema':'resident-request-v1','action':action,'authorization':auth,'proposal':proposal}
def check_request(req,g,cas):
 exact_keys(req,['schema','action','authorization','proposal'],'requestFields')
 require(req['schema']=='resident-request-v1','requestSchema')
 exact_keys(req['proposal'],['result_ct','expired_ct','next_state'],'proposalFields')
 validate_action(req['action'],req['authorization'],g,cas)

def make_action(g,head,kind,route,request_id,nonce,**extra):
 return {'schema':'resident-action-v1',**identity_fields(g),'kind':kind,'route':route,'request_id':request_id,'nonce':nonce,'parent_revision':head['revision'],'parent_state':head['state_digest'],'recipient':g['recipient'],**extra}
