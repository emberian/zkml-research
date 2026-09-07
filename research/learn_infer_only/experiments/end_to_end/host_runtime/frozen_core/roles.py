"""Trusted setup/issuer/command-authorizer and keyless host process entry points."""
import argparse
from model import *
HERE=Path(__file__).resolve().parent

def setup(args):
 root=Path(args.root).resolve();root.mkdir(parents=True,exist_ok=False)
 private=root/'.private';private.mkdir(mode=0o700)
 for role in ['issuer','command','authority','reader']:(private/role).mkdir(mode=0o700)
 binary=Path(args.binary).resolve();base={'crypto_binary':str(binary),'crypto_binary_sha256':sha(binary.read_bytes())}
 log=root/'commands.jsonl';crypto=Crypto(base,'trusted_setup',log);params=crypto.run('params')
 pk=root/'public_key.bin';sk=private/'reader'/'bfv_secret.bin';zero=root/'zero.ct'
 key=crypto.run('keygen',pk=pk,sk=sk,zero=zero)
 issuer_vk=create_signing_key(private/'issuer'/'signing.key');command_vk=create_signing_key(private/'command'/'signing.key');authority_vk=create_signing_key(private/'authority'/'signing.key')
 query_dir=root/'queries';query_dir.mkdir();policy=[]
 for index,item in enumerate(read_json(args.queries)):
  out=query_dir/f'q{index:02d}.json';meta=crypto.run('encode-query',vector=item['path'],out=out)
  policy.append({'query_ct':meta['sha256'],'route':item['route']})
 g={'schema':'resident-genesis-v1','crypto':params,'key_id':key['key_id'],'public_key_sha256':sha(pk.read_bytes()),'zero_ct_sha256':sha(zero.read_bytes()),'capacity':32,'routes':[0,1],
  'issuer_vk':issuer_vk,'command_vk':command_vk,'authority_vk':authority_vk,'recipient':'benchmark-recipient-R','query_policy':policy,
  'feature_policy':'trusted-issuer-signed577-int8-bound127-v1','custody':'R: explicitly trusted single full-key reader; classical Ed25519 role authentication',
  'journal_program':'keyless-recomputation-delta-journal-v1','crypto_binary_sha256':base['crypto_binary_sha256'],
  'journal_sources':{name:sha((HERE/name).read_bytes()) for name in ['common.py','model.py','roles.py','authority.py','reader.py']}}
 write_json(root/'genesis.json',g);base.update({'genesis_path':str(root/'genesis.json'),'genesis_sha256':digest(g),'command_log':str(log)})
 write_json(root/'host_config.json',base)
 socket_prefix='/tmp/rsj-'+os.urandom(6).hex()
 for role in ['issuer','command','authority','reader']:
  cfg={**base,'role':role}
  if role!='reader':cfg['signing_key']=str(private/role/'signing.key')
  if role=='issuer':cfg['public_key']=str(pk)
  if role=='reader':cfg['bfv_secret_key']=str(sk);cfg['bfv_secret_sha256']=sha(sk.read_bytes())
  if role in ['authority','reader']:
   role_dir=root/role;role_dir.mkdir();cfg.update({'db':str(role_dir/'journal.sqlite3'),'cas':str(role_dir/'cas'),'socket':socket_prefix+'-'+role+'.sock'})
  if role=='authority':cfg['reader_socket']=socket_prefix+'-reader.sock'
  if role=='reader':cfg['db']=str(private/'reader'/'answers.sqlite3')
  write_json(private/role/'config.json',cfg,True)
 print(json.dumps({'ok':True,'genesis':digest(g),'key_id':g['key_id'],'query_count':len(policy),'root':str(root)}))

def issue(args):
 cfg=read_json(args.config);g=load_genesis(cfg);head=read_json(args.head)
 require(cfg['role']=='issuer','issuerRole');pk=Path(cfg['public_key']);require(sha(pk.read_bytes())==g['public_key_sha256'],'issuerPinnedPublicKey')
 out=Path(args.out);out.mkdir(parents=True,exist_ok=False)
 meta=Crypto(cfg,'issuer',cfg['command_log']).run('issuer-encrypt',pk=pk,vector=args.vector,out=out/'fresh.ct')
 require(meta['key_id']==g['key_id'] and meta['params_id']==g['crypto']['params_id'],'issuerKeyParams')
 action=make_action(g,head,'Learn',args.route,args.request_id,args.nonce,record_id=args.record_id,fresh_ct=meta['sha256'],feature_policy=g['feature_policy'],range_assertion=[-127,127])
 signed=sign(action,cfg['signing_key'],'resident-issuer-v1');write_json(out/'authorization.json',signed)
 print(json.dumps({'ok':True,'authorization_sha256':digest(signed),'fresh_ct':meta['sha256']}))

def authorize(args):
 cfg=read_json(args.config);g=load_genesis(cfg);require(cfg['role']=='command','commandRole')
 raw=Path(args.query).read_bytes();query=json.loads(raw)
 require(raw==canonical(query),'queryCanonicalEncoding');hexdigest=sha(raw)
 require({'query_ct':hexdigest,'route':args.route} in g['query_policy'],'queryNotPreregistered')
 action=make_action(g,read_json(args.head),'Infer',args.route,args.request_id,args.nonce,query_ct=hexdigest)
 signed=sign(action,cfg['signing_key'],'resident-query-authorization-v1');write_json(args.out,signed)
 print(json.dumps({'ok':True,'authorization_sha256':digest(signed)}))

def propose(args):
 cfg=read_json(args.config);g=load_genesis(cfg);head=read_json(args.head);auth=read_json(args.authorization)
 cas=CAS(args.cas,g,Crypto(cfg,'host',cfg['command_log']));a=auth['payload'];validate_action(a,auth,g,cas)
 require(a['parent_revision']==head['revision'] and a['parent_state']==head['state_digest'],'hostParent')
 require(validate_state(head['state'],g,cas)==head['state_digest'],'hostStateDigest')
 new,delta,proposal=transition(head['state'],a,g,cas);req=request_for(a,auth,proposal);write_json(args.out,req)
 print(json.dumps({'ok':True,'request_sha256':digest(req),'result_ct':proposal['result_ct'],'next_state':digest(new)}))

def main():
 p=argparse.ArgumentParser();subs=p.add_subparsers(dest='command',required=True)
 s=subs.add_parser('setup');s.add_argument('--root',required=True);s.add_argument('--binary',required=True);s.add_argument('--queries',required=True)
 i=subs.add_parser('issue');a=subs.add_parser('authorize')
 for sub in [i,a]:
  for key in ['config','head','request-id','nonce','out']:sub.add_argument('--'+key,required=True)
  sub.add_argument('--route',type=int,required=True)
 i.add_argument('--vector',required=True);i.add_argument('--record-id',required=True);a.add_argument('--query',required=True)
 h=subs.add_parser('propose')
 for key in ['config','head','authorization','cas','out']:h.add_argument('--'+key,required=True)
 args=p.parse_args()
 try:globals()[{'setup':'setup','issue':'issue','authorize':'authorize','propose':'propose'}[args.command]](args)
 except Refusal as e:print(json.dumps({'ok':False,'reason':str(e)}));raise SystemExit(2)
if __name__=='__main__':main()
