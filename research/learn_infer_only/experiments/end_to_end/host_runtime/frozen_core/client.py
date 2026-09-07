import argparse,json
from common import rpc,read_json
p=argparse.ArgumentParser();p.add_argument('--socket',required=True);p.add_argument('--message',required=True);a=p.parse_args()
try:print(json.dumps(rpc(a.socket,read_json(a.message))))
except (OSError,EOFError) as e:print(json.dumps({'transport_error':type(e).__name__}));raise SystemExit(3)
