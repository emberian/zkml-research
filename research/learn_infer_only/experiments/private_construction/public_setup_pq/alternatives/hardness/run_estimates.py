"""Bounded parameter-estimator calls only; never construct a crypto instance."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
EXPERIMENTS = HERE.parents[3]
OLD = EXPERIMENTS/'he_closure_costs/estimator'
SOURCE = OLD/'runtime/pinned-estimator'
os.environ['DOT_SAGE'] = str(HERE/'runtime/sage_cache')
os.environ['MPLCONFIGDIR'] = str(HERE/'runtime/mpl')
os.environ['XDG_CACHE_HOME'] = str(HERE/'runtime/xdg')
sys.dont_write_bytecode = True
sys.path.insert(0,str(SOURCE))
from sage.all import ZZ, QQ, RR, RealField, log, oo, pi, sqrt
from sage.version import version as sage_version
from estimator import LWE, ND
from estimator.reduction import ADPS16, MATZOV, ReductionCost
from estimator.lwe_dual import DualHybrid
from estimator.lwe_guess import distinguish

MODELS = {
 'MATZOV_classical': lambda: MATZOV(nn='list_decoding-classical'),
 'ADPS16_classical': lambda: ADPS16(mode='classical'),
 'ADPS16_quantum_core_svp': lambda: ADPS16(mode='quantum'),
 'MATZOV_quantum_depth_width': lambda: MATZOV(nn='list_decoding-dw'),
}
def expired(*args): raise TimeoutError('bounded parameter-computation deadline')
signal.signal(signal.SIGALRM,expired)
def call_attack(attack,p,model):
 if attack=='dual': return LWE.dual(p,red_cost_model=model)
 if attack=='usvp': return LWE.primal_usvp(p,red_cost_model=model,red_shape_model='gsa')
 if attack=='bdd': return LWE.primal_bdd(p,red_cost_model=model,red_shape_model='gsa')
 if attack=='dual_hybrid': return LWE.dual_hybrid(p,red_cost_model=model)
 if attack=='dual_fixed_beta2':
  return DualHybrid.cost(distinguish,p.normalize(),beta=2,zeta=0,h1=0,red_cost_model=model,log_level=1)
 raise ValueError(attack)
def values(cost):
 fields={str(k):str(v) for k,v in cost.items() if k!='problem'}
 logs={}
 for k in ['rop','red','mem','m','N','guess']:
  if k in cost:
   v=cost[k]
   try: logs[k]=float(log(v,2)) if v>0 and v!=oo else str(v)
   except Exception: logs[k]=None
 return fields,logs
def prime_endpoints():
 dest=HERE/'moduli.json'
 if dest.exists(): return json.loads(dest.read_text())
 started=time.monotonic();signal.alarm(60)
 low=ZZ(2**288).next_prime(proof=True)
 high=ZZ(2**289).previous_prime()
 assert low.is_prime(proof=True) and high.is_prime(proof=True)
 assert 2**288<low<high<2**289
 signal.alarm(0)
 out={'low':str(low),'high':str(high),'low_offset_above_2pow288':str(low-2**288),
      'high_offset_below_2pow289':str(2**289-high),
      'low_is_prime_proof_true':True,'high_is_prime_proof_true':True,
      'procedure':'Sage Integer.next_prime(proof=True); previous_prime then both is_prime(proof=True)',
      'sage_version':sage_version,'seconds_primality_computation':time.monotonic()-started}
 dest.write_text(json.dumps(out,indent=2)+'\n');return out
def main():
 a=argparse.ArgumentParser()
 a.add_argument('--n',nargs='+',type=int,default=[1024])
 a.add_argument('--sigma-bits',nargs='+',type=int,default=[10])
 a.add_argument('--q',nargs='+',choices=['low','high'],default=['low','high'])
 a.add_argument('--m',type=int,default=16384)
 a.add_argument('--models',nargs='+',choices=MODELS,default=list(MODELS))
 a.add_argument('--attacks',nargs='+',default=['dual','usvp','bdd'])
 a.add_argument('--seconds',type=int,default=45)
 a.add_argument('--output',default='baseline.jsonl')
 args=a.parse_args(); qs=prime_endpoints()
 manifest={'estimator_commit':'53da5982597709ba0fdf94ea37a84d822310fd84',
           'sage_version':sage_version,'python':sys.version,'invocation':sys.argv,
           'source_path':str(SOURCE),'red_shape_model':'gsa',
           'source_hashes':{f:hashlib.sha256((SOURCE/'estimator'/f).read_bytes()).hexdigest()
                            for f in ['nd.py','lwe_parameters.py','lwe_dual.py','lwe_primal.py','reduction.py']},
           'scope':'Heuristic parameter estimator only. No cryptographic instance or attack execution.'}
 dest=HERE/args.output
 dest.with_suffix('.manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 with dest.open('w') as out:
  for n in args.n:
   for sb in args.sigma_bits:
    for label in args.q:
     q=ZZ(qs[label]); xe=ND.DiscreteGaussianAlpha(QQ(2**sb)/q,q)
     p=LWE.Parameters(n=n,q=q,Xs=ND.UniformMod(q),Xe=xe,m=args.m)
     for modelname in args.models:
      for attack in args.attacks:
       row={'q_label':label,'q_exact':str(q),'n':n,'m_input':args.m,'sigma_width_exponent':sb,
            'error_stddev_estimator':str(xe.stddev),'input_repr':repr(p),
            'normalized_repr':repr(p.normalize()),'model':modelname,'attack':attack}
       print('START',n,sb,label,modelname,attack,flush=True)
       started=time.monotonic();signal.alarm(args.seconds)
       try:
        cost=call_attack(attack,p,MODELS[modelname]())
        row['fields'],row['log2_fields']=values(cost);row['status']='EXECUTED'
       except Exception as e:
        row['status']='TIMEOUT' if isinstance(e,TimeoutError) else 'ERROR'
        row['exception']=repr(e);row['traceback']=traceback.format_exc()
       finally: signal.alarm(0)
       row['seconds_estimator_not_attack']=time.monotonic()-started
       out.write(json.dumps(row)+'\n');out.flush()
       print('RESULT',row['status'],row.get('log2_fields'),row.get('fields',{}).get('beta'),flush=True)
if __name__=='__main__':main()
