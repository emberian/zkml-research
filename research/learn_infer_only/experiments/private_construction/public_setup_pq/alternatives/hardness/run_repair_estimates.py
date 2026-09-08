"""Same pinned estimator driver, separate rigorously proven repair moduli."""
import json
import signal
import time
import run_estimates as base

def repair_primes():
    dest=base.HERE/'moduli_repair.json'
    if dest.exists(): return json.loads(dest.read_text())
    started=time.monotonic();signal.alarm(60)
    low=base.ZZ(2**292).next_prime(proof=True)
    high=base.ZZ(2**293).previous_prime()
    assert low.is_prime(proof=True) and high.is_prime(proof=True)
    assert 2**292<low<high<2**293
    signal.alarm(0)
    out={'low':str(low),'high':str(high),'low_offset_above_2pow292':str(low-2**292),
         'high_offset_below_2pow293':str(2**293-high),
         'low_is_prime_proof_true':True,'high_is_prime_proof_true':True,
         'procedure':'Sage next_prime(proof=True); previous_prime then both is_prime(proof=True)',
         'sage_version':base.sage_version,'seconds_primality_computation':time.monotonic()-started}
    dest.write_text(json.dumps(out,indent=2)+'\n');return out

base.prime_endpoints=repair_primes
if __name__=='__main__':base.main()
