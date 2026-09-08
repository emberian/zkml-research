"""Correct the direct dual API's explicit normalized-input precondition."""
import run_repair_estimates as repair

base=repair.base
raw_call=base.call_attack
def corrected_call(attack,params,model):
    if attack!='dual':raise ValueError('Only the six authorized normalized-dual calls')
    normalized=params.normalize()
    assert normalized.n==16384 and normalized.m==245760
    assert normalized.Xs==normalized.Xe
    return raw_call(attack,normalized,model)
base.call_attack=corrected_call
if __name__=='__main__':base.main()
