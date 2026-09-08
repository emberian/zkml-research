"""Six authorized normalized dual entries; dimension-aware preflight checks."""
import run_repair_estimates as repair

base=repair.base
raw_call=base.call_attack
def corrected_call(attack,params,model):
    if attack!='dual':raise ValueError('Only the six authorized normalized-dual calls')
    normalized=params.normalize()
    assert normalized.n==16384 and normalized.m==245760
    assert type(normalized.Xs).__name__==type(normalized.Xe).__name__=='DiscreteGaussian'
    assert normalized.Xs.mean==normalized.Xe.mean==0
    assert normalized.Xs.stddev==normalized.Xe.stddev
    assert len(normalized.Xs)==16384 and len(normalized.Xe)==245760
    return raw_call(attack,normalized,model)
base.call_attack=corrected_call
if __name__=='__main__':base.main()
