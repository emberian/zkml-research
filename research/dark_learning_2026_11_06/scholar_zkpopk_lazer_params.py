"""Generate the exact binary relation profile for the LaZer linear backend.

This emits INPUT parameters for upstream lin-codegen.sage, not security-estimated
output parameters and not a claimed LaZer proof. No external package required.
Run: python3 scholar_zkpopk_lazer_params.py > /tmp/scholar-bfv-params.py
Then, on a qualified LaZer/Sage host:
  cd <lazer>/scripts
  sage lin-codegen.sage /tmp/scholar-bfv-params.py > /tmp/scholar-bfv-params.h
The generated parameters still need review and backend execution.
"""
import math
import bfv_ref as bfv


def profile(N=8192):
    primes=bfv.ntt_primes(61,4,2*N)
    Q=math.prod(primes[:3]); t=primes[3]; H=8*t+(t-1)//2
    widths=[2,5,(t-1).bit_length(),(2*H).bit_length()]
    # Each variable's shifted value + its complement-to-public-upper-bound.
    # Six polynomial equations: key, ciphertext, and four exact range sums.
    cols=2*sum(widths)
    return dict(N=N,Q=Q,t=t,primes=primes[:3],mod=t*Q,dim=(6,cols),widths=widths,
                wpart=[list(range(cols))],wl2=[0],wbin=[1],wlinf=1)


def emit():
    p=profile()
    print('# Exact binary BFV relation. INPUT ONLY: run the upstream estimator/codegen.')
    print('vname = "scholar_bfv_exact"')
    for k,v in [('deg',p['N']),('mod',p['mod']),('dim',p['dim']),('wpart',p['wpart']),
                ('wl2',p['wl2']),('wbin',p['wbin']),('wlinf',p['wlinf'])]:
        print(f'{k} = {v!r}')


if __name__=='__main__': emit()


def compile_linear(rel,extended_binary_witness=None):
    """Sparse A,target for A*w=target in Z_(tQ)[X]/(X^N+1).

    Every witness column is a binary polynomial. This returns ordinary Python
    objects; it does NOT pretend that a lattice backend has proved them.
    """
    N,M,t,Q=rel.N,rel.mod,rel.reg.t,rel.reg.Q
    columns=[]; lookup={}; witness=[]
    for name,lo,hi in rel.groups:
        width=(hi-lo).bit_length()
        for complement in (False,True):
            for bit in range(width):
                lookup[name,complement,bit]=len(columns)
                columns.append(dict(variable=name,complement=complement,bit=bit))
                if extended_binary_witness is not None:
                    poly=[]
                    for nm,i,l,h,w,start in rel.spec:
                        if nm==name:
                            idx=start+(width if complement else 0)+bit
                            poly.append(extended_binary_witness[2*idx])
                    witness.append(poly)
    rows=[[] for _ in range(6)]
    def add(row,col,poly,scale):
        rows[row].append((col,[(scale*x)%M for x in poly]))
    unit=[1]+[0]*(N-1)
    for col,desc in enumerate(columns):
        name,c,b=desc['variable'],desc['complement'],desc['bit']
        scale=1<<b
        group=next(i for i,g in enumerate(rel.groups) if g[0]==name)
        add(2+group,col,unit,scale)
        if c: continue
        if name=='s':
            add(0,col,rel.reg.a,t*scale); add(1,col,rel.ct[1],t*scale)
        elif name=='e_pk': add(0,col,unit,t*scale)
        elif name=='m': add(1,col,unit,-Q*scale)
        elif name=='eta': add(1,col,unit,-scale)
    targets=[rel.target[i*N:(i+1)*N] for i in range(6)]
    return dict(degree=N,modulus=M,shape=(6,len(columns)),columns=columns,rows=rows,
                target=targets,witness=witness if extended_binary_witness is not None else None)


def check_compiled(compiled):
    """Independent sparse polynomial matrix multiplication for compiler testing."""
    N,M=compiled['degree'],compiled['modulus']
    result=[]
    for row in compiled['rows']:
        out=[0]*N
        for col,poly in row:
            product=bfv.negacyclic_mul(poly,compiled['witness'][col])[0]
            out=[(x+y)%M for x,y in zip(out,product)]
        result.append(out)
    return result==compiled['target']
