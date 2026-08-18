# Does linear-layer DENSITY destroy leading-term coprimality (=> not FreeLunch)?
# Jarvis (sparse affine) died to Groebner; Rescue/Vision (dense MDS) survive.
# Prediction: full inverse layer + SPARSE linear (permutation) => coprime LMs (modelable);
#             full inverse layer + DENSE MDS => LMs share MDS top var (not modelable).
import time
from sympy import symbols, groebner, Poly
exec(open('dbd_ideal_degree.py').read().split('def report')[0])

def bobbin_layer(t,R,linear):  # linear in {'mds','perm','identity'}
    if linear=='mds': M=mds(t)
    elif linear=='perm': M=[[1 if j==(i+1)%t else 0 for j in range(t)] for i in range(t)]  # cyclic shift (sparse, invertible)
    else: M=[[1 if i==j else 0 for j in range(t)] for i in range(t)]
    c=[[(5*r+2*i+1)%P for i in range(t)] for r in range(R)]
    gens=[]; s0=list(symbols('s0_0:%d'%t)); gens+=s0
    eqs=[]; s=s0; allw=[]
    for r in range(R):
        y=list(symbols('y%d_0:%d'%(r,t))); allw+=y; gens+=y
        for i in range(t): eqs.append(s[i]*y[i]-1)
        My=matvec(M,y); s=[My[i]+c[r][i] for i in range(t)]
    return eqs,gens,allw

for linear in ['mds','perm']:
    for t,R in [(3,3),(4,3)]:
        eqs,gens,w=bobbin_layer(t,R,linear)
        sbox=[e for e in eqs if Poly(e,*gens,modulus=P).total_degree()==2]
        lms=[grevlex_LM(e,gens) for e in sbox]
        supp=[set(i for i,x in enumerate(m) if x>0) for _,m in lms]
        coprime=all(not(supp[i]&supp[j]) for i in range(len(supp)) for j in range(i+1,len(supp)))
        # count how many pairs collide
        collisions=sum(1 for i in range(len(supp)) for j in range(i+1,len(supp)) if supp[i]&supp[j])
        print("linear=%-4s t=%d R=%d: coprime_LM=%-5s collisions=%d/%d pairs"%(
            linear,t,R,str(coprime),collisions,len(supp)*(len(supp)-1)//2))
