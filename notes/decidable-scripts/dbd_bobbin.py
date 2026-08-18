# Bobbin's actual in-circuit witness: inverse S-box as x*y=1 (deg 2), full layer + MDS.
# Question: does the deg-2 witness give a coprime-leading-term (free) GB? pure powers?
import time
from sympy import symbols, groebner, Poly
exec(open('dbd_ideal_degree.py').read().split('def report')[0])  # helpers: grevlex_LM, mds, matvec, P

def bobbin(t,R):
    M=mds(t); c=[[(5*r+2*i+1)%P for i in range(t)] for r in range(R)]
    gens=[]; s0=list(symbols('s0_0:%d'%t)); gens+=s0
    eqs=[]; s=s0; allw=[]
    for r in range(R):
        y=list(symbols('y%d_0:%d'%(r,t))); allw+=y; gens+=y
        for i in range(t): eqs.append(s[i]*y[i]-1)   # inversion witness: y_i = 1/s_i, deg 2, coprime monomial s_i*y_i
        My=matvec(M,y); s=[My[i]+c[r][i] for i in range(t)]
    eqs.append(s0[0]); eqs.append(s[0])
    return eqs,gens,allw

for t,R in [(2,2),(2,3),(3,2)]:
    eqs,gens,w=bobbin(t,R)
    sbox=[e for e in eqs if Poly(e,*gens,modulus=P).total_degree()==2]
    t0=time.time()
    lms=[grevlex_LM(e,gens) for e in sbox]
    supp=[set(i for i,x in enumerate(m) if x>0) for _,m in lms]
    coprime=all(not(supp[i]&supp[j]) for i in range(len(supp)) for j in range(i+1,len(supp)))
    purepow=all(len(s)==1 for s in supp); tc=time.time()-t0
    t1=time.time(); G=groebner(eqs,*gens,order='grevlex',modulus=P); tg=time.time()-t1
    isone = (len(G.exprs)==1 and G.exprs[0]==1)
    print("BOBBIN xy=1  t=%d R=%d: coprime_LM=%s pure_power=%s  cert=%.4fs GB=%.3fs polys=%d %s"%(
        t,R,coprime,purepow,tc,tg,len(G.exprs), "(inconsistent CICO here)" if isone else ""))
    # sample leading monomials
    print("   sample S-box LMs:", [str(l) for l,_ in lms[:4]])
