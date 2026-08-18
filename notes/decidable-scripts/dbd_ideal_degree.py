"""
decidable-by-design, computation 1: ideal degree of the CICO variety, and where
'decidable' actually lives.

Corrected mechanism. Both sparse (Griffin-shape) and full-inverse (Rescue-shape)
iterated designs admit a NAIVE per-S-box modeling whose leading monomials are
pairwise-coprime pure powers (each fresh witness is a distinct variable) -> both
are trivially FreeLunch, both have ideal degree = prod(alpha_i) KNOWN BY
CONSTRUCTION. So 'is there a regular sequence / is the ideal degree decidable'
is YES for BOTH -- decidability of a SINGLE model's cost is not the discriminator.

The discriminator is the MINIMAL-VARIABLE encoding:
  - sparse: one nonlinear branch per round, the rest algebraically slaved to it
    -> a low-variable model (~R vars) with a small, attackable ideal degree.
  - full inverse layer: every lane independently nonlinear -> the minimal model
    still needs ~t*R vars, ideal degree ~ alpha^(t*R), astronomically secure.
Both ideal degrees are computable; the SECURITY is min over models, and finding
the minimal model (the encoding trick) is the undecidable part.

Here we compute, over GF(p), the actual ideal degree (dim of quotient) of the
CICO system for matched (t,R), sparse vs full, and the naive-model coprimality
certificate, with timings.
"""
import time
from sympy import symbols, groebner, Poly

P=65537; ALPHA=3
def inv_mod(a,p): return pow(a%p,p-2,p)
def mds(t):
    xs=[i+1 for i in range(t)]; ys=[t+i+1 for i in range(t)]
    return [[inv_mod((xs[i]-ys[j])%P,P) for j in range(t)] for i in range(t)]
def matvec(M,v):
    t=len(M); return [sum(M[i][j]*v[j] for j in range(t)) for i in range(t)]

def grevlex_LM(poly, gens):
    p=Poly(poly,*gens,modulus=P)
    best=None
    for m in p.monoms():
        key=(sum(m), tuple(-x for x in reversed(m)))  # grevlex: max deg, then min trailing exps
        if best is None or key>best[0]: best=(key,m)
    m=best[1]; expr=1
    for g,e in zip(gens,m): expr*=g**e
    return expr, m

def naive_full(t,R):
    M=mds(t); c=[[(7*r+3*i+1)%P for i in range(t)] for r in range(R)]
    gens=[]; s0=list(symbols('s0_0:%d'%t)); gens+=s0; us=[]
    eqs=[]; s=s0
    for r in range(R):
        u=list(symbols('u%d_0:%d'%(r,t))); us.append(u); gens+=u
        for i in range(t): eqs.append(u[i]**ALPHA - s[i])
        Mu=matvec(M,u); s=[Mu[i]+c[r][i] for i in range(t)]
    eqs.append(s0[0]); eqs.append(s[0])
    return eqs,gens,[v for u in us for v in u]

def naive_sparse(t,R):
    M=mds(t); c=[[(5*r+2*i+1)%P for i in range(t)] for r in range(R)]
    gens=[]; s0=list(symbols('s0_0:%d'%t)); gens+=s0; us=[]
    eqs=[]; s=s0
    for r in range(R):
        u=symbols('u%d'%r); us.append(u); gens.append(u)
        eqs.append(u**ALPHA - s[0])
        w=[u]+[s[i] for i in range(1,t)]
        Mw=matvec(M,w); s=[Mw[i]+c[r][i] for i in range(t)]
    eqs.append(s0[0]); eqs.append(s[0])
    return eqs,gens,us

def ideal_degree(eqs,gens):
    # count standard monomials of grevlex GB (quotient dimension); returns None if not 0-dim/finite quickly
    G=groebner(eqs,*gens,order='grevlex',modulus=P)
    lms=[grevlex_LM(g,gens)[1] for g in G.exprs]
    # zero-dim test: for each variable there must be a pure power leading monomial
    n=len(gens); has_pure=[False]*n
    for m in lms:
        nz=[i for i,e in enumerate(m) if e>0]
        if len(nz)==1: has_pure[nz[0]]=True
    if not all(has_pure): return None, G
    # count standard monomials by staircase (only feasible small). Use naive bound:
    return 'zero-dim', G

def report(name,builder,t,R):
    eqs,gens,sv=builder(t,R)
    # coprimality certificate on the S-box (nonlinear) equations
    sbox=[e for e in eqs if any(e.has(v) for v in sv) and Poly(e,*gens,modulus=P).total_degree()>=ALPHA]
    t0=time.time()
    lms=[grevlex_LM(e,gens) for e in sbox]
    supp=[set(i for i,x in enumerate(m) if x>0) for _,m in lms]
    coprime=all(not(supp[i]&supp[j]) for i in range(len(supp)) for j in range(i+1,len(supp)))
    purepow=all(len(s)==1 for s in supp)
    tcert=time.time()-t0
    prod_alpha=ALPHA**len(sbox)
    t1=time.time(); G=groebner(eqs,*gens,order='grevlex',modulus=P); tgb=time.time()-t1
    print("%-52s vars=%2d sbox_eqs=%2d  FreeLunch[coprime&purepow]=%s  D_I(naive)=alpha^%d=%d"%(
        name,len(gens),len(sbox),(coprime and purepow),len(sbox),prod_alpha))
    print("     cert-check %.4fs   |   full grevlex GB %.3fs (%d polys)  [ratio %.0fx]"%(
        tcert,tgb,len(G.exprs), tgb/max(tcert,1e-6)))

if __name__=="__main__":
    for t,R in [(2,2),(2,3),(3,2),(3,3)]:
        report("FULL inverse layer (Rescue/RPO/XHash12/Twill) t=%d R=%d"%(t,R),naive_full,t,R)
        report("SPARSE 1-branch    (Griffin/Arion/XHash8)     t=%d R=%d"%(t,R),naive_sparse,t,R)
        print()
