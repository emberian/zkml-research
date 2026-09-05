# Verify the reviewer's toy RMFE over R = Z/2^k, S = R[u]/(u^3+u+1):
#   phi(a,b) = a + (b-a)u  ;  psi(c0+c1u+c2u^2) = (c0, c0+c1+c2)
# Claim: degree-2 RMFE (psi(phi(x)phi(y)) = x*y componentwise), degree-3 fails.
import itertools
k=4; M=2**k
def mul(p,q):
    # multiply in R[u]/(u^3+u+1): u^3 = -u - 1
    r=[0]*5
    for i in range(3):
        for j in range(3):
            r[i+j]=(r[i+j]+p[i]*q[j])%M
    # reduce u^4 = u*u^3 = -u^2 - u ; u^3 = -u -1
    c4=r[4]; r[2]=(r[2]-c4)%M; r[1]=(r[1]-c4)%M; r[4]=0
    c3=r[3]; r[1]=(r[1]-c3)%M; r[0]=(r[0]-c3)%M; r[3]=0
    return r[:3]
def phi(a,b): return [a%M,(b-a)%M,0]
def psi(c): return ((c[0])%M, (c[0]+c[1]+c[2])%M)
ok2=True; fail3=0; tot3=0
vals=range(M)
for a1,b1,a2,b2 in itertools.product(vals,repeat=4):
    if psi(mul(phi(a1,b1),phi(a2,b2)))!=((a1*a2)%M,(b1*b2)%M): ok2=False
print("degree-2 RMFE holds for all inputs over Z/%d:"%M, ok2)
import random
random.seed(1)
for _ in range(2000):
    a=[random.randrange(M) for _ in range(6)]
    tot3+=1
    got=psi(mul(mul(phi(a[0],a[1]),phi(a[2],a[3])),phi(a[4],a[5])))
    want=((a[0]*a[2]*a[4])%M,(a[1]*a[3]*a[5])%M)
    if got!=want: fail3+=1
print("degree-3: %d/%d random triples FAIL"%(fail3,tot3))
# explicit counterexample: x=y=z=(0,1): phi=u ; u^3 = -u-1 -> psi = (-1, -1-1) = (M-1, M-2) vs want (0,1)
print("explicit u^3 case: psi(u^3) =", psi(mul(mul(phi(0,1),phi(0,1)),phi(0,1))), "want (0,1)")
# check irreducibility of u^3+u+1 mod 2 (no roots in F2) -> S = GR(2^k,3)
print("u^3+u+1 mod 2 roots:", [x for x in (0,1) if (x**3+x+1)%2==0], "(none => irreducible over F2, S = GR(2^k,3))")
