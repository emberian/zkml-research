"""Literal bigint model of fhe-math 0.1.1 RnsScaler, separate from ideal rounding."""
from math import prod
M256=(1<<256)-1
M128=(1<<128)-1

def project_theta(value,n,d,round_up):
    rounded=(n*value+d//2)//d
    theta=(n*value)%d
    sign=d>1 and (theta>d//2 if d%2 else theta>=d//2)
    if sign: theta=d-theta
    # Both signs are retained exactly; match source's asymmetric rational rounding.
    ceil=(not sign) if round_up else sign
    fixed=((theta<<127)+(d-1 if ceil else 0))//d
    return rounded,(-fixed if sign else fixed)

class ScalerModel:
    def __init__(self,base,to,n,d):
        self.base=base;self.to=to;self.M=prod(base);self.n=n;self.d=d
        self.garner=[(self.M//q)*pow(self.M//q,-1,q) for q in base]
        self.gamma,self.tgamma=project_theta(self.M,n,d,False)
        data=[project_theta(g,n,d,True) for g in self.garner]
        self.omega=[x[0] for x in data];self.tomega=[x[1] for x in data]
        self.shift=min(127,min(191-(q*len(base)-1).bit_length() for q in base))
        self.tgarner=[((g<<self.shift)+self.M//2)//self.M for g in self.garner]
    def scale(self,rests):
        acc=sum(r*g for r,g in zip(rests,self.tgarner))&M256
        v=((acc>>(self.shift-1))&M128)
        v=(v+1)//2
        w=0;sign=False;true_acc=0
        if self.n!=self.d:
            true_acc=sum(r*th for r,th in zip(rests,self.tomega))-v*self.tgamma
            acc=true_acc&M256
            sign=(acc>>191)>0
            if sign:
                w=((((~acc&M256)>>126)&M128)+1)//2
            else:
                w=(((acc>>126)&M128)+1)//2
        signedw=-w if sign else w
        y=sum(r*om for r,om in zip(rests,self.omega))-v*self.gamma+signedw
        return [y%q for q in self.to],dict(v=v,w=signedw,integer=y,
            selected_lift=sum(r*g for r,g in zip(rests,self.garner))-v*self.M,
            theta_acc=true_acc)

def ideal_center(x,m):
    x%=m
    return x if 2*x<m else x-m

def ideal_scale(x,m,n,d):
    return (n*ideal_center(x,m)+d//2)//d

if __name__=='__main__':
    qbase=[68719403009,68719230977,137438822401];q=prod(qbase)
    s=ScalerModel(qbase,[65537],1,1)
    for offset in range(-3,4):
        x=q//2+offset;out,d=s.scale([x%qi for qi in qbase]);
        print(offset,d['selected_lift']-ideal_center(x,q))
