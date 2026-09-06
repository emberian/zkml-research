"""Literal unsigned-word formulas transcribed from pinned fhe-math 0.1.1 source."""
def shoup(B,p,a,b,check=True):
 M=B*B;s=(((B*b)%M)//p)%B;q=((a*s)%M)//B
 if check:
  assert 0<=a<B and 0<=b<p and 2*p<B
  assert 0<=B*b<M and 0<=a*s<M and 0<=q*p<=a*b<M
 value=((a*b%M-q*p%M)%M)%B
 if check:assert 0<=value<2*p and value%p==a*b%p
 return value,s

def select(B,t,f,c):
 mask=(-int(c))%B;return ((t^f)&mask)^f

def reduce1(B,p,x,check=True):
 if check:assert 0<=x<2*p<B
 value=select(B,x,(x-p)%B,x<p)
 if check:assert value==x%p
 return value

def barrett(B,p,a,check=True):
 M=B*B;c=M//p;lo=c%B;hi=c//B;al=a%B;ah=a//B
 ll=((al*lo)%M)//B;hl=ah*lo%M;lh=al*hi%M;mid=(lh+hl+ll)%M
 q=(mid//B+(ah*hi)%M)%M
 if check:
  assert 1<p and 2*p<B and 0<=a<M
  assert lo+hi<B and all(0<=z<M for z in [al*lo,ah*lo,al*hi,ah*hi,lh+hl+ll,q])
  assert q==a*c//M and 0<=q*p<=a<M
 value=((a-(q*p)%M)%M)%B
 if check:assert 0<=value<2*p and value%p==a%p
 return value,mid
