"""A general fixed public projection basis, completed using identity rows."""
import hashlib,json
from pathlib import Path
P=28439893;D=577;R=16

def pivots(rows,p):
 a=[[int(v)%p for v in row] for row in rows];columns=[];rank=0
 for col in range(len(a[0])):
  pivot=next((i for i in range(rank,len(a)) if a[i][col]),None)
  if pivot is None:continue
  a[rank],a[pivot]=a[pivot],a[rank];z=pow(a[rank][col],-1,p);a[rank]=[(v*z)%p for v in a[rank]]
  for i in range(rank+1,len(a)):
   z=a[i][col]
   if z:a[i]=[(v-z*w)%p for v,w in zip(a[i],a[rank])]
  columns.append(col);rank+=1
  if rank==len(a):break
 return columns

def inverse(a,p):
 n=len(a);m=[[v%p for v in row]+[int(i==j) for j in range(n)] for i,row in enumerate(a)]
 for col in range(n):
  pivot=next(i for i in range(col,n) if m[i][col]);m[col],m[pivot]=m[pivot],m[col];z=pow(m[col][col],-1,p);m[col]=[(v*z)%p for v in m[col]]
  for i in range(n):
   if i==col:continue
   z=m[i][col]
   if z:m[i]=[(v-z*w)%p for v,w in zip(m[i],m[col])]
 return [row[n:] for row in m]

def center(v,p=P):
 v%=p;return v if v<=p//2 else v-p

class GeneralBasis:
 def __init__(self,registry):
  self.registry=registry;self.p=P;self.d=D;self.r=R
  if registry['dimension']!=D or registry['p']!=P or len(registry['queries'])!=R:raise ValueError('wrong fixed full-profile basis shape')
  self.rows=[q['vector'] for q in registry['queries']]
  if any(len(row)!=D or row[-1]!=0 or any(type(v) is not int or abs(v)>127 for v in row) for row in self.rows):raise ValueError('wrong fixed query vector')
  self.pivots=pivots(self.rows,P)
  if len(self.pivots)!=R or self.pivots!=registry['pivot_columns']:raise ValueError('query rows must have full rank and canonical pivots')
  self.rest=[i for i in range(D) if i not in self.pivots]
  if self.rest!=registry['identity_columns']:raise ValueError('noncanonical identity completion')
  self.inv=inverse([[row[j] for j in self.pivots] for row in self.rows],P)
  for i in range(R):
   for j in range(R):
    assert sum(self.inv[i][k]*self.rows[k][self.pivots[j]] for k in range(R))%P==int(i==j)
  self.bounds=[127*sum(abs(x) for x in row) for row in self.rows]
  if max(self.bounds)*2>=P//2:raise ValueError('fixed two-input signed score range does not fit p/2')
 def transform(self,x):
  if len(x)!=D:raise ValueError('wrong input dimension')
  return [center(sum(a*b for a,b in zip(row,x))) for row in self.rows]+[center(x[j]) for j in self.rest]
 def inverse(self,a):
  if len(a)!=D:raise ValueError('wrong transform dimension')
  x=[0]*D
  for i,j in enumerate(self.rest):x[j]=a[R+i]%P
  residual=[(a[i]-sum(row[j]*x[j] for j in self.rest))%P for i,row in enumerate(self.rows)]
  for i,j in enumerate(self.pivots):x[j]=sum(v*w for v,w in zip(self.inv[i],residual))%P
  return x

def load(path):
 path=Path(path);raw=path.read_bytes();return GeneralBasis(json.loads(raw)),hashlib.sha256(raw).hexdigest()
