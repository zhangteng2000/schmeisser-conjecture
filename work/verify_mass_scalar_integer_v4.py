"""Independent pure-integer replay of the one-dimensional mass certificates.

The arithmetic kernel was extracted unchanged from the audited v5 kernel.
No Arb module or certificate-generator module is imported.
"""
import argparse,gzip,hashlib,json,time
from pathlib import Path
from mass_integer_arithmetic import I,P,S,threshold,esp_coefficients,polynomial

class Checker:
 def __init__(self,h):
  self.lo,self.hi=h['N_range'];assert 3<=self.lo<=self.hi
  self.t=threshold(self.hi)
  self.coef=esp_coefficients(self.lo) if self.lo==self.hi<=128 else None
  self.errors=[];previous=0
  for av,bv in h['error_panels']:
   a,b=I(float.fromhex(av)),I(float.fromhex(bv))
   assert a.l==a.h==previous and b.l==b.h and a.h<b.l
   self.errors.append((a,b));previous=b.h
  assert self.errors and previous==S
  aa=self.lo*(self.lo+1);bb=self.hi*(self.hi+1)
  self.kfactor=1+I((bb-aa)**2)/(4*aa*bb)
  self.nfactor=1+I((self.hi-self.lo)**2)/(4*(self.lo+1)*(self.hi+1))
 def setup(self,box,num=24576):
  u=I.box(*box)
  if u<self.t:return True
  u=u.floor(self.t).meet(I.box(0,1))
  if u.zero():return None
  e=(1-u).positive();kap=I(num)/(4096*self.hi);h=kap*e/u;D=u+h;b=u+h/2
  mt=(1-kap*kap*e/(4*u*u*D)).positive().cap(1)
  m=e*mt;te=kap/(2*u*D)
  return u,e,h,D,b,mt,m,te,kap
 def error(self,d):
  u,e,h,D,b,mt,m,te,kap=d;lo,hi=self.lo,self.hi
  ans=I(40*lo)/(3*(lo-1)*(lo+3)*u*u)
  if self.coef is not None:
   finite=sum((aa*u.half(k)*e.half(k-2)*polynomial(poly,e) for k,aa,poly in self.coef),I(0))
   ans=ans.cap(finite)
  z=e/u
  if z<1:
   K=min(10,lo);v=I(1)/(lo-1)
   for k in range(3,K+1):v+=(I(k-1)/(lo-1)).half(k)*z.half(k-2)
   if hi>K:v+=z.half(K-1)/(1-z.positive().sqrt())
   ans=ans.cap(v/(u*u))
  for av in ['1/2','1/4','1/16','3/4']:
   a=I(av);beta=(1-u*a*(2-a)).positive();da=(1-u*a).positive()
   front=I(40*lo)/(3*(lo-1)*(lo+3)*(2-a)**3*u*u)
   old=I('5/6')*(1-a)*u*self.kfactor*(lo*(lo+1)*beta.half(lo-3)).floor(hi*(hi+1)*beta.half(hi-3))
   tail=old
   if e>0:
    raw=(1-a)*self.nfactor*((lo+1)*(beta.half(lo)+da**lo)).floor((hi+1)*(beta.half(hi)+da**hi))/e
    tail=tail.cap(raw)
   ans=ans.cap(front+tail)
  return ans
 def riemann(self,d):
  u,e=d[:2];lo,hi=self.lo,self.hi;out=I(0)
  for a,b in self.errors:
   beta=(1-u*a*(2-a)).positive();da=(1-u*a).positive();db=1-u*b
   val=None
   if db>0:
    val=I('5/6')*u*b*b/db*self.kfactor*(lo*(lo+1)*beta.half(lo-1)).floor(hi*(hi+1)*beta.half(hi-1))
   if e>0:
    raw=self.nfactor*((lo+1)*(beta.half(lo)+da**lo)).floor((hi+1)*(beta.half(hi)+da**hi))/e
    val=raw if val is None else val.cap(raw)
   if val is None:return None
   out+=(b-a)*val
  return out
 def moment(self,d):
  u,e,h,D,b,mt,m,te,kap=d
  if not self.lo*b*b/D>=90:return None
  return kap/(2*u*u*b)-I('11/10')*mt*D/(self.lo*b**3)-(self.hi+1)*te*e.half(self.lo)
 def base_three(self,d):
  u,e,h,D,b,mt,m,te,kap=d;values=[];mesh=16
  for k in range(mesh+1):
   x=I(k)/mesh
   if k==0:v=I(0)
   elif k==mesh:v=e.sqrt()
   else:
    A=x*(2-x)-kap/u*x*(1-x)
    Q=(1-2*u*x+u*x*x-h*x*(1-x)).positive()
    v=e*A/(Q.sqrt()+1-x)
   values.append(v)
  V=(values[0]+values[-1]+2*sum(values[1:-1],I(0)))/mesh
  return 1/u+te*(1-e.half(3))-I('3/2')*mt*(1+V)
 def recurrence(self,d,steps):
  u,e,h,D,b,mt,m,te,kap=d;lo,hi=self.lo,self.hi
  assert 0<=steps<=(lo-2)//2
  rl,rh=lo-2*steps,hi-2*steps
  if lo==hi and rl==2:value=1/u-2+kap/(2*u)
  elif lo==hi and rl==3:value=self.base_three(d)
  else:
   value=1/u-rh
   if e>0:value=value.floor(-1/(u*e))
   if e<=I('1/4'):value=value.floor(1/u-3)
  correction=kap*kap*e/(4*u**3*D)
  for j in range(steps-1,-1,-1):
   nl,nh=lo-2*j,hi-2*j
   ac=(I(nh)/(nh-1)).hull(I(nl)/(nl-1))
   ep=e.half(nl).hull(e.half(nh))
   value=-1/(I.box(nl-1,nh-1)*u)+ac*correction+te*(1-ep)+ac*m*value
  return value
 def polar_candidate(self,d,num):
  if num==24576:return True
  u,e,h,D,b,mt,m,te,kap=d
  if not(h>0 and h<=1 and kap/u<=4):return False
  values=[]
  for N in [self.lo,self.hi]:
   values.append(2*((1+h*u).half(N+2)-(1-h).half(N+2))/((N+2)*h*(1+u)))
  return values[0].floor(values[1])<1
 def check(self,box,reason):
  if reason in ('threshold','local_N3'):num=24576
  else:
   prefix,reason=reason.split(':',1);num=int(prefix);assert num>=24576
  d=self.setup(box,num)
  if d is True:return True
  if d is None:return False
  if reason=='threshold':return False
  u,e=d[:2]
  if reason=='local_N3':return self.lo==self.hi==3 and e<=I('1/100')
  if not self.polar_candidate(d,num):return False
  method,flag=reason.rsplit('_',1);assert flag in ('0','1')
  err=self.error(d)
  if flag=='1':
   extra=self.riemann(d)
   if extra is not None:err=err.cap(extra)
  j=self.moment(d) if method=='moment' else self.recurrence(d,int(method))
  return j is not None and j>err+e**self.lo/u

def verify(path,quiet=False):
 assert __debug__
 path=Path(path);start=time.time();nodes=leaves=0;counts={}
 with gzip.open(path,'rt',encoding='utf8') as f:
  h=json.loads(next(f));assert h['format']=='mass-scalar-tree-v4'
  edges=[float.fromhex(v) for v in h['u_edges']]
  assert edges[0]==0 and edges[-1]==1 and all(a<b for a,b in zip(edges,edges[1:]))
  stack=list(zip(edges,edges[1:]));c=Checker(h)
  for line in f:
   parts=line.strip().split()
   if parts==['END']:
    assert not stack and not f.read().strip();break
   assert stack and parts;box=stack.pop();nodes+=1
   if parts[0]=='S':
    assert len(parts)==2;mid=float.fromhex(parts[1]);a,b=box;assert a<mid<b
    stack.extend([(mid,b),(a,mid)])
   else:
    assert parts[0]=='L' and len(parts)==2
    try:ok=c.check(box,parts[1])
    except ZeroDivisionError:ok=False
    if not ok:return dict(PASS=False,N_range=h['N_range'],node=nodes,box=box,reason=parts[1],seconds=time.time()-start)
    leaves+=1;counts[parts[1]]=counts.get(parts[1],0)+1
  else:raise ValueError('missing END')
 result=dict(PASS=True,N_range=h['N_range'],nodes=nodes,leaves=leaves,counts=counts,seconds=time.time()-start,precision_bits=P,certificate=path.as_posix(),certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),arithmetic_dependency_sha256=hashlib.sha256(Path(__file__).with_name('mass_integer_arithmetic.py').read_bytes()).hexdigest())
 out=path.with_name(path.name.replace('.tree.gz','.integer.json'));out.write_text(json.dumps(result,indent=2))
 if not quiet:print(json.dumps(result),flush=True)
 return result

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('path');a=ap.parse_args();verify(a.path)
