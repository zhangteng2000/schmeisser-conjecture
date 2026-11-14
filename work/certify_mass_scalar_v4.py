"""One-dimensional Arb exclusion after the uniform polar mass lemma.

Uses the exact power-chord refinement for the lowest degrees.
Generation alone is not an independent verification.
"""
import argparse,gzip,hashlib,io,json,time
from pathlib import Path
from flint import arb,ctx
from mass_arb_helpers import interval,coeffs,polyval,panels,halfpower
ctx.prec=112

class Checker:
 def __init__(self,lo,hi,error_ratio=1.12):
  assert 3<=lo<=hi
  self.lo,self.hi=lo,hi
  self.threshold=(1+arb(hi)/2)**(arb(2)/hi)-1
  self.coef=coeffs(lo) if lo==hi<=128 else None
  self.errors=panels(hi,min(error_ratio,1.03) if lo<20 else error_ratio)
  aa=lo*(lo+1);bb=hi*(hi+1)
  self.kfactor=1+arb((bb-aa)**2)/(4*aa*bb)
  self.nfactor=1+arb((hi-lo)**2)/(4*(lo+1)*(hi+1))
 def setup(self,box,num=24576):
  u=interval(*box)
  if u<self.threshold:return True
  u=u.max(self.threshold).intersection(interval(0,1))
  if u.contains(0):return None
  e=(1-u).nonnegative_part();kap=arb(num)/(4096*self.hi);h=kap*e/u;D=u+h;b=u+h/2
  mt=(1-kap*kap*e/(4*u*u*D)).nonnegative_part().min(1)
  m=e*mt;te=kap/(2*u*D)
  return u,e,h,D,b,mt,m,te,kap
 def error(self,d):
  u,e,h,D,b,mt,m,te,kap=d;lo,hi=self.lo,self.hi
  ans=40*arb(lo)/(3*(lo-1)*(lo+3)*u*u)
  if self.coef is not None:
   finite=sum((aa*halfpower(u,k)*halfpower(e,k-2)*polyval(poly,e) for k,aa,poly in self.coef),arb(0))
   ans=ans.min(finite)
  z=e/u
  if z<1:
   K=min(10,lo);v=arb(1)/(lo-1)
   for k in range(3,K+1):v+=halfpower(arb(k-1)/(lo-1),k)*halfpower(z,k-2)
   if hi>K:v+=halfpower(z,K-1)/(1-z.nonnegative_part().sqrt())
   ans=ans.min(v/(u*u))
  for aa in ['1/2','1/4','1/16','3/4']:
   a=arb(aa);beta=(1-u*a*(2-a)).nonnegative_part();da=(1-u*a).nonnegative_part()
   front=40*arb(lo)/(3*(lo-1)*(lo+3)*(2-a)**3*u*u)
   old=arb('5/6')*(1-a)*u*self.kfactor*(lo*(lo+1)*halfpower(beta,lo-3)).max(hi*(hi+1)*halfpower(beta,hi-3))
   tail=old
   if e>0:
    raw=(1-a)*self.nfactor*((lo+1)*(halfpower(beta,lo)+da**lo)).max((hi+1)*(halfpower(beta,hi)+da**hi))/e
    tail=tail.min(raw)
   ans=ans.min(front+tail)
  return ans
 def riemann(self,d):
  u,e=d[:2];lo,hi=self.lo,self.hi;out=arb(0)
  for a,b in self.errors:
   beta=(1-u*a*(2-a)).nonnegative_part();da=(1-u*a).nonnegative_part();db=1-u*b
   val=None
   if db>0:
    val=arb('5/6')*u*b*b/db*self.kfactor*(lo*(lo+1)*halfpower(beta,lo-1)).max(hi*(hi+1)*halfpower(beta,hi-1))
   if e>0:
    raw=self.nfactor*((lo+1)*(halfpower(beta,lo)+da**lo)).max((hi+1)*(halfpower(beta,hi)+da**hi))/e
    val=raw if val is None else val.min(raw)
   if val is None:return None
   out+=(b-a)*val
  return out
 def moment(self,d):
  u,e,h,D,b,mt,m,te,kap=d
  if not self.lo*b*b/D>=90:return None
  return kap/(2*u*u*b)-arb('11/10')*mt*D/(self.lo*b**3)-(self.hi+1)*te*halfpower(e,self.lo)
 def base_three(self,d):
  u,e,h,D,b,mt,m,te,kap=d;values=[];mesh=16
  for k in range(mesh+1):
   x=arb(k)/mesh
   if k==0:v=arb(0)
   elif k==mesh:v=e.sqrt()
   else:
    A=x*(2-x)-kap/u*x*(1-x)
    Q=(1-2*u*x+u*x*x-h*x*(1-x)).nonnegative_part()
    v=e*A/(Q.sqrt()+1-x)
   values.append(v)
  V=(values[0]+values[-1]+2*sum(values[1:-1],arb(0)))/mesh
  return 1/u+te*(1-halfpower(e,3))-arb('3/2')*mt*(1+V)
 def recurrence(self,d,steps):
  u,e,h,D,b,mt,m,te,kap=d;lo,hi=self.lo,self.hi
  steps=min(steps,(lo-2)//2);rl=lo-2*steps;rh=hi-2*steps
  if lo==hi and rl==2:value=1/u-2+kap/(2*u)
  elif lo==hi and rl==3:value=self.base_three(d)
  else:
   value=1/u-rh
   if e>0:value=value.max(-1/(u*e))
   if e<=arb('1/4'):value=value.max(1/u-3)
  correction=kap*kap*e/(4*u**3*D)
  for j in range(steps-1,-1,-1):
   nl,nh=lo-2*j,hi-2*j
   ac=(arb(nh)/(nh-1)).union(arb(nl)/(nl-1))
   ep=halfpower(e,nl).union(halfpower(e,nh))
   value=-1/(interval(nl-1,nh-1)*u)+ac*correction+te*(1-ep)+ac*m*value
  return value
 def polar_candidate(self,d,num):
  if num==24576:return True
  u,e,h,D,b,mt,m,te,kap=d
  if not(h>0 and h<=1 and kap/u<=4):return False
  values=[]
  for N in [self.lo,self.hi]:
   values.append(2*(halfpower(1+h*u,N+2)-halfpower(1-h,N+2))/((N+2)*h*(1+u)))
  return values[0].max(values[1])<1
 def attempt(self,d):
  u,e=d[:2];err=self.error(d);remainder=e**self.lo/u
  candidates=[]
  j=self.moment(d)
  if j is not None:
   candidates.append(('moment',j))
   if j>err+remainder:return 'moment_0'
  used=set()
  for k in [8,16,32,64,128,256]:
   k=min(k,(self.lo-2)//2)
   if k in used:continue
   used.add(k);j=self.recurrence(d,k);candidates.append((str(k),j))
   if j>err+remainder:return f'{k}_0'
  alternate=self.riemann(d)
  if alternate is not None:
   err=err.min(alternate)
   for name,j in candidates:
    if j>err+remainder:return name+'_1'
  return None

 def check(self,box):
  d=self.setup(box)
  if d is True:return 'threshold'
  if d is None:return None
  if self.lo==self.hi==3 and d[1]<=arb('1/100'):return 'local_N3'
  why=self.attempt(d)
  if why:return '24576:'+why
  if self.lo==self.hi<20:
   low,high=24576,4*self.hi*4096
   while high-low>1:
    middle=(low+high)//2;dd=self.setup(box,middle)
    if self.polar_candidate(dd,middle):low=middle
    else:high=middle
   if low>24576:
    dd=self.setup(box,low)
    if self.polar_candidate(dd,low):
     why=self.attempt(dd)
     if why:return str(low)+':'+why
  return None

def run(lo,hi,limit=200000,quiet=False,folder='mass_scalar_v4_pilot'):
 start=time.time();c=Checker(lo,hi);dest=Path('work')/folder;dest.mkdir(exist_ok=True)
 source=Path(__file__);deps=[Path('work/mass_arb_helpers.py')]
 header=dict(format='mass-scalar-tree-v4',N_range=[lo,hi],precision_bits=ctx.prec,u_edges=[0.0.hex(),1.0.hex()],error_panels=[[float(a).hex(),float(b).hex()] for a,b in c.errors],source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),dependencies={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in deps})
 cert=dest/f'N_{lo}_{hi}.tree.gz';stack=[(0.,1.)];nodes=leaves=0;counts={};unresolved=[]
 with gzip.open(cert,'wt',encoding='utf8',newline='\n') as f:
  f.write(json.dumps(header,separators=(',',':'))+'\n')
  while stack and nodes<limit and not unresolved:
   box=stack.pop();nodes+=1;why=c.check(box)
   if why:
    leaves+=1;counts[why]=counts.get(why,0)+1;f.write('L '+why+'\n')
   else:
    a,b=box;mid=(a+b)/2
    if not a<mid<b:unresolved.append(box);f.write('U\n')
    else:f.write('S '+mid.hex()+'\n');stack.extend([(mid,b),(a,mid)])
  f.write('END\n' if not stack and not unresolved else 'INCOMPLETE\n')
 result=dict(PASS=not stack and not unresolved,N_range=[lo,hi],nodes=nodes,leaves=leaves,pending=len(stack),unresolved=unresolved,counts=counts,seconds=time.time()-start,certificate=cert.as_posix(),certificate_sha256=hashlib.sha256(cert.read_bytes()).hexdigest(),source_sha256=header['source_sha256'],dependencies=header['dependencies'])
 (dest/f'N_{lo}_{hi}.json').write_text(json.dumps(result,indent=2))
 if not quiet:print(json.dumps(result),flush=True)
 return result

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--lo',type=int,required=True);ap.add_argument('--hi',type=int);ap.add_argument('--limit',type=int,default=200000);ap.add_argument('--folder',default='mass_scalar_v4_pilot');a=ap.parse_args()
 run(a.lo,a.hi or a.lo,a.limit,folder=a.folder)
