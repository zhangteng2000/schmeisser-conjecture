"""Exact outward-rounded integer interval arithmetic and ESP coefficients."""
import math
P=192
S=1<<P

def ceildiv(a,b):
 return -((-a)//b)


class I:
 __slots__=('l','h')
 def __init__(self,a=0,b=None,raw=False):
  if raw:self.l=a;self.h=a if b is None else b
  elif isinstance(a,I):self.l=a.l;self.h=a.h
  elif isinstance(a,int):self.l=self.h=a*S
  elif isinstance(a,str) and '/' in a:
   n,d=map(int,a.split('/'));self.l=n*S//d;self.h=ceildiv(n*S,d)
  elif isinstance(a,float):
   n,d=a.as_integer_ratio();self.l=n*S//d;self.h=ceildiv(n*S,d)
  else:raise TypeError(type(a))
  assert self.l<=self.h
 @staticmethod
 def box(a,b):
  x=I(a);y=I(b);return I(x.l,y.h,raw=True)
 def __add__(self,y):
  y=I(y);return I(self.l+y.l,self.h+y.h,raw=True)
 __radd__=__add__
 def __neg__(self):return I(-self.h,-self.l,raw=True)
 def __sub__(self,y):return self+-I(y)
 def __rsub__(self,y):return I(y)+-self
 def __mul__(self,y):
  y=I(y);p=(self.l*y.l,self.l*y.h,self.h*y.l,self.h*y.h)
  return I(min(p)//S,ceildiv(max(p),S),raw=True)
 __rmul__=__mul__
 def __truediv__(self,y):
  y=I(y)
  if y.l<=0<=y.h:raise ZeroDivisionError
  if y.h<0:return (-self)/(-y)
  vals=[(a*S,b) for a in (self.l,self.h) for b in (y.l,y.h)]
  return I(min(a//b for a,b in vals),max(ceildiv(a,b) for a,b in vals),raw=True)
 def __rtruediv__(self,y):return I(y)/self
 def __pow__(self,n):
  assert isinstance(n,int) and n>=0
  if n==0:return I(1)
  if self.l>=0:
   ol=oh=S;al,ah=self.l,self.h
   while n:
    if n&1:ol=ol*al//S;oh=ceildiv(oh*ah,S)
    n//=2
    if n:al=al*al//S;ah=ceildiv(ah*ah,S)
   return I(ol,oh,raw=True)
  if self.h<=0:
   out=(-self)**n;return -out if n%2 else out
  if n%2:
   lo=I(-self.l,raw=True)**n;hi=I(self.h,raw=True)**n
   return I(-lo.h,hi.h,raw=True)
  hi=I(max(-self.l,self.h),raw=True)**n
  return I(0,hi.h,raw=True)
 def sqrt(self):
  assert self.l>=0
  a=math.isqrt(self.l*S);b=math.isqrt(self.h*S)
  if b*b<self.h*S:b+=1
  return I(a,b,raw=True)
 def half(self,n):
  x=self.positive()
  return (x**(n//2))*(x.sqrt() if n%2 else 1)
 def positive(self):return I(max(0,self.l),max(0,self.h),raw=True)
 def cap(self,y):
  y=I(y);return I(min(self.l,y.l),min(self.h,y.h),raw=True)
 def floor(self,y):
  y=I(y);return I(max(self.l,y.l),max(self.h,y.h),raw=True)
 def meet(self,y):
  y=I(y);l=max(self.l,y.l);h=min(self.h,y.h)
  if l>h:raise ValueError('empty intersection')
  return I(l,h,raw=True)
 def hull(self,y):
  y=I(y);return I(min(self.l,y.l),max(self.h,y.h),raw=True)
 def __lt__(self,y):return self.h<I(y).l
 def __le__(self,y):return self.h<=I(y).l
 def __gt__(self,y):return self.l>I(y).h
 def __ge__(self,y):return self.l>=I(y).h
 def zero(self):return self.l<=0<=self.h
 def __repr__(self):return f'I({self.l}/{S},{self.h}/{S})'


def threshold(N):
 # floor(S*((N+2)/2)^(2/N)) computed by one exact integer root.
 target=((N+2)**2 << (P*N))//4
 # Floating arithmetic selects an initial guess only. Exact integer
 # inequalities validate both the starting side and the final root.
 z=int(math.exp(math.log((N+2)/2)*2/N)*S)+(1<<(P-45))
 while z**N<target:z+=1<<(P-45)
 while True:
  y=((N-1)*z+target//z**(N-1))//N
  if y>=z:break
  z=y
 assert z**N<=target<(z+1)**N
 return I(z-S,z+1-S,raw=True)


def polynomial(a,x):
 v=I(0)
 for c in a[::-1]:v=v*x+c
 return v


def esp_coefficients(N):
 # Three independent standard ESP bounds, combined coefficientwise.
 newton=[I(0) for _ in range(N+1)];newton[0]=I(1)
 result=[]
 for k in range(2,N+1):
  newton[k]=sum((N*I(N-1).half(j-2)*newton[k-j] for j in range(2,k+1)),I(0))/k
  comb=math.comb(N,k)
  sch=comb*(I(k-1)/(N-1)).half(k)
  den=k**k*(N-k)**(N-k) if k<N else N**N
  cau=(I(N**N)/den).sqrt()
  aa=sch.cap(cau).cap(newton[k])/comb
  result.append((k,aa,[math.comb(k+j,k) for j in range(N-k+1)]))
 return result

