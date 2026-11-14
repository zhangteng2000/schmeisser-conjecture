"""Arb helpers for the scalar certificate generator."""
import math
from flint import arb

def interval(lo,hi):
 # The binary endpoints are exact Arb inputs. Let Arb take the hull;
 # forming a floating midpoint/radius could lose a boundary endpoint.
 return arb(lo).union(arb(hi))


def coeffs(N):
 newton=[arb(0)]*(N+1);newton[0]=arb(1)
 out=[]
 for k in range(2,N+1):
  newton[k]=sum((arb(N)*arb(N-1)**(arb(j-2)/2)*newton[k-j] for j in range(2,k+1)),arb(0))/k
  schoen=arb(math.comb(N,k))*arb(f'{k-1}/{N-1}')**(arb(k)/2)
  saddle=arb(N**N)/arb(k**k*(N-k)**(N-k)) if k<N else arb(1)
  if k==N:saddle=arb(1)
  # At k=N the saddle coefficient is exactly 1.
  A=schoen.min(saddle.sqrt()).min(newton[k])
  out.append((k,A/math.comb(N,k),[math.comb(k+j,k) for j in range(N-k+1)]))
 return out


def polyval(coef,x):
 ans=arb(0)
 for c in reversed(coef):ans=ans*x+c
 return ans


def halfpower(x,N):
 x=x.nonnegative_part()
 return x**(arb(N)/2)


def panels(N,ratio=1.5):
 # Every stored float is used as an exact binary endpoint, and Arb forms
 # the midpoint/length. The panels therefore cover [0,1] without gaps.
 edges=[0.];a=2.**(-math.ceil(math.log2(max(64,16*N*N))))
 while a<.5:edges.append(a);a*=ratio
 edges.append(.5)
 edges+= [1-x for x in reversed(edges[:-1])]
 return [(arb(a),arb(b)) for a,b in zip(edges,edges[1:])]

