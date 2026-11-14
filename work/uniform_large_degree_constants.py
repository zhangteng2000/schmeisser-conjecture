"""Exact finite constants for the new independent N>=6000 argument.

This audits numerical comparisons only. The analytic proof is in the
companion text, not formalized by this script.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import hashlib,json

checks=[]
def need(name,condition):
    if not condition:raise ValueError(name)
    checks.append(name)
def E(x,k):return sum((x**j/F(factorial(j)) for j in range(k+1)),F(0))
N0=6000
need('e<87/32 from the elementary series tail',F(1)+1+F(1,2)+F(1,6)+F(5,96)==F(87,32))
need('e^8<N0/2+1',F(87,32)**8<N0//2+1)
need('universal relaxed quadratic is nonnegative',F(87,32)**3<F(5,2)**4)
need('e>5/2 from a finite positive sum',E(F(1),3)>F(5,2))
need('coefficient exponential remainder',F(23,7)<4)
need('moment-series tail at Na=90',F(6*90**2)/F(5,2)**22<F(1,1000))
need('moment-series relative coefficient',1+F(8,90)+F(1,1000)<F(11,10))
need('Na>=90 in low-u case',F(3,2)*N0>90**2)
need('Na>=90 in high-u case',F(N0,2)>90)
need('second endpoint exponential lower bound',E(F(79,10),32)>2600)
need('second endpoint exponent',8-F(16,N0)>F(79,10))
need('second endpoint normalized contribution <1/20',F(128)*(1+F(1,N0))/2600<F(1,20))
need('second endpoint maximum is at t=16',F(2,16)<F(1,2)-F(1,N0))
need('center remainder <1/1000',F(16,2**16)<F(1,1000))
need('low-u b bound at left endpoint',F(13,N0)+F(3,16)<F(501,1000))
need('low-u b bound at right endpoint',F(1,2)+F(3,N0)<F(501,1000))
need('middle-u b bound',F(4,5)+F(3,4*N0)<F(801,1000))
need('low-u tail exp6 lower bound',E(F(6),32)>403)
need('low-u tail exp8 lower bound',E(F(8),32)>2980)
need('low-u triangle tail <73/100',(1+F(1,N0))*256*(F(1,403)+F(1,2980))<F(73,100))
need('old-error tail exponent at N0',F(31*(N0-3),640)>280)
need('old-error tail is decreasing',F(3,N0)<F(31,640))
need('old-error normalized tail <1/1000',1000*N0*N0*(N0+1)<2**280)
common=F(11,10)+F(1,20)+F(1,1000)
margins={
    'u<=1/2':F(3000,501)-common-F(320,81)-F(73,100),
    '1/2<=u<=4/5':F(3000,801)-common-F(2560,1029)-F(1,1000),
    '4/5<=u<1':F(3)-common-F(163840,89373)-F(1,1000),
}
for name,value in margins.items():need('strict final margin '+name,value>0)
# Independent local epsilon cap for the finite one-dimensional reduction.
need('N3 proposed h<=1/20',F(3,100)/F(99,100)<F(1,20))
need('N3 polar Taylor strictness',2*F(99,100)*F(9,10)>1)
need('N3 sqrt(1-h)>9/10',1-F(1,20)>F(9,10)**2)
need('N3 theta/epsilon lower bound',F(3,2)/(1+F(1,100)+F(1,10000))>F(37,25))
need('N3 right increment <7/40',F(3,2)*(1+F(1,10))-F(37,25)*(1-F(1,1000))<F(7,40))
need('N3 finite ESP error coefficient',F(1,2)*(1+F(3,100))+F(1,10)==F(123,200))
need('N3 strict local gap',1-F(7,40)-F(123,200)==F(21,100))
result=dict(status='PASS',scope='finite rational constants, not a formalization of the analytic lemmas',N_floor=N0,checks=len(checks),verified=checks,margins={k:str(v) for k,v in margins.items()},source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
if __name__=='__main__':
    Path('work/uniform_large_degree_constants.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
