# -*- coding: utf-8 -*-
"""Do the two papers' second-moment claims agree?

single_primitive: exact recurrence S_2(m) = 2S_2(m-1) + 2S_2(m-2) - 2S_2(m-3), m >= 4,
                  initial values 6, 14, 36.   Characteristic polynomial x^3 - 2x^2 - 2x + 2.
projection:       S_2(m) ~ lambda_2^m with lambda_2 computed numerically at tick 385.
"""
from fractions import Fraction as Fr

STD=[0,1,1]
while len(STD)<90: STD.append(STD[-1]+STD[-2])
SP=[0]+[STD[k+1] for k in range(1,85)]

def S2_sp(m):
    """single_primitive: fibres are residue classes mod F_{m+2} of {0,1}^{m+1}."""
    mod=SP[m+2]; c=[0]*mod; c[0]=1
    for j in range(1,m+2):
        k=SP[j]%mod
        c=[c[(n-k)%mod]+c[n] for n in range(mod)]
    return sum(x*x for x in c), sum(c)

def S2_proj(m):
    """projection: fibres are single coefficients of prod_{j=1}^m (1+z^{F_j})."""
    w=[STD[j] for j in range(1,m+1)]; N=sum(w); c=[0]*(N+1); c[0]=1
    for k in w:
        for n in range(N,k-1,-1): c[n]+=c[n-k]
    return sum(x*x for x in c)

print("1) single_primitive: does its stated recurrence reproduce its own S_2?")
vals=[S2_sp(m)[0] for m in range(1,22)]
tot =[S2_sp(m)[1] for m in range(1,22)]
print(f"   S_2(1..6) brute = {vals[:6]}   (paper's initial values are 6, 14, 36)")
print(f"   fibre totals = 2^(m+1)? {all(t==2**(m+1) for m,t in zip(range(1,22),tot))}")
bad=[m for m in range(4,22) if vals[m-1]!=2*vals[m-2]+2*vals[m-3]-2*vals[m-4]]
print(f"   recurrence holds for m=4..21: {not bad}   violations: {bad}")

print()
print("2) the characteristic root against projection's lambda_2")
# largest real root of x^3 - 2x^2 - 2x + 2
f=lambda x: x**3-2*x**2-2*x+2
lo,hi=2.0,3.0
for _ in range(200):
    mid=(lo+hi)/2
    if f(mid)<0: lo=mid
    else: hi=mid
root=(lo+hi)/2
print(f"   dominant root of x^3-2x^2-2x+2 = {root:.12f}")
r=[S2_proj(m+1)/S2_proj(m) for m in range(18,26)]
print(f"   projection S_2(m+1)/S_2(m), m=18..25: {[f'{x:.9f}' for x in r[:4]]} ... {r[-1]:.12f}")
print(f"   difference at m=25: {abs(r[-1]-root):.3e}")
rs=[S2_sp(m+1)[0]/S2_sp(m)[0] for m in range(14,20)]
print(f"   single_primitive S_2(m+1)/S_2(m), m=19: {rs[-1]:.12f}   diff {abs(rs[-1]-root):.3e}")

print()
print("3) is x^3-2x^2-2x+2 irreducible over Q?  (rational root test)")
cands=[1,-1,2,-2]
print(f"   f(+-1), f(+-2) = {[f(c) for c in cands]}  -> no rational root: {all(f(c)!=0 for c in cands)}")
print("   a cubic with no rational root is irreducible over Q, so lambda_2 has degree 3")
