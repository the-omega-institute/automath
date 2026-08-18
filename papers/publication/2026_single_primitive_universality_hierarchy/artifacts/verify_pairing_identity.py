"""single_primitive: the referee says the claim "the fold's pairing of the two residue
representatives removes the parity factor" is true but only observed.  Decompose it.

d_m(x) = R(v_x) + R(v_x + M),  M = F_{m+2},  R = representations by distinct Fibonacci parts
using the m+1 weights F_2..F_{m+2}.  Then
    S_2 = sum_x d_m(x)^2 = T_2 + 2C,
    T_2 = sum over the FULL value range of R(n)^2,
    C   = sum_x R(v_x) R(v_x + M)   (the cross term the pairing creates),
while U(m) = sum_{n < M} R(n)^2 is the TRUNCATED sum, which carries (X-1)(X+1).
Test which of T_2, C, S_2 satisfy the bare cubic X^3 - 2X^2 - 2X + 2.
"""
import sys
from collections import Counter
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
F=[0,1,2]
while len(F)<40: F.append(F[-1]+F[-2])
def counts(m):
    c=Counter({0:1})
    for i in range(1, m+2):
        w=F[i]; nc=Counter()
        for v,k in c.items(): nc[v]+=k; nc[v+w]+=k
        c=nc
    return c
def rec_ok(seq, lo, hi, co=(2,2,-2)):
    return [m for m in range(lo,hi+1) if seq[m]!=sum(cc*seq[m-i-1] for i,cc in enumerate(co))]
S2={};T2={};C={};U={}
print(f'{"m":>3} {"S_2":>12} {"T_2":>12} {"C":>12} {"U":>12} {"S2=T2+2C":>10}')
for m in range(1,17):
    c=counts(m); M=F[m+2]
    T2[m]=sum(k*k for k in c.values())
    r=Counter()
    for v,k in c.items(): r[v%M]+=k
    S2[m]=sum(k*k for k in r.values())
    C[m]=sum(c.get(v,0)*c.get(v+M,0) for v in range(M))
    U[m]=sum(c.get(n,0)**2 for n in range(M))
    print(f'{m:3d} {S2[m]:12d} {T2[m]:12d} {C[m]:12d} {U[m]:12d} {str(S2[m]==T2[m]+2*C[m]):>10}')
print()
print('--- which satisfy  a(m) = 2a(m-1) + 2a(m-2) - 2a(m-3)? ---')
for name,seq in (('S_2',S2),('T_2',T2),('C  ',C),('U  ',U)):
    v=rec_ok(seq,4,16)
    print(f'   {name}: violations {len(v)}  {"" if not v else v}')
print()
print('--- control: a perturbed recurrence must fail on all four ---')
for name,seq in (('S_2',S2),('T_2',T2),('C  ',C)):
    print(f'   {name} with (2,2,-1): violations {len(rec_ok(seq,4,16,(2,2,-1)))} of 13')
