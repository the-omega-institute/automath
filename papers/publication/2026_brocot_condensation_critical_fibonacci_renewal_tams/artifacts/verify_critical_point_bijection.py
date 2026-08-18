"""Enumerate by denominator instead of by cost: for every reduced p/q with 0<p<q<=Q,
compute the negative continued fraction of q/p and d = sum(e_i - 1).
Checks: (a) the cost classes reproduce the composition enumeration exactly;
(b) B_s(1) = sum_{q>=2} phi(q) q^{-s} = zeta(s-1)/zeta(s) - 1, so sigma_0 solves
    zeta(s-1)/zeta(s) = 2; (c) mu_C = sum (2d+1) q^{-sigma_0} converges.
"""
import sys, math
from math import gcd
from collections import Counter
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

def negcf_d(p, q):
    """p/q = 1/(e1 - 1/(e2 - ...)), return sum(e_i - 1)"""
    # work with x = q/p > 1
    a, b = q, p          # x = a/b
    d = 0
    while True:
        e = -(-a // b)   # ceil(a/b)
        d += e - 1
        # x' = 1/(e - x) = b/(e*b - a)
        num, den = b, e*b - a
        if den == 0:
            return d
        a, b = num, den
        g = gcd(a, b); a//=g; b//=g

Q = 3000
byd = Counter(); qs_by_d = {}
tot = 0
for q in range(2, Q+1):
    for p in range(1, q):
        if gcd(p, q) == 1:
            d = negcf_d(p, q)
            byd[d] += 1
            qs_by_d.setdefault(d, []).append(q)
            tot += 1
print(f'reduced fractions with q <= {Q}: {tot}')
print('count by d (small d):', [(d, byd[d]) for d in range(1, 8)])
print('expected 2^(d-1)     :', [(d, 2**(d-1)) for d in range(1, 8)],
      '  (equal only while all denominators <= Q)')

def phi_list(N):
    ph = list(range(N+1))
    for i in range(2, N+1):
        if ph[i] == i:
            for j in range(i, N+1, i): ph[j] -= ph[j]//i
    return ph
ph = phi_list(Q)
print('\n--- (b) does B_s(1) equal the phi sum?  compare term by term ---')
for s in (2.4, 2.5, 3.0):
    lhs = sum(q**(-s) for d in qs_by_d for q in qs_by_d[d])
    rhs = sum(ph[q]*q**(-s) for q in range(2, Q+1))
    print(f'   s={s}: enumerated {lhs:.10f}   phi-sum {rhs:.10f}   diff {abs(lhs-rhs):.2e}')

print('\n--- sigma_0 from zeta(s-1)/zeta(s) = 2 (mpmath, exact functional) ---')
try:
    from mpmath import mp, zeta, findroot
    mp.dps = 30
    f = lambda s: zeta(s-1)/zeta(s) - 2
    sig = findroot(f, 2.5)
    print(f'   sigma_0 = {sig}')
    sigma0 = float(sig)
except Exception as e:
    print('   mpmath unavailable:', e)
    lo, hi = 2.05, 4.0
    for _ in range(200):
        mid=(lo+hi)/2
        if sum(ph[q]*q**(-mid) for q in range(2,Q+1)) > 1: lo=mid
        else: hi=mid
    sigma0=(lo+hi)/2
    print(f'   sigma_0 (truncated phi sum) = {sigma0:.10f}')

print('\n--- convergence check of the enumerated B_{sigma_0}(1) as Q grows ---')
vals=[]
for QQ in (500, 1000, 2000, 3000):
    v = sum(q**(-sigma0) for d in qs_by_d for q in qs_by_d[d] if q <= QQ)
    vals.append((QQ, v)); print(f'   Q={QQ:5d}: {v:.8f}')
print('   target 1.0 -> tail at Q=3000 is', f'{1-vals[-1][1]:.2e}')

print('\n--- mu_C = sum (2d+1) q^{-sigma_0} ---')
for QQ in (500, 1000, 2000, 3000):
    mu = sum((2*d+1)*q**(-sigma0) for d in qs_by_d for q in qs_by_d[d] if q <= QQ)
    print(f'   Q={QQ:5d}: mu_C = {mu:.8f}')
