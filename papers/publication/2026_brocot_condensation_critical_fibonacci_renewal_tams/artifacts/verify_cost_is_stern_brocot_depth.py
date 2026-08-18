"""Test my analytic account of the critical tail constant.

Fact used: d(p/q) = sum of the regular continued-fraction partial quotients of q/p, minus 1.
So the class d consists of the q/p = [a_0; a_1, ..., a_k] with sum a_i = n := d+1, and
b_{2d+1}(sigma) = sum over that class of K(a_0,...,a_k)^{-sigma}, K the continuant.

For q to stay of order n one partial quotient must carry almost all of n while the rest form
BOUNDED patterns on the two sides of it.  Then K ~ a_i * K(left) * K(right), so
    b_{2d+1}(sigma) ~ n^{-sigma} * ( sum over finite tails t of K(t)^{-sigma} )^2 .
If  S := sum_t K(t)^{-sigma_0}  equals 2*rho = 4, the constant is 4 rho^2 = 16, not 2 rho^2 = 8.

Two checks: (A) verify d(p/q) = sum a_i - 1; (B) compute S directly.
"""
import sys, math
from math import gcd
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
sigma0 = 2.4787507857339602606714872614
rho = 2.0

def negcf_d(p, q):
    a, b = q, p; d = 0
    while True:
        e = -(-a // b); d += e - 1
        num, den = b, e*b - a
        if den == 0: return d
        a, b = num, den
        g = gcd(a, b); a//=g; b//=g

def cf_sum(p, q):
    """sum of regular CF partial quotients of q/p"""
    a, b = q, p; s = 0
    while b:
        s += a // b
        a, b = b, a % b
    return s

print('--- (A) is d(p/q) = sum a_i(q/p) - 1 ? ---')
bad = 0; tot = 0
for q in range(2, 400):
    for p in range(1, q):
        if gcd(p, q) == 1:
            tot += 1
            if negcf_d(p, q) != cf_sum(p, q) - 1: bad += 1
print(f'   checked {tot} fractions, mismatches: {bad}')

print()
print('--- (B) S = sum over all finite sequences t of K(t)^{-sigma_0} ---')
print('    K(t) enumerates continuants; sum by depth with pruning on K^{-sigma} < eps')
EPS = 1e-14
total = 1.0   # empty tail, K = 1
frontier = [(1, 0)]   # (K_i, K_{i-1}) ; start K_0 = 1, K_{-1} = 0
depth = 0
while frontier and depth < 60:
    nxt = []
    add = 0.0
    for (k1, k0) in frontier:
        a = 1
        while True:
            k = a*k1 + k0
            w = k**(-sigma0)
            if w < EPS: break
            add += w
            nxt.append((k, k1))
            a += 1
            if a > 4000: break
    total += add
    depth += 1
    if depth <= 8 or add < 1e-10:
        print(f'   depth {depth:2d}: added {add:.10f}  running total {total:.10f}  frontier {len(nxt)}')
    if add < 1e-12: break
    frontier = nxt
    if len(frontier) > 4_000_000: print('   frontier cap hit'); break
print(f'   S = {total:.8f}     2*rho = {2*rho}     S^2 = {total**2:.6f}     2 rho^2 = 8')
