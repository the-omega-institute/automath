"""Sanna's actual quantity: U(N) = sum_{n < N} R(n)^2, R = Fibonacci partition function
(number of representations of n as a sum of DISTINCT Fibonacci numbers, unbounded index).
For n < F_{m+2} every representation uses weights <= F_{m+1}, so R(n) = R_{m+1}(n) there.
Question: does U(F_{m+2}) satisfy a(m) = 2a(m-1) + 2a(m-2) - 2a(m-3) too?
If it does, the recurrence in the manuscript is not new; only the initial data is.
"""
import sys
from collections import Counter
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
F = [0, 1, 2]
while len(F) < 40: F.append(F[-1] + F[-2])

MAX = 26
c = Counter({0: 1})
for i in range(1, MAX):
    w = F[i]
    nc = Counter()
    for v, k in c.items():
        nc[v] += k; nc[v+w] += k
    c = nc
R = c   # R[n] = # representations using weights F_1..F_{MAX-1}

U = {}
print(f'{"m":>2} {"F_{m+2}":>9} {"U(m)=sum_{n<F_{m+2}} R(n)^2":>28}')
for m in range(1, 20):
    N = F[m+2]
    U[m] = sum(R[n]**2 for n in range(N))
    print(f'{m:2d} {N:9d} {U[m]:28d}')

def viol(seq, coeffs, lo, hi):
    return [m for m in range(lo, hi+1)
            if seq[m] != sum(cc*seq[m-i-1] for i, cc in enumerate(coeffs))]
print('\n--- U(m) against a(m) = 2a(m-1) + 2a(m-2) - 2a(m-3) ---')
v = viol(U, [2,2,-2], 4, 19)
print('  violations:', v if v else 'NONE')
print('  U initial:', [U[m] for m in range(1, 8)])

print('\n--- control: a deliberately wrong recurrence must fail ---')
for co in ([2,2,-1], [2,1,-2], [1,2,-2]):
    print(f'   coeffs {co}: violations = {len(viol(U, co, 4, 19))}')

print('\n--- minimal linear recurrence of U by Hankel rank ---')
from fractions import Fraction
seq = [U[m] for m in range(1, 20)]
def find_rec(seq, order):
    import itertools
    n = len(seq)
    if n < 2*order + 1: return None
    rows = [[Fraction(seq[i+j]) for j in range(order)] for i in range(n-order)]
    rhs = [Fraction(seq[i+order]) for i in range(n-order)]
    # gaussian elimination least-norm exact solve on first `order` equations, then verify
    import copy
    A = [r[:] + [rhs[i]] for i, r in enumerate(rows[:order])]
    for col in range(order):
        p = next((r for r in range(col, order) if A[r][col] != 0), None)
        if p is None: return None
        A[col], A[p] = A[p], A[col]
        pv = A[col][col]
        A[col] = [x/pv for x in A[col]]
        for r in range(order):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [a - f*b for a, b in zip(A[r], A[col])]
    sol = [A[i][order] for i in range(order)]
    for i in range(order, len(seq)):
        if seq[i] != sum(sol[j]*seq[i-order+j] for j in range(order)): return None
    return sol
for o in range(1, 6):
    s = find_rec(seq, o)
    if s:
        print(f'  minimal order = {o}, coefficients (oldest first) = {s}')
        break
else:
    print('  no recurrence of order <= 5')
