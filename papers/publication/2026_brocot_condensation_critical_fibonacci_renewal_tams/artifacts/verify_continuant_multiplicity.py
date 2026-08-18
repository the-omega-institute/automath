"""Turn the numerical guess S = 2 rho into a checked statement.

Claim: as t ranges over ALL finite sequences (a_1,...,a_k) of positive integers, including the
empty one, the continuant K(t) takes each value q with multiplicity exactly 2*phi(q).
Reason: [0;a_1,...,a_k] with a_k >= 2 is the canonical CF of a rational in (0,1) with denominator
K(t), and each such rational has exactly two representations, the other being
[0;a_1,...,a_k - 1,1], with the same continuant.
Hence S := sum_t K(t)^{-s} = 2 sum_{q>=1} phi(q) q^{-s} = 2 zeta(s-1)/zeta(s) = 2 rho_s.
At sigma_0, rho = 2, so S = 4 exactly and b_C = S^2 = 4 rho^2 = 16.
"""
import sys
from collections import Counter
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

QMAX = 60
mult = Counter()
# enumerate all finite sequences with continuant <= QMAX, by DFS on (K_prev, K_cur)
def walk(k0, k1, depth):
    # k1 = K(a_1..a_j), k0 = K(a_1..a_{j-1})
    mult[k1] += 1
    a = 1
    while True:
        k = a*k1 + k0
        if k > QMAX: break
        walk(k1, k, depth+1)
        a += 1
sys.setrecursionlimit(10000)
walk(0, 1, 0)      # empty sequence: K = 1, with K_prev = 0

def phi_list(N):
    ph = list(range(N+1))
    for i in range(2, N+1):
        if ph[i] == i:
            for j in range(i, N+1, i): ph[j] -= ph[j]//i
    return ph
ph = phi_list(QMAX)

print(f'{"q":>4} {"multiplicity":>13} {"2*phi(q)":>10} {"match":>6}')
bad = 0
for q in range(1, 25):
    m = mult[q]; e = 2*ph[q]
    ok = (m == e)
    bad += (not ok)
    print(f'{q:4d} {m:13d} {e:10d} {str(ok):>6}')
allbad = [q for q in range(1, QMAX+1) if mult[q] != 2*ph[q]]
print(f'\nmismatches over 1 <= q <= {QMAX}: {len(allbad)}  {allbad[:8]}')

sigma0 = 2.4787507857339602606714872614
S_trunc = sum(m*q**(-sigma0) for q, m in mult.items())
S_pred  = 2*sum(ph[q]*q**(-sigma0) for q in range(1, QMAX+1))
print(f'\nS truncated at q <= {QMAX}: enumerated {S_trunc:.8f}   2*phi-sum {S_pred:.8f}')
try:
    from mpmath import mp, zeta, mpf
    mp.dps = 25
    s0 = mpf('2.478750785733960260671487261390')
    print(f'S = 2*zeta(s-1)/zeta(s) exactly = {2*zeta(s0-1)/zeta(s0)}')
    print(f'b_C = S^2 = {(2*zeta(s0-1)/zeta(s0))**2}      paper says 8')
except Exception as e:
    print('mpmath:', e)
