"""Check the referee's diagnosis of golden_mean_folding Theorem 6.1.

Conventions taken from the report's own worked example: position i of a length-m raw word
carries weight F_{i+1} with F_1 = F_2 = 1, so N_3(110) = 1 + 2 = 3.  X_m is the length-m
no-adjacent-ones language, Fold_m(w) = Zeckendorf digits of N_m(w) mod F_{m+2}, truncated
to m positions.  tau is raw prefix truncation, pi is truncation of a folded word.

Claims under test:
  A. Fold_3(110) = 001, rho_{3,2}(110) = 00, Fold_2(00) = 00      [non-vacuity instance]
  B. the natural diagram pi.Fold_{m+1} = Fold_m.tau fails for 011 at 3->2 (00 vs 01)
  C. it holds for a word EXACTLY when N_{m+1}(w) < F_{m+3}         [no-upper-wrap region]
  D. all adjacent diagrams commute for every prefix EXACTLY when the word has no adjacent 1s
"""
import sys
from itertools import product
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
F = [0, 1, 1]
while len(F) < 50: F.append(F[-1] + F[-2])
def N(w): return sum(int(b) * F[i+2] for i, b in enumerate(w))
def zeck(n, m):
    z = [0]*m
    for i in range(m, 0, -1):
        if F[i+1] <= n: z[i-1] = 1; n -= F[i+1]
    return ''.join(map(str, z)) if n == 0 else None
def Fold(w):
    m = len(w)
    return zeck(N(w) % F[m+2], m)
def tau(w): return w[:-1]
def pi(x): return x[:-1]

print('--- A: the report worked example ---')
print(f'  N_3(110) = {N("110")}   Fold_3(110) = {Fold("110")}   (report: 3, 001)')
r = pi(Fold('110')); print(f'  rho_(3,2)(110) = pi(Fold_3(110)) = {r}   Fold_2({r}) = {Fold(r)}   (report: 00, 00)')
print(f'  Fold_2(tau(110)) = Fold_2(11) = {Fold("11")}   (report: 00)')

print('\n--- B: the natural diagram at 011, 3 -> 2 ---')
print(f'  pi(Fold_3(011)) = {pi(Fold("011"))}     Fold_2(tau(011)) = Fold_2(01) = {Fold("01")}   (report: 00 vs 01)')

print('\n--- C: diagram holds  iff  N_{m+1}(w) < F_{m+3} ---')
bad = []; tot = 0; hold = 0
for m in range(1, 15):
    for t in product('01', repeat=m+1):
        w = ''.join(t); tot += 1
        lhs = pi(Fold(w)); rhs = Fold(tau(w))
        h = (lhs == rhs); hold += h
        pred = N(w) < F[m+3]
        if h != pred: bad.append((m, w, lhs, rhs, N(w), F[m+3]))
print(f'  words tested: {tot}   diagram holds for: {hold}')
print(f'  mismatches between "diagram holds" and "N < F_(m+3)": {len(bad)}')
if bad: print('   first few:', bad[:5])

print('\n--- D: every prefix diagram commutes  iff  no adjacent 1s ---')
bad2 = []; tot2 = 0; allok = 0
for n in range(2, 17):
    for t in product('01', repeat=n):
        w = ''.join(t); tot2 += 1
        ok = all(pi(Fold(w[:k+1])) == Fold(w[:k]) for k in range(1, n))
        allok += ok
        legal = '11' not in w
        if ok != legal: bad2.append((w, ok, legal))
print(f'  words tested: {tot2}   all-resolution compatible: {allok}')
print(f'  mismatches with "no adjacent 1s": {len(bad2)}')
if bad2: print('   first few:', bad2[:5])

print('\n--- and on that class, is the fold already the identity? ---')
nid = [w for n in range(1, 15) for t in product('01', repeat=n)
       for w in [''.join(t)] if '11' not in w and Fold(w) != w]
print(f'  legal words where Fold(w) != w: {len(nid)}   ->',
      'fold is the identity on X_n' if not nid else nid[:5])
