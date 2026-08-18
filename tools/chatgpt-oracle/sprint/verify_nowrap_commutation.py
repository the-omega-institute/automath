"""Does the no-wrap characterisation transfer to fibonacci_folding's convention, and what is
the density of the set where naive truncation DOES commute?

fibonacci_folding: Omega_m = {0,1}^m, N(w) = sum w_i F_{i+1} (F_1=F_2=1), Fold_m = truncate the
Zeckendorf word of N(w) to m places, which equals the Zeckendorf form of N mod F_{m+2}.
tau = raw truncation Omega_{m+1} -> Omega_m (drop the top coordinate),
pi = drop the top coordinate of a folded word.

Claims to test:
  (i)  pi(Fold_{m+1}(w)) = Fold_m(tau(w))  iff  N_{m+1}(w) < F_{m+3}
  (ii) it holds at every depth iff w has no adjacent 1s, where the fold is already the identity
  (iii) density of the good set in Omega_{m+1}
"""
import sys
from itertools import product
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
F=[0,1,1]
while len(F)<60: F.append(F[-1]+F[-2])
def N(w): return sum(int(b)*F[i+2] for i,b in enumerate(w))
def zeck(n,m):
    z=[0]*m
    for i in range(m,0,-1):
        if F[i+1]<=n: z[i-1]=1; n-=F[i+1]
    return ''.join(map(str,z)) if n==0 else None
def Fold(w):
    m=len(w); return zeck(N(w)%F[m+2], m)
print(f'{"m":>3} {"|Omega_(m+1)|":>14} {"diagram holds":>14} {"N<F_(m+3)":>11} {"mismatch":>9} {"density":>9}')
for m in range(1,17):
    tot=0; hold=0; pred=0; bad=0
    for t in product('01', repeat=m+1):
        w=''.join(t); tot+=1
        h = (Fold(w)[:-1] == Fold(w[:-1]))
        p = (N(w) < F[m+3])
        hold+=h; pred+=p; bad += (h!=p)
    print(f'{m:3d} {tot:14d} {hold:14d} {pred:11d} {bad:9d} {hold/tot:9.5f}')
print()
print('--- (ii) all-depth commutation vs no adjacent 1s ---')
bad2=0; tot2=0; ok2=0
for n in range(2,18):
    for t in product('01', repeat=n):
        w=''.join(t); tot2+=1
        allh = all(Fold(w[:k+1])[:-1]==Fold(w[:k]) for k in range(1,n))
        ok2+=allh
        if allh != ('11' not in w): bad2+=1
print(f'   words tested {tot2}, all-depth good {ok2}, mismatches with the golden-mean condition: {bad2}')
print()
print('--- density limit ---')
import math
phi=(1+5**0.5)/2
for m in (12,14,16):
    tot=2**(m+1); hold=sum(1 for t in product('01',repeat=m+1) if N(''.join(t))<F[m+3])
    print(f'   m={m}: density {hold/tot:.6f}')
print(f'   note |X_(m+1)|/2^(m+1) would be {F[18]/2**17:.6f} at m=16 (for comparison)')
