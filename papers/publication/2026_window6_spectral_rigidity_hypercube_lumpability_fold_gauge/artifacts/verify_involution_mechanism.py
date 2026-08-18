"""Confirm the mechanism: sigma swaps two coordinates and complements both, and the sum of their
binary weights is a Fibonacci number lying beyond the visible window.  Then ask which m admit such
a pair, since Fibonacci numbers that are sums of two distinct powers of two are famously scarce."""
import sys
from itertools import product
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
F=[0,1,1]
while len(F)<200: F.append(F[-1]+F[-2])
fibset={F[k]:k for k in range(2,120)}

print('--- Fibonacci numbers that are a sum of two DISTINCT powers of two ---')
found=[]
for k in range(3,90):
    n=F[k]
    for a in range(0,80):
        if 2**a>=n: break
        r=n-2**a
        if r>0 and r!=2**a and (r & (r-1))==0:
            b=r.bit_length()-1
            if a<b: found.append((n,k,b,a))
for n,k,a,b in found: print(f'   F_{k} = {n} = 2^{a} + 2^{b}')
print(f'   total below F_90: {len(found)}')

print()
print('--- for each m, which coordinate pairs (i<j) give 2^(m-i)+2^(m-j) = F_k beyond the window? ---')
def fold(w):
    m=len(w); N=sum(int(b)*2**(m-1-i) for i,b in enumerate(w))
    z=[0]*160; n=N; r=150
    while r>=1:
        if F[r+1]<=n: z[r-1]=1; n-=F[r+1]
        r-=1
    return ''.join(str(z[i]) for i in range(m))
actual={3,6,8,9}
print(f'{"m":>3} {"candidate (i,j,F_k)":>28} {"sigma preserves fold?":>22}')
for m in range(2,17):
    cands=[]
    for i in range(1,m+1):
        for j in range(i+1,m+1):
            s=2**(m-i)+2**(m-j)
            if s in fibset: cands.append((i,j,fibset[s],s))
    works=[]
    for (i,j,k,s) in cands:
        V=[''.join(t) for t in product('01',repeat=m)]
        ok=True
        for w in V:
            l=list(w); a,b=l[i-1],l[j-1]
            l[i-1]='1' if b=='0' else '0'; l[j-1]='1' if a=='0' else '0'
            if fold(''.join(l))!=fold(w): ok=False; break
        if ok: works.append((i,j,k,s))
    mark='<-- has nontrivial refinement' if m in actual else ''
    print(f'{m:3d} {str([(i,j,f"F_{k}={s}") for i,j,k,s in cands]):>28} {str([(i,j) for i,j,_,_ in works]):>22} {mark}')
