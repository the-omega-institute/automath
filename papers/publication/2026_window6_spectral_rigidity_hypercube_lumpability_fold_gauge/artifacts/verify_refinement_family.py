"""Extend the sweep using only cell counts (cheap): when is the coarsest equitable refinement
nontrivial, and is the discarded dimension always 2^{m-2}?"""
import sys
from itertools import product
from collections import Counter
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
F=[0,1,1]
while len(F)<90: F.append(F[-1]+F[-2])
def fold(w):
    m=len(w); N=sum(int(b)*2**(m-1-i) for i,b in enumerate(w))
    z=[0]*82; n=N; r=80
    while r>=1:
        if F[r+1]<=n: z[r-1]=1; n-=F[r+1]
        r-=1
    return ''.join(str(z[i]) for i in range(m))
print(f'{"m":>3} {"fold cells":>11} {"refined":>9} {"profile":>22} {"discarded":>10} {"2^(m-2)":>9} {"match":>6}')
hits=[]
for m in range(3,17):
    V=[''.join(t) for t in product('01',repeat=m)]
    col={w:fold(w) for w in V}
    labs=sorted(set(col.values())); idx={l:i for i,l in enumerate(labs)}
    c={w:idx[col[w]] for w in V}
    def nb(w): return [w[:i]+('1' if w[i]=='0' else '0')+w[i+1:] for i in range(m)]
    while True:
        classes={}
        for w in V: classes.setdefault((c[w],tuple(sorted(c[u] for u in nb(w)))),[]).append(w)
        new={}
        for i,(k,ws) in enumerate(sorted(classes.items())):
            for w in ws: new[w]=i
        if len(set(new.values()))==len(set(c.values())): break
        c=new
    cells=Counter(c.values()); k=len(cells)
    prof=Counter(Counter(c.values()).values())
    disc=2**m-k
    ok = (disc==2**(m-2)) if disc else False
    if disc: hits.append(m)
    print(f'{m:3d} {len(labs):11d} {k:9d} {str(dict(sorted(prof.items()))):>22} {disc:10d} {2**(m-2):9d} {str(ok):>6}')
print()
print('m with a nontrivial refinement:', hits)
