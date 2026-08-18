"""Is the window6 phenomenon a family?  For each m compute the coarsest equitable refinement
of the fold partition of Q_m and record: cell count, size profile, whether the cells are the
orbits of an involution, the quotient spectrum, and whether the discarded sector carries the
adjacency spectrum of Q_{m-2}.
"""
import sys
from itertools import product
from collections import Counter
import numpy as np
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
F=[0,1,1]
while len(F)<80: F.append(F[-1]+F[-2])
def fold(w):
    m=len(w); N=sum(int(b)*2**(m-1-i) for i,b in enumerate(w))
    z=[0]*72; n=N; r=70
    while r>=1:
        if F[r+1]<=n: z[r-1]=1; n-=F[r+1]
        r-=1
    return ''.join(str(z[i]) for i in range(m))
def nbrs(w): return [w[:i]+('1' if w[i]=='0' else '0')+w[i+1:] for i in range(len(w))]

print(f'{"m":>3} {"cells":>6} {"refined":>8} {"profile (size:count)":>26} {"discarded dim":>14} {"= spec A(Q_(m-2))":>18}')
for m in range(3,13):
    V=[''.join(t) for t in product('01',repeat=m)]
    col={w:fold(w) for w in V}
    labs=sorted(set(col.values())); idx={l:i for i,l in enumerate(labs)}
    c={w:idx[col[w]] for w in V}
    while True:
        sig={w:(c[w],tuple(sorted(c[u] for u in nbrs(w)))) for w in V}
        classes={}
        for w in V: classes.setdefault(sig[w],[]).append(w)
        new={}
        for i,(k,ws) in enumerate(sorted(classes.items())):
            for w in ws: new[w]=i
        if len(set(new.values()))==len(set(c.values())): break
        c=new
    cells={}
    for w in V: cells.setdefault(c[w],[]).append(w)
    prof=Counter(len(v) for v in cells.values())
    k=len(cells)
    order=sorted(cells); pos={l:i for i,l in enumerate(order)}
    B=np.zeros((k,k))
    for i,l in enumerate(order):
        rep=cells[l][0]
        for u in nbrs(rep): B[i,pos[c[u]]]+=1
    qs=Counter(round(float(e.real),6) for e in np.linalg.eigvals(B))
    A=np.zeros((2**m,2**m)); vi={w:i for i,w in enumerate(V)}
    for w in V:
        for u in nbrs(w): A[vi[w],vi[u]]=1
    full=Counter(round(float(e.real),6) for e in np.linalg.eigvals(A))
    rem=Counter(full); rem.subtract(qs); rem={v:n for v,n in rem.items() if n}
    d=m-2
    if d>=1:
        V2=[''.join(t) for t in product('01',repeat=d)]
        i2={w:i for i,w in enumerate(V2)}
        A2=np.zeros((2**d,2**d))
        for w in V2:
            for j in range(d):
                u=w[:j]+('1' if w[j]=='0' else '0')+w[j+1:]
                A2[i2[w],i2[u]]=1
        s2=Counter(round(float(e.real),6) for e in np.linalg.eigvals(A2))
        match = (dict(sorted(rem.items()))=={k2:v2 for k2,v2 in sorted(s2.items())})
    else:
        match=None
    print(f'{m:3d} {len(set(col.values())):6d} {k:8d} {str(dict(sorted(prof.items()))):>26} {sum(rem.values()):14d} {str(match):>18}')
