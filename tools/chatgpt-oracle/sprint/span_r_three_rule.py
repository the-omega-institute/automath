"""Tighten the negative result: three-rule systems, support <= 3."""
import sys
from itertools import product, combinations
sys.setrecursionlimit(200000)
def wordsn(n): return [''.join(t) for t in product('01', repeat=n)]
W = {n: wordsn(n) for n in range(1, 12)}
def gm(n): return [w for w in W[n] if '11' not in w]
def succ(w, R):
    o = set()
    for p, q in R.items():
        L = len(p)
        for i in range(len(w)-L+1):
            if w[i:i+L] == p: o.add(w[:i]+q+w[i+L:])
    return o
def nf1(w, R, cap=3000):
    col = {}; nfs = set()
    def dfs(u):
        col[u] = 1; s = succ(u, R)
        if not s: nfs.add(u)
        for v in s:
            c = col.get(v, 0)
            if c == 1: return False
            if c == 0:
                if len(col) > cap: return False
                if not dfs(v): return False
        col[u] = 2; return True
    if not dfs(w): return None
    return next(iter(nfs)) if len(nfs) == 1 else None
def check(R, LM):
    r = max(len(p) for p in R); nf = {}
    for L in range(1, LM+1):
        for w in W[L]:
            v = nf1(w, R)
            if v is None or '11' in v: return None
            nf[w] = v
    for L in range(1, LM):
        for w in W[L]:
            if nf['0'+w][1:] != nf[w]: return None
    if nf['0'*min(5,LM)] != '0'*min(5,LM): return None
    seen = {}
    for w in W[LM]:
        for i in range(LM-(r-1)):
            k = (i, w[:i+r])
            if k in seen and seen[k] != nf[w][i]: return None
            seen[k] = nf[w][i]
    img = set(nf[w] for w in W[LM])
    return None if len(img) <= 1 else img
singles = []
for s in (2, 3):
    for p in W[s]:
        for q in W[s]:
            if q != p: singles.append({p: q})
trip = []
for c in combinations(range(len(singles)), 3):
    ps = [next(iter(singles[i])) for i in c]
    if len(set(ps)) < 3: continue
    m = {}
    for i in c: m.update(singles[i])
    trip.append(m)
print('three-rule candidates:', len(trip), flush=True)
ok = []
for n, R in enumerate(trip):
    if n % 5000 == 0: print(f'  {n}/{len(trip)}', flush=True)
    if check(R, 6) is not None: ok.append(R)
print('screen survivors:', len(ok), flush=True)
LM = 10; G = set(gm(LM)); surj = 0
for R in ok:
    img = check(R, LM)
    if img is None: continue
    s = (img == G)
    surj += s
    print(f'  rules={R}  |image|={len(img)}/{len(G)} surjective={s}')
print('SURJECTIVE THREE-RULE MEMBERS:', surj)
