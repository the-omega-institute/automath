"""Widen to support <= 4 with a cheap screen, and ask the question that decides it:
does ANY member of the class have full image (surjective onto X_m), as Fold_m does?
Fold_m is an idempotent projection ONTO X_m, so a class member that is a genuine
analogue must at least be surjective.
"""
import sys
from itertools import product
sys.setrecursionlimit(200000)

def successors(w, rules):
    out = set()
    for pat, rep in rules.items():
        L = len(pat)
        for i in range(len(w)-L+1):
            if w[i:i+L] == pat:
                out.add(w[:i]+rep+w[i+L:])
    return out

def nf_unique(w, rules, cap=4000):
    colour = {}; nfs = set()
    def dfs(u):
        colour[u] = 1
        succ = successors(u, rules)
        if not succ: nfs.add(u)
        for v in succ:
            c = colour.get(v, 0)
            if c == 1: return False
            if c == 0:
                if len(colour) > cap: return False
                if not dfs(v): return False
        colour[u] = 2
        return True
    ok = dfs(w)
    if not ok: return None, 'nonterminating'
    if len(nfs) != 1: return None, 'not-confluent'
    return next(iter(nfs)), 'ok'

W = {n: [''.join(t) for t in product('01', repeat=n)] for n in range(1, 12)}
def gm(n):  # golden-mean language
    return [w for w in W[n] if '11' not in w]

def check(rules, LMAX):
    r = max(len(p) for p in rules)
    nf = {}
    for L in range(1, LMAX+1):
        for w in W[L]:
            v, why = nf_unique(w, rules)
            if v is None: return None, why
            if '11' in v: return None, 'image-has-11'
            nf[w] = v
    for L in range(1, LMAX):
        for w in W[L]:
            if nf['0'+w][1:] != nf[w]: return None, 'zero-padding-changes-output'
    if nf['0'*min(5,LMAX)] != '0'*min(5,LMAX): return None, 'zero-not-stable'
    seen = {}
    for w in W[LMAX]:
        for i in range(LMAX-(r-1)):
            k = (i, w[:i+r])
            if k in seen and seen[k] != nf[w][i]: return None, 'clause-ii-fails'
            seen[k] = nf[w][i]
    img = set(nf[w] for w in W[LMAX])
    if len(img) <= 1: return None, 'constant'
    return (nf, img), 'OK'

singles = []
for s in (2, 3, 4):
    for pat in W[s]:
        for rep in W[s]:
            if rep != pat: singles.append({pat: rep})
cands = list(singles)
for a in range(len(singles)):
    for b in range(a+1, len(singles)):
        pa = next(iter(singles[a])); pb = next(iter(singles[b]))
        if pa == pb: continue
        m = dict(singles[a]); m.update(singles[b]); cands.append(m)
print('candidates (support <= 4, 1-2 rules):', len(cands), flush=True)

screened = []
tally = {}
for n, R in enumerate(cands):
    if n % 5000 == 0: print(f'  screen {n}/{len(cands)}', flush=True)
    res, why = check(R, 6)
    tally[why] = tally.get(why, 0) + 1
    if why == 'OK': screened.append(R)
print('\n--- screen at length 6, raw tally ---')
for k, v in sorted(tally.items(), key=lambda x: -x[1]): print(f'  {k:32s} {v}')
print(f'  screen survivors: {len(screened)}', flush=True)

LM = 10
final = []
for R in screened:
    res, why = check(R, LM)
    if why == 'OK': final.append((R, res[0], res[1]))
print(f'\n--- confirmed at length {LM}: {len(final)} ---')
G = set(gm(LM)); print(f'|X_{LM}| (golden-mean words) = {len(G)}   |{{0,1}}^{LM}| = {2**LM}\n')
surj = 0
for R, nf, img in final:
    idem = all(nf[w] == w for w in gm(LM))
    print(f'rules={R}')
    print(f'   |image| = {len(img)} / {len(G)}   surjective={img==G}   identity on X_{LM}={idem}')
    if img == G: surj += 1
print(f'\nSURJECTIVE MEMBERS: {surj}')
