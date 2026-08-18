"""Drop the confluent-rewrite requirement, keep only what clause (ii) + (i) force:
a bounded-delay local map, i.e. a sliding block code phi with window r,
  phi(w)_i = f(w_i, ..., w_{i+r-1}).
Ask whether ANY such f is a genuine analogue of Fold_m, i.e.
  (a) image avoids '11'                       [codomain is X]
  (b) f fixes X pointwise (idempotent there)  [Fold_m is an idempotent projection]
  (c) image is ALL of X                       [Fold_m is onto]
(b) forces f(b) = b_1 on every window b with no '11'; the only freedom is on
windows containing '11'.  Enumerate that freedom exhaustively for r = 3, 4, 5.
"""
from itertools import product

def wordsn(n): return [''.join(t) for t in product('01', repeat=n)]
def gm(n): return [w for w in wordsn(n) if '11' not in w]

def run(r, LM=10, report=True):
    blocks = wordsn(r)
    free = [b for b in blocks if '11' in b]
    forced = {b: b[0] for b in blocks if '11' not in b}
    allw = wordsn(LM)
    target = set(gm(LM - (r-1)))
    good = []
    for bits in product('01', repeat=len(free)):
        f = dict(forced)
        f.update(dict(zip(free, bits)))
        img = set()
        ok = True
        for w in allw:
            out = ''.join(f[w[i:i+r]] for i in range(LM-r+1))
            if '11' in out: ok = False; break
            img.add(out)
        if not ok: continue
        # idempotence on X is automatic from `forced`; verify surjectivity
        if img == target:
            good.append((f, len(img)))
    if report:
        print(f'r={r}: free windows={len(free)}, maps tried={2**len(free)}, '
              f'|X_{LM-r+1}|={len(target)}  ->  members with (a)+(b)+(c): {len(good)}')
    return good

for r in (3, 4):
    g = run(r)
    for f, n in g[:3]:
        nz = {k: v for k, v in f.items() if '11' in k}
        print(f'    example rule on 11-windows: {nz}')

# r=5 is 2^19 maps; screen on short words first
r = 5; LM = 9
blocks = wordsn(r); free = [b for b in blocks if '11' in b]
forced = {b: b[0] for b in blocks if '11' not in b}
short = wordsn(7); allw = wordsn(LM); target = set(gm(LM-r+1))
cnt = 0; kept = []
for bits in product('01', repeat=len(free)):
    f = dict(forced); f.update(dict(zip(free, bits)))
    bad = False
    for w in short:
        out = ''.join(f[w[i:i+r]] for i in range(7-r+1))
        if '11' in out: bad = True; break
    if bad: continue
    img = set()
    for w in allw:
        out = ''.join(f[w[i:i+r]] for i in range(LM-r+1))
        if '11' in out: bad = True; break
        img.add(out)
    if bad: continue
    cnt += 1
    if img == target: kept.append(f)
print(f'r=5: free windows={len(free)}, maps tried={2**len(free)}, '
      f'passed (a)+(b): {cnt}, and also (c) surjective: {len(kept)}')
