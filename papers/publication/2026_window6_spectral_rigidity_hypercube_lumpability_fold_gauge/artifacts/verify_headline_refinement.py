"""Independent check of the window6 headline theorem, taken from the fiber table
printed in Definition 2.x of the manuscript.  This verifies the THEOREM given that
table; it does not re-derive that the table equals Fold_6 (separate check).
"""
import re, io, itertools, sys
from fractions import Fraction
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

src = io.open(r"D:\omega\automath\papers\publication\2026_window6_spectral_rigidity_hypercube_lumpability_fold_gauge\main.tex",
              encoding='utf-8').read()
fiber_section = src.split('The fibers, in lexicographic order of', 1)[1].split('\\end{definition}', 1)[0]
blocks = re.findall(r'\\begin\{array\}\{c\|l\}(.*?)\\end\{array\}', fiber_section, re.S)
blk = '\\\\'.join(blocks)
cells = {}
for line in blk.split('\\\\'):
    line = line.strip()
    if '&' not in line: continue
    lab, rest = line.split('&', 1)
    lab = lab.strip()
    words = [w.strip() for w in rest.replace('\n',' ').split(',') if re.fullmatch(r'[01]{6}', w.strip())]
    if words: cells[lab] = words
print('cells parsed:', len(cells), ' total words:', sum(len(v) for v in cells.values()))
allw = [w for v in cells.values() for w in v]
assert len(set(allw)) == 64 == len(allw), 'NOT a partition of the 64 vertices'
print('partition of Q_6 verified: 64 distinct vertices')
print('fibre-size vector:', tuple(len(cells[k]) for k in cells))

V = [''.join(t) for t in itertools.product('01', repeat=6)]
idx = {w: i for i, w in enumerate(V)}
def nbrs(w):
    return [w[:i] + ('1' if w[i]=='0' else '0') + w[i+1:] for i in range(6)]

colour = {}
for c, (lab, ws) in enumerate(cells.items()):
    for w in ws: colour[w] = c
print('\n--- is the 21-cell partition equitable? ---')
def refine(col):
    while True:
        sig = {w: (col[w], tuple(sorted(col[u] for u in nbrs(w)))) for w in V}
        classes = {}
        for w in V: classes.setdefault(sig[w], []).append(w)
        new = {}
        for c, (k, ws) in enumerate(sorted(classes.items())):
            for w in ws: new[w] = c
        if len(set(new.values())) == len(set(col.values())): return new
        col = new
bad = []
for lab, ws in cells.items():
    sigs = set()
    for w in ws:
        sigs.add(tuple(sorted(colour[u] for u in nbrs(w))))
    if len(sigs) > 1: bad.append(lab)
print('  cells with non-constant neighbour signature:', len(bad), '->',
      'NOT equitable' if bad else 'equitable')

ref = refine(dict(colour))
k = len(set(ref.values()))
sizes = {}
for w in V: sizes[ref[w]] = sizes.get(ref[w], 0) + 1
from collections import Counter
dist = Counter(sizes.values())
print(f'\n--- coarsest equitable refinement ---')
print(f'  cells = {k}   size distribution = {dict(dist)}')
print(f'  claim: 48 cells, 32 singletons and 16 pairs ->',
      k == 48 and dist.get(1) == 32 and dist.get(2) == 16)

# quotient spectrum of the 48-cell equitable partition
import numpy as np
cellsr = {}
for w in V: cellsr.setdefault(ref[w], []).append(w)
order = sorted(cellsr)
B = np.zeros((k, k))
for i, c in enumerate(order):
    rep = cellsr[c][0]
    for u in nbrs(rep):
        B[i, order.index(ref[u])] += 1
ev = np.linalg.eigvals(B)
ev = sorted(round(e.real, 6) for e in ev)
cnt = Counter(ev)
print('\n--- quotient spectrum ---')
print('  eigenvalues (value: multiplicity):', dict(sorted(cnt.items())))
mult = tuple(cnt[v] for v in sorted(cnt))
print('  multiplicity vector:', mult)
print('  claim (1,5,11,14,11,5,1) ->', mult == (1,5,11,14,11,5,1))

# discarded 16-dimensional sector
A = np.zeros((64,64))
for w in V:
    for u in nbrs(w): A[idx[w], idx[u]] = 1
full = sorted(round(e.real,6) for e in np.linalg.eigvals(A))
fc = Counter(full)
rem = Counter(fc); rem.subtract(cnt); rem = {v:c for v,c in rem.items() if c}
print('\n--- discarded sector (Q_6 spectrum minus quotient spectrum) ---')
print('  dimension:', sum(rem.values()), '  spectrum:', dict(sorted(rem.items())))
A4 = np.zeros((16,16))
V4 = [''.join(t) for t in itertools.product('01', repeat=4)]
i4 = {w:i for i,w in enumerate(V4)}
for w in V4:
    for j in range(4):
        u = w[:j] + ('1' if w[j]=='0' else '0') + w[j+1:]
        A4[i4[w], i4[u]] = 1
s4 = Counter(sorted(round(e.real,6) for e in np.linalg.eigvals(A4)))
print('  spectrum of A(Q_4):', dict(sorted(s4.items())))
print('  claim "discarded sector carries A(Q_4)" ->', dict(sorted(rem.items())) == dict(sorted(s4.items())))
