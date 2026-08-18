"""Independent check of the four-state carry transducer in fibonacci_folding Appendix B.

The object, stated so the convention cannot drift again: for a raw word omega of length M
with Fibonacci weights F_2..F_{M+1}, compute the FULL Zeckendorf normalization of its
value, pad the raw word with two high-order zeros so the normalization is visible, and
read raw/normalized pairs from HIGH weight to LOW weight.  At a cut before position k,
P = sum over positions j > k of (a_j - z_j) * weight_j, and y^- is the normalized digit
just read (the one at the next-higher position).

This is NOT the terminal digit of a finite window; reading left-to-right or using the last
digit of a finite window label computes a different object.  That mistake is the reason
this check is being redone.
"""
import sys
from itertools import product
from collections import Counter, defaultdict
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

F = [0, 1, 1]
while len(F) < 64: F.append(F[-1] + F[-2])
def W(i): return F[i+1]           # weight of position i (1-indexed)

def zeck(n, L):
    """greedy Zeckendorf digits z_1..z_L, weights F_2..F_{L+1}"""
    z = [0]*L
    for i in range(L, 0, -1):
        if W(i) <= n:
            z[i-1] = 1; n -= W(i)
    assert n == 0, n
    return z

MAXM = 18
states = set(); trans = set(); edge_labels = defaultdict(set)
形 = Counter()
for M in range(3, MAXM+1):
    L = M + 2                       # two high-order zero pads
    for a in product((0,1), repeat=M):
        raw = list(a) + [0, 0]
        n = sum(b*W(i+1) for i, b in enumerate(raw))
        z = zeck(n, L)
        # read from high position L down to 1
        P = 0; yprev = 0
        for k in range(L, 0, -1):
            # state at the cut BEFORE reading position k
            if P == 0: form = 'P=0'
            elif P == -W(k+1): form = 'P=-w(k+1)'
            elif P == -W(k): form = 'P=-w(k)'
            else: form = f'OTHER({P} at k={k})'
            形[form] += 1
            s = (form, yprev if form != 'P=-w(k+1)' else '*')
            states.add(s)
            x, y = raw[k-1], z[k-1]
            P = P + (x - y) * W(k)
            if P == 0: nform = 'P=0'
            elif P == -W(k): nform = 'P=-w(k+1)'      # w(k)=W(k) is next cut's w(k+1)
            elif P == -W(k-1): nform = 'P=-w(k)'
            else: nform = f'OTHER({P} at k={k-1})'
            ns = (nform, y if nform != 'P=-w(k+1)' else '*')
            trans.add((s, (x, y), ns))
            edge_labels[s].add((x, y))
            yprev = y

print('--- state-form raw counts (printed before any conclusion) ---')
for k, v in 形.most_common(): print(f'  {k:24s} {v}')
print()
print('distinct states :', len(states))
for s in sorted(states, key=str): print('   ', s)
print('distinct transitions :', len(trans))
for s, lab, ns in sorted(trans, key=str):
    print(f'    {str(s):26s} --{lab[0]}{lab[1]}--> {ns}')
print()
rr = all(len(edge_labels[s]) == len(set(edge_labels[s])) for s in edge_labels)
dup = [(s, lab) for s in edge_labels for lab in edge_labels[s]
       if sum(1 for (a,l,b) in trans if a==s and l==lab) > 1]
print('right-resolving (no state has two edges with the same label):', not dup, dup[:3])
lab01 = sorted({(s, ns) for (s, l, ns) in trans if l == (0,1)})
print('edges carrying pair label 01 :', len(lab01), '->',
      'synchronizing word' if len(lab01) == 1 else 'NOT unique')
print('all eight interior transitions realized :', len(trans))

# --- does the referee's boundary qualification hold?  It claims A --01--> B cannot
# --- occur at the lowest cuts, so "exactly eight edges" is an INTERIOR statement.
print()
print('--- lowest cut position k at which each transition occurs ---')
lowest = {}
for M in range(3, 15):
    L = M + 2
    for a in product((0,1), repeat=M):
        raw = list(a) + [0, 0]
        n = sum(b*W(i+1) for i, b in enumerate(raw))
        z = zeck(n, L)
        P = 0; yprev = 0
        for k in range(L, 0, -1):
            if P == 0: form = 'P=0'
            elif P == -W(k+1): form = 'P=-w(k+1)'
            elif P == -W(k): form = 'P=-w(k)'
            else: form = 'OTHER'
            s = (form, yprev if form != 'P=-w(k+1)' else '*')
            x, y = raw[k-1], z[k-1]
            P2 = P + (x - y) * W(k)
            if P2 == 0: nf = 'P=0'
            elif P2 == -W(k): nf = 'P=-w(k+1)'
            elif P2 == -W(k-1): nf = 'P=-w(k)'
            else: nf = 'OTHER'
            ns = (nf, y if nf != 'P=-w(k+1)' else '*')
            key = (s, (x, y), ns)
            if key not in lowest or k < lowest[key]: lowest[key] = k
            P = P2; yprev = y
for key, k in sorted(lowest.items(), key=lambda t: (t[1], str(t[0]))):
    s, lab, ns = key
    print(f'    k>={k:2d}   {str(s):22s} --{lab[0]}{lab[1]}--> {ns}')
