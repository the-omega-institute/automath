"""Check the referee's proposed repair of Proposition 3.2 (window6).

At eps = 1/6 with m = 6, for a source cell x and target cell y the admissible entries are
  intersection over omega in F^{-1}(x) of [ c_omega(y)/6 - 1/6 , c_omega(y)/6 + 1/6 ],
so the box is [L_xy, U_xy] with
  L_xy = max(0, (max_omega c_omega(y) - 1)/6),  U_xy = min(1, (min_omega c_omega(y) + 1)/6),
where c_omega(y) = number of neighbours of omega lying in cell y.
A stochastic row exists inside the box iff  sum_y L_xy <= 1 <= sum_y U_xy.
The referee reports max_x sum_y L = 1/2 and min_x sum_y U = 7/2.
"""
import re, io, itertools, sys
from fractions import Fraction
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
src = io.open(r"D:\omega\automath\papers\publication\2026_window6_spectral_rigidity_hypercube_lumpability_fold_gauge\main.tex",
              encoding='utf-8').read()
fiber_section = src.split('The fibers, in lexicographic order of', 1)[1].split(chr(92)+'end{definition}', 1)[0]
blocks = re.findall(r'\\begin\{array\}\{c\|l\}(.*?)\\end\{array\}', fiber_section, re.S)
blk = (chr(92) * 2).join(blocks)
cells = {}
for line in blk.split(chr(92)*2):
    if '&' not in line: continue
    lab, rest = line.split('&', 1)
    ws = [w.strip() for w in rest.replace('\n', ' ').split(',') if re.fullmatch(r'[01]{6}', w.strip())]
    if ws: cells[lab.strip()] = ws
labels = list(cells)
cell_of = {w: lab for lab, ws in cells.items() for w in ws}
def nbrs(w): return [w[:i] + ('1' if w[i] == '0' else '0') + w[i+1:] for i in range(6)]
print('cells:', len(cells), ' vertices:', sum(len(v) for v in cells.values()))

sumL, sumU = {}, {}
for x in labels:
    tot_L = Fraction(0); tot_U = Fraction(0)
    for y in labels:
        cs = [sum(1 for u in nbrs(w) if cell_of[u] == y) for w in cells[x]]
        L = max(Fraction(0), Fraction(max(cs) - 1, 6))
        U = min(Fraction(1), Fraction(min(cs) + 1, 6))
        tot_L += L; tot_U += U
    sumL[x] = tot_L; sumU[x] = tot_U
bad = [x for x in labels if not (sumL[x] <= 1 <= sumU[x])]
print('\nrows where sum L <= 1 <= sum U fails :', bad if bad else 'NONE  (a stochastic row is selectable in every box)')
mx = max(sumL.values()); mn = min(sumU.values())
print(f'max_x sum_y L_xy = {mx}   referee says 1/2  -> {mx == Fraction(1,2)}')
print(f'min_x sum_y U_xy = {mn}   referee says 7/2  -> {mn == Fraction(7,2)}')
print('\ndistinct sum_y L values:', sorted(set(sumL.values())))
print('distinct sum_y U values:', sorted(set(sumU.values())))
print('\n--- control: at eps = 0 the boxes should mostly be empty/infeasible ---')
bad0 = 0
for x in labels:
    tL = Fraction(0); tU = Fraction(0)
    for y in labels:
        cs = [sum(1 for u in nbrs(w) if cell_of[u] == y) for w in cells[x]]
        tL += Fraction(max(cs), 6); tU += Fraction(min(cs), 6)
    if not (tL <= 1 <= tU): bad0 += 1
print(f'  rows failing at eps=0: {bad0} of {len(labels)}  (nonzero means the check discriminates)')
