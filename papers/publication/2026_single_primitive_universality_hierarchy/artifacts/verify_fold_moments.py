"""Independent check of the two exact claims in the rebuilt single_primitive abstract.
Convention taken from the abstract itself: Fold_m : {0,1}^{m+1} -> X_m is reduction
mod F_{m+2} followed by greedy Zeckendorf normalization, with F_1 = 1, F_2 = 2.
"""
from itertools import product
F = [0, 1, 2]                     # F_1 = 1, F_2 = 2
while len(F) < 40: F.append(F[-1] + F[-2])

def fibers(m):
    M = F[m+2]
    cnt = {}
    for w in product((0,1), repeat=m+1):
        v = sum(b*F[k+1] for k, b in enumerate(w)) % M
        cnt[v] = cnt.get(v, 0) + 1
    return cnt

print('m  |X_m|=F_{m+2}  sum d = 2^{m+1}   S_2(m)      max fibre M_m')
S2 = {}; MX = {}
for m in range(1, 19):
    c = fibers(m)
    S2[m] = sum(v*v for v in c.values())
    MX[m] = max(c.values())
    ok = (sum(c.values()) == 2**(m+1))
    print(f'{m:2d}  {F[m+2]:8d}      {sum(c.values()):8d} {str(ok):5s}  {S2[m]:10d}  {MX[m]:6d}')

print('\n--- claim 1: S_2(m) = 2 S_2(m-1) + 2 S_2(m-2) - 2 S_2(m-3), m >= 4;'
      ' initial values 6, 14, 36 ---')
print('  S_2(1),S_2(2),S_2(3) =', S2[1], S2[2], S2[3],
      '  matches (6,14,36):', (S2[1], S2[2], S2[3]) == (6, 14, 36))
bad = [m for m in range(4, 19) if S2[m] != 2*S2[m-1] + 2*S2[m-2] - 2*S2[m-3]]
print('  recurrence violations for 4 <= m <= 18:', bad if bad else 'NONE')

print('\n--- claim 2: M_{2s-1} = F_{s+1},  M_{2s} = 2 F_s ---')
b1 = []; b2 = []
for s in range(1, 10):
    if 2*s-1 in MX and MX[2*s-1] != F[s+1]: b1.append((s, MX[2*s-1], F[s+1]))
    if 2*s   in MX and MX[2*s]   != 2*F[s]: b2.append((s, MX[2*s], 2*F[s]))
print('  odd  M_{2s-1} vs F_{s+1}: ', b1 if b1 else 'all match')
print('  even M_{2s}   vs 2F_s:   ', b2 if b2 else 'all match')
for s in range(1, 8):
    print(f'    s={s}: M_{2*s-1}={MX[2*s-1]} F_{s+1}={F[s+1]} | M_{2*s}={MX[2*s]} 2F_{s}={2*F[s]}')

print('\n--- mutation test: perturb the recurrence itself, confirm the check fires ---')
for a, b, cc in [(2,2,-1), (2,1,-2), (3,2,-2)]:
    v = [m for m in range(4, 19) if S2[m] != a*S2[m-1] + b*S2[m-2] + cc*S2[m-3]]
    print(f'  S2(m)={a}S2(m-1)+{b}S2(m-2)+({cc})S2(m-3): violations = {len(v)}')
