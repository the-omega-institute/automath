"""folded_histograms: verify the sharp classification.

S_m(alpha,beta) = length-m block language of the rotation by alpha coded by [0,beta).
Fold_m(omega) = Zeckendorf digits of N_m(omega) = sum omega_j F_{j+1}, truncated to m,
and Fold_m(w)=Fold_m(w') iff N_m(w) = N_m(w') mod F_{m+2}.
Claim: Fold_m injective on S_m for EVERY m  <=>  injective at m=2  <=>  beta <= delta or
beta >= 1-delta, where delta = min(alpha, 1-alpha).
"""
import sys
from math import floor
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
F=[0,1,1]
while len(F)<40: F.append(F[-1]+F[-2])
def frac(x): return x-floor(x)
def words(alpha,beta,m):
    """distinct length-m coding words, via the arcs cut by the 2m breakpoints"""
    pts=sorted({frac(-j*alpha) for j in range(m)} | {frac(beta-j*alpha) for j in range(m)})
    out=set()
    for i in range(len(pts)):
        a=pts[i]; b=pts[(i+1)%len(pts)]
        mid = (a+b)/2 if b>a else frac((a+b+1)/2)
        w=''.join('1' if frac(mid+j*alpha)<beta else '0' for j in range(m))
        out.add(w)
    return out
def injective(ws,m):
    seen={}
    for w in ws:
        k=sum(int(c)*F[j+2] for j,c in enumerate(w)) % F[m+2]
        if k in seen: return False,(seen[k],w)
        seen[k]=w
    return True,None

import random
random.seed(11)
alphas=[(5**0.5-1)/2, 2**0.5-1, 3**0.5-1, 0.123456789, 0.7182818284]
print(f'{"alpha":>12} {"beta":>8} {"delta":>8} {"pred":>6} {"m=2":>6} {"all m<=12":>10} {"agree":>6}')
bad=0; tot=0
for alpha in alphas:
    d=min(alpha,1-alpha)
    for beta in [d*0.5, d*0.9, d, d*1.05, 0.5, 1-d*1.05, 1-d, 1-d*0.9, 1-d*0.5]:
        if not (0<beta<1): continue
        pred = (beta<=d+1e-12) or (beta>=1-d-1e-12)
        i2,_=injective(words(alpha,beta,2),2)
        allm=True
        for m in range(1,13):
            ok,_=injective(words(alpha,beta,m),m)
            if not ok: allm=False; break
        tot+=1; ag=(pred==i2==allm); bad+= not ag
        print(f'{alpha:12.8f} {beta:8.5f} {d:8.5f} {str(pred):>6} {str(i2):>6} {str(allm):>10} {str(ag):>6}')
print(f'\ncases {tot}, disagreements {bad}')
print()
print('--- the m=2 mechanism, checked directly ---')
print('  N_2(w) = w1 + 2*w2 mod 3, so 00 -> 0 and 11 -> 3 = 0: the ONLY forced collision')
for alpha in alphas[:3]:
    d=min(alpha,1-alpha)
    for beta in (d*0.9, 0.5, 1-d*0.9):
        W=words(alpha,beta,2)
        print(f'   alpha={alpha:.6f} beta={beta:.5f}: S_2={sorted(W)}  00&11 both present={("00" in W and "11" in W)}  injective={injective(W,2)[0]}')
