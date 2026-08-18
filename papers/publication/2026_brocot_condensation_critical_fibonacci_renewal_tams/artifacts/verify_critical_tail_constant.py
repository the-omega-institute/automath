"""The paper's Lemma (critical tail summation) asserts the SHARP constant
    b_{2d+1}(sigma_0) ~ b_C * d^{-sigma_0},    b_C = 2 (zeta(s-1)/zeta(s))^2 = 8 at s = sigma_0.
Test that constant directly.
"""
import sys, math
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
sigma0 = 2.4787507857339602606714872614

def denoms(d):
    out = []
    def rec(rem, num, den):
        if rem == 0: out.append(num); return
        for a in range(1, rem+1):
            e = a + 1
            if num is None: rec(rem-a, e, 1)
            else: rec(rem-a, e*num - den, num)
    rec(d, None, None)
    return out

print(f'{"d":>4} {"b_(2d+1)":>16} {"b*d^sigma0":>13} {"increment":>11}')
prev=None; rows=[]
for d in list(range(4, 26)):
    b = sum(q**(-sigma0) for q in denoms(d))
    v = b * d**sigma0
    rows.append((d, v))
    inc = v-prev if prev else float('nan')
    print(f'{d:4d} {b:16.9e} {v:13.6f} {inc:11.6f}')
    prev = v

print()
print('paper claims b_C = 8')
d0,v0 = rows[-1]
incs = [rows[i][1]-rows[i-1][1] for i in range(1,len(rows))]
r = incs[-1]/incs[-2] if len(incs)>1 and incs[-2] else float('nan')
print(f'  last value at d={d0}: {v0:.4f}   last increment {incs[-1]:.5f}, ratio to previous {r:.4f}')
if 0 < r < 1:
    print(f'  geometric extrapolation of the remaining tail: +{incs[-1]*r/(1-r):.4f}  ->  limit ~ {v0+incs[-1]*r/(1-r):.3f}')
# Richardson with 1/d correction
xs=[1/d for d,_ in rows[-8:]]; ys=[v for _,v in rows[-8:]]
n=len(xs); mx=sum(xs)/n; my=sum(ys)/n
c=sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs)
print(f'  fit v(d) = A + B/d      ->  A = {my-c*mx:.4f}')
xs=[1/math.sqrt(d) for d,_ in rows[-8:]]
mx=sum(xs)/n; c=sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs)
print(f'  fit v(d) = A + B/sqrt(d) ->  A = {my-c*mx:.4f}')
print()
print(f'  2*rho^2 at sigma_0 where rho = zeta(s-1)/zeta(s) = 2  gives  2*4 = 8')
print(f'  measured level is roughly {v0:.1f} and still rising -> ratio to 8 is {v0/8:.3f}')
