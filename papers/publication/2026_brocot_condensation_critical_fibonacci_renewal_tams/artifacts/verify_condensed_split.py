"""My factor-2 diagnosis was wrong.  Check the referee's account instead:
split b_{2d+1}(sigma_0) * d^{sigma_0} into
  (a) the CONDENSED part: regular words having a partial quotient > (d+1)/2
  (b) the rest,
and see whether (a) converges to 2 rho^2 = 8 while (b) is merely slow to vanish.
Words are the canonical regular expansions of q/p with digit sum n = d+1.
"""
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
sigma0 = 2.4787507857339602606714872614

def walk(n):
    """yield (continuant, max_digit) over canonical regular words with digit sum n,
       canonical = last digit >= 2 (and the single-word case a_0 = n)."""
    out = []
    def rec(rem, k0, k1, mx):
        # k1 = continuant so far, k0 = previous
        if rem == 0:
            out.append((k1, mx)); return
        for a in range(1, rem+1):
            if a == rem and a < 2 and rem != 1:
                continue          # canonical: terminal digit >= 2 unless the word is a single 1
            if a == rem and a == 1:
                # terminal digit 1 not allowed in canonical form except the whole word (1)
                if k1 != 1: continue
            rec(rem-a, k1, a*k1 + k0, max(mx, a))
    rec(n, 0, 1, 0)
    return out

print(f'{"d":>4} {"total":>10} {"one large digit":>16} {"rest":>10}   (all scaled by d^sigma_0)')
for d in (10, 15, 20, 25):
    n = d + 1
    tot = big = 0.0
    for K, mx in walk(n):
        w = K**(-sigma0)
        tot += w
        if mx > (d+1)/2: big += w
    sc = d**sigma0
    print(f'{d:4d} {tot*sc:10.5f} {big*sc:16.5f} {(tot-big)*sc:10.5f}')
print()
print('referee reports  total 8.406 / 11.584 / 13.220 / 13.861')
print('and              condensed 5.060 / 6.366 / 8.166 / 8.658  ->  heading to 2 rho^2 = 8')
