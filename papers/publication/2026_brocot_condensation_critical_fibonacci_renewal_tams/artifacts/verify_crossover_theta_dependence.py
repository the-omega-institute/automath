"""Cancel the absolute normalisation: compare the RATIO inc(theta)/inc(0) at the same m
against g(theta)/g(0) = (1 - e^{-theta/mu}) * mu / theta.  This is far less sensitive to the
value of mu_C, which is itself still drifting."""
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
from mpmath import mp, zeta, mpf, e
mp.dps=30
s0=mpf('2.478750785733960260671487261390')
Fib=[0,1,1]
while Fib[-1] < 4*10**7: Fib.append(Fib[-1]+Fib[-2])
parts=[1,2]
while parts[-1] < 4*10**7: parts.append(parts[-1]+parts[-2])
MAXN=3_000_000
R=[0]*(MAXN+1); R[0]=1
for f in parts:
    if f>MAXN: break
    for n in range(MAXN,f-1,-1):
        if R[n-f]: R[n]+=R[n-f]
def Z(m,s):
    lo,hi=Fib[m+1]-1,Fib[m+2]-1
    return sum(R[N]**(-float(s)) for N in range(lo,hi) if R[N])
def inc(m,s): return Z(m,s)-Z(m-1,s)
def th(m,lam):
    s=s0+mpf(lam)/m; return m*(2 - zeta(s-1)/zeta(s))

print(f'{"m":>4} {"lambda":>8} {"theta_m":>9} {"inc(t)/inc(0)":>14} {"pred ratio":>11} {"discrepancy":>12}')
for m in (24,27,30):
    i0=inc(m,s0)
    for lam in (0.2,0.4,0.8,-0.4):
        s=s0+mpf(lam)/m; t=th(m,lam)
        meas=inc(m,s)/i0
        for mu in (mpf('16.85'),):
            pred=(1-e**(-t/mu))*mu/t
        print(f'{m:4d} {lam:8.2f} {float(t):9.5f} {float(meas):14.6f} {float(pred):11.6f} {float(meas/pred):12.5f}')
print()
print('--- how sensitive is the predicted ratio to mu_C? ---')
m=30; lam=mpf('0.8'); t=th(m,lam)
for mu in (mpf('16'),mpf('17'),mpf('18'),mpf('20')):
    print(f'   mu_C={float(mu):5.1f}: pred ratio {float((1-e**(-t/mu))*mu/t):.6f}')
print(f'   measured at m=30, lambda=0.8: {float(inc(30,s0+lam/30)/inc(30,s0)):.6f}')
