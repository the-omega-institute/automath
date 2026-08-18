"""Redo the test on the agent's terms:
 (a) mu_C = 21.774226 from the paper's own calibration, not my 16.85 from a drifting increment;
 (b) the ALONG-WINDOW increment Z_m(s_m) - Z_{m-1}(s_{m-1}), since the theorem's sequence has s
     varying with the layer, not a fixed-s adjacent-layer difference;
 (c) and check the size of the known correction term, which the paper gives as j^{2-sigma_0}.
"""
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
from mpmath import mp, zeta, mpf, e
mp.dps=30
s0=mpf('2.478750785733960260671487261390')
muC=mpf('21.774225990')
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
def th(m,lam):
    s=s0+mpf(lam)/m; return m*(2 - zeta(s-1)/zeta(s))

print(f'the paper says the correction is O(j^(2-sigma_0)); at m=30 that is {float(mpf(30)**(2-s0)):.4f}')
print(f'so a 20-30 percent gap at m=30 is expected, not evidence of a wrong constant')
print()
print(f'{"lam":>6} {"m":>4} {"theta_m":>8} {"Z_m/m":>9} {"along-window inc":>17} {"2(1-e^-t/mu)/t":>15} {"ratio":>7}')
for lam in (0.0, 0.4, 0.8, -0.4):
    for m in (26, 30):
        sm=s0+mpf(lam)/m; sm1=s0+mpf(lam)/(m-1)
        t=th(m,lam) if lam!=0 else mpf('1e-9')
        aw = Z(m,sm)-Z(m-1,sm1)
        pred = 2*(1-e**(-t/muC))/t
        print(f'{lam:6.2f} {m:4d} {float(t):8.4f} {Z(m,sm)/m:9.6f} {aw:17.6f} {float(pred):15.6f} {float(aw/pred):7.4f}')
print()
print('--- the ratio test again, but along-window and with the paper mu_C ---')
for m in (24,27,30):
    i0=Z(m,s0)-Z(m-1,s0)
    for lam in (0.4,0.8):
        sm=s0+mpf(lam)/m; sm1=s0+mpf(lam)/(m-1); t=th(m,lam)
        meas=(Z(m,sm)-Z(m-1,sm1))/i0
        pred=(1-e**(-t/muC))*muC/t
        print(f'  m={m} lam={float(lam):.1f} theta={float(t):.4f}: measured {float(meas):.6f}  predicted {float(pred):.6f}  ratio {float(meas/pred):.4f}')
