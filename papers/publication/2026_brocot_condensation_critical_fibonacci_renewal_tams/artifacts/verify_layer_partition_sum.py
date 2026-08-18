"""Compute Z_m^R(-sigma_0) directly from R(N) and see what Z_m/m converges to.

R(N) = number of representations of N as a sum of DISTINCT Fibonacci numbers 1,2,3,5,8,...
I_m = [F_{m+1}-1, F_{m+2}-1),  Z_m^R(t) = sum_{N in I_m} R(N)^t.
The paper's theorem at theta = 0 says Z_m^R(-sigma_0) grows linearly; the agent's corrected
crossover says Z_m/m -> 2/mu_C at theta = 0, while the statement I gave it says m*Z_m -> 1/(2 mu_C).
Those differ by a factor of 4 and by a power of m, so the data settles it.
"""
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
sigma0 = 2.4787507857339602606714872614
F=[1,2]
while F[-1] < 3*10**7: F.append(F[-1]+F[-2])   # parts 1,2,3,5,...
# Fibonacci layer bounds use F_{m+1}-1 with F_1=1,F_2=1 convention: layer m = [Fib(m+1)-1, Fib(m+2)-1)
Fib=[0,1,1]
while Fib[-1] < 3*10**7: Fib.append(Fib[-1]+Fib[-2])

MAXN = 3_000_000
R=[0]*(MAXN+1); R[0]=1
for f in F:
    if f > MAXN: break
    for n in range(MAXN, f-1, -1):
        if R[n-f]: R[n]+=R[n-f]

print(f'{"m":>3} {"|I_m|":>10} {"Z_m":>14} {"Z_m/m":>10} {"m*Z_m":>14}')
rows=[]
for m in range(6, 34):
    lo, hi = Fib[m+1]-1, Fib[m+2]-1
    if hi > MAXN: break
    z = sum(R[N]**(-sigma0) for N in range(lo, hi) if R[N])
    rows.append((m, z))
    print(f'{m:3d} {hi-lo:10d} {z:14.6f} {z/m:10.6f} {m*z:14.4f}')
print()
print('--- which normalisation is stable? ---')
last = rows[-6:]
print('  Z_m/m over the last six m :', [f'{z/m:.5f}' for m,z in last])
print('  m*Z_m over the last six m :', [f'{m*z:.2f}' for m,z in last])
print()
if last:
    v = last[-1][1]/last[-1][0]
    print(f'  Z_m/m at the largest m = {v:.6f}')
    print(f'  if that is 2/mu_C then mu_C = {2/v:.4f}')
    print(f'  (my enumerated mu_C at Q=3000 was 17.295 and still rising)')
