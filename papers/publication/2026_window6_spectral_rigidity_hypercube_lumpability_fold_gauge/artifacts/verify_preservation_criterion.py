"""Proposed criterion, to be tested against brute force on every candidate.

Adding F_k puts a new Zeckendorf digit at position k-1.  If Z(N) already carries a digit at
position k-2, the two merge (F_{k-1} + F_k = F_{k+1}) and the digit at k-2 is consumed.
So sigma preserves the fold exactly when
   (1) k - 1 > m                                   [the new digit lands above the window]
   AND
   (2) k - 2 > m  OR  no admissible N has a Zeckendorf digit at position k-2
                                                   [nothing visible is consumed]
where admissible means the two swapped bits are both clear.
"""
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
F=[0,1,1]
while len(F)<200: F.append(F[-1]+F[-2])
fibidx={F[k]:k for k in range(2,120)}
def zpos(N):
    out=[]; n=N; r=100
    while r>=1:
        if F[r+1]<=n: n-=F[r+1]; out.append(r)
        r-=1
    return out
def low(N,m): return [r for r in zpos(N) if r<=m]

print(f'{"m":>3} {"i,j":>7} {"F_k":>10} {"brute":>6} {"criterion":>10} {"agree":>6}')
bad=0; tot=0
for m in range(2,17):
    for i in range(1,m+1):
        for j in range(i+1,m+1):
            s=2**(m-i)+2**(m-j)
            if s not in fibidx: continue
            k=fibidx[s]; wi=1<<(m-i); wj=1<<(m-j)
            brute=all(low(N,m)==low(N+s,m) for N in range(2**m) if not (N & wi) and not (N & wj))
            c1 = (k-1 > m)
            if k-2 > m: c2=True
            else:
                c2 = not any((k-2) in zpos(N) for N in range(2**m) if not (N & wi) and not (N & wj))
            crit = c1 and c2
            tot+=1; ag=(brute==crit); bad += not ag
            print(f'{m:3d} {f"{i},{j}":>7} {f"F_{k}={s}":>10} {str(brute):>6} {str(crit):>10} {str(ag):>6}')
print()
print(f'candidates tested: {tot}   disagreements: {bad}')
