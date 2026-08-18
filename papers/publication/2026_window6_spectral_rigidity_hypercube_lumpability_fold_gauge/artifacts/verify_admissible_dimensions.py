"""Push the sweep past m=16 cheaply.  Only four Fibonacci numbers are sums of two distinct powers
of two, so each m has at most four candidate coordinate pairs; test each by streaming over words
and short-circuiting, with no 2^m-sized lists held in memory."""
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
F=[0,1,1]
while len(F)<200: F.append(F[-1]+F[-2])
fibidx={F[k]:k for k in range(2,120)}
def zeck_low(N, m):
    """first m Zeckendorf digits of N (positions 1..m, weights F_2..F_{m+1})"""
    z=0; n=N; r=100
    while r>=1:
        if F[r+1]<=n:
            n-=F[r+1]
            if r<=m: z |= (1<<(r-1))
        r-=1
    return z
print(f'{"m":>3} {"candidates":>34} {"preserving pairs":>18}')
hits=[]
for m in range(3,23):
    cands=[]
    for i in range(1,m+1):
        for j in range(i+1,m+1):
            s=2**(m-i)+2**(m-j)
            if s in fibidx: cands.append((i,j,fibidx[s],s))
    good=[]
    for (i,j,k,s) in cands:
        wi=1<<(m-i); wj=1<<(m-j)
        ok=True
        for N in range(2**m):
            if (N & wi) or (N & wj): continue     # only the (0,0) pattern moves upward
            if zeck_low(N, m) != zeck_low(N+s, m): ok=False; break
        if ok: good.append((i,j,f'F_{k}={s}'))
    if good: hits.append(m)
    print(f'{m:3d} {str([(i,j,f"F_{k}") for i,j,k,s in cands]):>34} {str(good):>18}')
print()
print('m admitting a fold-preserving swap-and-complement involution:', hits)
