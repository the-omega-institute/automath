# -*- coding: utf-8 -*-
"""Redo with single_primitive's fold as it is actually defined: reduction mod F_{m+2}."""
STD=[0,1,1]
while len(STD)<90: STD.append(STD[-1]+STD[-2])
SP=[0]+[STD[k+1] for k in range(1,85)]        # their F_k = standard F_{k+1}

def M_sp(m):
    """Omega_m = {0,1}^{m+1}, weights F_1..F_{m+1}, fibres are residue classes mod F_{m+2}."""
    mod=SP[m+2]
    c=[0]*mod
    c[0]=1
    for j in range(1,m+2):
        k=SP[j]%mod
        c=[c[(n-k)%mod]+c[n] for n in range(mod)]
    return max(c), sum(c)

def D_proj(m):
    w=[STD[j] for j in range(1,m+1)]
    N=sum(w); c=[0]*(N+1); c[0]=1
    for k in w:
        for n in range(N,k-1,-1): c[n]+=c[n-k]
    return max(c)

print("single_primitive with modular fibres, against its own formula and listed values")
listed=[2,2,3,4,5,6,8,10,13,16]
ok=True
print("  m   brute   formula   listed   total=2^(m+1)?")
for m in range(1,19):
    b,tot=M_sp(m)
    f = SP[(m+1)//2+1] if m%2==1 else 2*SP[m//2]
    lst=listed[m-1] if m<=10 else None
    good=(b==f) and (lst is None or b==lst) and tot==2**(m+1)
    ok&=good
    print(f" {m:3d}  {b:6d}   {f:6d}   {str(lst):>6}   {tot==2**(m+1)}   {'ok' if good else 'MISMATCH'}")
print("single_primitive verified:",ok)
print()
print("relation between the two papers' maxima")
for m in range(2,16):
    b,_=M_sp(m)
    print(f"  m={m:3d}   M_m(single_primitive)={b:6d}   D_m(projection)={D_proj(m):6d}   "
          f"D_{{m+1}}={D_proj(m+1):6d}")
