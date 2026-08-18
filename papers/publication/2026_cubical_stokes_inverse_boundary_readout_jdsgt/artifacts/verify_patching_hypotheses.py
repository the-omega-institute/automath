"""cubical_stokes: verify the repaired patching theorem on small dual networks, and check that the
two counterexamples fail exactly where the added hypotheses say they should.

Theorem: with B the reduced incidence matrix of a sink-connected augmented dual graph,
    min { max_e |f_e|/a_e : B f = v }  =  h_K := max_{S nonempty} v(S)/a(delta S).
"""
import sys, itertools, random
from fractions import Fraction
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
try:
    from scipy.optimize import linprog
    HAVE=True
except Exception as ex:
    HAVE=False; print('scipy unavailable:', ex)

def hK(cells, faces, v, a):
    """max over nonempty S of v(S)/a(delta S); faces are (C1,C2) with C2 possibly '*'"""
    best=None; arg=None
    for r in range(1,len(cells)+1):
        for S in itertools.combinations(cells,r):
            Sset=set(S)
            d=[i for i,(c1,c2) in enumerate(faces) if (c1 in Sset) != (c2 in Sset)]
            ad=sum(a[i] for i in d)
            if ad==0: continue
            val=sum(v[c] for c in S)/ad
            if best is None or val>best: best, arg = val, S
    return best, arg

def min_norm(cells, faces, v, a):
    """min M s.t. exists f with Bf=v and |f_e| <= M a_e; LP in variables (f, M)"""
    n=len(faces); idx={c:i for i,c in enumerate(cells)}
    Aeq=[[0.0]*(n+1) for _ in cells]; beq=[float(v[c]) for c in cells]
    for j,(c1,c2) in enumerate(faces):
        if c1 in idx: Aeq[idx[c1]][j]+= 1.0
        if c2 in idx: Aeq[idx[c2]][j]+= -1.0
    Aub=[]; bub=[]
    for j in range(n):
        r=[0.0]*(n+1); r[j]=1.0; r[n]=-float(a[j]); Aub.append(r); bub.append(0.0)
        r=[0.0]*(n+1); r[j]=-1.0; r[n]=-float(a[j]); Aub.append(r); bub.append(0.0)
    c=[0.0]*n+[1.0]
    res=linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                bounds=[(None,None)]*n+[(0,None)], method='highs')
    return res.x[-1] if res.success else None

print('--- random sink-connected networks satisfying the hypotheses ---')
random.seed(7)
bad=0; tested=0
for trial in range(60):
    nc=random.randint(2,5); cells=list(range(nc))
    faces=[]; a=[]
    for i in range(nc):                      # every cell gets a boundary face -> sink connected
        faces.append((i,'*')); a.append(random.randint(1,4))
    for i in range(nc):                       # a few internal faces
        for j in range(i+1,nc):
            if random.random()<0.5: faces.append((i,j)); a.append(random.randint(1,4))
    v={c:random.randint(1,5) for c in cells}
    if not HAVE: break
    h,_=hK(cells,faces,v,a); m=min_norm(cells,faces,v,a)
    tested+=1
    if m is None or abs(m-h)>1e-7: bad+=1; print(f'  MISMATCH trial {trial}: h_K={h} min={m}')
print(f'  tested {tested}, mismatches {bad}')

print()
print('--- counterexample 1: a shared face with incidences (+1,+1), violating reduced incidence ---')
# two cells sharing a face whose column is (+1,+1); model by an edge that leaves BOTH cells
cells=[0,1]; faces=[(0,'*'),(1,'*')]; a=[1,1]; v={0:1,1:1}
h,_=hK(cells,faces,v,a); m=min_norm(cells,faces,v,a)
print(f'   with the face repaired as a proper internal edge: h_K={h:.4f} min={m:.4f} equal={abs(h-m)<1e-7}')
import numpy as np
Aeq=np.array([[1.0,0.0,1.0],[0.0,1.0,1.0]])   # the (+1,+1) column appended
beq=np.array([1.0,1.0]); aa=[1,1,1]
from scipy.optimize import linprog as lp
n=3
Aub=[]; bub=[]
for j in range(n):
    r=[0.0]*(n+1); r[j]=1.0; r[n]=-aa[j]; Aub.append(r); bub.append(0.0)
    r=[0.0]*(n+1); r[j]=-1.0; r[n]=-aa[j]; Aub.append(r); bub.append(0.0)
res=lp([0.0]*n+[1.0], A_ub=Aub,b_ub=bub,
       A_eq=np.hstack([Aeq,np.zeros((2,1))]), b_eq=beq,
       bounds=[(None,None)]*n+[(0,None)], method='highs')
print(f'   with the (+1,+1) column present: LP min = {res.x[-1]:.4f}')
print(f'   h_K computed from the cut formula ignores that column-sign defect, so the identity is not')
print(f'   the same statement - which is exactly why the hypothesis is needed.')

print()
print('--- counterexample 2: a closed component with positive source and no boundary face ---')
cells=[0,1]; faces=[(0,1)]; a=[1]; v={0:1,1:1}
h,_=hK(cells,faces,v,a); m=min_norm(cells,faces,v,a)
print(f'   h_K={h}   LP min={m}   (LP infeasible => None, since sum v over the closed component is 2 != 0)')
