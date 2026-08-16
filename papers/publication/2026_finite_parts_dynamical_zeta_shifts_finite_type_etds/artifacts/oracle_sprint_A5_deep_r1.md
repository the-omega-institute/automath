Linear radial rigidity, a collision–jet inequality, and prime-primary extensions
1. Arithmetic input and notation
For an integer p≥2, define the critical multiplicative Mahler coboundary operator
δp​R(z):=R(z)pR(zp)​.
The manuscript proves the following lifting principle. If H∈Q(z)×, H(0)=1, is zero- and pole-free on the relevant Mahler orbit, and the normalized critical product associated with H has an algebraic value at one nonzero algebraic point, then
H=δp​R
for a unique normalized R∈Q(z)×. Under positivity on a real radial segment, product value 1 is equivalent to R(α)=1. 
The published inputs entering that lifting theorem are precisely:


Kumiko Nishioka, On a problem of Mahler for transcendency of function values, J. Austral. Math. Soc. Ser. A 33 (1982), 386–393: in the specialization used here, a transcendental analytic solution of the critical p-Mahler equation has transcendental value at every admissible nonzero algebraic point. The manuscript verifies the parameters
N=0,n=1,m=M=p,U=L=1,p2<p3,
together with the coefficient-height, denominator and orbit-nonvanishing hypotheses. 


Keiji Nishioka, Algebraic function solutions of a certain class of functional equations, Arch. Math. (Basel) 44 (1985), 330–335: an algebraic Laurent-series solution of
f(zp)=R(z,f(z)),R∈C(z,Y),
belongs to C(z). In the present application,
R(z,Y)=Yp/H(z). 


The manuscript then uses the divisor identity
e(α)=r(αp)−pr(α),(1.1)
where
e(α)=ordz=α​H,r(α)=ordz=α​R,
to obtain an Op​(DlogD) bound for the total degree of R, counted with multiplicity.  The first result below instead controls the number of distinct zeros and poles. That distinction removes the logarithm from the radial sampling problem.

2. Sharp squarefree complexity of a critical Mahler certificate
For a reduced rational function
R=BA​,(A,B)=1,A(0)=B(0)=1,
write
ρ(R):=degrad(AB),
where the radical is taken over Q​. Thus ρ(R) is the number of distinct nonzero zeros and poles of R, without multiplicity.
Theorem 2.1 — Sharp squarefree Mahler bound
Let p≥2, and let
H(z)=P1​(z)P0​(z)​=R(z)pR(zp)​
with P0​,P1​∈Q[z] coprime,
P0​(0)=P1​(0)=1,D:=degP0​+degP1​,
and R∈Q(z)× normalized by R(0)=1. Then
2(p−1)ρ(R)≤D.​(2.1)
The constant 2(p−1) is sharp for every p≥2.
Proof
Let
S:={α∈Q​×:r(α)=0},s:=∣S∣=ρ(R).
Because P0​/P1​ is reduced,
D=α∈Q​×∑​∣e(α)∣.(2.2)
For β∈S, put
dβ​:=#{α∈S:αp=β}.
Define a finitely supported function
ϕ:Q​×→{−1,0,1} by
ϕ(α)=⎩⎨⎧​−sgnr(α),sgnr(αp),0,​α∈S,α∈/S, αp∈S,otherwise.​
Since ∣ϕ∣≤1, equations (1.1) and (2.2) give
D​≥α∑​e(α)ϕ(α)=β∈S∑​r(β)​αp=β∑​ϕ(α)−pϕ(β)​.​(2.3)
Fix β∈S. Of its p distinct p-th roots, exactly
p−dβ​ lie outside S. Each such external root contributes
∣r(β)∣ to (2.3). Each of the dβ​ internal roots contributes at worst
−∣r(β)∣. Finally,
−pr(β)ϕ(β)=p∣r(β)∣.
Consequently, the total contribution associated with β is at least
2(p−dβ​)∣r(β)∣≥2(p−dβ​).
Summing,
D​≥2β∈S∑​(p−dβ​)=2​ps−β∈S∑​dβ​​.​(2.4)
Now
β∈S∑​dβ​=#{α∈S:αp∈S}≤s.
Substitution into (2.4) yields
D≥2(p−1)s,
which is (2.1).
For sharpness, take
R(z)=1−zq,q≥1.
Then ρ(R)=q, while
δp​R(z)=(1−zq)p1−zpq​=(1−zq)p−11+zq+⋯+z(p−1)q​
is reduced, and its numerator and denominator both have degree
(p−1)q. Hence
D=2(p−1)q=2(p−1)ρ(R).□
Corollary 2.2 — Exact denominator bound after logarithmic differentiation
Put
u(z):=zR(z)R′(z)​.
Then
u(zp)−u(z)=pz​H(z)H′(z)​,(2.5)
and, when u is written in reduced form, its denominator has degree exactly ρ(R). Therefore
degden(u)≤⌊2(p−1)D​⌋.​(2.6)
Proof
Logarithmic differentiation of H=δp​R gives (2.5). If
r(α)=ordα​R,
then
R(z)R′(z)​=α∈S∑​z−αr(α)​.
Every α∈S is therefore a genuine simple pole of R′/R, with nonzero residue. Multiplication by z creates no cancellation because 0∈/S. Thus the reduced denominator is, up to a nonzero scalar,
α∈S∏​(z−α).
Its degree is ∣S∣=ρ(R), and (2.6) follows from Theorem 2.1. □
This is compatible with the manuscript’s sharp
Θp​(DlogD) bound for degA+degB: the logarithmic factor is carried by repeated multiplicities along long p-power divisor chains, not by the number of distinct singularities. The manuscript’s sharp family explicitly has this multiplicity accumulation. 

3. Collision–jet uncertainty
The squarefree bound has a stronger real consequence than the ordinary estimate obtained from deg(A−B).
Theorem 3.1 — Collision–jet inequality
Under the hypotheses of Theorem 2.1, suppose in addition that, for some x>0,
R(t)>0(0≤t≤x),
and that R≡1. Define
ν:=ordz=0​(R(z)−1)=ordz=0​(H(z)−1)(3.1)
and
cx​(R):=#{y∈(0,x):R(y)=1}.
Then
cx​(R)+ν≤ρ(R)≤⌊2(p−1)D​⌋.​(3.2)
Equivalently,
2(p−1)(cx​(R)+ν)≤D.​(3.3)
Proof
Write
f(t):=logR(t).
Since R(0)=1, equation (3.1) implies that f has a zero of order ν at 0. Let
0<y1​<⋯<yk​<x
be all the distinct points satisfying R(yi​)=1. Thus k=cx​(R), and f vanishes at
0,y1​,…,yk​.
The derivative f′=R′/R has a zero of order at least ν−1 at 0. Rolle’s theorem supplies at least one further zero of f′ in each of
(0,y1​), (y1​,y2​),…,(yk−1​,yk​).
Hence the numerator of R′/R has at least
(ν−1)+k
zeros, counted with multiplicity.
On the other hand,
RR′​=α∈S∑​z−αr(α)​=∏α∈S​(z−α)N(z)​
for a nonzero polynomial N satisfying
degN≤∣S∣−1=ρ(R)−1.
Therefore
ν−1+k≤ρ(R)−1,
which proves k+ν≤ρ(R). The second inequality follows from Theorem 2.1.
Finally, if
R(z)=1+azν+O(zν+1),a=0,
then
R(zp)=1+O(zpν),R(z)p=1+pazν+O(zν+1),
so
H(z)=1−pazν+O(zν+1).
This proves the equality of the two orders in (3.1). □
The first inequality in (3.2) is itself sharp. Given distinct
0<y1​<⋯<yk​<x and ν≥1, a sufficiently small nonzero rational ε makes
Rε​(z)=1+εzνi=1∏k​(z−yi​)
positive on [0,x]. Generically, Rε​ has
k+ν distinct nonzero roots, so
cx​(Rε​)+ν=ρ(Rε​).
This sharpness and the sharpness of the second inequality are separate statements; simultaneous equality in both is not asserted.

4. Prime-primary Adams collapse
Let ℓ be a prime and let G be a finite abelian ℓ-group. For a character χ∈G, write
Pχ,τ​(z)=det(I−zAχ,τ​)
and, for two cocycles τ,τ′,
Hχ​(z):=Pχ,τ′​(z)Pχ,τ​(z)​.
The relevant symmetry is weaker than imposing Adams invariance on each extension separately.
Definition 4.1 — Relative unit-Adams invariance
The pair (τ,τ′) is relatively unit-Adams invariant at ℓ if
Hχu​(z)=Hχ​(z)(4.1)
for every χ∈G and every integer u coprime to ℓ.
The manuscript’s separate condition
Pχu,τ​=Pχ,τ​,Pχu,τ′​=Pχ,τ′​
implies (4.1), but (4.1) permits cancellation between the two systems.
For
Egτ​(z)=n≥1∑​pn,g​(τ)log(1−zn),
define the Fourier profile difference
Δχ​(z):=−g∈G∑​χ(g)(Egτ​(z)−Egτ′​(z)).(4.2)
The manuscript’s Adams–Möbius formula expresses this difference in terms of all Hχm​(zk).  Under (4.1), the complete prime-primary collapse is
Δχ​(z)=−j≥0∑​ℓ−j\Log0​Hχ​(zℓj)+j≥1∑​ℓ−j\Log0​Hχℓ​(zℓj).​(4.3)
Indeed, write k=ℓjq, (q,ℓ)=1. In the Möbius divisor sum, the divisors with nonzero Möbius value are d∣q, and, when j≥1, also ℓd. Relative unit-Adams invariance gives
Hχd​=Hχ​,Hχℓd​=Hχℓ​.
The factor
d∣q∑​μ(d)
vanishes unless q=1, leaving exactly (4.3). For ℓ=2, this is the manuscript’s dyadic collapse.  For G=C3​, it identifies the precise symmetry that removes the manuscript’s generic C3​ obstruction: equality of the two conjugate determinant ratios Hχ​=Hχˉ​​ collapses the infinitely many primes 2mod3 to one ternary Mahler orbit.
Moreover, (4.1) implies
Hχ​∈Q(z).(4.4)
To see this, an automorphism of the cyclotomic character field sends χ to χu for some u coprime to ℓ. It therefore sends Hχ​ to Hχu​=Hχ​. Thus Hχ​ is fixed by the full Galois group.

5. Linear and hybrid radial rigidity
Theorem 5.1 — Prime-primary collision–jet rigidity
Let ℓ be prime and let G be a finite abelian ℓ-group. Let τ,τ′ be one-step G-cocycles over primitive base matrices A,A′ of sizes v,v′, with Perron roots λ,λ′>1. Put
x=min{λ−1,(λ′)−1}.
Assume relative unit-Adams invariance (4.1).
Suppose that, for some L≥0,
pn,g​(τ)=pn,g​(τ′)(1≤n≤L, g∈G),(5.1)
and that, for K≥1, the full profile vectors agree at K distinct radii
0<y1​,…,yK​<x,Egτ​(yi​)=Egτ′​(yi​)(5.2)
for every g∈G and every i. Assume that at least one yi​ is algebraic.
Then:
K+L≥max{v,v′}⟹pn,g​(τ)=pn,g​(τ′) for all n,g.​(5.3)
If the two base determinants are already known to agree,
det(I−zA)=det(I−zA′),(5.4)
then the stronger criterion holds:
K+L≥⌊2(ℓ−1)v+v′​⌋⟹pn,g​(τ)=pn,g​(τ′) for all n,g.​(5.5)
Proof
Set
P1​(z)=det(I−zA),P1′​(z)=det(I−zA′).
Summing (5.2) over g gives
logP1​(yi​)=logP1′​(yi​),
and both determinants are positive on (0,x). Hence
P1​(yi​)=P1′​(yi​)(1≤i≤K).(5.6)
Condition (5.1) implies
logP1​(z)−logP1′​(z)=O(zL+1),
and therefore
P1​(z)−P1′​(z)=O(zL+1).(5.7)
The polynomial P1​−P1′​ has degree at most
M0​:=max{v,v′}.
Equations (5.6)–(5.7) give it a zero of multiplicity at least L+1 at zero and K further distinct zeros. If K+L≥M0​, it has more zeros, counted with multiplicity, than its degree. Thus
P1​=P1′​,H1​=1.(5.8)
Fourier transformation of (5.2) gives
Δχ​(yi​)=0(5.9)
for every character χ.
We now prove Hχ​=1 by induction on the order of χ. The trivial case is (5.8). Let χ have order ℓa, and suppose that Hψ​=1 for every character of order less than ℓa. In particular,
Hχℓ​=1.
Formula (4.3) becomes
Δχ​(z)=−j≥0∑​ℓ−j\Log0​Hχ​(zℓj).(5.10)
By (4.4), Hχ​∈Q(z). Twisted spectral domination makes its numerator and denominator zero-free on the common open Perron disc. Since Hχ​(0)=1 and Hχ​ is real, it is positive on (0,x).
Choose an algebraic sampled radius y0​. If Hχ​=1, equations (5.9)–(5.10) give
j≥0∏​Hχ​(y0ℓj​)ℓ−j=1.(5.11)
The scalar lifting theorem supplies a unique normalized
Rχ​∈Q(z)×
such that
Hχ​(z)=Rχ​(z)ℓRχ​(zℓ)​,Rχ​(y0​)=1.(5.12)
Substitution of (5.12) into (5.10) telescopes:
Δχ​(z)​=−j≥0∑​ℓ−j(logRχ​(zℓj+1)−ℓlogRχ​(zℓj))=ℓlogRχ​(z).​(5.13)
Consequently every sampled radius satisfies
Rχ​(yi​)=1.(5.14)
Condition (5.1) gives
Δχ​(z)=O(zL+1),
so, by (5.13),
νχ​:=ord0​(Rχ​−1)≥L+1.(5.15)
Write Hχ​=P0,χ​/P1,χ​ in reduced form and put
Dχ​=degP0,χ​+degP1,χ​.
The original determinant numerator has degree at most v, and the denominator has degree at most v′; cancellation can only reduce these degrees. Hence
Dχ​≤v+v′.(5.16)
Applying Theorem 3.1 to (5.14)–(5.15) yields
K+L+1≤K+νχ​≤⌊2(ℓ−1)Dχ​​⌋≤⌊2(ℓ−1)v+v′​⌋.(5.17)
For the cross-base assertion, the last quantity is at most
max{v,v′}. Thus (5.17) contradicts
K+L≥max{v,v′}. Under (5.4), it directly contradicts (5.5). Therefore Hχ​=1, closing the induction.
All character determinants now agree. The standard determinant/trace/primitive-orbit dictionary and Fourier inversion recover every primitive length–element count.  □
Corollary 5.2 — Linear radial determination
Under the hypotheses of Theorem 5.1, with no initial periodic information (L=0),
max{v,v′} full radial profile vectors, one algebraically anchored, determine all primitive data.​(5.18)
In particular, for bases of size at most V,
M(V)=V​(5.19)
is a valid universal radial determination number for every relatively unit-Adams-invariant finite abelian ℓ-group extension.
For ℓ=2, this replaces the manuscript’s
2V⌈log2​(4V)⌉
upper bound by V. The present manuscript obtains the former bound by applying its O(DlogD) total-certificate-degree estimate in each character channel. 
Corollary 5.3 — Exact order of binary radial sampling complexity
Let NC2​​(V) be the manuscript’s universal binary radial determination number. Then
⌊4V−2​⌋+1≤NC2​​(V)≤V.​(5.20)
Consequently,
NC2​​(V)=Θ(V).​(5.21)
The lower bound is furnished by the manuscript’s explicit pairs on
4m+2 vertices with m rational collisions and different periodic data.  Thus (5.21) closes the manuscript’s O(VlogV) versus Ω(V) order gap.
Corollary 5.4 — First-discrepancy versus collision obstruction
In a nontrivial character channel satisfying the hypotheses above, let
nχ​:=ordz=0​Δχ​(z).
Equivalently, nχ​ is the first length at which the corresponding Fourier-weighted primitive data differ. If cχ​ is the total number of positive radial collisions in the common Perron interval and at least one of those collisions is algebraic, then
cχ​+nχ​≤⌊2(ℓ−1)Dχ​​⌋.​(5.22)
For two C2​-extensions on one v-vertex base,
cχ​+nχ​≤v.​(5.23)
Thus late first disagreement and many radial collisions cannot occur simultaneously. Equation (5.22) is not merely a sampling statement: it is a structural uncertainty law between the finite Taylor jet of the dynamical zeta channel and its finite set of positive special-value collisions.

6. Odd-prime realizable multi-collisions
The prime-primary theorem is not vacuous for odd primes. The following construction extends the manuscript’s binary realizable lower-bound mechanism to Cℓ​ for every odd prime ℓ, while retaining genuine Cℓ​-holonomy and strict twisted spectral gap.
Theorem 6.1 — Odd-prime multi-collisions with delayed first discrepancy
Let ℓ≥3 be prime and m≥1. There exist two one-step Cℓ​-cocycles τm​,τm′​ over the same positive primitive base with
Vm​=ℓ(2m+1)(6.1)
vertices such that:


every nontrivial character determinant is invariant under all unit Adams operations;


both cocycles have strict twisted spectral gap;


their complete element-profile vectors agree at m distinct rational radii in the open Perron interval;


their primitive length–element data agree for every length n≤m;


their first disagreement is at length m+1, and its complete element vector is explicit.


Construction and proof
Set
a:=ℓℓ,K:=4ℓ2,si​:=a(K(m+1)+i)(1≤i≤m).(6.2)
Put q=2m+1, and index a q×q matrix Cm​ by
u0​,…,um​,w1​,…,wm​.
Its only nonzero entries are
(Cm​)ui−1​,ui​​=−a,(Cm​)ui−1​,wi​​=si​,(Cm​)wi​,ui​​=si​,(6.3)
for 1≤i≤m, together with
(Cm​)um​,u0​​=−a.(6.4)
Exactly as in the manuscript’s staged-cycle determinant calculation,
Qm​(z):=det(I−zCm​)=1+azi=1∏m​(−az+si2​z2).(6.5)
All entries of Cm​ are divisible by ℓℓ.
Define an ℓq×ℓq cyclic block matrix Bm​, with blocks indexed modulo ℓ, by
(Bm​)0,1​=ℓℓ−1Cm​​,(Bm​)j,j+1​=ℓIq​(1≤j≤ℓ−2),(Bm​)ℓ−1,0​=ℓIq​,(6.6)
all other blocks being zero. Also put
Bm′​:=Cm⊕ℓ​.(6.7)
The block-companion determinant identity gives
det(I−zBm​)=det(I−zℓCm​)=Qm​(zℓ),(6.8)
whereas
det(I−zBm′​)=Qm​(z)ℓ.(6.9)
Every entry of Bm​ and Bm′​ is divisible by ℓ.
Let
S:=ℓsm​,Am​:=SJVm​​,(6.10)
where JVm​​ is the all-ones matrix. For M=Bm​ or Bm′​, define edge-count matrices
N0​(M):=ℓAm​+(ℓ−1)M​,Ng​(M):=ℓAm​−M​(g∈Cℓ​, g=0).(6.11)
These matrices are integral. They are nonnegative because
S>i,jmax​∣Mij​∣,S>(ℓ−1)i,jmax​(−Mij​).
Moreover,
N0​(M)+g=0∑​Ng​(M)=Am​.
For every nontrivial character χ of Cℓ​,
g=0∑​χ(g)=−1,
and therefore its twisted block is
N0​(M)+g=0∑​χ(g)Ng​(M)=N0​(M)−Ng​(M)=M.(6.12)
Thus every nontrivial character block is Bm​ for the first cocycle and Bm′​ for the second. In particular, unit-Adams invariance is automatic.
Since Am​ is positive and dominates ∣Bm​∣ and ∣Bm′​∣ strictly,
rad(Bm​),rad(Bm′​)<rad(Am​).(6.13)
The base Perron root is
λm​=SVm​=ℓ2(2m+1)sm​.
Define
ym,i​:=si2​a​.(6.14)
These radii are distinct, positive and rational. They lie in the open Perron interval. Indeed, using 2m+1≤2(m+1),
s12​aλm​​≥a2K2(m+1)2,=aℓ2(2m+1)sm​≤2a2ℓ2(K+1)(m+1)2,​
and
K2=16ℓ4>2ℓ2(K+1)=8ℓ4+2ℓ2.
Hence s12​>aλm​, so every ym,i​<λm−1​.
The i-th factor in (6.5) vanishes at ym,i​, and therefore
Qm​(ym,i​)=1.(6.15)
For every nontrivial character, the determinant ratio is
Hm​(z)=Qm​(z)ℓQm​(zℓ)​=δℓ​Qm​(z).(6.16)
The prime-primary telescope gives
Δχ​(z)=ℓlogQm​(z).(6.17)
Thus (6.15) makes every nontrivial Fourier profile difference vanish at all m radii. The trivial channel also vanishes because the base is common. Fourier inversion gives equality of the full element-profile vectors.
The polynomial Qm​ is nonconstant, and
Qm​(zℓ)=Qm​(z)ℓ
by comparison of the least nonconstant term. Hence the primitive data are not equal.
More precisely,
Qm​(z)=1+cm​zm+1+O(zm+2),cm​=(−1)mam+1.(6.18)
Since ℓ(m+1)>m+1,
logHm​(z)=−ℓcm​zm+1+O(zm+2).(6.19)
It follows that all nontrivial twisted traces agree through length m, while
Tr(Bmm+1​)−Tr((Bm′​)m+1)=ℓ(m+1)cm​.(6.20)
The trivial trace difference is zero. Fourier inversion on Cℓ​, followed by the triangular primitive-orbit inversion, therefore gives equality of every primitive length–element count for n≤m, and at the first differing length,
pm+1,0​(τm​)−pm+1,0​(τm′​)=(ℓ−1)cm​,​(6.21)
while, for every g=0,
pm+1,g​(τm​)−pm+1,g​(τm′​)=−cm​.​(6.22)
This proves all assertions. □
Corollary 6.2 — Linear lower bound for odd-prime symmetric extensions
Let NCℓ​UAI​(V) be the least number of radial locations that determines all primitive element data for unit-Adams-invariant Cℓ​-extensions on a common base of at most V vertices. For V≥3ℓ,
NCℓ​UAI​(V)≥⌊2⌊V/ℓ⌋−1​⌋+1.​(6.23)
Theorem 5.1 gives
NCℓ​UAI​(V)≤max{1,⌊ℓ−1V​⌋}.​(6.24)
Hence, for every fixed prime ℓ,
NCℓ​UAI​(V)=Θℓ​(V).​(6.25)
When the dependence on ℓ is retained and V is sufficiently larger than ℓ, the lower and upper bounds are both of order V/ℓ, up to absolute constant factors.

7. Antecedent check
The closest Mahler literature located was the following.
Arreche–Zhang construct complete residue obstructions for deciding whether a rational function is of the form g(zp)−g(z), and their twisted extension treats pλg(zp)−g(z). Their theory organizes poles into Mahler trees and cycles, but I found no bound of the form
2(p−1)degrad(AB)≤D,
no level-one collision bound, and no collision–jet inequality. arXiv+1
Chyzak–Dreyfus–Dumas–Mezzarobba compute rational solutions of general linear Mahler equations using denominator bounds and polynomial reconstruction. Their later first-order-factor work develops degree bounds, singularity exploration, Gräffe transforms and squarefree-factor manipulations. I found no input-only bound for the number of distinct zeros and poles of a normalized multiplicative certificate, and no application to positive special-value collisions. SPECFUN+2arXiv+2
On the dynamical side, Boyle–Schmieding treat complete periodic-data invariants, K-theoretic obstructions and families of nonconjugate finite-group extensions with the same zeta data; their results do not concern finite radial special-value determination. arXiv Parry–Pollicott’s Chebotarev theorem gives asymptotic Frobenius-class orbit counts, not finite inverse recovery from Euler-profile values. 剑桥大学出版社 O’Hare’s finite-data theorem concerns derivative data at periodic points of smooth expanding circle maps and approximate smooth conjugacy, a different finite-data problem. arXiv
Exact-form searches were also made for variants of “squarefree degree of a Mahler rational solution,” “support of R(zp)/R(z)p,” “multiplicative Mahler coboundary divisor,” “finite radial determination,” and the prime-primary Adams collapse.
Novelty conclusion: I found no antecedent for Theorems 2.1, 3.1, 5.1 or 6.1. This means “no antecedent was found in the checked literature,” not “no antecedent exists.”

8. Confidence and publication status
Correctness confidence: 0.96. The squarefree divisor inequality, collision–jet argument, Adams–Möbius collapse and matrix realization are algebraic and close under direct checking. The step of least independent certainty is the imported algebraic-special-value lifting interface: specifically, applying the manuscript’s Theorem 3.8 after descending only the relative ratio Hχ​ to Q(z). The theorem as printed requires only rationality of Hχ​, the zero-free orbit conditions and the coefficient-growth hypotheses, all of which remain valid; I see no mathematical gap there.
Novelty confidence: 0.84. Confidence is higher for the dynamical consequences and odd-prime extension than for the possibility that the elementary divisor inequality has appeared, in equivalent language, somewhere in the broader difference-algebra literature. The searches above found complete summability criteria, general denominator algorithms and squarefree Gräffe constructions, but not this inequality or its collision consequences.
Publication value: these results belong as a central new section inside the present manuscript, not as a remark. Theorem 5.1 should replace the present O(VlogV) headline by a linear theorem, while Corollary 5.3 closes the sampling-complexity order exactly. Theorem 6.1 removes the restriction to the prime 2 under the natural prime-to-ℓ Adams symmetry and supplies realizable odd-prime lower bounds. The combined package is strong enough to carry the mathematical claim of a submission, but it should not be split into a separate paper because its special-value lifting, profile coordinates and periodic-data dictionary are the central machinery of the existing article.
