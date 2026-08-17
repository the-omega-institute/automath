The attached revision correctly identifies the logical gap: one-rewrite support does not control the causal cone of completed normalization, and the m=5 example leaves the claimed threshold unproved. 
The two conclusions are:
The sharp general core bound is m+1.​
There is no bound independent of m, even with rewrite span fixed at r=3. In fact, the Fibonacci fold has deletion-minimal cores of the full possible length m+1 for every m≥5.
Independently,
Φm​ is injective for every m≥3.​
For m≥4, three consecutive labels give an explicit arithmetic decoder. The case m=3 is a separate finite argument.
1. The sharp core bound
I count the length of a core by the number of raw coordinates, as in the length-6 example at m=5.
Index a raw lift by positions 0,…,m. For two lifts u,v, put
di​=ui​−vi​∈{−1,0,1}.
Write
M=Fm+2​.
The pair u,v is a two-label ambiguity exactly when
Δ0​(d):=i=0∑m−1​di​Fi+2​≡0(modM),(1)
and
Δ1​(d):=i=1∑m​di​Fi+1​≡0(modM).(2)
Indeed, these are precisely the value differences of the first and second length-m windows.
The trivial upper bound is m+1, since two consecutive m-windows have only m+1 raw coordinates. The point is that this upper bound is attained.
Odd m
Let m=2q+1, q≥1, and take
dodd=(0,−1,−1,(0,−1)q−1,1).(3)
Equivalently, one may take the binary lifts
u=02q+11,v=011(01)q−10.(4)
For q=2, this is exactly
u=000001,v=011010.
Using
k=1∑q​F2k+1​=F2q+2​−1,k=1∑q​F2k+2​=F2q+3​−2,
one gets
Δ0​=−2−k=1∑q​F2k+2​=−F2q+3​=−Fm+2​,(5)
and
Δ1​=F2q+2​−1−k=1∑q​F2k+1​=0.(6)
So the two labels agree.
It remains to prove that every coordinate is active.
Set
a:=Fm+1​,b:=Fm​,M=a+b.
After deleting coordinate j, the new window length is m−1, so the new modulus is a=Fm+1​. Let Cj​ be the value difference of the first shortened window. Explicitly,
Cj​=⎩⎨⎧​i<j∑​di​Fi+2​+j<i≤m−1∑​di​Fi+1​,i=0∑m−2​di​Fi+2​,​0≤j<m,j=m.​(7)
Substitution into (7), or induction using
Cj​−Cj−1​=(dj−1​−dj​)Fj+1​,(8)
gives
C0​=−a,C1​=1−a,(9)
Cj​=−a+(−1)jFj​(2≤j≤m−1),(10)
and
Cm​=−b.(11)
For every j≥1, Cj​ is not divisible by a:


1−a, −a+Fj​, and −b lie strictly between −a and 0;


−a−Fj​ lies strictly between −2a and −a.


For j=0, the first shortened difference C0​=−a does vanish modulo a, but the second shortened-window difference is
D0​=i=2∑m​di​Fi​=Fm​−k=1∑q​F2k​=1.(12)
Thus deletion of coordinate 0 also destroys the ambiguity. No coordinate is passive.
So (3) is a core of length m+1 for every odd m≥3.
Even m
Let m=2q≥6, and take
deven=(0,−1,−1,(0,−1)q−3,1,−1,−1,1).(13)
Equivalently,
u=02q−31001,v=011(01)q−30110.(14)
For example, at m=6,
u=0001001,v=0110110.
Here the positive entries of d are at m−3 and m, while the negative entries are at 1, at every even position 2,4,…,m−2, and at m−1.
The first-window difference is
Δ0​​=Fm−1​−2−k=1∑q−1​F2k+2​−Fm+1​=Fm−1​−2Fm+1​=−Fm+2​,​(15)
and the second-window difference is
Δ1​​=Fm−2​+Fm+1​−1−k=1∑q−1​F2k+1​−Fm​=Fm−2​+Fm+1​−2Fm​=0.​(16)
So this is again a two-label ambiguity.
The deletion values are
C0​=−a,D0​=1,C1​=1−a,(17)
Cj​=−a+(−1)jFj​(2≤j≤m−4),(18)
Cm−3​=−a−Fm−1​,(19)
and
Cm−2​=Cm−1​=Cm​=−b.(20)
Again, every Cj​ with j≥1 lies strictly between two consecutive multiples of a, and D0​=1. Hence no deletion preserves the ambiguity.
Thus there are full-length cores for every even m≥6.
Consequence
For the Fibonacci fold,
Lcore​≤m+1​
is the sharp uniform bound, attained for every m≥5 and also at m=3.
Therefore there is no bound g(r) independent of m. The rewrite span remains fixed at r=3, while the minimal core length tends to infinity and in fact fills the entire union of the two windows.
More generally, under the manuscript’s convention that “span r” means rewrite support of size at most r, this also rules out an m-independent bound for every r≥3.
The only small exception is m=4: direct enumeration gives the four ambiguity differences
±(0,−1,−1,1,0),±(0,0,−1,−1,1),
and each has a passive coordinate, reducing to the m=3 core. Thus, if K(m) denotes the largest core arising from an m-window ambiguity,
K(3)=4,K(4)=4,K(m)=m+1(m≥5).(21)
2. Injectivity of Φm​
The core classification is unnecessary. There is an arithmetic cancellation among three consecutive rolling window values.
Let x=(xt​)t∈Z​, and let
yt​=(Φm​(x))t​.
Write
rt​:=N(yt​)∈{0,…,Fm+2​−1}.
Thus rt​ is the residue represented by the label. Put again
M=Fm+2​,a=Fm+1​,b=Fm​.
Before reduction modulo M, the value of the window ending at t is
St​=k=1∑m​xt−m+k​Fk+1​,St​≡rt​(modM).(22)
Using Fj+2​=Fj+1​+Fj​, all interior terms cancel in
St−2​−St−1​−St​.
The exact identity is
St−2​−St−1​−St​=xt−m−1​+xt−m​−Mxt−1​−axt​.(23)
Consequently, if
τt​:=(rt−2​−rt−1​−rt​)modM∈{0,…,M−1},(24)
then
τt​≡xt−m−1​+xt−m​−axt​(modM).(25)
If xt​=0, then
τt​∈{0,1,2}.(26)
If xt​=1, then −a≡M−a=b(modM), so
τt​∈{b,b+1,b+2}={Fm​,Fm​+1,Fm​+2}.(27)
For m≥4, Fm​≥3, so the two sets in (26) and (27) are disjoint. Therefore
xt​={0,1,​τt​∈{0,1,2},τt​∈{Fm​,Fm​+1,Fm​+2}.​​(28)
This is an explicit decoder from the three labels
yt−2​, yt−1​, yt​.
Hence Φm​ is injective for every m≥4. More strongly, the claimed three-label inverse exists directly, with no core reduction.
Equivalently, the cancellation is encoded by the polynomial identity
(1−z−z2)j=0∑m−1​Fj+2​zj=1+z−Fm+2​zm−Fm+1​zm+1.(29)
The term Fm+2​zm vanishes modulo the window modulus, leaving exactly the bit-separating relation above.
The case m=3
Here M=5, a=3, b=2. The two sets in (26) and (27) overlap at 2, so the threshold decoder (28) alone is not enough.
Suppose two configurations have the same labels, and let
dt​=xt​−xt′​∈{−1,0,1}.
Every length-3 difference block must satisfy
dn​+2dn+1​+3dn+2​≡0(mod5).(30)
There are exactly five possibilities:
(−1,−1,1),(0,−1,−1),(0,0,0),(0,1,1),(1,1,−1).(31)
Their overlap graph is immediate:
(0,−1,−1)⟶(−1,−1,1),
but no allowed block begins with (−1,1); similarly,
(0,1,1)⟶(1,1,−1),
but no allowed block begins with (1,−1). The blocks (−1,−1,1) and (1,1,−1) therefore cannot occur in a right-infinite admissible difference sequence. The only indefinitely extendable block is
(0,0,0)⟶(0,0,0).
Thus every bi-infinite difference sequence satisfying (30) is identically zero. Hence x=x′, and
Φ3​ is injective.​
This agrees with the manuscript’s direct m=3 calculation, which is independent of the withdrawn core reduction: it finds only two ambiguous pairs and shows that their successor-label sets are disjoint. 
Therefore
Φm​ is injective for all m≥3.​(32)
Since Φm​ is a continuous shift-commuting map from the compact full shift onto its image, injectivity implies that it is a homeomorphism onto that image; its inverse is again a sliding block code. Thus the conjugacy conclusion is true, although the finite-core proof of it is not.
For comparison, m=2 genuinely fails: the constant configurations 0Z and 1Z have the same constant label sequence.
Computational checks performed
The proofs above are analytic. I also made two exhaustive checks.
For cores, for every 1≤m≤12, I enumerated all 3m+1 difference words d∈{−1,0,1}m+1, tested the two ambiguity congruences (1)–(2), and then tested all m+1 coordinate deletions using the shorter modulus Fm+1​. Full-length cores occurred at m=2,3 and at every 5≤m≤12; none occurred at m=4. The two formula families above prove that this continues for all odd m≥3 and all even m≥6.
For injectivity, for every 1≤m≤12, I enumerated all ternary length-m blocks satisfying the window-kernel congruence, formed their (m−1)-overlap graph, and computed its recurrent strongly connected components. The only nonzero recurrent components occurred at m=2, corresponding to the two constant-sign difference sequences. For every m≥3 in that range, the sole recurrent component was the all-zero one.
