(1) Your enumeration is correct; the factor-2 diagnosis is not
I independently reproduced your finite sums from the negative-continuant recurrence. To the displayed precision I obtain exactly
d10152025​dσ0​b2d+1​(σ0​)8.4057692411.5844543913.2195505813.86148925.​​
So there is no systematic bias in your enumeration, no incorrect value of σ0​, and no failure of the negative-to-regular continued-fraction bijection. Your identity
d(p/q)=i∑​ai​−1
is precisely the manuscript’s termwise identification: the cost-2d+1 fractions correspond to canonical regular words of digit sum d+1, and hence
b2d+1​(s)=Zd+1​(s).
The paper proves this by the same negative-to-regular conversion you checked. 
The error is instead in treating the two contexts symmetrically as unrestricted finite words.
The two context sums are different
Write a canonical regular word containing its unique large digit as
(u,a,v),a=n−∣u∣1​−∣v∣1​.
Because the whole regular expansion is canonical, its terminal digit must be at least 2. Consequently,
u∈WL​butv∈WR​,
where


WL​ is the set of all finite positive words, with no terminal condition;


WR​ is the set of canonical words, whose final digit is at least 2, together with the empty word.


The one-large-digit cut is explicitly a bijection with WL​×WR​, not with WL​×WL​. 
Their masses are
u∈WL​∑​K(u)−s=2ρs​,v∈WR​∑​K(v)−s=ρs​.
The manuscript establishes the asymmetry, including the empty-word and digit-sum-one endpoints, exactly.  Thus the product is
(2ρs​)(ρs​)=2ρs2​,
and at ρσ0​​=2,
bC​=2ρσ0​2​=8.
Where your extra factor 2 enters
Your numerical series
S=all finite positive words t∑​K(t)−σ0​
really does converge to
S=2ρσ0​​=4.
But that is the left-context mass. It is not the mass on each side.
The familiar two-expansion identity
(…,a)⟷(…,a−1,1)
is a terminal continued-fraction ambiguity. It can therefore be used to explain why unrestricted left words have twice the canonical mass. It cannot be applied independently to the right context while retaining a unique representation of the whole rational.
For example, a canonical suffix ending in 3 and a noncanonical suffix ending in 2,1 represent the same whole rational. Counting both as right contexts double-counts that cost-class element. On the left, by contrast, the context is followed by the large digit, so it is not the terminal portion of the whole continued fraction and no canonical terminal restriction applies.
Equivalently, one may choose the opposite convention—canonicalize the left side and allow an unrestricted right side—but one then again obtains
ρs​⋅2ρs​=2ρs2​.
One cannot take both sides unrestricted without introducing a twofold representation multiplicity.
The statement “the large quotient may sit anywhere” supplies no further factor: its position is already encoded by the entire prefix u. Summing over all u∈WL​ already sums over all possible positions and left patterns.
Why your data look like convergence to 16
The values through d=25 are severely preasymptotic. I separated your exact sum into the part with a regular partial quotient exceeding (d+1)/2—the part to which the context product directly applies—and its complement. All entries below are scaled by dσ0​:
d10152025​total8.4057711.5844513.2195513.86149​one large digit5.060486.365578.166168.65773​no digit>(d+1)/23.345295.218885.053395.20376​​
At d=25, roughly 5.20 of the observed 13.86 is still coming from the noncondensed sector. That sector eventually vanishes on the dσ0​ scale, but it has plainly not begun doing so numerically by d=25.
The manuscript proves
Zn​(s)−Pn​(s)=O(n1−2s),
where Pn​ is the one-large-digit contribution. Therefore, after multiplying by ns, the noncondensed contribution is O(n1−s)→0.  The sharpened proof uses a balanced cut and bounds the complement by a convolution of two denominator layers. 
For the condensed sector, dominated convergence gives directly
nsPn​(s)⟶u∈WL​∑​v∈WR​∑​{K(u)K(v)}−s=2ρs2​.
The exact continuant factorization behind this is
K(u,a,v)=K(u)K(v)(a+λL​(u)+λR​(v)),
so this is not a heuristic factorization. 
There is also a substantial positive finite-size correction:
Zn​(s)=2ρs2​n−s(1+nsEX​+o(n−1)).
Since b2d+1​=Zd+1​,
dsb2d+1​(s)=2ρs2​[1+ds(EX−1)​+o(d−1)].
At this exponent the context first moments converge slowly, so the asymptotic regime is late. An A+B/d fit over d≤25, before the noncondensed contribution has started to visibly fall, has no reliable interpretation. The apparent increment ratio 0.744 is a finite-range transient, not evidence for a limiting value 16.
Adjudication: the exact enumeration is right, but it does not contradict the paper. The correct leading constant is
bC​=2ρσ0​2​=8​.
Your proposed 16 counts the terminal continued-fraction ambiguity independently on both sides and thereby counts every generic canonical right context twice.
(2) Nothing in the paper should move
Because bC​=8 is correct, the printed values of KC​, the stable normalizer, and the renewal coefficient remain unchanged. Lemma 4.1 correctly derives
Pr{C=2d+1}∼8d−σ0​,Pr{C>x}∼KC​x−α,
with
α=σ0​−1,KC​=α2αbC​​.
 
For completeness, under the counterfactual assumption bC​=16, the consequences would have been purely quantitative:
KCnew​=2KCold​,amnew​=(2KCold​m)1/α=21/αamold​.
The following would change:


The m3−σ0​ coefficient in the Fibonacci partition-function expansion would double, because it is linear in KC​. The leading 2m/μC​ term would not change. 


The renewal correction
uj​−μC​1​∼μC2​(σ0​−2)KC​​j2−σ0​
would double. 


The stable-domain theorem would survive unchanged in type, index, and spectral sign after replacing the normalizer by 21/αam​. With the old normalizer, the limit would instead be 21/αSα​, not the canonically normalized Sα​. 


In the Gibbs geometry theorem, Jm​/m⇒U, the centering Jm​/μC​, and the negative spectral sign would all remain unchanged. Only the stable scale would change. With the corrected normalizer the displayed limiting vector would be identical; with the old normalizer its second coordinate would acquire a factor 21/α. 


Crucially,
μC​=EC
would not move. It is the mean of the exact probability distribution bj​(σ0​), not a quantity inferred from the asymptotic coefficient. Nor would σ0​ or α move.
Thus even had the constant been doubled, the qualitative mathematics—finite mean, regular-variation index, stable domain of attraction, renewal exponent, uniform macroscopic cost, and spectral orientation—would all survive. Only amplitudes and normalizations would be wrong.
(3) The crossover theorem is not affected
The crossover statement I proposed used
sm​→σ0​,m(1−Bsm​​(1))→θ,
equivalently, for sm​=σ0​+λ/m+o(m−1),
θ=κλ,κ=−∂s​Bs​(1)​s=σ0​​>0.
Its macroscopic renewal prediction was
mZmR​(−sm​)​⟶θ2(1−e−θ/μC​)​,
with the continuous value 2/μC​ at θ=0, and the generator-cost fraction converging to Uθ​ with density
fθ​(t)=1−e−θ/μC​θ/μC​​e−θt/μC​,0<t<1,
uniform when θ=0.
That macroscopic crossover law does not involve KC​. It depends on the near-critical renewal defect θ and the critical mean μC​. Therefore even the counterfactual change 8↦16 would not alter the partition-function crossover or the tilted-Uθ​ law.
The stable refinement used
am​=(KC​m)1/α
and predicted
(mJm​​,am​Hm​−Jm​/μC​​)⟹(Uθ​,−μC−1−1/α​Uθ1/α​Sα​).
Under the counterfactual doubled constant, only am​ would be multiplied by 21/α. With that replacement, the same crossover limit would remain valid. The mean μC​, the tilted macroscopic law, the stable index, and the spectral sign would remain as stated.
Since the actual local constant is 8, there is no correction to propagate into the proposed crossover theorem. The crossover still requires its own uniform near-critical renewal and triangular-array stable estimates—the fixed-critical theorem does not automatically prove those—but this constant is not an obstacle and supplies no reason to modify the proposed statement.
