1. Verdict: reject
Single strongest reason: the main result is too slight and too specifically engineered for ETDS. The sharp window theorem is correct, but its purported all-resolution content reduces to a two-letter interval-overlap test, followed in the high-density case by an elementary residue argument. The surrounding discrepancy and Parry-measure calculations do not turn that observation into a broader dynamical theorem. This is a significance problem, not something a major revision could repair.
2. The point a hostile referee attacks first

“Thus losslessness at all resolutions is decided at resolution two.” 

That sentence is accurate, but it gives the hostile referee the rejection argument almost verbatim. Theorem 4.1 has only the following content:


if the two-letter word 11 is absent, every realized word is already in the golden-mean language and the fold is the identity;


if 00 is absent, complements are in the golden-mean language and the residue map separates them;


if both 00 and 11 occur, they collide under Fold2​.


Those three alternatives are exactly what the theorem states.  There is no genuinely long-block rigidity mechanism hiding behind the “all resolutions” formulation. Once Proposition 2.6 has made the fold a residue map, the principal classification is essentially a one-paragraph consequence of elementary interval geometry.
A hostile referee will therefore describe the main theorem as “the 00/11 overlap criterion plus complementation,” and will say that the forty-eight-page apparatus magnifies a very small phenomenon rather than uncovering a substantial one. That is the manuscript’s real vulnerability.
3. The high-density half
It holds up. The complementation step is correct, including the modular point that could easily have gone wrong.
Let
Tm​:=j=1∑m​Fj+1​=Fm+3​−2.
For the coordinatewise complement u,
Nm​(u)=Tm​−Nm​(u).
Thus it is not generally true that Nm​(u)≡−Nm​(u)(modFm+2​): the constant Tm​ need not vanish modulo Fm+2​. But the proof does not make that false claim. It compares two words, and the constant cancels:
Nm​(u)−Nm​(v)=−(Nm​(u)−Nm​(v)).
That equality is exact over the integers, not merely modulo Fm+2​. 
When β≥1−δ(α), the two-letter cylinder 00 has zero mass. Therefore a positive-mass word in Sm​(α,β) cannot contain adjacent zeros, so its complement belongs to Xm​. For distinct u,v, the complements u,v are distinct legal words. Since
Nm​:Xm​⟶{0,…,Fm+2​−1}
is bijective,
0<∣Nm​(u)−Nm​(v)∣<Fm+2​.
Consequently this difference is not divisible by Fm+2​; the exact negation identity gives the same conclusion for Nm​(u)−Nm​(v). Proposition 2.6 then implies
Foldm​(u)=Foldm​(v).
The required bijection and residue characterization are stated and proved in Propositions 2.5–2.6. 
There is one support-language subtlety, but the manuscript has handled it correctly. The theorem is formulated on
Sm​(α,β)=suppμm​,
so “00 has zero mass” is enough: any positive-mass m-cylinder containing 00 would be contained in a translate of that zero-mass two-cylinder. Moreover, the earlier half-open-boundary argument states that a word actually produced at a partition boundary also occurs on an adjacent positive-length atom, preventing an isolated zero-mass boundary word from slipping outside the support convention. 
So the high-density proof is airtight. Its problem is not correctness; it is that it is extremely elementary.
4. Demoting Sturmian injectivity to a corollary
The demotion is honest. The new theorem does not quietly import anything special from the Sturmian case.
For β=α:


if α<21​, then δ(α)=α=β, so one is exactly on the low-density boundary and the fold is the identity on the realized language;


if α>21​, then 1−δ(α)=α=β, so one is exactly on the high-density boundary and the complement argument gives injectivity;


α=21​ is excluded because α is irrational.


That is precisely the proof of Corollary 4.2. 
The general theorem does not use Sturmian complexity m+1, the three-gap frequency formulas, balance, recurrence, substitution structure, or the special m+1-point partition. Those ingredients are needed later for entropy estimates, endpoint calculations and the injective-placement optimization, but not for injectivity.
The higher-block conjugacy also does not restore a hidden Sturmian hypothesis. Once Jm​ is injective on the realized m-block alphabet, its coordinatewise extension is a one-block relabeling with a one-block inverse on the image. Theorem 4.4 uses exactly that argument. 
The only implicit bridge is the standard identification of Sm​(α) with the length-m factor language of the Sturmian subshift Xα​. That deserves an explicit citation at the transition to Theorem 4.4, but it is a standard coding fact and is independent of the injectivity proof. It does not make the corollary circular or dishonest.
