Bottom line
The literal change is reachable, essentially immediately. It does not rescue the paper.
The complete answer is that the centered radial homotopy has an exact ℓ∞-operator norm governed by the maximum (k−1)-codegree of the support hypergraph, with side lengths supplying weights. On the unit cube the sharp constant for arbitrary constant k-forms is
2kn−k+1​​
rather than 1/(2k).
This theorem is already almost contained in the manuscript’s Proposition 2.6: that proposition defines the relevant incidence multiplicity and proves the corresponding contraction estimate. Passing from contraction to Kk​ only integrates tk−1, producing the factor 1/k. 
A preliminary precision: on a k-dimensional box, every constant k-form is a scalar multiple of dx1​∧⋯∧dxk​. There is no arbitrary-orientation problem there. The requested extension is meaningful only for constant k-forms on an n-dimensional box, n≥k.
1. The incidence obstruction
Let
R=r=1∏n​[0,Lr​],c=(2L1​​,…,2Ln​​),
and write
ω=I∈(k[n]​)∑​aI​dxI​.
The centered radial homotopy is
(Kk​ω)(x)=∫01​tk−1ιx−c​ω(c+t(x−c))dt.
This is exactly the operator used in the manuscript. 
Fix a (k−1)-index J. The dxJ​-coefficient of Kk​ω receives a contribution from every k-index of the form J∪{i}. For a constant form,
coeffJ​(Kk​ω)(x)=k1​i∈/J∑​σ(J,i)(xi​−ci​)aJ∪{i}​,(1)
where σ(J,i)∈{±1} is the exterior-algebra insertion sign.
For one coordinate monomial aI​dxI​, deleting the different indices of I gives different output orientations dxI∖{i}​. Therefore no output coefficient receives more than one summand. That is why coefficient-ℓ∞, unlike an ℓ1 norm, sees only
2Li​​∫01​tk−1dt=2kLi​​.
On the unit cube this is 1/(2k).
For a general form, distinct k-indices can share the same (k−1)-index:
I1​=J∪{p},I2​=J∪{q}.
Both contract into dxJ​, so their contributions add in (1). The exterior signs do not save the estimate: the coordinates xp​−cp​ and xq​−cq​ can independently be chosen positive or negative by selecting a suitable corner of the box. Thus every incident summand can be made to add with the same sign.
The controlling combinatorial quantity is therefore
dM​(J)=#{I∈M:J⊂I},
where M⊆(k[n]​) is the orientation support. Its maximum
Δk−1​(M)=∣J∣=k−1max​dM​(J)
is the maximum (k−1)-codegree, equivalently the maximum row sum of the unsigned (k−1)-versus-k incidence matrix.
This is exactly the manuscript’s m(ω) or m(M). 
On the unit cube, the factor 1/(2k) survives precisely when
Δk−1​(M)≤1.
Equivalently, no two members of M share k−1 indices. In hypergraph language, M is a partial Steiner system S(k−1,k,n), or a (k−1)-packing. The manuscript’s example
dx1​∧dx3​+dx2​∧dx3​
has the shared lower face J={3}, codegree 2, and consequently gives ∥K2​ω∥=1/2, rather than 1/4. 
2. The complete theorem
Here is the manuscript-ready theorem.
Theorem: exact weighted incidence norm of the centered radial homotopy
Let 1≤k≤n, let
R=r=1∏n​[0,Lr​]⊂Rn,
and let M⊆(k[n]​) be a nonempty family of coordinate k-orientations. Define
ΩMk​(R)={ω=I∈M∑​aI​(x)dxI​:aI​∈C∞(R)},
with
∥ω∥coeff,∞​=I∈Mmax​∥aI​∥L∞(R)​.
Set
ΔL​(M):=J∈(k−1[n]​)max​i∈/JJ∪{i}∈M​∑​Li​.(2)
Then
∥Kk​ω∥coeff,∞​≤2kΔL​(M)​∥ω∥coeff,∞​​(3)
for every ω∈ΩMk​(R).
Moreover, the constant in (3) is optimal. In fact,
∥Kk​∥ΩMk​(R)→Ωk−1(R)​=2kΔL​(M)​,​(4)
and the same norm is obtained if the supremum is restricted either to constant forms or to closed forms.
For an individual constant form
ω=∣I∣=k∑​aI​dxI​,
one has the exact identity
∥Kk​ω∥coeff,∞​=2k1​J∈(k−1[n]​)max​i∈/J∑​Li​∣aJ∪{i}​∣.​(5)
Here absent coefficients are interpreted as zero.
Proof
For a general smooth form, the dxJ​-coefficient is
i∈/JJ∪{i}∈M​∑​σ(J,i)(xi​−ci​)∫01​tk−1aJ∪{i}​(c+t(x−c))dt.
Since ∣xi​−ci​∣≤Li​/2,
∣coeffJ​(Kk​ω)(x)∣≤2k1​i∈/JJ∪{i}∈M​∑​Li​∥ω∥coeff,∞​.
Taking the maximum over J proves (3).
Now suppose that ω is constant. Then the radial integral is exactly 1/k, giving (1). For a fixed J, choose each coordinate xi​ to be 0 or Li​ according to the sign of σ(J,i)aJ∪{i}​. All the terms in (1) then have the same sign, and hence
x∈Rsup​∣coeffJ​(Kk​ω)(x)∣=2k1​i∈/J∑​Li​∣aJ∪{i}​∣.
Maximizing over J proves (5).
Finally, choose J∗​ attaining the maximum in (2), and take
ω∗​=i∈/J∗​J∗​∪{i}∈M​∑​σ(J∗​,i)dxJ∗​∪{i}​.
Then ∥ω∗​∥coeff,∞​=1, ω∗​ is constant and closed, and at the corner xi​=Li​ its dxJ∗​​-coefficient under Kk​ equals ΔL​(M)/(2k). Thus the constant is sharp even on constant closed forms.
Consequences
On the unit cube In,
∥Kk​∥M​=2kΔk−1​(M)​.​
For all coordinate orientations,
M=(k[n]​),Δk−1​(M)=n−k+1,
so
∥Kk​∥all constant k-forms on In​=2kn−k+1​.​(6)
On an anisotropic box, if
L(1)​≤⋯≤L(n)​
are the ordered side lengths, then for all orientations
∥Kk​∥=2k1​r=k∑n​L(r)​.​(7)
Indeed, the maximizing J consists of the k−1 shortest coordinate directions.
For one coordinate monomial dxI​,
∥Kk​∥{I}​=2k1​i∈Imax​Li​.
Notice that on an anisotropic k-box this is generally larger than
m(R)=2∑i​Li−1​1​.
Thus the standard radial homotopy is not the anisotropically optimal primitive unless the relevant side lengths are equal. The paper’s affine minimizer is doing a different weighting.
3. Two-week odds
Probability of proving and correctly writing the theorem above in two weeks: 98–99%.
Realistically, it is a one- or two-day result. The unit-cube upper estimate is already obtained by integrating the manuscript’s Proposition 2.6 against tk−1. The exact lower bound comes from constant coefficients and one corner of the box.
The more important probability is different:
Probability that adding this theorem causes the same referee to regard the 28-page paper as substantial: below 15%.
The theorem resolves the obstruction completely, but it resolves it as a maximum-row-sum calculation. A referee who reduced the box theorem to five lines will reduce this theorem to another five lines.
There is also a crucial distinction. The theorem computes the norm of the specified operator Kk​. It does not compute
inf{∥η∥coeff,∞​:dη=ω}
for an arbitrary constant k-form ω in dimension n>k. That coupled optimal-primitive problem could be genuinely substantive. The weighted-codegree formula does not solve it, and I would not promise a complete sharp solution to that stronger problem in two weeks.
4. What the paper becomes
Adding the theorem above does not justify 28 pages. It makes the paper more complete but not deeper.
The honest standalone version is approximately:


2 pages for the homotopy formula and exact incidence theorem;


3 pages for the box extremum, equality trace and deficit estimate;


1–2 pages for slicing;


2 pages for the one-cube Whitney transcription.


That is an 8–10-page note, including a very short introduction. Archiv der Mathematik is shape-appropriate because it explicitly seeks short, broadly readable research papers and normally imposes a ten-page ceiling. Whether this result clears even that journal’s significance threshold is borderline. Springer Nature Link+1 A still smaller version could be submitted as a Mathematical Notes Short Communication; its current short communications are commonly only a few printed pages. Springer Nature Link+1
My editorial preference would be:
absorb it into a larger paper, unless you can add the genuinely coupled theorem for optimal primitives of arbitrary constant forms, or a correct nonlocal cubical compatibility theorem. The exact Kk​ incidence calculation alone is not a new load-bearing result.
5. Is the referee right that this is bookkeeping?
Yes. On the surviving results you listed, the referee is right.
The box extremum is Stokes or the divergence theorem plus the explicit affine field. The rigidity statement is the equality case of the pointwise flux inequality. The stability statement is the same deficit identity followed by
∣sf−mR​∣≤(M−sf)+(M−mR​).
That is literally how the manuscript proves it: the exact deficit is obtained by integrating a nonnegative pointwise duality gap and invoking the divergence theorem, and the trace estimate is then a single triangle-inequality manipulation.  
The remaining pieces have the same character:


slicing is Fubini applied to the box identity;


the incidence theorem is the ℓ∞-norm of an incidence row;


the one-cube Whitney statement is a finite-dimensional transfer of the same identity.


The one thing that is not bookkeeping is the question or viewpoint: near-optimal interior coefficient norm reads out boundary trace. That is a clean observation. But a clean interpretation of an equality case is not, by itself, a 28-page research contribution.
So the hard editorial conclusion is:

The exact incidence theorem is true, sharp, fully reachable, and worth inserting. It completes the mathematics but does not answer the significance objection. As presently constituted, this is either an 8–10-page note or supporting material for a larger theorem.
