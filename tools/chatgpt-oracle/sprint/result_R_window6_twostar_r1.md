1. Status of the sharp lemma
The statement needs the hypothesis m≥6. Taken literally for all m, it is false:
Φ2​(0)=Φ2​(3),Φ3​(0)=Φ3​(5),Φ4​(0)=Φ4​(8).
After identifying a retained Zeckendorf word with its numerical value, for example,
Φ3​(0)=Φ3​(5)=(0,{1,2,4}),
so the difference is 5, not 34 or 144. The corresponding low-dimensional differences are 3,5,8.
For the intended range m≥6, I found no counterexample, and exact exhaustive verification can be extended from your m≤16 to m≤25:
mnon-singleton Φm​-fibresdifference6163471434864144912814410514411≤m≤250—
Thus the corrected conjecture is:
m≥6,Φm​(a)=Φm​(b), a=b⟹∣a−b∣∈{34,144}.(ST)
I do not presently have a valid uniform proof of (ST). The important conclusion is that the sparse-Fibonacci classification by itself does not prove it. There is a genuinely additional “two-star rigidity” statement missing.
Exact certificate for 11≤m≤25
The computation need not compare or hash the full multisets. Let
ρm​(n)=the numerical value represented by Foldm​(n)
and define
Cm​(n)=j=0∑m−1​(ρm​(nxor2j)−ρm​(n))3.
Then
Γm​(n):=(ρm​(n),Cm​(n))
is a function of Φm​(n). Therefore
Γm​(a)=Γm​(b)⟹Φm​(a)=Φm​(b).
Exact integer sorting of all Γm​(n), 0≤n<2m, gives no duplicate for every 11≤m≤25. This is not a probabilistic hash test: the values can be computed in signed 128-bit arithmetic and compared exactly. For 6≤m≤10, direct comparison of the complete sorted neighbor multisets gives the table above.
So there is a clean computer-assisted theorem through m=25, but not yet an all-m proof.

2. The uniform reduction, and the precise missing step
There is a useful all-m reduction that explains both why 34 and 144 appear and why the remaining argument is not automatic.
Let φ=(1+5​)/2, and let
Tm​={k≥m+2∑​ϵk​Fk​:ϵk​∈{0,1}, ϵk​ϵk+1​=0}.
These are the integers whose first m Zeckendorf digits vanish. Every n decomposes as
n=Hm​(n)+ρm​(n),Hm​(n)∈Tm​.
Consequently,
Foldm​(a)=Foldm​(b)⟹b−a∈Tm​−Tm​.
The increasing enumeration of Tm​ is explicitly
Tm​(r)=Fm+1​r+Fm​⌊φr+1​⌋,r≥0.
Indeed, shift every digit in the Zeckendorf expansion of r upward by m, and use
Fk+m​=Fm+1​Fk​+Fm​Fk−1​,∑dk​Fk−1​=⌊φr+1​⌋.
In particular, consecutive gaps in Tm​ are Fm+1​ or Fm+2​. This is the generalized-Beatty structure associated with shifted Zeckendorf expansions. arXiv+1
Now suppose Φm​(a)=Φm​(b). Put
D=b−a.
Matching the two equal neighbor multisets gives a permutation π of the bit coordinates such that
Foldm​(axor2i)=Foldm​(bxor2π(i)).
Write
εi​(a)=1−2ai​∈{−1,+1},
where ai​ is the bit of weight 2i, and define
ui​=επ(i)​(b)2π(i)−εi​(a)2i.
Then the matched neighbor integers differ by
D+ui​,
and hence
D∈Tm​−Tm​,D+ui​∈Tm​−Tm​.
Therefore
ui​∈(Tm​−Tm​)−(Tm​−Tm​).
Moreover,
i=0∑m−1​ui​=−2D.
This follows from
i∑​εi​(a)2i=(2m−1)−2a.
If a=b, at least one ui​ is nonzero: if all ui​=0, comparison of absolute powers forces π(i)=i, and then comparison of signs forces every bit of a and b to agree.
Each nonzero ui​ is a signed sum or difference of at most two powers of two:
ui​=±2p±2q,
with the single-power case included when the coordinates coincide and the signs differ.
The uniform Diophantine estimate
The identity
Fk​φ−Fk+1​=(−1)k+1φ−k
gives, for every H∈Tm​,
∥Hφ∥≤j≥0∑​φ−(m+2+2j)=φ−(m+1).
Here ∥x∥ denotes distance to the nearest integer. It follows that
x∈Tm​−Tm​⟹∥xφ∥≤2φ−(m+1)
and hence
u∈(Tm​−Tm​)−(Tm​−Tm​)⟹∥uφ∥≤4φ−(m+1).
Thus every nontrivial signature collision produces a nonzero sparse integer
u=±2p±2q,p,q<m,
satisfying
∥uφ∥≤4φ−(m+1).(1)
This reduction is completely uniform and does not use the classification of Fibonacci numbers that are sums of two powers of two.
Why this does not yet prove the sharp lemma
Condition (1) is weaker than saying that u, or D, is a single Fibonacci number. Even the exact tail-difference condition admits additional sparse numbers. For example,
68=64+4=2F9​,288=256+32=2F12​,
and whenever Fk​∈Tm​,
2Fk​=(Fk​−0)−(0−Fk​)∈(Tm​−Tm​)−(Tm​−Tm​).
So the sparse-Fibonacci theorem
Fk​=2p+2q
cannot be applied at this stage. One must first prove that the star matching has the much stronger form seen in all computations.
The exact missing statement is something like the following.

Two-star rigidity lemma.
If m≥6 and Φm​(a)=Φm​(b) with a=b, then there are two coordinates p=q and an index k≥m+2 such that
b=axor2pxor2q,b−a=±Fk​=±(2p+2q),
and, after choosing the matching permutation, π fixes every other coordinate and transposes p and q.

In the observed collisions, the two exceptional matched neighbor pairs are literally the same vertices:
a+2p=b−2q,a+2q=b−2p.
Equivalently, the corresponding two ui​'s are −D, and all other ui​'s vanish. The identity ∑ui​=−2D is then exact for the transparent reason that there are precisely two common neighbors.
Once this two-star rigidity statement is proved independently, the sparse-Fibonacci classification becomes a clean, noncircular second ingredient:


star geometry shows D=Fk​=2p+2q;


sparse-Fibonacci arithmetic shows only F9​=34 and F12​=144 are compatible with the window inequalities.


Without the first step, invoking the sparse-Fibonacci classification is incomplete.
A generic continued-fraction estimate does not close the gap. Bad approximability gives only
∥uφ∥≫∣u∣−1≳2−m,
whereas the collision estimate is of order φ−m. Since 2−m is smaller than φ−m, these bounds overlap rather than contradict each other. A Subspace-Theorem or sparse-power approximation argument is a plausible route to finiteness of exceptional sparse returns, but quoting the theorem does not supply the required star structure or an explicit threshold. arXiv+1
So the answer to your second question is:


the structural proof should be uniform in m and independent of the sparse-Fibonacci classification;


the final identification of 34 and 144 should use that classification as a separate arithmetic input;


the structural step has not yet been obtained from the settled lemmas.



3. Complete classification theorem conditional on the sharp lemma
Here is the theorem I would put in the paper.
Theorem — Sporadic stable refinement and eventual rigidity
For m≥6, let Rm​ denote the unique coarsest equitable refinement of the partition induced by Foldm​. Assume the sharp two-star statement
Φm​(a)=Φm​(b),a=b⟹∣a−b∣∈{34,144}(ST)
for every m≥6.
Then:


Rm​ is non-discrete exactly for
m∈{6,8,9}.


In these three cases, Rm​ is the orbit partition of the affine involution
(ar​,as​)⟼(1−as​,1−ar​)
on the following pairs of positions, numbered from the most significant bit:
(m;r,s)=(6;1,5),(8;1,4),(9;2,5).


In each exceptional dimension,
∣Rm​∣=3⋅2m−2.
More precisely, Rm​ has
2m−1 singleton cellsand2m−2 doubleton cells.


The refinement is discrete at m=7 and at every m≥10. Thus the sharp eventual-rigidity threshold is
m0​=10.


Proof
First, (ST) implies that every fibre of Φm​ has size at most two. Indeed, if
a<b<c
belonged to one fibre, then each of
b−a,c−b,c−a
would belong to {34,144}. But
c−a=(b−a)+(c−b)∈{68,178,288},
a contradiction.
The value 178 should be included here; it is the case 34+144, omitted in the list in the question.
The closure lemma therefore applies: any non-discrete stable refinement is the orbit partition of a nontrivial fold-preserving involutory cube automorphism.
By the already established arithmetic classification of such involutions, one must have a Fibonacci relation
Fk​=2p+2q
with
m≥p+1,m≤k−3.
The only compatible possibilities are
F9​=34=32+2,F12​=144=128+16,
giving precisely
m=6, 8, 9.
Thus Rm​ is discrete for m=7 and for every m≥10.
Conversely, in the three listed dimensions the explicitly given transformations are fold-preserving involutory automorphisms. The relevant binary weights are
32+2=34=F9​
for m=6, and
128+16=144=F12​
for m=8,9. Their orbit partitions are equitable refinements of the fold partition. By the closure lemma and uniqueness in the involution classification, these are the coarsest equitable refinements.
It remains to count the orbits. For the transformation on positions r,s, a word is fixed exactly when
(ar​,as​)=(1−as​,1−ar​),
or equivalently
ar​+as​=1.
There are two choices for (ar​,as​) and 2m−2 choices for the remaining coordinates, giving
2⋅2m−2=2m−1
fixed vertices and therefore 2m−1 singleton cells.
The remaining 2m−1 vertices occur in two-cycles, giving
22m−1​=2m−2
doubleton cells. Hence
∣Rm​∣=2m−1+2m−2=3⋅2m−2.
Since m=9 is non-discrete and every m≥10 is discrete, the threshold m0​=10 is sharp. ∎
The local pairs at m=7 and m=10 cause no contradiction: they show that the first color-refinement step is non-discrete, but those pairs are split at later rounds because they do not extend to a global fold-preserving automorphism.
For completeness, if the paper treats every positive dimension, direct low-dimensional checks add the exceptional cases m=2,3. The complete list would then be
m∈{2,3,6,8,9},
with the same cell-count formula 3⋅2m−2 in every non-discrete case; m=1,4,5,7 and all m≥10 are discrete.

4. The realistic fallback
The strongest honest fallback has three layers.
Unconditional structural proposition
Include the uniform tail-difference reduction:

A nontrivial Φm​-collision produces D and sparse integers ui​ satisfying
D,D+ui​∈Tm​−Tm​,i∑​ui​=−2D,
with at least one nonzero
ui​=±2p±2q
and
∥ui​φ∥≤4φ−(m+1).

That is a genuine all-length theorem and isolates the arithmetic obstruction precisely.
Unconditional computer-assisted theorem through m=25
State:

For 6≤m≤25, every nontrivial fibre of Φm​ is a doubleton. Such doubletons occur only as follows:
m6,78,9,10​∣a−b∣34144,​​
and Φm​ is injective for 11≤m≤25.

Consequently, without any conjectural input, the stable refinement is non-discrete exactly at m=6,8,9 in the verified range, has 3⋅2m−2 cells there, and is discrete at m=7 and 10≤m≤25.
The supplement should archive:


the exact implementation of ρm​;


full multiset comparison for m≤10;


exact sorting of (ρm​,Cm​) for 11≤m≤25;


source and output hashes;


an explicit statement that no probabilistic hashing is used.


Conditional all-length classification
Then state the classification theorem above as conditional on (ST), or better, conditional on the stronger and more geometrically meaningful two-star rigidity lemma.
That is the cleanest current paper architecture. It does not falsely advertise an all-m proof, but it gives:


an unconditional uniform arithmetic reduction;


a substantial exact range, now through m=25;


a complete conditional theorem with the sharp threshold m0​=10;


one precisely named missing result, rather than an amorphous conjectural gap.
