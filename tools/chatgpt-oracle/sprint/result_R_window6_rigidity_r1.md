The orbit counts are exactly right
Let σp,q​ be the map that leaves all coordinates except p,q unchanged and acts by
(ap​,aq​)⟼(1−aq​,1−ap​).
It is an involution because applying it twice returns (ap​,aq​).
A vertex is fixed precisely when
ap​=1−aq​,aq​=1−ap​,
which is equivalent to
ap​+aq​=1.
Thus the pair (ap​,aq​) is either (0,1) or (1,0), while the other m−2 coordinates are arbitrary. Hence
∣Fix(σp,q​)∣=2⋅2m−2=2m−1.
The remaining 2m−1 vertices have ap​=aq​. On those vertices the involution exchanges 00 and 11, so they form
22m−1​=2m−2
two-cycles. Therefore the orbit partition contains
2m−1 singletons,2m−2 pairs,
and hence
2m−1+2m−2=3⋅2m−2
cells.
So your interpretation is exactly correct. It gives 48,192,384 at m=6,8,9.

1. Eventual rigidity: not yet proved from the sparse classification
The computation now makes the conjecture extremely convincing, but the classification of the two observed affine involutions does not by itself prove eventual rigidity.
The logical gap is this:

A nontrivial coarsest equitable refinement need not, in general, be an orbit partition of an automorphism.

Equitable equivalence is weaker than automorphic equivalence. In color-refinement terminology, two vertices can remain indistinguishable even when no graph automorphism exchanges them. Thus proving that the only fold-preserving affine involutions occur at m=6,8,9 rules out the observed mechanism, but does not rule out a non-schurian stable cell of size 3 or larger.
There is, however, a precise missing theorem that would close the argument.
Define the one-step colored-star signature
Φm​(a):=(Foldm​(a), {{Foldm​(a⊕ei​):1≤i≤m}}),
where the second component is a multiset.
Your computations, and my reconstruction of them, give the refinement profiles
m67891011​numbers of cells after successive rounds21⟶48,34⟶114⟶125⟶128,55⟶192,89⟶384,144⟶1019⟶1024,233⟶2048,​​
and for 12≤m≤16 the first refinement is already discrete.
In particular, the computational evidence supports the much stronger statement
Φm​ is injective for every m≥11.
An even weaker theorem would suffice:

Two-star multiplicity theorem. For every m≥6, every fiber of Φm​ has cardinality at most 2.

Here is why that theorem would finish the classification.
The graph-theoretic closure lemma
Suppose E is an equitable partition of a simple graph and every cell of E has size 1 or 2. Define τ by fixing every singleton and exchanging the two vertices in every two-element cell. Then τ is a graph automorphism.
Indeed, between two two-element cells, the adjacency matrix is a 2×2 zero-one matrix. Equitability gives equal row sums and equal column sums, so it has the form
(αβ​βα​),
which is invariant under simultaneously swapping the two rows and the two columns. Edges involving singleton cells are preserved for the same reason. Thus τ preserves every edge.
Consequently:


if the first refinement has blocks of size at most 2, then the stable refinement also has blocks of size at most 2;


if that stable refinement is non-discrete, it produces a nontrivial fold-preserving involutory automorphism of Qm​;


a complete classification of such involutions would then force the stable partition to be exactly one of the three orbit partitions at m=6,8,9.


So the remaining theorem is not “classify more sparse Fibonacci numbers.” It is the structural statement that no colored star occurs three or more times, or, more strongly, that colored stars are unique from m=11 onward.
I do not currently see a proof of that from the sparse-number classification. It is a genuine carry-normalization theorem involving arbitrary matchings of the m neighboring labels. I would call it hard but focused: it is plausible as a principal theorem, not as an automatic corollary of the identities 34=32+2 and 144=128+16.

A second possible route: separation plus coprime fiber sizes
There is another way to exclude non-affine equitable refinements completely.
Coprime covering-collapse lemma
Let G be connected and let P be a vertex partition such that:


no two vertices in one P-cell have graph distance 1 or 2;


the greatest common divisor of the P-cell sizes is 1.


Then the coarsest equitable refinement of P is discrete.
Proof. Let E be an equitable refinement. Since it refines P, no two vertices of an E-cell are at distance 1 or 2. Therefore a vertex can have at most one neighbor in any specified E-cell: two such neighbors would be at distance 2.
Hence every quotient neighbor count is 0 or 1. If two quotient cells B,C are adjacent, every vertex of B has exactly one neighbor in C, and conversely. Counting the edges between them gives
∣B∣=∣C∣.
The quotient is connected because G is connected, so every E-cell has one common size k. Every original P-cell is a union of E-cells, so k divides every original cell size. The gcd hypothesis forces k=1. Therefore E is discrete. □
Applied here, a uniform proof of
dH​(a,b)≥3whenevera=b,Foldm​(a)=Foldm​(b),(S)
together with
gcd{∣Foldm−1​(w)∣:w∈Xm​}=1,(G)
would prove discreteness without saying anything about automorphisms.
Computationally, condition (S) starts at m=12. Thus a proof of (S) and (G) for every m≥12, followed by the exact m=10,11 computations, would prove the sharp threshold M=10.
This route may be more promising than proving full one-step injectivity. But again, (S) is broader than the single-Fibonacci sparse classification.
For example:
56=F10​+F2​,124=F11​+F9​+F2​
have the same first seven Zeckendorf digits, while their binary words differ in two coordinates:
56⊕124=68=64+4.
Here 68 is not itself a Fibonacci number.
Similarly,
89=F11​,377=F14​
have zero first-nine-digit prefix and
89⊕377=288=256+32.
Thus close pairs in fold fibers can arise from differences between two high Zeckendorf tails, not only from a single identity
Fn​=2a+2b.
That is exactly why the existing sparse classification does not automatically prove (S).

2. The status of M=10
The sharp value, assuming the conjecture, is plainly
M=10,
because m=9 is non-discrete and m=10 is discrete.
But M=10 is not presently proved by the ingredients stated in the question.
The situation is not really “M=10 versus some ineffective constant.” It is:


prove a uniform structural lemma, and the exact value M=10 follows;


without that structural lemma, even an ineffective eventual threshold has not been established.


There are two credible proof packages:


Prove the two-star multiplicity theorem for all m≥6, and combine it with the full classification of fold-preserving hypercube involutions.


Prove the separation and gcd statements (S) and (G) for all m≥12, use the coprime covering-collapse lemma, and handle m=10,11 by the exact certificates already available.


The second package would give an explicit threshold. There is no mathematical reason to formulate only an ineffective eventual statement if that route succeeds.
The bottleneck is (S), or an equivalent carry-rigidity statement. The gcd clause looks more like a finite-tail counting lemma; the separation clause is where arbitrary high Zeckendorf tails meet two-coordinate binary changes.

3. Does the sparse-binary classification close the argument?
No, not by itself.
It closes the classification of the observed global affine mechanism only if it has actually proved the full stabilizer statement
Aut(Qm​,Foldm​)=⎩⎨⎧​⟨σ1,5​⟩,⟨σ1,4​⟩,⟨σ2,5​⟩,1,​m=6,m=8,m=9,m=7 or m≥10.​(A)
Even the full statement (A) would not alone imply discreteness: color refinement can have non-singleton cells that are not automorphism orbits.
What would make (A) sufficient is the two-star multiplicity theorem. Once all stable cells have size at most 2, the graph-theoretic lemma above turns every nontrivial stable partition into an involution. Then (A) closes the proof completely.
So the precise logical picture is:
sparse affine classification+two-star multiplicity⟹complete equitable classification.​
Without the second summand, the computation through m=16 is compelling evidence, but the family theorem is not proved.

4. The theorem I would ultimately put in the paper
The following is the correct final theorem once the missing uniform star/separation argument has been supplied. I would not state it as proved on the basis of the present computation and affine classification alone.
Theorem — Sporadic equitable non-rigidity of the binary Zeckendorf-prefix fold
Let F0​=0,F1​=1, and Fn+2​=Fn+1​+Fn​. For m≥6, let
Qm​=({0,1}m,Em​)
be the m-dimensional hypercube. For
a=(a1​,…,am​)∈{0,1}m
write
Nm​(a)=i=1∑m​ai​2m−i,
and let
Nm​(a)=r≥1∑​zr​(Nm​(a))Fr+1​,zr​(Nm​(a))zr+1​(Nm​(a))=0,
be its greedy Zeckendorf expansion. Define
Foldm​(a)=(z1​(Nm​(a)),…,zm​(Nm​(a))),
and let Em​ denote the coarsest equitable refinement, in Qm​, of the partition into fibers of Foldm​.
For 1≤p<q≤m, define
σp,q(m)​(a)i​=⎩⎨⎧​1−aq​,1−ap​,ai​,​i=p,i=q,i∈/{p,q}.​
Then the following hold.


The partition Em​ is non-discrete if and only if
m∈{6,8,9}.


At the three exceptional resolutions,
E6​=Orb(σ1,5(6)​),E8​=Orb(σ1,4(8)​),E9​=Orb(σ2,5(9)​).
In particular, each exceptional refinement consists of
2m−1 singleton cellsand2m−2 two-element cells,
and therefore has
3⋅2m−2
cells.


For m=7 and every m≥10,
Em​={{a}:a∈{0,1}m}.
Thus the sharp eventual-rigidity threshold is M=10.


Equivalently, if H:{0,1}m→Y has equitable fibers and
Foldm​=ρ∘H
for some map ρ:Y→Xm​, then
∣Y∣≥{3⋅2m−2,2m,​m∈{6,8,9},m=7 or m≥10.​
Equality is unique up to relabeling of Y; in the exceptional cases it is attained by the corresponding orbit map, and in the rigid cases it forces H to be bijective.


The m=6 clause agrees with the existing proved orbit-partition statement for σ1,5(6)​. 
My decision-grade conclusion is therefore: the proposed final theorem is very likely true, and M=10 is almost certainly the correct sharp threshold, but it is not yet proved by the sparse affine classification. The missing theorem is a uniform colored-star or short-distance rigidity statement, and that is a substantive theorem rather than a bookkeeping extension of the computation.
