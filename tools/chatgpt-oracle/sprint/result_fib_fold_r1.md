1. Verdict
Reject.
Single strongest reason: the finite-core theorem on which the claimed conjugacy threshold rests is false. Theorem 5.2 asserts that every ambiguity reduces to a core of length at most r+1, and Theorem 5.3 specializes this to the assertion that no Fibonacci core has length at least 5. There is an explicit length-5 counterexample. Consequently, the proof of Theorem 5.5 does not establish the advertised conjugacy result.   
This is not a local omission. One of the two “structural theorems” highlighted in the abstract fails, and the entire decoder architecture has to be rebuilt.
2. ETDS significance threshold
No. Even if the correctness problem were repaired, this is too small for Ergodic Theory and Dynamical Systems.
The genuinely model-specific contribution is the derivation of a four-state presentation for one Fibonacci normalization rule. Once that graph is known, the strict-sofic factor, Parry statistics, Markov-chain CLT, covariance formula, rational spectrum, rotation polygon, frontier entropy, transfer recurrence, large deviations, and pressure–entropy duality are standard finite-state consequences. The paper itself concedes that the later formulas are “standard Parry-measure and transfer-matrix calculations.” 
The purported breadth is supposed to come from Theorems 4.5 and 5.2. Theorem 4.5 is largely condition (ii) of Definition 4.3 rewritten as a follower-graph statement, while Theorem 5.2 is false. That leaves a competent case study, not a major symbolic-dynamics result. ETDS presents itself as a venue for major contributions and central problems in dynamics; this manuscript does not approach that level. 剑桥大学出版社
Right-sized journal: Dynamical Systems, after the finite-core section is replaced and the manuscript is cut substantially. That is a natural specialist venue for a concrete symbolic system with exact finite-state calculations. 泰尔与方在线
3. The first hostile attack
The vulnerable statement is:

“Then every ambiguous two-label block in the image shift of Φm​ strips to an ambiguous core of length at most r+1.”

That is Theorem 5.2. Its proof says that the relevant coordinates lie in the union of one rewrite support for the first label and one shifted rewrite support for the second label. 
This confuses the support of one rewrite with the causal support of a cascade of rewrites.
Here is a counterexample in the paper’s low-to-high convention. Take m=5 and the two length-6 raw blocks
u=000001,v=011010.
Their consecutive five-window labels agree:
u:v:​Fold5​(00000)=00000,Fold5​(00001)=00001,Fold5​(01101)=00000,Fold5​(11010)=00001.​
Indeed,
N(01101)=F3​+F4​+F6​=2+3+8=13=F7​,
so its normalized 1 lies just outside the length-5 window, while
N(11010)=F2​+F3​+F5​=1+2+5=8=F6​,
giving 00001. Thus u and v are distinct lifts of the same two-label block
(00000,00001).
Under the paper’s own definition, a coordinate is passive only when deleting it from both lifts leaves two distinct lifts of the same two-label block in Gm−1​.  For deletions j=1,…,6, the resulting output pairs are:
j123456​u after deletion(0000,0001)(0000,0001)(0000,0001)(0000,0001)(0000,0001)(0000,0000)​v after deletion(0000,1010)(0101,1010)(0101,1010)(0100,1001)(0001,0010)(0001,0000)​​
No deletion preserves the ambiguity. Therefore this is an ambiguous core of length 5, directly contradicting Lemma C.4 and Theorem 5.3’s sentence “No minimal ambiguous core has length at least 5.”  
The conceptual failure is exactly what Proposition 4.1 should have warned the authors about: local Fibonacci carries can propagate through the entire visible window. A bound on individual rewrite span does not bound the dependence cone of a completed normalization. 
The conjugacy assertion for m≥3 may still be true—I do not have a counterexample to that assertion—but this manuscript does not prove it.
4. Is the pentagon a real rigidity theorem?
It is the routine output of enumerating five simple cycles in a four-state graph.
The proof does exactly that. It invokes the classical cycle description, lists all five simple cycles, records their five rotation vectors, and takes their convex hull.  This is precisely Ziemian’s mechanism: for a locally constant observable on an SFT, the rotation set is the convex hull of the rotation vectors of the elementary loops. DML-PL+1
The alleged “rigidity” of the two upper faces is also standard finite-dimensional linear programming. A stationary flow maximizes a supporting functional exactly when it is supported on the union of the cycles maximizing that functional. The paper identifies those two edge unions and computes the Perron root of their common 3×3 adjacency matrix:
det(λI−C)=λ3−λ−1.
That is why the plastic constant appears. 
So:


The coordinates of the pentagon are a legitimate model-specific computation.


The frontier subshifts are a neat exact observation.


Neither constitutes a new rigidity principle.


Theorem 4.12 deserves to be a proposition or worked consequence of the graph, not one of the paper’s headline structural results.


The difficult part, to the extent there is one, is obtaining and validating the four-state graph. The pentagon itself is almost automatic once the graph has been printed.
5. Abstract and introduction versus actual hypotheses
There are multiple mismatches. They are not merely stylistic.
(a) “Unique compatible restriction” omits the codomain restriction
The abstract says there is a “unique compatible restriction on microstates,” and the introduction similarly speaks of the unique map making the square commute.  
Lemma 3.4 proves uniqueness only among maps
T:Ωm+1​⟶Xm​,
that is, maps whose values are already normalized. 
Without the codomain Xm​, uniqueness is false: one may choose different preimages under Foldm​. The manuscript itself notes, for example, that
Fold2​(00)=Fold2​(11)=00.

The front matter must say “unique compatible restriction taking values in Xm​.”
(b) “Follower memory at most r−1” is stronger than Theorem 4.5
The abstract and introduction claim that the pair shift has follower memory at most r−1.  
Theorem 4.5 proves only that synchronized pair prefixes with the same terminal (r−1)-block have the same follower set.  Those quantifiers are not interchangeable.
Indeed, ordinary follower memory 2 is false for the printed Fibonacci graph. The admissible words
01∣10∣11,10∣10∣11
have the same final two symbols 10∣11, but the first terminates in state 01, whose only next label is 10, whereas the second terminates in state 11, whose only next label is 00. This follows directly from the transition table. 
The valid phrase is “synchronized follower memory at most r−1,” not “follower memory at most r−1.”
(c) The introduction drops m≥r from the finite-core theorem
The introduction says that Theorem 5.2 proves, in the general span-r setting, that every two-label ambiguity has a core of length at most r+1. 
The actual theorem begins:

“Fix m≥r.”


Thus the introduction states the result for all window lengths while the theorem states it only for m≥r. More seriously, as shown above, even the restricted theorem is false.
(d) “Exact conjugacy threshold m≥3” is false as a quantifier statement
The abstract calls m≥3 the “exact conjugacy threshold.”  Theorem 5.5 proves the positive claim for m≥3, and Proposition 5.6 proves failure at m=2. 
But m=1 is also a conjugacy: Fold1​ is the identity on {0,1}, so the induced code Φ1​ is the identity full-shift code. This follows immediately from the definitions.  
Thus, assuming Theorem 5.5 eventually receives a valid proof, the injective cases are
m=1orm≥3,
not “exactly m≥3.” The authors can call 3 the eventual threshold, but not the exact threshold without excluding m=1.
(e) The abstract suppresses the measure in all statistical claims
The abstract attributes density 4/9, variance 118/243, covariance formulas, and a power spectrum to “the discrepancy factor.” 
Those quantities are not invariants of the topological factor. They are calculated under the particular bulk law, namely the Parry law induced by uniform Bernoulli microstates. Theorems 4.9–4.11 require that measure.  
This cannot be left implicit: the same shift supports invariant measures with discrepancy densities ranging from 0 to 1, as its own rotation polygon shows. The abstract should say “under the uniform-input bulk law.”
(f) The introduction overstates Proposition 4.2
The introduction says that “no rule depending only on a uniformly bounded tail can repair” the failure of commutation. 
Proposition 4.2 rules out only maps of the form
ω1​⋯ωm−ℓ​Pm,ℓ​(ωm−ℓ+1​⋯ωm+1​),
which leave the first m−ℓ coordinates literally unchanged and modify only the final ℓ output sites. 
That is a no-go theorem for bounded-support tail corrections, not for every conceivable rule whose decision is based on bounded tail data. The prose should use the narrower formulation.
So the answer is yes: the front matter repeatedly weakens hypotheses or strengthens conclusions. The pattern is systematic.
6. Is the length justified?
No. The paper manufactures scale.
The four-state graph and perhaps the extremal full-window discrepancy example justify a paper. They do not justify 38 pages containing this many separately named results.
The manuscript itself states that, once the graph is identified, the later formulas follow from standard Parry and transfer-matrix calculations.  Appendix D similarly admits that its remaining material is linear algebra and symbolic elimination.  Nevertheless, elementary stationary distributions, a standard Markov CLT, diagonalization of a 4×4 matrix, summation of a geometric covariance series, five-cycle enumeration, Cayley–Hamilton, Gärtner–Ellis, and the ordinary pressure variational principle are promoted into a sequence of theorem-level events.
There is also substantial duplication between the main text and the appendices. The discriminant and negative-y root analysis is expressly auxiliary and unused for the positive-weight asymptotics, yet occupies additional space. 
A corrected paper should be roughly half this length:


retain the finite-window obstruction;


derive and validate the pair presentation;


state the strict-sofic factor and the decoder result, with a valid proof;


collect the statistical, rotational, and thermodynamic computations as concise corollaries;


delete the unused discriminant material and repeated tables.


At present, the number of named propositions and the volume of appendices exaggerate the mathematical scale rather than reflect it.
