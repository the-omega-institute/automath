<!-- oracle metadata: {"timestamp": "2026-04-11T22:44:44.280766", "model": "chatgpt-5.4-pro-extended", "response_length": 10474} -->

1. Overall assessment

Major revision

The paper has a potentially publishable core. The window-level fold, the anomaly viewpoint, the explicit bulk constants, and the sequence-level coding questions are interesting, and I did not see evidence that the main formulas are plainly false. Small finite-window checks support several claims. However, the manuscript is not ready for acceptance. The main problems are substantive: the literature review overstates novelty by omitting directly relevant work on two-sided normalization and the normalized digit density 
5
/
18
5/18, Appendix B’s four-state bulk model is asserted rather than rigorously derived, and Appendix C contains a concrete false enumeration in the 
𝑚
=
4
m=4 base case, which undermines the current proof of the conjugacy theorem. 

main

 
Springer
+2
St Andrews Research Repository
+2

My editorial reading is: interesting results, but proof architecture and novelty positioning both need substantial repair before the paper can be judged on its mathematical merits alone.

2. Novelty rating for each theorem

Theorem 4.5. MEDIUM. The exact joint law of 
(
𝑋
0
,
𝑌
0
)
(X
0
	​

,Y
0
	​

) may be new, but the two-sided normalization viewpoint is not, and the normalized digit density 
𝑃
(
𝑌
0
=
1
)
=
5
/
18
P(Y
0
	​

=1)=5/18 already appears in earlier work. 
Springer
+2
St Andrews Research Repository
+2

Theorem 4.9. HIGH. The explicit autocovariance formula and rational power spectral density for the anomaly process look genuinely new and model-specific.

Theorem 5.2. HIGH. The explicit conjugacy threshold at 
𝑚
≥
3
m≥3 and bounded-memory inverse are strong and, if proved rigorously, appear genuinely new.

Theorem 6.1. MEDIUM. The exact recurrence and generating function are useful and likely new in this formulation, but they arise from standard transfer-matrix machinery once the state model is in place.

Theorem 6.3. LOW. Nice exact factorization, but essentially an algebraic computation from a quartic characteristic polynomial.

3. Issue table

The table below refers to the current proof structure in Sections 4 to 6 and Appendices A to D. 

main

ID	Section	Severity	Description	Suggested fix
B1	Introduction, Sections 4 and 6	BLOCKER	Novelty is overstated because the paper omits directly relevant Bernoulli-convolution / goldenshift / normalization literature. In particular, the two-sided normalization viewpoint and the output density 
5
/
18
5/18 are not new.	Rewrite the literature review and every novelty claim theorem by theorem. Cite the missing works and explicitly separate new results from previously known ones.
B2	Appendix C, Theorem 5.2	BLOCKER	There is a concrete error in the 
𝑚
=
4
m=4 base case. Lemma C.4 says there are four ambiguous two-label blocks, but direct enumeration gives eight, including omitted pairs such as 
(
0001
,
0000
)
(0001,0000), 
(
0001
,
0010
)
(0001,0010), 
(
1001
,
0000
)
(1001,0000), and 
(
1001
,
0010
)
(1001,0010). This makes Lemma C.4 and the reduction in Lemma C.5 unreliable in their current form.	Replace the current argument with a rigorous fiber-product proof, or give a complete classification of all ambiguous cores and prove the reduction to those cores.
B3	Appendix B, Theorems 4.5 to 4.9	BLOCKER	The four-state sofic model is built from a “direct enumeration” of 16 synchronized length-4 factors, but completeness of that enumeration is not proved. All bulk laws, covariance formulas, and transfer-matrix calculations depend on this step.	Derive the graph from an explicit normalization transducer or provide a full combinatorial proof that exactly those 16 factors occur and no others do.
M1	Proposition B.4, Section 4.3	MEDIUM	The finite-volume to bulk limit is too compressed. The manuscript does not explicitly justify why uniform microstate words induce the path-counting measure needed for the Parry-measure limit argument.	Add a lemma showing the correspondence between uniform microstate words and admissible pair-word / path labels, with boundary effects isolated. Then invoke the standard sofic local-limit theorem precisely.
M2	Section 6, Appendix D	MEDIUM	The boundary-vector formula 
𝑍
𝑚
(
𝑦
)
=
𝛼
𝑇
𝑀
(
𝑦
)
𝑚
𝛽
(
𝑦
)
Z
m
	​

(y)=α
T
M(y)
m
β(y) is presented without a clean combinatorial derivation of the states, initial condition, or terminal vector. As written, 
𝛽
(
𝑦
)
β(y) looks ad hoc.	Introduce the weighted automaton formally, define the state interpretation, and derive 
𝛼
,
𝛽
α,β from initial and terminal conditions before extracting the recurrence.
L1	Appendix A	LOW	The irreducibility argument for “no 
11
11” is imprecise. The sentence that any 
11
11 is preceded by 0 is not literally correct inside a block like 
111
111.	Rephrase using the leftmost occurrence of 
11
11 in a maximal run.
L2	Introduction / terminology	LOW	The “gauge anomaly” language is heavier than the mathematics and partially obscures the symbolic-dynamics content.	Keep the term if desired, but relate it more transparently to restriction discrepancy / non-commutation of truncation with normalization.
4. Missing references

The manuscript needs a serious literature pass. The following are the most important omissions I see.

Alexander and Zagier (1991), The entropy of a certain infinitely convolved Bernoulli measure. This is relevant because the Fibonacci-graph / random-walk viewpoint is already present there, which is close in spirit to Sections 4 and 6. 
londmathsoc.onlinelibrary.wiley.com
+1

Sidorov and Vershik (1998), Ergodic properties of the Erdös measure, the entropy of the goldenshift, and related problems. This is highly relevant because it constructs a two-sided goldenshift and studies two-sided normalization / Fibonacci-graph dynamics, which is directly adjacent to the manuscript’s bulk model. 
Springer

Kempton (2014), Digit frequencies and Bernoulli convolutions. This is especially important. It studies the normalization map 
𝑃
P from Bernoulli 
{
0
,
1
}
{0,1}-digits to greedy golden-mean expansions, explicitly discusses two-sided normalization, and proves the normalized digit-1 frequency 
5
/
18
5/18. That overlaps the mean in Corollary 6.5 and materially affects the paper’s novelty claims. 
St Andrews Research Repository
+1

Grabner, Kirschenhofer, and Tichy (2002), Combinatorial and Arithmetical Properties of Linear Numeration Systems. This is relevant for the Erdős-measure / Fibonacci-graph / normalization perspective and should be discussed when positioning Sections 4 and 6. 
Semantic Scholar
+1

Dumont, Sidorov, and Thomas (1999), Number of representations related to a linear recurrent basis. This is relevant background for Section 6, because it studies representation counts in linear recurrent bases and is close in spirit to fold-fiber multiplicities and weighted counting. 
impan.pl

5. Specific improvements needed to reach acceptance

First, the paper needs a corrected and much sharper novelty statement. Right now it blurs together genuinely new parts with material that overlaps earlier normalization and Erdős-measure work.

Second, the core technical appendices must be rebuilt. Appendix B has to justify the four-state automaton rigorously. Appendix C has to be rewritten because the current 
𝑚
=
4
m=4 base case is factually wrong as stated.

Third, Section 6 needs a transparent transfer-matrix derivation. Once the state model is clear, the recurrence and discriminant factorization are fine. But the current presentation makes the reader reverse-engineer the construction.

Fourth, the manuscript should clearly separate three layers: classical normalization machinery, model-specific finite-state realization, and the genuinely new anomaly statistics. That would make the paper much easier to referee and much easier to trust.

6. Concrete fixes

B1. Novelty and literature positioning

Rewrite the end of the introduction around a precise theorem-by-theorem novelty map. State explicitly that:

two-sided normalization / goldenshift viewpoints already exist,

the normalized digit density 
5
/
18
5/18 is not new,

the likely new content is the window-level multiscale diagram, the anomaly process and its exact second-order statistics, the conjugacy threshold, and the explicit partition-function algebra.

A short comparison subsection titled “Relation to Erdős measure / goldenshift literature” would solve much of this.

B2. Repair Theorem 5.2

Delete the current 
𝑚
=
4
m=4 base-case proof and replace it with one of these:

A fiber-product proof. Build the fiber product 
𝐺
𝑚
×
𝐺
𝑚
G
m
	​

×G
m
	​

, remove the diagonal, and prove that for 
𝑚
≥
3
m≥3 every admissible three-label block has the same third-edge appended bit on every lift.

A complete ambiguous-core classification. Prove a precise reduction lemma showing that every ambiguous pair reduces to a finite list of cores, then list all cores correctly. For 
𝑚
=
4
m=4, the current list of four must be replaced by the full list of eight ambiguous two-label blocks.

Either route would be acceptable. The present heuristic “passive prefix” discussion is not enough by itself.

B3. Repair Appendix B

Add a full derivation of the 16 synchronized length-4 factors. A clean route is:

define the synchronized regime after a long 00-prefix,

classify all possible length-3 synchronized prefixes,

prove exactly which fourth symbols can follow each prefix,

derive the follower sets and the four-state graph from that classification.

If you prefer a transducer-based proof, then define the normalization transducer explicitly and derive the same graph from it. Scripts can remain as supplementary audit material, but not as a substitute for the derivation.

M1. Make the bulk-limit argument explicit

Insert a lemma before Theorem 4.5 proving that the map from a microstate word to its reversed pair word is injective and that interior factors of uniform length-
𝑀
M microstate words correspond to admissible labeled paths, up to 
𝑂
(
1
)
O(1) boundary effects. Then the Parry-measure convergence becomes a standard corollary instead of a handwave.

M2. Make Section 6 self-contained

Introduce the weighted automaton as an actual combinatorial object. State what each state means, what weight each transition carries, what the initial state is, and what terminal completions are encoded by 
𝛽
(
𝑦
)
β(y). Once that is done, formula (10), the recurrence, and the generating function follow cleanly and transparently.

On balance: worth another round after major revision, not ready yet.