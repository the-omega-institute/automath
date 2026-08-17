1. Verdict
Reject.
Single strongest reason: Theorem 6.6 is false under its stated hypotheses. Its proof silently assumes that the cell-face incidence matrix is the incidence matrix of a dual graph—so every internal face has opposite incidence signs in its two adjacent cells—and also assumes that every component can discharge flux to an exterior sink. Neither assumption appears in the theorem. The result is advertised for an arbitrary finite pure cubical complex. 
This is not merely a missing sentence in the exposition: without those hypotheses the claimed numerical formula is wrong.
2. Significance and venue
It does not clear the Journal of Dynamical and Control Systems threshold. Indeed, it is barely in the journal’s subject.
JDCS is explicitly centered on smooth dynamical systems, geometric control, optimization and related differential-geometric control questions. Its current author guidance also says that originality, correctness and satisfactory presentation are insufficient when a submission uses only established standard methods. Springer Nature Link+1 This paper contains no dynamical system, no control system, no evolution, no controllability question and no stability problem in the dynamical-systems sense. “Boundary readout” does not make it a control paper.
Even after the false global theorem is repaired, the contribution is too small for JDCS. The sharp homotopy bound is a one-line contraction estimate followed by integration; the box result is the divergence theorem plus a saturation identity; and the discrete result is finite-dimensional max-flow/min-cut and linear-programming duality. The manuscript itself acknowledges that the homotopy formula, calibration principle, max-flow/min-cut argument and Whitney identities are classical. 
Right-sized journal: Results in Mathematics, after correction and substantial compression. It is a broad pure-and-applied mathematics journal suited to a self-contained sharp-inequality note of this level. Springer Nature Link
3. Correctness: a theorem is false
The explicit counterexample
Theorem 6.6 begins with an arbitrary finite pure cubical complex, independently oriented top cells and codimension-one faces, and its cell-face incidence matrix B. It then asserts
min{∥f∥K,a,∞​:Bf=v}=hK​.

Take k=1. Let K consist of two unit intervals C1​,C2​ joined at a middle vertex e1​, with outer vertices e0​,e2​. Orient both intervals toward the middle vertex:
∂C1​=e1​−e0​,∂C2​=e1​−e2​.
Take all vertex weights ae​=1 and both cell volumes vC1​​=vC2​​=1. In the order e0​,e1​,e2​,
B=(−10​11​0−1​).
The cut ratio is
a(δ{C1​})v({C1​})​=21​,a(δ{C2​})v({C2​})​=21​,
while for the full set,
a(δ{C1​,C2​})v({C1​,C2​})​=22​=1.
Thus hK​=1.
Now set
fe0​​=−21​,fe1​​=21​,fe2​​=−21​.
Then
Bf=(−(−1/2)+1/21/2−(−1/2)​)=(11​)=v,
but
∥f∥K,a,∞​=21​<hK​.
So part 1 of Theorem 6.6 is false.
Exactly where the proof breaks
The proof says to regard each face as an edge of the dual graph and calls B its signed incidence matrix. It then sums Bf=v over a cut Q, cancelling all internal faces. 
In the counterexample, the shared vertex e1​ has incidence +1 in both rows. Its column is therefore not a graph-incidence column (+1,−1); it is (+1,+1). The internal contribution is 2fe1​​, not zero. Hence the displayed cut identity used for complementary slackness is simply false.
This is precisely the structural kind of failure you asked about: a local cell-face incidence array is treated as if it globally had the cancellation property of a coherently oriented dual graph. The proof never establishes that global property.
A second independent missing hypothesis
Even after coherent orientation is imposed, the theorem also needs every connected component to meet the exterior sink. Take K to be the boundary of a three-dimensional cube, regarded as a pure two-dimensional cubical complex with its six square cells coherently oriented. Every edge belongs to two cells, so there is no exterior face. Summing all cell equations gives
C∑​(Bf)C​=0
for every f, whereas ∑C​vC​>0. Thus Bf=v has no solution. Moreover, for the full cell set, δC=∅, so the defining ratio v(C)/a(δC) has zero denominator. The theorem nevertheless claims FhK​​=∅.
A repair would require, at minimum:


a coherently oriented cubical pseudomanifold or cubical domain, so each internal face has opposite incidences;


at least one exterior face in every connected component; and


preferably a direct formulation saying that B is the node-edge incidence matrix of the dual graph with an exterior sink.


Under those assumptions, the linear-programming argument appears repairable. But the theorem currently printed—and prominently advertised—is false.
The continuous part
I did not find the analogous cascade or pointwise-to-uniform failure in Theorems 3.1–5.8. In particular, the slicing in Theorem 5.8 is legitimate: every active slice is itself a primitive problem with norm at least mB,I​ and at most the global norm M; integrating the slice estimate therefore gives the asserted global L1 estimate. The equality argument at M=mB,I​ is also genuinely slice-uniform.
There are two smaller repairs:


In Theorem 5.4, the inequality
∣sf−mR​∣≤(M−sf)+(M−mR​)
uses M≥mR​. That fact already follows from Lemma 5.3 because the associated field is admissible, but it should be invoked before the inequality rather than supposedly deduced afterward.


Proposition 6.4 proves sharpness by saying it is enough to take n=k+1. For a theorem stated at each fixed n≥k+1, the authors should explicitly embed that example into a (k+1)-face of In. The repair is routine.


Neither of those is comparable to the failure of Theorem 6.6.
4. Front-matter hypotheses
Yes. There are two material overstatements.
The blanket continuous claim is false
The introduction says:

“For constant differential forms on axis-aligned boxes the answer is yes”

where “the answer” is that sharp interior saturation determines the boundary trace. 
That is true for a top-degree form on a box of the same dimension. It is false for lower-degree constant forms on a higher-dimensional box. The actual sliced theorem only controls specified active coefficients, not the whole trace.  The manuscript later admits this explicitly. 
A concrete counterexample is on I3 with
ω=dx1​∧dx2​.
The canonical minimizer is
η0​=21​[(x1​−21​)dx2​−(x2​−21​)dx1​],∥η0​∥coeff,∞​=41​.
For every ∣ε∣≤41​,
ηε​=η0​+εdx3​
still satisfies
dηε​=dx1​∧dx2​,∥ηε​∥coeff,∞​=41​.
But its full boundary trace varies with ε; for example, on x1​=0 the added term εdx3​ survives. Thus exact norm saturation does not determine the full trace. Only the active coefficient singled out in Theorem 5.8 is rigid.
The introductory sentence must be restricted to top-degree data, or rewritten to distinguish full trace determination from active-coefficient determination.
The global cubical claim omits necessary structural hypotheses
The abstract says that the dual-graph theorem works on “finite cubical complexes,” and the main-results discussion repeats that the global profile is governed by a dual-graph Cheeger ratio.  
That needs the coherent-orientation and exterior-sink hypotheses identified above. Strictly speaking, this is not a discrepancy between the front matter and a more careful theorem statement—the theorem itself is equally under-hypothesized. Both must be corrected.
The top-degree box assertions in the abstract—exact m(R), the affine minimizer and canonical trace for minimizers—do match Theorem 5.4.
5. Length
The length is not justified. Scale is being manufactured.
The paper is essentially three short notes joined together:


an elementary coefficient estimate for the radial homotopy;


a box calibration and boundary-deficit identity;


a finite-dimensional flow/linear-programming calculation.


Too many routine steps receive standalone names and full theorem-style treatment. Lemma 2.5 is a one-line coordinate bound. Proposition 3.2 is the homotopy identity applied to dω. Corollary 3.3 is its k=1 translation. Lemma 5.1 is the divergence theorem. Proposition 5.2 is the identity
MP1​(Ω)−Vol(Ω)=P1​(Ω)(M−C∞​(Ω)).
Lemma 5.3 is a one-line box calibration. Definition 5.5 does not need to exist. Corollary 5.7 merely observes that the displayed primitive attains the already-computed constant. Proposition 6.1 is standard Whitney algebra, Proposition 6.3 is basis inspection, and Corollary 6.7 is just Proposition 6.4 with k=1.
The manuscript’s own theorem-by-theorem comparison effectively concedes how much of this is classical or immediately derived. 
The 27-page version should be cut to roughly 14–16 pages:


remove the theorem-by-theorem apologia in §1.1;


merge Lemma 5.1, Proposition 5.2, Lemma 5.3 and Theorem 5.4 into one theorem with one proof;


fold Proposition 3.2 and Corollary 3.3 into remarks after Theorem 3.1;


cite or drastically shorten the standard Whitney identities;


retain a corrected Theorem 6.6 and the strict-loss example only if the authors want a genuine discrete component.


The duplicated section headings “4” and “5” on the same page are merely editorial sloppiness, but they reinforce the impression that this is not a submission-ready manuscript.
