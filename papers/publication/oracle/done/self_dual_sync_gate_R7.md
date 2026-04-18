<!-- oracle metadata: {"timestamp": "2026-04-10T23:36:44.338638", "model": "chatgpt-5.4-pro-extended", "response_length": 8496} -->

I reviewed the attached manuscript as a referee. My recommendation is below. 

main

1. Overall assessment

Major revision

The paper has a clear and potentially publishable core: one explicit self-dual ten-state example is carried through determinant, completion, quotient geometry, Galois group, and cyclotomic twists. That said, the current version is not yet acceptable because the proof of the asymptotic/root-separation part in Section 3.4 has substantive logical errors, and several computationally essential steps are not documented at a level that makes the paper fully checkable from the manuscript alone. The novelty is also modest and needs sharper positioning. 

main

2. Novelty rating
Result	Rating	One-line justification
Theorem 1.1(i)	LOW	Explicit determinant/factorization for one fixed 10-state matrix is useful, but essentially a worked computation.
Theorem 1.1(ii)	LOW	The completion formula and parity symmetry are straightforward consequences of the explicit determinant and self-duality.
Theorem 1.1(iii)	MEDIUM	The genus-6 curve, genus-3 quotient, and generic 
𝑆
6
S
6
	​

 statement for this concrete kernel are the most distinctive part of the paper.
Theorem 1.2(i)	LOW	The degree law and evenness are routine once the resultant product formula and symmetry are set up.
Theorem 1.2(ii)	LOW	The 
𝑚
=
2
m=2 computation is a direct specialization.
Theorem 1.2(iii)	MEDIUM	The full large-
𝑚
m expansion is nontrivial and potentially interesting, but it is still example-specific and the current proof is not rigorous enough.
3. Issue table

The table below lists the main issues that need attention before the paper can be considered for acceptance. 

main

ID	Section	Severity	Description	Suggested fix
B1	§3.4, Lemma 3.13 and Theorem 3.14	BLOCKER	The root-separation proof is not valid as written. In Step 1 the sign inference is reversed: from 
𝑤
′
(
2
)
<
0
w
′
(2)<0 and 
𝑠
<
2
s<2, one gets 
𝑤
(
𝑠
)
>
1
/
3
w(s)>1/3, not 
𝑤
(
𝑠
)
<
1
/
3
w(s)<1/3. Step 3 only proves 
𝑐
0
>
0
c
0
	​

>0, not 
𝑐
0
>
1
/
3
c
0
	​

>1/3. Step 4 is also wrong in using a fixed compact set 
𝐾
K, because other conjugates 
2
cos
⁡
(
𝑎
𝜋
/
𝑚
)
2cos(aπ/m) also approach 
±
2
±2 as 
𝑚
→
∞
m→∞. Hence Lemma 3.13 does not establish Theorem 3.14.	Replace Lemma 3.13 with a new rigorous proof. The clean route is via spectral radii of 
𝐵
(
𝑒
𝑖
𝜃
)
B(e
iθ
), strict Perron-Frobenius inequality away from 
𝑢
=
1
u=1, and local monotonicity near 
𝑠
=
2
s=2.
M1	Lemma 3.13, Step 4	MEDIUM	The statement “the next closest conjugate to 
+
2
+2 comes from 
𝑎
=
3
a=3” is false whenever 
3
∣
𝑚
3∣m, since then 
3
∉
(
𝑍
/
2
𝑚
𝑍
)
×
3∈
/
(Z/2mZ)
×
.	Replace this by a statement about the smallest admissible 
𝑎
>
1
a>1, or simply use that every admissible 
𝑎
≠
1
a

=1 satisfies 
𝑎
≥
3
a≥3.
M2	Appendix A; Props. 3.6, 3.9, 3.12	MEDIUM	Several key steps rely on a supplementary Sage worksheet that is mentioned but not provided with the manuscript. As submitted, the computational backbone is not fully reproducible.	Provide the supplement, give software/version information, and archive exact code and outputs. At minimum include enough exact certificates in the appendix to verify the Gröbner basis, discriminant data, finite-field factorizations, and jet recursion.
M3	§2.2, Definition 2.2 and Figure 1	MEDIUM	The object is motivated as the recurrent core of a two-track comparison automaton, but the underlying labelled graph/system is never specified. As written, claims like “after discarding transient states, exactly ten patterns remain” are not independently checkable.	Either define the paper’s object directly as the explicit transition system/matrix, or add the source labelled graph and the derivation of the ten-state recurrent core.
M4	Introduction, §1.2, §4	MEDIUM	The paper openly says it does not introduce a general method. That is acceptable for a short note, but then the manuscript must explain much more sharply why this example matters. Right now the significance is borderline.	Add a concise “why this example is worth isolating” discussion, ideally comparing with nearby/self-dual kernels or explaining why the completion mechanism here is unexpectedly rich.
L1	Lemma 3.5	LOW	The specialization argument for irreducibility omits the point that specialization can collapse a factor to a constant. Here the constant term 
1
1 in 
𝑤
w rescues the argument, but this should be stated.	Add one sentence explaining why any nontrivial factorization in 
𝑄
[
𝑠
,
𝑤
]
Q[s,w] has positive 
𝑤
w-degree in both factors and survives the specialization 
𝑠
=
3
s=3.
L2	Proposition 3.9, Step 1	LOW	“discriminant of the degree-six resolvent” is inaccurate terminology. No resolvent is introduced.	Replace by “discriminant of the degree-six polynomial 
Δ
^
(
𝑤
,
𝑠
)
Δ
(w,s) with respect to 
𝑤
w”.
L3	§3.3	LOW	The notation 
Φ
𝑚
+
Φ
m
+
	​

 is nonstandard and can be confused with the usual cyclotomic polynomial.	Rename it, or emphasize earlier and more prominently that it denotes the minimal polynomial of 
2
cos
⁡
(
𝜋
/
𝑚
)
2cos(π/m).
4. Missing references

There is no glaring foundational omission, but I would strongly recommend adding a few references that fit the paper’s framing more directly.

David Fried (1982), Flow equivalence, hyperbolic systems and a new zeta function for flows. This is relevant if the authors want to situate the “completed/twisted determinant” viewpoint in the broader homological or twisted dynamical-zeta literature. 
Springer
+1

H. M. Stark and A. A. Terras (2001), Artin L-functions of graph coverings. This is more directly aligned with the paper’s “Artin-style 
𝐿
L-factorisation” language than ST96/ST00 alone. 
scite.ai

Y.-B. Choe, J. H. Kwak, Y. S. Park, I. Sato (2007), Bartholdi zeta and L-functions of weighted digraphs, their coverings and products. This is especially relevant if the authors keep emphasizing weighted digraphs and covering-factor decompositions. 
ScienceDirect

Hyman Bass (1992), The Ihara-Selberg Zeta Function of a Tree Lattice. If the graph-zeta framing remains prominent, this is a natural foundational citation. 
World Scientific

5. Specific improvements needed to reach acceptance

First, Section 3.4 must be rewritten so that the asymptotic theorem is proved rigorously, not heuristically. Right now that section is the main obstacle.

Second, the computational parts need publication-standard reproducibility. For a paper whose main contribution is an explicit case study, exact certificates and accessible code are part of the proof, not optional extras.

Third, the kernel itself should be made self-contained. Either the paper is about an explicitly given 10-state weighted digraph, or it is about a synchronisation construction from a specified labelled system. At present it sits awkwardly between the two.

Fourth, the authors need to sharpen the framing. The manuscript should explain why this example is mathematically illuminating, not just computable.

6. Concrete fixes for each BLOCKER and MEDIUM issue
ID	Concrete fix
B1	Prove Lemma 3.13 by identifying, for 
𝑠
=
2
cos
⁡
𝜃
s=2cosθ, the minimal-modulus 
𝑤
w-root with 
1
/
𝜌
(
𝐵
(
𝑒
𝑖
𝜃
)
)
1/ρ(B(e
iθ
)). Since (
M1	Replace the incorrect “
𝑎
=
3
a=3” claim by a statement involving the smallest admissible 
𝑎
>
1
a>1 with 
gcd
⁡
(
𝑎
,
2
𝑚
)
=
1
gcd(a,2m)=1. For comparison estimates, it is enough to use 
𝑎
≥
3
a≥3.
M2	Upload the Sage worksheet with the submission, archive it in a stable repository, and state the exact software version. In the paper itself, include exact outputs for the Gröbner basis 
{
1
}
{1}, the discriminant degree/leading coefficient, the relevant finite-field factorizations, and the jet coefficients used in Proposition 3.12.
M3	Either add a short subsection specifying the original labelled graph/automaton and showing how the ten recurrent states arise, or remove the derivational narrative and define the kernel directly by the explicit transition table and matrix.
M4	Add a compact positioning paragraph explaining what is structurally special here. For example: why self-duality compresses the twist parameter to a degree-6 completed determinant, why that unexpectedly yields genus 6 and generic 
𝑆
6
S
6
	​

, and why this is not typical for arbitrary self-dual kernels. Also add the missing references above if the current framing is retained.

In its current form I would not recommend acceptance, but I do think the paper could become publishable after a serious revision centered on Section 3.4 and on reproducibility.