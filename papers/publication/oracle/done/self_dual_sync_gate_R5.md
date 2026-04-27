<!-- oracle metadata: {"timestamp": "2026-04-08T10:33:43.050173", "model": "chatgpt-5.4-pro-extended", "response_length": 11377} -->

I reviewed the uploaded paper 

main

1. Overall assessment

Major revision

My read is that several core explicit calculations are likely correct, and the paper does contain a coherent package of results for one concrete kernel. But the manuscript has one serious conceptual problem: the “cyclic lift” result in Section 3.5 is not the natural lift associated with the weighted matrix 
𝐵
(
𝑢
)
=
𝐵
0
+
𝑢
𝐵
1
B(u)=B
0
	​

+uB
1
	​

, so the announced dynamical interpretation of the cyclotomic twists is not actually established. In addition, the paper is under-positioned relative to established literature on graph-covering 
𝐿
L-functions and finite-group extensions of shifts of finite type, and too many key claims are left as opaque CAS outputs. As written, I would not recommend acceptance. With substantial repair, I could imagine it as a short note in a specialized venue. 
Cambridge University Press & Assessment
+7
worldscientific.com
+7
ScienceDirect
+7

2. Novelty rating for each theorem

The theorem labels below follow the manuscript. 

main

Result	Novelty	One-line justification
Theorem 1.1(i)	LOW	Explicit determinant and 
𝑢
=
1
u=1 factorization are straightforward symbolic computations for a fixed 10-state example.
Theorem 1.1(ii)	LOW	The completion 
(
𝑢
=
𝑟
2
,
 
𝑠
=
𝑟
+
𝑟
−
1
,
 
𝑤
=
𝑧
𝑟
)
(u=r
2
, s=r+r
−1
, w=zr) and parity relation are direct consequences of the self-duality.
Theorem 1.1(iii)	MEDIUM	The genus-6/genus-3 geometry plus generic 
𝑆
6
S
6
	​

 Galois group is a nontrivial explicit package for this example, but it is still a case study using standard tools.
Theorem 1.2(i)	LOW	The degree law is essentially immediate from the resultant product formula once 
Δ
^
Δ
 is known.
Theorem 1.2(ii)	LOW	The 
𝑚
=
2
m=2 value is a direct special-case factorization.
Theorem 1.2(iii) / Theorem 3.11	MEDIUM	The explicit large-
𝑚
m expansion appears new for this kernel, but it comes from a standard implicit-function jet computation.
Theorem 3.7	LOW	This is a technical restatement/refinement of Theorem 1.2(i), with little independent novelty.
3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Section 3.5, Abstract, Introduction	BLOCKER	The paper claims a dynamical interpretation via “cyclic lifts,” but Proposition 3.13 studies 
𝑀
⊗
𝑃
𝑞
M⊗P
q
	​

, which is not the label-dependent cyclic lift attached to 
𝐵
(
𝑢
)
=
𝐵
0
+
𝑢
𝐵
1
B(u)=B
0
	​

+uB
1
	​

. The natural lift should be 
𝐵
0
⊗
𝐼
𝑞
+
𝐵
1
⊗
𝑃
𝑞
B
0
	​

⊗I
q
	​

+B
1
	​

⊗P
q
	​

. As written, the link between 
𝑅
𝑚
,
𝜌
𝑚
R
m
	​

,ρ
m
	​

 and cyclic lifts is not proved.	Replace Section 3.5 with the correct skew-product lift and its Fourier decomposition, or delete all cyclic-lift claims.
B2	Propositions 3.1, 3.4, 3.6, 3.9, Appendix A	BLOCKER	Central claims are justified by phrases like “symbolic computation,” “Gröbner-basis computation,” or “verified by computer algebra,” but no scripts, outputs, or exact certificates are supplied. For a paper whose contribution is largely explicit computation, this is not enough.	Provide a supplementary verification package with exact code and machine-checkable outputs.
M1	Section 1.2, bibliography	MEDIUM	The literature review misses foundational work on graph-covering 
𝐿
L-functions and finite-group/SFT extensions. This makes the novelty look larger than it is and hides the closest conceptual precedents.	Add the missing references and explain clearly what is new here: one fully explicit self-dual example, not a new general theory.
M2	Proposition 3.6	MEDIUM	The Galois-group proof skips the precise Dedekind/Frobenius step that turns squarefree mod-
𝑝
p factorization into cycle types in the specialization Galois group, and then into information about the generic group.	State and cite the exact specialization and mod-
𝑝
p factorization theorem being used.
M3	Section 3.2, notation before Proposition 3.4	MEDIUM	The paper defines the function field 
𝑘
(
𝐶
a
𝑓
𝑓
)
k(C
aff
	​

) and smooth projective models before explicitly proving irreducibility of 
Δ
^
Δ
, and the base field 
𝑘
k is not fixed cleanly.	Prove irreducibility earlier, or reorder the arguments and specify the base field.
M4	Section 2.2	MEDIUM	The 10-state “synchronisation kernel” is too opaque. The state labels are unexplained and there is no diagram of the automaton.	Add a graph figure and a paragraph explaining how the comparison automaton is built and why these 10 states arise.
M5	Lemma 3.10	MEDIUM	The root-separation argument is plausible, but phrasing is imprecise. In particular, for even 
𝑚
m the minimal-modulus root of 
𝑅
𝑚
R
m
	​

 is not unique because 
±
𝑤
∗
(
𝑠
𝑚
)
±w
∗
(s
m
	​

) both occur.	Rewrite the statement in terms of minimal modulus, not uniqueness, and give explicit constants or a sharper root-gap argument.
L1	Title, Abstract, Introduction	LOW	The framing still sounds broader than the contribution. The paper is really an explicit case study/note.	Reframe it honestly as a worked example.
L2	Section 3.3	LOW	“Completed determinant” and 
Φ
𝑚
+
Φ
m
+
	​

 are nonstandard terminology/notation.	Add a short notation remark and relation to standard real cyclotomic terminology.
4. Missing references

These are the most important omissions I see.

Ki-ichiro Hashimoto, “On zeta and L-functions of finite graphs” (1990). This is a direct antecedent for graph 
𝐿
L-functions and character-twisted factorizations, much closer to the present cyclotomic-twist story than the current bibliography suggests. 
worldscientific.com

H. M. Stark and A. A. Terras, “Zeta Functions of Finite Graphs and Coverings” (1996), and Part II (2000). These works develop graph coverings, Artin-style 
𝐿
L-functions, and factorization formulas for zeta functions of coverings. That is directly relevant to the manuscript’s twist/lift narrative. 
ScienceDirect
+1

Motoko Kotani and Toshikazu Sunada, “Zeta Functions of Finite Graphs” (2000). Standard determinant and Perron-Frobenius treatment, relevant for the paper’s determinant-centric viewpoint. 
ms.u-tokyo.ac.jp

Roy Adler, Bruce Kitchens, Brian Marcus, “Finite group actions on shifts of finite type” (1985). Foundational for finite-group extensions of SFTs, which is the correct dynamical framework for the label-tracking cyclic lift. 
Cambridge University Press & Assessment

Ulf-Rainer Fiebig, “Periodic points and finite group actions on shifts of finite type” (1993). Very relevant for the “periodic data” and polynomial invariants of finite-group actions on SFTs. 
Cambridge University Press & Assessment

Mark Pollicott and Richard Sharp, “Rates of Recurrence for 
𝑍
𝑞
Z
q
 and 
𝑅
𝑞
R
q
 Extensions of Subshifts of Finite Type” (1994). This is directly relevant to periodic-orbit asymptotics in group extensions and should be discussed if the paper wants a dynamical interpretation of twisted growth. 
OUP Academic

Mike Boyle and Scott Schmieding, “Finite group extensions of shifts of finite type: 
𝐾
K-theory, Parry and Livšic” (2017). This shows that the matrix-over-group-ring viewpoint already has a developed symbolic-dynamical framework. 
Cambridge University Press & Assessment

Audrey Terras, Zeta Functions of Graphs (2010/2011). A standard monograph covering Ihara zeta, coverings, and Artin-style factors. 
Cambridge University Press & Assessment
+1

5. Specific improvements needed to reach acceptance

Fix the cyclic-lift section. This is the main mathematical problem. The manuscript must either prove the correct lift/twist correspondence or drop those claims entirely.

Make the explicit computations reproducible. Right now the reader is asked to trust black-box CAS output for several central steps.

Reposition the paper in the literature. The current bibliography does not reflect the closest prior work on graph-covering 
𝐿
L-functions and SFT group extensions.

Tighten the proofs around Proposition 3.6 and Lemma 3.10. These arguments are basically salvageable, but they need cleaner statements and references.

Improve accessibility of the construction. A figure of the 10-state automaton and a short derivation of the state set would materially improve readability.

Either broaden the conceptual takeaway or narrow the pitch. As it stands, the paper is best presented as a short explicit note.

6. Concrete fixes

B1. Correct the lift.
Define the actual 
𝑞
q-cyclic label lift

𝐵
~
𝑞
:
=
𝐵
0
⊗
𝐼
𝑞
+
𝐵
1
⊗
𝑃
𝑞
,
B
q
	​

:=B
0
	​

⊗I
q
	​

+B
1
	​

⊗P
q
	​

,

where 
𝑃
𝑞
P
q
	​

 is the cyclic permutation matrix on 
𝑍
/
𝑞
𝑍
Z/qZ. Then diagonalize 
𝑃
𝑞
P
q
	​

 by the discrete Fourier transform to obtain

det
⁡
(
𝐼
−
𝑧
𝐵
~
𝑞
)
=
∏
𝑗
=
0
𝑞
−
1
det
⁡
(
𝐼
−
𝑧
(
𝐵
0
+
𝜔
𝑞
𝑗
𝐵
1
)
)
=
∏
𝑗
=
0
𝑞
−
1
Δ
(
𝑧
,
𝜔
𝑞
𝑗
)
.
det(I−z
B
q
	​

)=
j=0
∏
q−1
	​

det(I−z(B
0
	​

+ω
q
j
	​

B
1
	​

))=
j=0
∏
q−1
	​

Δ(z,ω
q
j
	​

).

After pairing conjugate characters and passing to 
𝑤
=
𝑧
𝑟
w=zr, this gives the real factors involving 
Δ
^
(
𝑤
,
2
cos
⁡
(
𝜋
𝑗
/
𝑞
)
)
Δ
(w,2cos(πj/q)). That is the correct route to connect lifts, twists, and 
𝑅
𝑚
R
m
	​

. If the authors do not want to do this, then all mentions of “cyclic lifts” should be removed from the title, abstract, introduction, and Section 3.5.

B2. Supply a verification package.
Include a supplementary file or repository containing:

construction of the 
10
×
10
10×10 matrix from the transition list;

exact determinant expansion;

Gröbner-basis computation for 
⟨
𝐹
,
𝐹
𝑥
,
𝐹
𝑦
⟩
⟨F,F
x
	​

,F
y
	​

⟩;

discriminant computation for 
disc
⁡
𝑤
Δ
^
disc
w
	​

Δ
;

mod-
7
7 and mod-
19
19 factorizations used in Proposition 3.6;

the recursive implicit-differentiation code producing the sixth-order jet in Proposition 3.9.
In the appendix, quote the exact outputs, not just that a CAS was used.

M1. Rewrite the literature review.
Add a paragraph that separates three strands:

graph zeta and graph-covering 
𝐿
L-functions;

finite-group extensions of shifts of finite type and periodic data;

the present paper’s new part, namely a single explicit self-dual kernel for which determinant, quotient geometry, Galois group, and cyclotomic asymptotics are all computed concretely.

M2. Repair Proposition 3.6.
State the precise theorem being used: squarefree factorization mod 
𝑝
p gives Frobenius cycle type in the specialization Galois group, and a non-branch specialization embeds into the generic Galois group. Then cite a standard source and point out explicitly why 
𝑠
=
2
,
3
s=2,3 avoid the discriminant locus.

M3. Fix the logical order around irreducibility.
Insert a short lemma right after Proposition 3.3: since 
Δ
^
(
𝑤
,
3
)
Δ
(w,3) is irreducible mod 
7
7, it is irreducible over 
𝑄
Q, hence 
Δ
^
(
𝑤
,
𝑠
)
Δ
(w,s) is irreducible over 
𝑄
(
𝑠
)
Q(s). Then define 
𝑋
X and 
𝑌
Y over 
𝑘
=
𝑄
‾
k=
Q
	​

 or 
𝑘
=
𝑄
k=Q.

M4. Explain the kernel.
Add one figure of the labeled directed graph and one paragraph saying what each state encodes in the path-comparison process. At present the construction reads as an unexplained lookup table.

M5. Sharpen Lemma 3.10.
Replace “the smallest-modulus root” by “a minimal-modulus root,” or treat the even-
𝑚
m symmetry separately. Better still, give an explicit disk 
𝐷
D and an explicit lower bound on the modulus of the other roots for 
𝑠
s near 
2
2, either analytically or by interval-certified numerics.

My recommendation stays at Major revision. The paper has a viable core, but it needs a real structural repair before it is publishable.