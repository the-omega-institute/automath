<!-- oracle metadata: {"timestamp": "2026-04-10T07:06:44.213743", "model": "chatgpt-5.4-pro-extended", "response_length": 10473} -->

Referee report on the attached manuscript. 

main

Overall assessment

Major revision

The core results in Sections 3 and 4 appear mathematically sound, but the paper is not ready for acceptance. The main reason is a serious error in Proposition 5.1: the proof uses a Euclidean/comass type estimate, while the paper’s norm is the coordinate coefficient sup norm. As written, the proposition is false in that generality. Beyond that, the paper overstates novelty. The sharp constant in Theorem 3.1 is clean, but it is obtained from the standard radial homotopy formula by a very short argument on a highly restricted class. Section 4 is essentially a one-cube Whitney transfer of that same estimate, not a new cubical homotopy theory. Section 5 also needs to be repositioned relative to the anisotropic max-flow/min-cut, Cheeger, and calibrability literature, which is directly relevant to the norm duality issue there. Grieser formulates the continuous vector-field lower bound with a Euclidean norm constraint and explicitly connects it to the continuous max-flow/min-cut theorem, while Caselles and coauthors develop the anisotropic dual-norm/perimeter framework that matches the coefficient-sup setting much more closely. 
Numdam
+3
arXiv
+3
arXiv
+3

Novelty rating for each theorem

Theorem	Rating	One-line justification
Theorem 3.1	LOW	The sharp factor 
1
/
(
2
𝑘
)
1/(2k) is neat, but once one restricts to coordinate-monomial forms and the coefficient sup norm, the proof is very close to an immediate calculation from the standard radial homotopy formula.
Theorem 5.2	MEDIUM	The boundary-trace rigidity statement is the most distinctive part of the paper, but it is still elementary and should be positioned against anisotropic calibration/calibrable-set theory. 
Numdam

I would rate the other main labeled results as follows: Proposition 4.1 is LOW, since it is an almost formal 
𝐼
∘
𝐾
∘
𝑊
I∘K∘W transfer; Corollary 3.4 and Corollary 4.4 are LOW, since they are direct repackagings of the main estimate.

Issue table

ID	Section	Severity	Description	Suggested fix
B1	5.1	BLOCKER	Proposition 5.1 mixes the paper’s coefficient sup norm with a Euclidean perimeter bound. The proof uses (	V\cdot \nu
M1	1, 5	MEDIUM	Section 5 is not situated in the anisotropic Cheeger / calibrability / max-flow-min-cut literature, even though that is the natural framework for the corrected statement.	Add a literature paragraph and cite Grieser, Nozawa, Strang, Leonardi, and Caselles et al.; explain the 
ℓ
∞
ℓ
∞
-
ℓ
1
ℓ
1
 duality.
M2	Abstract, 1, 4	MEDIUM	Novelty is overstated. Section 4 is mostly a formal Whitney transfer, and Theorem 3.1 is a short computation on a very narrow class.	Recast the paper as a short sharp-constant note on a restricted class. Compress Section 4 unless genuinely new cubical content is added.
M3	1, 2, throughout	MEDIUM	The coordinate dependence of the “coefficient-
𝐿
∞
L
∞
” norm is not highlighted strongly enough. This is exactly what causes confusion in Section 5.	Introduce notation such as 
∥
⋅
∥
c
o
e
f
f
,
∞
∥⋅∥
coeff,∞
	​

, and explicitly contrast it with comass/Euclidean 
𝐿
∞
L
∞
 norms.
M4	3.1, 3.2, 4.1	MEDIUM	The phrase “operator norm on this class” is imprecise, because the admissible class of coordinate-monomial forms is not a linear subspace.	Replace by “sharp sup-ratio over the admissible family,” or define a restricted norm notation tailored to that family.
L1	4.2	LOW	The hypercube / near-detailed-balance corollaries feel ornamental. They add little mathematically and have no worked example.	Either cut them to remarks, or add a substantive example showing why this reformulation matters.
L2	5.2, Remark 5.4	LOW	The remark that minimizers are not unique in the interior is asserted but not exhibited.	Give one explicit example of adding an exact perturbation with zero boundary trace, or delete the claim.
L3	Throughout	LOW	The manuscript does not separate standard background from new content sharply enough.	Mark Theorem 3.1(1), the Whitney identities, and the basic homotopy-transfer machinery as standard, then isolate the genuinely new assertions.

Missing references

These are the main omissions I would expect to see addressed.

Section 5 related, important

D. Grieser, The first eigenvalue of the Laplacian, isoperimetric constants, and the max flow min cut theorem (Arch. Math., 2006). This is relevant because it discusses the continuous vector-field lower bound and its connection to max-flow/min-cut, but in the Euclidean norm setting. That is exactly the comparison needed to explain why Proposition 5.1, as written, is not the right general statement for the coefficient norm. 
arXiv
+1

R. Nozawa, Max-flow min-cut theorem in an anisotropic network (Osaka J. Math., 1990). This is directly relevant if the authors keep the coefficient 
ℓ
∞
ℓ
∞
 norm and correct the boundary term to an anisotropic perimeter. 
Project Euclid

G. Strang, Maximum flows and minimum cuts in the plane (J. Global Optim., 2010), or the earlier continuum max-flow/min-cut references cited by Grieser and Leonardi. This is part of the natural background for Proposition 5.1. 
Cvgmt
+1

G. P. Leonardi, An overview on the Cheeger problem (2015). This is a useful survey reference for the Cheeger-type lower bound context of Section 5. 
Cvgmt

V. Caselles, G. Facciolo, E. Meinhardt, Anisotropic Cheeger Sets and Applications (SIIMS, 2009), and V. Caselles, A. Chambolle, S. Moll, M. Novaga, A characterization of convex calibrable sets in 
𝑅
𝑁
R
N
 with respect to anisotropic norms (Ann. IHP, 2008). These are highly relevant because they formulate anisotropic perimeter 
𝑃
𝜙
(
𝐸
)
=
∫
𝜙
∘
(
𝜈
𝐸
)
 
𝑑
𝐻
𝑁
−
1
P
ϕ
	​

(E)=∫ϕ
∘
(ν
E
	​

)dH
N−1
 and dual-norm bounded calibration fields, which is the correct framework once the paper keeps the coefficient norm. 
IPOL
+1

Positioning related, helpful but less urgent

Chaumont-Frelet, Licht, Vohralík and the surrounding explicit-constant de Rham literature should be used more precisely for positioning. Their work concerns broader, different norms/geometries, and they also reference related explicit constant work by Guerini and Savo. This would help the introduction place the present note more honestly. 
arXiv

Specific improvements needed to reach acceptance

First, Section 5 must be made correct. Right now Proposition 5.1 is the main obstacle.

Second, the paper needs a more modest and more accurate statement of novelty. The real contribution is not a new homotopy theory. It is an exact coefficient-sup constant for the standard radial homotopy on a very narrow admissible family, plus a cube-specific boundary rigidity observation.

Third, the norm must be handled much more carefully. The paper should explicitly state, early and repeatedly, that this is a coordinate-dependent coefficient norm, not the usual geometric 
𝐿
∞
L
∞
 or comass norm.

Fourth, Section 4 should either be compressed or strengthened. In its current form, it reads as a formal corollary rather than as an independent contribution.

Fifth, the introduction and discussion should clearly distinguish:

what is standard,

what is an immediate corollary,

what is actually new.

Without those changes, the paper is too narrow and too overstated for acceptance.

Concrete fixes for each BLOCKER and MEDIUM issue

B1. Proposition 5.1

Actionable fix:

Keep the coefficient norm used in the paper.

Rewrite Proposition 5.1 as an anisotropic statement:

V
o
l
(
𝐸
)
≤
∥
𝑉
∥
𝐿
∞
(
Ω
;
ℓ
∞
)
∫
∂
𝐸
∣
𝜈
𝐸
∣
1
 
𝑑
𝐻
𝑛
−
1
.
Vol(E)≤∥V∥
L
∞
(Ω;ℓ
∞
)
	​

∫
∂E
	​

∣ν
E
	​

∣
1
	​

dH
n−1
.

Equivalently,

𝐶
∞
(
Ω
)
≥
sup
⁡
𝐸
V
o
l
(
𝐸
)
𝑃
1
(
𝐸
)
,
𝑃
1
(
𝐸
)
:
=
∫
∂
𝐸
∣
𝜈
𝐸
∣
1
 
𝑑
𝐻
𝑛
−
1
.
C
∞
	​

(Ω)≥
E
sup
	​

P
1
	​

(E)
Vol(E)
	​

,P
1
	​

(E):=∫
∂E
	​

∣ν
E
	​

∣
1
	​

dH
n−1
.

Then note that for the cube 
𝐼
𝑘
I
k
, one has 
𝑃
1
(
𝐼
𝑘
)
=
2
𝑘
P
1
	​

(I
k
)=2k, so the lower bound becomes 
1
/
(
2
𝑘
)
1/(2k), matching the earlier sharp upper bound.

Alternatively, if the authors insist on Euclidean perimeter 
𝐻
𝑛
−
1
(
∂
𝐸
)
H
n−1
(∂E), they must switch to the Euclidean/comass norm in Section 5 and explicitly tell the reader that Section 5 uses a different norm from Sections 2 to 4. I think this is the worse option because it breaks the coherence of the paper.

M1. Missing anisotropic literature context

Actionable fix:

Add a short paragraph at the end of the introduction and another at the start of Section 5:

explain that the coefficient sup norm corresponds to an 
ℓ
∞
ℓ
∞
 bound on calibration fields,

explain that the dual boundary quantity is the 
ℓ
1
ℓ
1
 anisotropic perimeter,

cite Grieser, Nozawa, Leonardi, and Caselles et al. 
arXiv
+2
Cvgmt
+2

Then state explicitly what is new relative to that literature: the cube-specific equality case and boundary-trace rigidity in this exact coordinate setting.

M2. Overstated novelty

Actionable fix:

Rewrite the abstract and introduction so that they say:

Theorem 3.1 gives an exact constant on a highly restricted class.

Proposition 4.1 is an immediate one-cube Whitney transfer, not a new cubical homotopy.

Theorem 5.2 is the most distinctive contribution.

I would also demote the near-detailed-balance corollary to a remark unless the authors can add a nontrivial example.

M3. Norm dependence not explicit enough

Actionable fix:

After the first norm definition, add a boxed remark such as:
“All 
𝐿
∞
L
∞
 estimates in Sections 2 to 4 use the coordinate coefficient sup norm relative to the fixed standard coordinates on the cube. This is not the comass norm and is not invariant under change of basis.”

Use notation like 
∥
⋅
∥
c
o
e
f
f
,
∞
∥⋅∥
coeff,∞
	​

 throughout.

In Section 5, explicitly identify the dual anisotropic perimeter if the authors keep this norm.

M4. “Operator norm on this class” is imprecise

Actionable fix:

Replace phrases like “sharp as an operator norm on this class” by:
“sharp for the restricted sup-ratio over nonzero admissible coordinate-monomial forms.”

If the authors want a compact notation, define

∥
𝐾
𝑘
∥
c
o
o
r
d
:
=
sup
⁡
{
∥
𝐾
𝑘
𝜔
∥
∞
∥
𝜔
∥
∞
:
𝜔
≠
0
,
 
𝜔
 coordinate-monomial
}
.
∥K
k
	​

∥
coord
	​

:=sup{
∥ω∥
∞
	​

∥K
k
	​

ω∥
∞
	​

	​

:ω

=0, ω coordinate-monomial}.

This avoids suggesting a Banach-space operator norm on a non-linear class.

My bottom line is this: the paper contains a correct and tidy core observation, but it needs one substantive mathematical correction and a significant reframing of scope and novelty before it is publishable.