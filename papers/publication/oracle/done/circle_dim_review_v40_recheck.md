
============================================================
For the manuscript Cayley–Chebyshev Mode Calculus, Poisson Entropy Asymptotics, and Cardinal Reconstruction in a Strip RKHS, my recommendation is:

1. Overall assessment

Major revision

The paper has a potentially publishable core, especially in the entropy-asymptotic part around the explicit eighth-order expansion and the defect-ladder results. In its current form, however, it is not ready for acceptance. The main problems are substantive, not cosmetic: Theorem 6.3 and Theorems 7.4–7.5 are false as stated because algebraic spans are treated as completed Hilbert subspaces; the strip-RKHS kernels in Proposition 7.3 are written with 
𝑧
−
𝑤
z−w rather than 
𝑧
−
𝑤
ˉ
z−
w
ˉ
, which is incompatible with the standard complex RKHS formalism; and the proof of Theorem 6.4 uses the incorrect identity 
𝜑
(
−
𝑟
)
=
𝜑
(
𝑟
)
φ(−r)=φ(r). In addition, the bibliography is unfinished, with many [?] placeholders, and the novelty claims in Section 7 are stronger than the paper itself justifies. 

main

 

circle_dimension_haar_jfa

 

circle_dimension_haar_jfa

 

main

2. Novelty rating for each theorem

These ratings are my assessment of apparent novelty, not a definitive priority judgment.

Theorem	Rating	One-line justification
4.2 Haar pullback uniqueness	LOW	Essentially a normalized change-of-variables argument once the angular parametrization is fixed.
5.1 Entropy identity in Cayley coordinates	LOW	Standard entropy change-of-variables formula in a specific chart.
5.6 Cayley–Chebyshev mode formula	MEDIUM	Explicit mode formulas are neat and useful, but structurally close to the classical Chebyshev generating function.
5.9 Odd-order vanishing in entropy expansion	MEDIUM	The parity cancellation is elegant and useful, though it rests on a fairly direct symmetry mechanism.
5.10 Eighth-order entropy expansion	HIGH	This looks like a genuine technical contribution and is one of the strongest parts of the paper.
5.11 Two-level defect ladder	HIGH	The defect decomposition appears original and conceptually interesting if correct.
5.12 Defect amplification	HIGH	This is the clearest conceptual advance in the manuscript.
5.13 Quantitative rigidity toward the symmetric two-point law	MEDIUM	A useful consequence of the defect identities, but the proof is relatively elementary once those identities are in place.
6.1 Mode Gram kernel	MEDIUM	The explicit kernel formula is nice, but the proof is short and the result is closer to a sharp identification than a deep theorem.
6.3 Mode space and RKHS completion	MEDIUM	The identification is attractive, but mathematically standard once density is proved.
6.4 Centered Poisson reconstruction	LOW	Fundamentally Laplace-transform uniqueness plus characteristic-function inversion.
6.7 Observation channels as evaluation functionals	LOW	More interpretive packaging than a major new theorem.
7.4 Lattice sampling	LOW	The paper itself acknowledges this as a standard consequence of classical shift-invariant-space theory. 

circle_dimension_haar_jfa


7.5 Cardinal reconstruction	LOW	Again mostly standard in structure; the novelty lies only in the explicit symbol/interpolant formulas. 

circle_dimension_haar_jfa

3. Issue table
ID	Section	Severity	Description	Suggested fix
I1	1, 2, 7, bibliography	BLOCKER	Many bibliography placeholders [?]; standard dependencies and prior work are not actually cited.	Complete bibliography and replace all placeholders with real references.
I2	Theorem 6.3	BLOCKER	The theorem concludes 
𝑆
=
𝐿
0
2
(
𝜔
)
S=L
0
2
	​

(ω) from 
𝑆
⊥
=
{
0
}
S
⊥
={0}; this proves only density, not equality.	Replace algebraic span by closed span, restate theorem, and adjust proof.
I3	Theorems 7.4–7.5	BLOCKER	
𝐻
𝐾
(
𝑍
)
H
K
	​

(Z) and 
𝑆
𝑍
S
Z
	​

 are defined as spans but then treated as complete Hilbert spaces supporting arbitrary 
ℓ
2
ℓ
2
 interpolation.	Define them as closed spans and formulate results as Riesz-basis statements for those closed subspaces.
I4	Proposition 7.3, Section 7	BLOCKER	The strip kernels use 
𝑧
−
𝑤
z−w rather than 
𝑧
−
𝑤
ˉ
z−
w
ˉ
; real/complex Hilbert conventions are not declared, so the RKHS-on-the-strip claim is not correct as written.	Work in a complex Hilbert space and correct the reproducing kernels to depend on 
𝑤
ˉ
w
ˉ
.
I5	Theorem 6.4	MEDIUM	The proof uses the false identity 
𝜑
(
−
𝑟
)
=
𝜑
(
𝑟
)
φ(−r)=φ(r).	Replace it by 
𝜑
(
−
𝑟
)
=
𝜑
(
𝑟
)
‾
φ(−r)=
φ(r)
	​

 and invoke Lévy inversion.
I6	Theorems 5.11–5.13	MEDIUM	Moment assumptions are imprecise: “under the hypotheses of Theorem 5.9” is too weak/ambiguous for 
𝐶
8
,
Δ
8
C
8
	​

,Δ
8
	​

, while 5.13 needs less than stated.	State exact moment hypotheses theorem by theorem.
I7	Section 5 and Appendix A	MEDIUM	Internal consistency problems: wrong theorem/equation cross-references, and Appendix A contains an inconsistent value for 
∫
𝑢
2
3
 
𝑑
𝜔
∫u
2
3
	​

dω.	Audit numbering and correct the appendix calculation.
I8	Abstract, Introduction, Section 7	MEDIUM	Novelty framing is overstated for the sampling/cardinal-reconstruction part, which the manuscript itself calls “standard consequences.”	Narrow the claimed novelty to the explicit symbol/cardinal-kernel/norm formulas.
I9	Sections 4–6	LOW	Several elementary results are promoted as major theorems, obscuring the genuinely new contribution.	Compress standard preliminaries or move some of them to an appendix.
I10	Global notation	LOW	Notation is overloaded and the dependency structure is hard to audit.	Add a notation/dependency roadmap, especially before Section 5 and Section 7.

The issues above arise directly from the theorem statements and proofs in Sections 5–7 and Appendix A. 

circle_dimension_haar_jfa

 

circle_dimension_haar_jfa

 

main

 

circle_dimension_haar_jfa

4. Missing references

At minimum, the paper should add the standard sources it is already implicitly using:

N. Aronszajn, Theory of Reproducing Kernels, for Sections 6–7.

D. V. Widder, The Laplace Transform, for uniqueness/inversion in Theorem 6.4.

E. Lukacs, Characteristic Functions, for characteristic-function inversion.

P. Duren, Theory of 
𝐻
𝑝
H
p
 Spaces, for the Hardy/Poisson-boundary discussion.

C. de Boor, R. DeVore, A. Ron, The Structure of Finitely Generated Shift-Invariant Spaces in 
𝐿
2
(
𝑅
𝑑
)
L
2
(R
d
), for Section 7.

A. Aldroubi, K. Gröchenig, Nonuniform Sampling and Reconstruction in Shift-Invariant Spaces, for the sampling framework.

A. R. Barron, Entropy and the Central Limit Theorem, and ideally also Carlen–Carvalho on entropy production, for the entropy-context claims.

M. D. Buhmann, on radial-basis/cardinal interpolation, for the Poisson/Cauchy analogue discussion in Section 7. 
Cambridge University Press & Assessment
+9
ams.org
+9
Google Books
+9

5. Specific improvements needed to reach acceptance

First, Sections 6 and 7 need a serious theorem-by-theorem repair, not a light edit. In particular, the authors must correct the span/completion errors, choose and state a consistent real-versus-complex Hilbert-space convention, and rewrite the strip-kernel formulas accordingly. Without that, the RKHS and Hardy-splitting parts are not mathematically reliable. 

circle_dimension_haar_jfa

 

circle_dimension_haar_jfa

Second, the paper needs a full bibliographic completion. In the current version, the placeholders prevent the reader from checking what is classical, what is adapted, and what is plausibly new. That alone is enough to block acceptance. 

main

Third, the authors should sharpen the manuscript’s focus. The strongest material is the explicit entropy expansion and the defect ladder in Section 5. The standard preliminaries and standard shift-invariant consequences should be clearly labeled as such, compressed, or partially moved to an appendix. The present structure makes the paper seem more novel in breadth than it really is. 

main

 

circle_dimension_haar_jfa

Fourth, the authors should add a one-page “assumption/dependency map” before Section 5, indicating exactly which moments are needed for each theorem and which appendix identities feed which coefficients. Right now the reader has to reconstruct that dependency graph manually.

6. Concrete fixes for each BLOCKER and MEDIUM issue
I1. Incomplete bibliography and placeholders

This must be fixed globally. A minimal actionable repair is:

After the sentence invoking reproducing kernels, cite Aronszajn.

After Laplace-transform uniqueness in Theorem 6.4, cite Widder.

After characteristic-function inversion in Theorem 6.4, cite Lukacs or Feller II.

After the Hardy/Poisson-boundary discussion in Proposition 7.1 / Remark 7.2, cite Duren.

After the shift-invariant-space discussion in Section 7, cite de Boor–DeVore–Ron and Aldroubi–Gröchenig.

After the entropic-CLT context in the introduction, cite Barron and optionally Carlen–Carvalho.

After the “Gaussian/Lorentz” interpolation comparison, cite Buhmann. 
Cambridge University Press & Assessment
+9
ams.org
+9
Google Books
+9

I2. Theorem 6.3 is false as stated

Current statement:

𝑆
:
=
span
⁡
{
Ψ
𝜀
:
𝜀
∈
𝑅
}
,
𝑆
=
𝐿
0
2
(
𝜔
)
.
S:=span{Ψ
ε
	​

:ε∈R},S=L
0
2
	​

(ω).

But the proof only shows 
𝑆
⊥
=
{
0
}
S
⊥
={0}, which implies

𝑆
‾
 
𝐿
2
(
𝜔
)
=
𝐿
0
2
(
𝜔
)
,
S
L
2
(ω)
=L
0
2
	​

(ω),

not 
𝑆
=
𝐿
0
2
(
𝜔
)
S=L
0
2
	​

(ω). 

circle_dimension_haar_jfa

Corrected statement

𝑆
0
:
=
span
⁡
{
Ψ
𝜀
:
𝜀
∈
𝑅
}
,
𝑆
0
‾
 
𝐿
2
(
𝜔
)
=
𝐿
0
2
(
𝜔
)
.
S
0
	​

:=span{Ψ
ε
	​

:ε∈R},
S
0
	​

	​

L
2
(ω)
=L
0
2
	​

(ω).

Then:

𝑈
0
:
𝑆
0
→
𝐻
𝐾
,
𝑈
0
(
Ψ
𝜀
)
=
𝐾
(
⋅
,
𝜀
)
,
U
0
	​

:S
0
	​

→H
K
	​

,U
0
	​

(Ψ
ε
	​

)=K(⋅,ε),

is an isometry and extends uniquely to a unitary

𝑈
:
𝐿
0
2
(
𝜔
)
→
𝐻
𝐾
.
U:L
0
2
	​

(ω)→H
K
	​

.

Corrected proof sketch
From the argument already given, 
𝑆
0
⊥
=
{
0
}
S
0
⊥
	​

={0}. By Hilbert-space duality, that is equivalent to 
𝑆
0
‾
=
𝐿
0
2
(
𝜔
)
S
0
	​

	​

=L
0
2
	​

(ω). Since 
𝑈
0
U
0
	​

 is isometric on 
𝑆
0
S
0
	​

 and the kernel sections span a dense subspace of 
𝐻
𝐾
H
K
	​

, 
𝑈
0
U
0
	​

 extends uniquely by continuity to all of 
𝐿
0
2
(
𝜔
)
L
0
2
	​

(ω), and the image is all of 
𝐻
𝐾
H
K
	​

.

I3. Theorems 7.4–7.5 must use closed spans

Current definitions:

𝐻
𝐾
(
𝑍
)
:
=
span
⁡
{
𝐾
(
⋅
,
𝑛
)
:
𝑛
∈
𝑍
}
,
𝑆
𝑍
:
=
span
⁡
{
Ψ
𝑛
:
𝑛
∈
𝑍
}
,
H
K
	​

(Z):=span{K(⋅,n):n∈Z},S
Z
	​

:=span{Ψ
n
	​

:n∈Z},

but the theorems then treat these as complete Hilbert spaces and claim interpolation for arbitrary 
𝛼
∈
ℓ
2
(
𝑍
)
α∈ℓ
2
(Z). That is impossible if “span” means finite linear combinations. 

main

Corrected definitions

𝐻
𝐾
(
𝑍
)
:
=
span
⁡
‾
{
𝐾
(
⋅
,
𝑛
)
:
𝑛
∈
𝑍
}
⊂
𝐻
𝐾
,
H
K
	​

(Z):=
span
	​

{K(⋅,n):n∈Z}⊂H
K
	​

,
𝑆
𝑍
:
=
span
⁡
‾
{
Ψ
𝑛
:
𝑛
∈
𝑍
}
⊂
𝐿
0
2
(
𝜔
)
.
S
Z
	​

:=
span
	​

{Ψ
n
	​

:n∈Z}⊂L
0
2
	​

(ω).

Corrected formulation

{
𝐾
(
⋅
,
𝑛
)
}
𝑛
∈
𝑍
{K(⋅,n)}
n∈Z
	​

 is a Riesz basis for 
𝐻
𝐾
(
𝑍
)
H
K
	​

(Z).

{
Ψ
𝑛
}
𝑛
∈
𝑍
{Ψ
n
	​

}
n∈Z
	​

 is a Riesz basis for 
𝑆
𝑍
S
Z
	​

.

The coefficient map

𝐶
:
𝑐
00
→
𝐻
𝐾
(
𝑍
)
,
𝐶
(
𝑐
)
=
∑
𝑛
𝑐
𝑛
𝐾
(
⋅
,
𝑛
)
,
C:c
00
	​

→H
K
	​

(Z),C(c)=
n
∑
	​

c
n
	​

K(⋅,n),

extends to an isomorphism 
𝐶
:
ℓ
2
(
𝑍
)
→
𝐻
𝐾
(
𝑍
)
C:ℓ
2
(Z)→H
K
	​

(Z).

The restriction map 
𝑅
𝑍
R
Z
	​

 is then an isomorphism because the Toeplitz Gram multiplier 
𝜎
σ satisfies 
𝐴
𝑍
≤
𝜎
≤
𝐵
𝑍
A
Z
	​

≤σ≤B
Z
	​

.

This repair also makes Theorem 7.5 correct: 
𝐿
=
𝑅
𝑍
−
1
𝛿
0
L=R
Z
−1
	​

δ
0
	​

 then belongs to the closed shift-generated space, and the cardinal series converges in that Hilbert space.

I4. Section 7 needs a correct complex RKHS formalism

As written, Proposition 7.3 defines kernels on the strip by

𝐾
+
(
𝑧
,
𝑤
)
=
1
2
(
2
−
𝑖
(
𝑧
−
𝑤
)
)
,
𝐾
−
(
𝑧
,
𝑤
)
=
1
2
(
2
+
𝑖
(
𝑧
−
𝑤
)
)
.
K
+
	​

(z,w)=
2(2−i(z−w))
1
	​

,K
−
	​

(z,w)=
2(2+i(z−w))
1
	​

.

For a complex RKHS, this is not the correct dependence on the second variable; one needs 
𝑤
ˉ
w
ˉ
, not 
𝑤
w. The current formulas are not Hermitian kernels on 
𝑆
S. 

circle_dimension_haar_jfa

Actionable repair
At the start of Section 7, declare that from this point onward 
𝐻
𝐾
H
K
	​

 is the complexification of the real Hilbert space, with inner product

⟨
𝑓
,
𝑔
⟩
𝐻
𝐾
:
=
1
2
𝜋
2
∫
𝑅
𝑒
2
∣
𝜉
∣
 
𝑓
^
(
𝜉
)
 
𝑔
^
(
𝜉
)
‾
 
𝑑
𝜉
,
⟨f,g⟩
H
K
	​

	​

:=
2π
2
1
	​

∫
R
	​

e
2∣ξ∣
f
^
	​

(ξ)
g
^
	​

(ξ)
	​

dξ,

linear in the first variable.

Then the correct evaluation representers are

𝐾
(
⋅
,
𝑤
)
^
(
𝜉
)
=
𝜋
𝑒
−
2
∣
𝜉
∣
𝑒
−
𝑖
𝑤
ˉ
𝜉
,
K(⋅,w)
	​

(ξ)=πe
−2∣ξ∣
e
−i
w
ˉ
ξ
,
𝐾
+
(
⋅
,
𝑤
)
^
(
𝜉
)
=
𝜋
𝑒
−
2
𝜉
𝑒
−
𝑖
𝑤
ˉ
𝜉
1
[
0
,
∞
)
(
𝜉
)
,
K
+
	​

(⋅,w)
	​

(ξ)=πe
−2ξ
e
−i
w
ˉ
ξ
1
[0,∞)
	​

(ξ),
𝐾
−
(
⋅
,
𝑤
)
^
(
𝜉
)
=
𝜋
𝑒
2
𝜉
𝑒
−
𝑖
𝑤
ˉ
𝜉
1
(
−
∞
,
0
]
(
𝜉
)
.
K
−
	​

(⋅,w)
	​

(ξ)=πe
2ξ
e
−i
w
ˉ
ξ
1
(−∞,0]
	​

(ξ).

Hence the kernels on 
𝑆
S are

𝐾
(
𝑧
,
𝑤
)
=
2
4
+
(
𝑧
−
𝑤
ˉ
)
2
,
K(z,w)=
4+(z−
w
ˉ
)
2
2
	​

,
𝐾
+
(
𝑧
,
𝑤
)
=
1
2
(
2
−
𝑖
(
𝑧
−
𝑤
ˉ
)
)
,
𝐾
−
(
𝑧
,
𝑤
)
=
1
2
(
2
+
𝑖
(
𝑧
−
𝑤
ˉ
)
)
.
K
+
	​

(z,w)=
2(2−i(z−
w
ˉ
))
1
	​

,K
−
	​

(z,w)=
2(2+i(z−
w
ˉ
))
1
	​

.

With these formulas,

⟨
𝑓
+
,
𝐾
+
(
⋅
,
𝑤
)
⟩
𝐻
𝐾
=
𝑓
+
(
𝑤
)
⟨f
+
	​

,K
+
	​

(⋅,w)⟩
H
K
	​

	​

=f
+
	​

(w)

is correct, and one recovers

𝐾
(
𝑧
,
𝑤
)
=
𝐾
+
(
𝑧
,
𝑤
)
+
𝐾
−
(
𝑧
,
𝑤
)
.
K(z,w)=K
+
	​

(z,w)+K
−
	​

(z,w).

If the authors do not want to work with a complex Hilbert space, then Proposition 7.3 should be weakened: keep the RKHS only on 
𝑅
R, and discuss holomorphic continuation on 
𝑆
S without claiming an RKHS structure on 
𝑆
S.

I5. Theorem 6.4 proof: fix the characteristic-function symmetry

The proof currently says:

𝜑
𝜈
𝑐
(
−
𝑟
)
=
𝜑
𝜈
𝑐
(
𝑟
)
,
φ
ν
c
	​

	​

(−r)=φ
ν
c
	​

	​

(r),

which is false in general. A characteristic function satisfies

𝜑
𝜈
𝑐
(
−
𝑟
)
=
𝜑
𝜈
𝑐
(
𝑟
)
‾
.
φ
ν
c
	​

	​

(−r)=
φ
ν
c
	​

	​

(r)
	​

.

This is a real mathematical error, even though the theorem itself is salvageable. 

main

Correct final step
From 
𝐴
A and 
𝐻
H, Laplace inversion gives 
ℜ
𝜑
𝜈
𝑐
(
𝑟
)
ℜφ
ν
c
	​

	​

(r) and 
ℑ
𝜑
𝜈
𝑐
(
𝑟
)
ℑφ
ν
c
	​

	​

(r) for 
𝑟
≥
0
r≥0. Then define, for 
𝑟
>
0
r>0,

𝜑
𝜈
𝑐
(
−
𝑟
)
:
=
𝜑
𝜈
𝑐
(
𝑟
)
‾
.
φ
ν
c
	​

	​

(−r):=
φ
ν
c
	​

	​

(r)
	​

.

This determines 
𝜑
𝜈
𝑐
φ
ν
c
	​

	​

 on all of 
𝑅
R. Now apply Lévy’s inversion theorem to recover 
𝜈
𝑐
ν
c
	​

, then reinsert the mean 
𝛾
ˉ
γ
ˉ
	​

 to recover 
𝜈
ν. This is the standard route via Laplace uniqueness plus characteristic-function inversion.

I6. Tighten moment assumptions in Theorems 5.11–5.13

Theorems 5.11 and 5.12 currently say “under the hypotheses of Theorem 5.9,” but 
𝐶
8
C
8
	​

 and 
Δ
8
Δ
8
	​

 come from the eighth-order expansion and therefore need the moment hypothesis of the eighth-order theorem, not the weaker general asymptotic theorem. Likewise, Theorem 5.13 only needs the data entering 
Δ
6
Δ
6
	​

, so the present umbrella reference is too vague. 

main

 

circle_dimension_haar_jfa

Recommended restatement

Theorem 5.11: assume 
𝜈
ν has mean 
𝛾
ˉ
γ
ˉ
	​

, variance 
𝜎
2
>
0
σ
2
>0, and finite centered seventh absolute moment.

Theorem 5.12: same assumptions.

Theorem 5.13: assume only mean 
𝛾
ˉ
γ
ˉ
	​

, variance 
𝜎
2
>
0
σ
2
>0, and finite centered fourth moment.

Why the last reduction works:

𝐶
6
=
𝜎
6
+
6
𝜇
3
2
−
8
𝜎
2
𝜇
4
64
,
C
6
	​

=
64
σ
6
+6μ
3
2
	​

−8σ
2
μ
4
	​

	​

,

so 
Δ
6
Δ
6
	​

 depends only on 
𝜇
3
,
𝜇
4
μ
3
	​

,μ
4
	​

. No seventh moment is needed for the 
𝑊
2
W
2
	​

-stability theorem.

I7. Repair the Appendix A inconsistency and Section 5 cross-references

Appendix A states

∫
𝑅
𝑢
2
(
𝑦
)
3
 
𝜔
(
𝑑
𝑦
)
=
−
3
32
,
∫
R
	​

u
2
	​

(y)
3
ω(dy)=−
32
3
	​

,

but one of the displayed computations gives 
−
3
/
64
−3/64. The theorem-level coefficient appears to use the correct value, but the appendix is internally inconsistent. 

circle_dimension_haar_jfa

Correct calculation
Since 
𝑢
2
(
tan
⁡
𝜃
)
=
−
1
2
(
𝑐
1
+
𝑐
2
)
u
2
	​

(tanθ)=−
2
1
	​

(c
1
	​

+c
2
	​

),

∫
𝑅
𝑢
2
(
𝑦
)
3
 
𝜔
(
𝑑
𝑦
)
=
−
1
8
𝜋
∫
−
𝜋
/
2
𝜋
/
2
(
𝑐
1
+
𝑐
2
)
3
 
𝑑
𝜃
.
∫
R
	​

u
2
	​

(y)
3
ω(dy)=−
8π
1
	​

∫
−π/2
π/2
	​

(c
1
	​

+c
2
	​

)
3
dθ.

A direct trigonometric expansion gives

1
𝜋
∫
−
𝜋
/
2
𝜋
/
2
(
𝑐
1
+
𝑐
2
)
3
 
𝑑
𝜃
=
3
4
,
π
1
	​

∫
−π/2
π/2
	​

(c
1
	​

+c
2
	​

)
3
dθ=
4
3
	​

,

hence

∫
𝑅
𝑢
2
(
𝑦
)
3
 
𝜔
(
𝑑
𝑦
)
=
−
1
8
⋅
3
4
=
−
3
32
.
∫
R
	​

u
2
	​

(y)
3
ω(dy)=−
8
1
	​

⋅
4
3
	​

=−
32
3
	​

.

The internal labels also need a proofread:

“This proves (5.19)” should match the theorem actually being proved.

“Theorem 5.8” in Section 5 is a lemma in the current numbering.

Theorem 5.11/5.12 proofs refer to the wrong equation numbers in several places. 

circle_dimension_haar_jfa

I8. Reframe the novelty of Section 7

The abstract and introduction currently advertise the sampling/cardinal-reconstruction results as if they were on the same novelty level as the entropy-defect results, yet Remark 7.6 explicitly places Theorems 7.4 and 7.5 in the “standard functional-analytic framework of principal shift-invariant spaces and RKHS sampling.” 

circle_dimension_haar_jfa

Concrete wording fix
In the abstract/introduction, replace broad claims such as:

“we prove a lattice-sampling theorem and a cardinal reconstruction formula”

by something like:

“we specialize classical shift-invariant-space sampling theory to the explicit kernel 
𝐾
(
𝑎
,
𝑏
)
=
2
/
(
4
+
(
𝑎
−
𝑏
)
2
)
K(a,b)=2/(4+(a−b)
2
), obtaining closed-form formulas for the lattice symbol, the cardinal kernel, and the exact interpolation norm.”

That would accurately isolate what is actually new: the explicit formulas, not the existence of the sampling theory itself.

My editorial bottom line is that the paper has a worthwhile core, but it needs a serious mathematical and bibliographic revision before it can be judged on its merits. The strongest path to acceptance is to repair Sections 6–7 rigorously, complete the references, and foreground the Section 5 entropy-defect results as the primary contribution. 

main
