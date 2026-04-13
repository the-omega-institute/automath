<!-- oracle metadata: {"timestamp": "2026-04-07T03:27:41.685575", "model": "o3-mini-high", "response_length": 15077} -->

I reviewed the manuscript Finite parts of dynamical ζ-functions for shifts of finite type. 

main

1. Overall assessment

Major revision

The paper contains an interesting core idea, namely the Adams-Möbius passage from twisted periodic determinant data to primitive Peter-Weyl channels. However, in its current form it is not correct in full generality. The finite-group part uses the wrong inner product and Fourier conventions for complex characters, and Appendix B repeats the same orientation error for Dirichlet characters. These are blocker-level problems because several central statements are only correct as written for groups whose irreducible characters are all real-valued. The literature positioning is also incomplete, especially around prime-orbit and Mertens-type results.

I do not recommend acceptance in the present form. I do think the manuscript could become publishable after a substantial and careful revision.

2. Novelty rating for each theorem

I do not currently see a theorem that clearly merits HIGH novelty as presently framed.

Main text
Theorem	Rating	One-line justification
1.1	LOW	This is an umbrella statement for a largely algebraic Möbius-Euler product identity plus a standard Mertens-type asymptotic.
1.2	MEDIUM	The cyclic-lift reconstruction package is a neat synthesis, although the one-layer reconstruction itself is elementary discrete Fourier inversion.
1.3	MEDIUM	The Adams-Möbius framing is the most original-looking part of the paper, but several components are formal once conventions are corrected.
3.1	LOW	The formula follows directly from the Euler product, Möbius inversion, and the simple Perron pole expansion.
3.4	LOW	The cyclic-lift determinant identity is an immediate tensor-spectrum computation plus 
∏
𝑘
=
0
𝑞
−
1
(
1
−
𝑥
𝜔
𝑞
𝑘
)
=
1
−
𝑥
𝑞
∏
k=0
q−1
	​

(1−xω
q
k
	​

)=1−x
q
.
3.8	MEDIUM	Recovering the reduced spectrum from 
{
Ψ
𝑞
}
{Ψ
q
	​

} is a clean observation, even if based on standard power-sum inversion and Newton identities.
3.9	LOW	This is just DFT interpolation of a degree 
≤
𝑑
−
1
≤d−1 polynomial from 
𝑞
≥
𝑑
q≥d samples.
4.4	LOW	After fixing the correct Fourier coefficients, this is a straightforward character expansion of periodic trace data.
4.11	LOW	This is a direct conjugacy-class Fourier inversion once 4.4 and the class indicator expansion are in place.
4.17	MEDIUM	The explicit class constants are worthwhile, but the Chebotarev density component is classical under the spectral-gap hypothesis.
4.20	MEDIUM	Conceptually nice, but essentially an orthogonality identity once the class constant formula is established.
5.2	LOW	Quotient functoriality is natural and largely formal from pullback of class functions.
5.4	LOW	The abelian/non-abelian splitting is conceptually useful, but mathematically it is immediate from character orthogonality.
5.6	MEDIUM	The exact identification of cyclic detection with the one-dimensional sector is a nice structural synthesis.
Appendices
Theorem	Rating	One-line justification
A.1	LOW	Standard perturbation-theoretic differentiation of a reduced determinant.
A.2	LOW	Routine holomorphic differentiation under the summation sign, once 3.1 is available.
A.3	LOW	A straightforward tail bound using 
𝑝
𝑛
(
𝐴
)
≤
Tr
⁡
(
𝐴
𝑛
)
/
𝑛
p
n
	​

(A)≤Tr(A
n
)/n.
B.1	LOW	Parseval plus standard aliasing.
B.5	LOW	Finite Fourier inversion on 
(
𝑍
/
𝑝
𝑍
)
×
(Z/pZ)
×
, though currently written with the wrong character orientation.
B.7	MEDIUM	The Cesàro extraction of boundary multiplicities is a mildly interesting spectral consequence.
B.10	LOW	Once 3.9 is known, this is a direct reformulation.
B.11	LOW	Mostly a polylogarithm repackaging of the cyclic-lift discrepancy.
C.2	LOW	A simple consequence of the square-root bound and elementary determinant estimates.
3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	§2.4, Prop. 4.1, Thms. 4.4, 4.20, 5.4	BLOCKER	The class-function Fourier coefficients and orthogonality are written with a bilinear pairing (\frac1{	G
B2	App. B.2, Prop. B.3, Thm. B.5	BLOCKER	The Gauss-sum identity uses 
𝜒
(
𝑛
)
χ(n) where the correct factor is 
𝜒
(
𝑛
)
‾
χ(n)
	​

. The prime-modulus character inversion is therefore incorrect for non-real characters.	Recompute with 
𝜏
𝑝
(
𝜒
,
𝑛
)
=
𝜒
(
𝑛
)
‾
 
𝜏
(
𝜒
)
τ
p
	​

(χ,n)=
χ(n)
	​

τ(χ), or redefine 
𝐴
𝑝
(
𝜒
)
A
p
	​

(χ) using 
𝜒
‾
χ
	​

. Update the Fourier inversion formula.
M1	Prop. 4.3	MEDIUM	The proof divides by an eigenvalue 
𝛼
α, so it excludes 
𝛼
=
0
α=0.	Use the characteristic-polynomial factorization 
det
⁡
(
𝑡
𝐼
−
𝐴
~
)
=
∏
𝜌
det
⁡
(
𝑡
𝐼
−
𝐴
𝜌
)
dim
⁡
𝜌
det(tI−
A
)=∏
ρ
	​

det(tI−A
ρ
	​

)
dimρ
, which handles 
𝛼
=
0
α=0 automatically.
M2	Intro., §1.1, §4.3, §5	MEDIUM	The manuscript does not adequately distinguish its contribution from classical prime-orbit, Mertens, and functorial orbit-counting literature.	Add specific comparison paragraphs and cite the missing foundational works listed below.
M3	§3, App. B	MEDIUM	Complex logarithm conventions are not fixed. Expressions such as 
log
⁡
(
1
−
(
𝜇
𝑗
/
𝜆
)
𝑞
)
log(1−(μ
j
	​

/λ)
q
), 
−
log
⁡
𝐹
𝐴
(
𝑒
𝑖
𝜃
)
−logF
A
	​

(e
iθ
), and Perron-point evaluations are formally ambiguous.	State once that all logarithms use the principal branch, and explain why all arguments stay in its domain because (
M4	§5.4	MEDIUM	The only worked example is 
𝑆
3
S
3
	​

, whose irreducible characters are all real. It therefore fails to test the general complex-character formulas, which is exactly where the current error lies.	Add a short 
𝐶
3
C
3
	​

 or 
𝐶
5
C
5
	​

 example to validate the corrected conjugation conventions.
L1	Throughout	LOW	The paper introduces many branding terms such as “fingerprint”, “shadow”, and “defect” for material that is often just linear algebra or Fourier inversion.	Reduce this terminology and foreground the exact mathematical statements.
L2	Appendices A-C	LOW	The appendices expand the scope substantially without comparable motivation and currently contain additional convention errors.	Either prune to the results that genuinely support the main paper, or explain why each appendix is needed.
4. Missing references

The following omissions are important.

Artin-Mazur, On Periodic Points (1965). This is the foundational source for the general dynamical zeta function viewpoint. 
JSTOR

Parry, An analogue of the prime number theorem for closed orbits of shifts of finite type and their suspensions (1983). This is the natural classical comparator for the SFT prime-orbit side of Section 3. 
Springer

Sharp, An analogue of Mertens' theorem for closed orbits of Axiom A flows (1991). This is the most relevant historical comparator for the paper’s Mertens-constant discussion. 
Springer

Pakapongpun-Ward, Functorial orbit counting (2009). This is directly relevant to the quotient/functorial viewpoint in Section 5. 
Cheriton School of Computer Science

Pollicott, Agmon’s complex Tauberian theorem and closed orbits for hyperbolic and geodesic flows (1992). This belongs in any discussion of Tauberian refinements and closed-orbit asymptotics. 
JSTOR

Parry-Pollicott, An analogue of the prime number theorem for closed orbits of Axiom A flows (1983). If the introduction continues to frame the paper against the broader hyperbolic-flow literature, the original Annals paper should be cited explicitly, not only the 1990 monograph. 
Annals of Mathematics

5. Specific improvements needed to reach acceptance

First, the finite-group Fourier formalism must be corrected globally. At present the main representation-theoretic statements are not valid for general finite groups.

Second, Appendix B must be rewritten with the correct Gauss-sum normalization. As written, the prime-modulus character inversion is wrong for complex Dirichlet characters.

Third, the introduction should stop presenting the paper as if it establishes a new prime-orbit or Mertens theorem in the classical sense. The genuine added value is the explicit finite-part identity and the Adams-Möbius primitive inversion machinery. That distinction needs to be made sharply and supported by the missing citations above. 
JSTOR
+4
Springer
+4
Springer
+4

Fourth, the paper needs one genuinely non-real character example. The current 
𝑆
3
S
3
	​

 example cannot detect the convention errors because every 
𝑆
3
S
3
	​

 irreducible character is real-valued.

Fifth, several peripheral results should be demoted or trimmed. In particular, Theorems 3.9, 5.2, A.3, B.1, and B.10 read more naturally as propositions or corollaries.

6. Concrete fixes
B1. Correct the class-function Fourier formalism

Replace equation (9) and every later use of character orthogonality by the Hermitian convention

⟨
𝑓
,
ℎ
⟩
=
1
∣
𝐺
∣
∑
𝑔
∈
𝐺
𝑓
(
𝑔
)
ℎ
(
𝑔
)
‾
=
1
∣
𝐺
∣
∑
𝑔
∈
𝐺
𝑓
(
𝑔
)
ℎ
(
𝑔
−
1
)
.
⟨f,h⟩=
∣G∣
1
	​

g∈G
∑
	​

f(g)
h(g)
	​

=
∣G∣
1
	​

g∈G
∑
	​

f(g)h(g
−1
).

Then irreducible characters are orthonormal, and the correct Fourier coefficients are

𝜙
^
(
𝜌
)
=
⟨
𝜙
,
𝜒
𝜌
⟩
=
1
∣
𝐺
∣
∑
𝑔
∈
𝐺
𝜙
(
𝑔
)
𝜒
𝜌
(
𝑔
)
‾
=
1
∣
𝐺
∣
∑
𝑔
∈
𝐺
𝜙
(
𝑔
)
𝜒
𝜌
(
𝑔
−
1
)
.
ϕ
	​

(ρ)=⟨ϕ,χ
ρ
	​

⟩=
∣G∣
1
	​

g∈G
∑
	​

ϕ(g)
χ
ρ
	​

(g)
	​

=
∣G∣
1
	​

g∈G
∑
	​

ϕ(g)χ
ρ
	​

(g
−1
).

Accordingly,

𝜙
=
∑
𝜌
∈
Irr
⁡
(
𝐺
)
𝜙
^
(
𝜌
)
𝜒
𝜌
.
ϕ=
ρ∈Irr(G)
∑
	​

ϕ
	​

(ρ)χ
ρ
	​

.

For the class indicator, the correct formula is

1
𝐶
(
𝑔
)
=
∣
𝐶
∣
∣
𝐺
∣
∑
𝜌
∈
Irr
⁡
(
𝐺
)
𝜒
𝜌
(
𝐶
)
‾
 
𝜒
𝜌
(
𝑔
)
=
∣
𝐶
∣
∣
𝐺
∣
∑
𝜌
∈
Irr
⁡
(
𝐺
)
𝜒
𝜌
(
𝐶
−
1
)
 
𝜒
𝜌
(
𝑔
)
.
1
C
	​

(g)=
∣G∣
∣C∣
	​

ρ∈Irr(G)
∑
	​

χ
ρ
	​

(C)
	​

χ
ρ
	​

(g)=
∣G∣
∣C∣
	​

ρ∈Irr(G)
∑
	​

χ
ρ
	​

(C
−1
)χ
ρ
	​

(g).

This is the only version that is true in general. The first displayed equality in Proposition 4.1, with 
𝜒
𝜌
(
𝐶
)
χ
ρ
	​

(C) instead of 
𝜒
𝜌
(
𝐶
−
1
)
χ
ρ
	​

(C
−1
), is false whenever non-real characters occur.

A minimal counterexample is 
𝐺
=
𝐶
3
=
⟨
𝑎
⟩
G=C
3
	​

=⟨a⟩. Then

1
3
∑
𝜓
∈
𝐶
3
^
𝜓
(
𝑎
)
𝜓
(
𝑔
)
=
1
{
𝑎
−
1
}
(
𝑔
)
,
3
1
	​

ψ∈
C
3
	​

	​

∑
	​

ψ(a)ψ(g)=1
{a
−1
}
	​

(g),

not 
1
{
𝑎
}
(
𝑔
)
1
{a}
	​

(g). This shows exactly why the conjugate or inverse is needed.

With this correction, Theorem 4.4 becomes

𝐿
𝜙
(
𝑧
)
=
∑
𝜌
∈
Irr
⁡
(
𝐺
)
𝜙
^
(
𝜌
)
 
log
⁡
det
⁡
(
𝐼
−
𝑧
𝐴
𝜌
)
−
1
,
L
ϕ
	​

(z)=
ρ∈Irr(G)
∑
	​

ϕ
	​

(ρ)logdet(I−zA
ρ
	​

)
−1
,

with the corrected 
𝜙
^
(
𝜌
)
ϕ
	​

(ρ). The proof is unchanged after the corrected expansion of 
𝜙
ϕ.

Likewise, Theorem 4.20 should use the Hermitian class-function inner product

⟨
𝐹
,
𝐻
⟩
𝐺
=
∑
𝐶
⊂
𝐺
∣
𝐶
∣
∣
𝐺
∣
𝐹
(
𝐶
)
𝐻
(
𝐶
)
‾
.
⟨F,H⟩
G
	​

=
C⊂G
∑
	​

∣G∣
∣C∣
	​

F(C)
H(C)
	​

.

Then

Π
𝜎
(
𝜆
−
1
)
=
∑
𝐶
⊂
𝐺
Δ
𝐶
(
𝐴
)
𝜒
𝜎
(
𝐶
)
,
Π
σ
	​

(λ
−1
)=
C⊂G
∑
	​

Δ
C
	​

(A)χ
σ
	​

(C),

because

∑
𝐶
⊂
𝐺
∣
𝐶
∣
∣
𝐺
∣
𝜒
𝜌
(
𝐶
−
1
)
𝜒
𝜎
(
𝐶
)
=
𝛿
𝜌
,
𝜎
,
C⊂G
∑
	​

∣G∣
∣C∣
	​

χ
ρ
	​

(C
−1
)χ
σ
	​

(C)=δ
ρ,σ
	​

,

and the Parseval identity becomes

∑
𝐶
⊂
𝐺
∣
𝐺
∣
∣
𝐶
∣
 
∣
Δ
𝐶
(
𝐴
)
∣
2
=
∑
𝜌
≠
1
∣
Π
𝜌
(
𝜆
−
1
)
∣
2
.
C⊂G
∑
	​

∣C∣
∣G∣
	​

∣Δ
C
	​

(A)∣
2
=
ρ

=1
∑
	​

∣Π
ρ
	​

(λ
−1
)∣
2
.

In Theorem 5.4, the proof should explicitly use this Hermitian inner product, not a bilinear one.

B2. Repair Appendix B.2

For prime 
𝑝
p and 
𝑝
∤
𝑛
p∤n,

𝜏
𝑝
(
𝜒
,
𝑛
)
:
=
∑
𝑎
∈
(
𝑍
/
𝑝
𝑍
)
×
𝜒
(
𝑎
)
𝜔
𝑝
𝑎
𝑛
.
τ
p
	​

(χ,n):=
a∈(Z/pZ)
×
∑
	​

χ(a)ω
p
an
	​

.

Set 
𝑏
=
𝑎
𝑛
b=an. Since multiplication by 
𝑛
n permutes 
(
𝑍
/
𝑝
𝑍
)
×
(Z/pZ)
×
,

𝜏
𝑝
(
𝜒
,
𝑛
)
=
∑
𝑏
𝜒
(
𝑏
𝑛
−
1
)
𝜔
𝑝
𝑏
=
𝜒
(
𝑛
−
1
)
𝜏
(
𝜒
)
=
𝜒
(
𝑛
)
‾
 
𝜏
(
𝜒
)
.
τ
p
	​

(χ,n)=
b
∑
	​

χ(bn
−1
)ω
p
b
	​

=χ(n
−1
)τ(χ)=
χ(n)
	​

τ(χ).

Therefore Proposition B.3 must read

𝐿
𝐴
(
𝜒
;
𝑝
)
=
𝜏
(
𝜒
)
∑
𝑛
≥
1


𝑝
∤
𝑛
𝑢
𝑛
(
𝐴
)
𝜒
(
𝑛
)
‾
𝑛
.
L
A
	​

(χ;p)=τ(χ)
n≥1
p∤n
	​

∑
	​

n
u
n
	​

(A)
χ(n)
	​

	​

.

Grouping terms by residue class modulo 
𝑝
p, one gets

𝐴
𝑝
(
𝜒
)
:
=
𝐿
𝐴
(
𝜒
;
𝑝
)
𝜏
(
𝜒
)
=
∑
𝑟
∈
(
𝑍
/
𝑝
𝑍
)
×
𝑉
𝑝
,
𝑟
(
𝐴
)
 
𝜒
(
𝑟
)
‾
.
A
p
	​

(χ):=
τ(χ)
L
A
	​

(χ;p)
	​

=
r∈(Z/pZ)
×
∑
	​

V
p,r
	​

(A)
χ(r)
	​

.

The inversion is then

𝑉
𝑝
,
𝑟
0
(
𝐴
)
=
1
𝑝
−
1
∑
𝜒
𝐴
𝑝
(
𝜒
)
𝜒
(
𝑟
0
)
,
V
p,r
0
	​

	​

(A)=
p−1
1
	​

χ
∑
	​

A
p
	​

(χ)χ(r
0
	​

),

because

1
𝑝
−
1
∑
𝜒
𝜒
(
𝑟
)
‾
𝜒
(
𝑟
0
)
=
𝛿
𝑟
,
𝑟
0
.
p−1
1
	​

χ
∑
	​

χ(r)
	​

χ(r
0
	​

)=δ
r,r
0
	​

	​

.

This is the cleanest way to repair Theorem B.5 without changing its overall structure.

M1. Fix Proposition 4.3 so that 
𝛼
=
0
α=0 is covered

Instead of writing 
det
⁡
(
𝐼
−
𝛼
−
1
𝐴
𝜎
)
=
0
det(I−α
−1
A
σ
	​

)=0, use the characteristic polynomial factorization

det
⁡
(
𝑡
𝐼
−
𝐴
~
)
=
∏
𝜌
∈
Irr
⁡
(
𝐺
)
det
⁡
(
𝑡
𝐼
−
𝐴
𝜌
)
dim
⁡
𝜌
.
det(tI−
A
)=
ρ∈Irr(G)
∏
	​

det(tI−A
ρ
	​

)
dimρ
.

Now any eigenvalue 
𝛼
α of 
𝐴
𝜎
A
σ
	​

, including 
𝛼
=
0
α=0, is a root of 
det
⁡
(
𝑡
𝐼
−
𝐴
~
)
det(tI−
A
). Hence

spec
⁡
(
𝐴
𝜎
)
⊂
spec
⁡
(
𝐴
~
)
,
𝜌
(
𝐴
𝜎
)
≤
𝜌
(
𝐴
~
)
.
spec(A
σ
	​

)⊂spec(
A
),ρ(A
σ
	​

)≤ρ(
A
).

The second part of the proof, namely 
𝜌
(
𝐴
~
)
=
𝜆
ρ(
A
)=λ, can remain as written.

M2. Reframe the novelty against the correct literature

The introduction should explicitly say something like this:

The prime-orbit asymptotic for shifts of finite type is classical. See Parry (1983). The existence of Mertens-type closed-orbit asymptotics in hyperbolic dynamics is also classical. See Sharp (1991). The present paper does not claim a new prime-orbit theorem. Its main contribution is instead the explicit finite-part identity at the Perron pole, together with the Adams-Möbius reconstruction of primitive Peter-Weyl channels from twisted determinant data.

That paragraph would materially improve the fairness of the literature positioning. The missing references in Section 4.3 and Section 5 should also include Pakapongpun-Ward for the functorial orbit-counting perspective. 
JSTOR
+4
Springer
+4
Springer
+4

M3. Fix the logarithm conventions

At the start of Section 3, add:

All logarithms are taken in the principal branch 
\Log
\Log on 
𝐶
∖
(
−
∞
,
0
]
C∖(−∞,0]. Since 
∣
𝜇
𝑗
∣
<
𝜆
∣μ
j
	​

∣<λ, each factor 
1
−
(
𝜇
𝑗
/
𝜆
)
𝑞
1−(μ
j
	​

/λ)
q
 has positive real part, so 
\Log
(
1
−
(
𝜇
𝑗
/
𝜆
)
𝑞
)
\Log(1−(μ
j
	​

/λ)
q
) is unambiguous. Likewise 
𝐹
𝐴
(
𝑒
𝑖
𝜃
)
=
∏
𝑗
=
2
𝑑
(
1
−
(
𝜇
𝑗
/
𝜆
)
𝑒
𝑖
𝜃
)
≠
0
F
A
	​

(e
iθ
)=∏
j=2
d
	​

(1−(μ
j
	​

/λ)e
iθ
)

=0 for all 
𝜃
θ, and each factor remains in the principal domain.

Then rewrite

Ψ
𝑞
(
𝐴
)
=
−
∑
𝑗
=
2
𝑑
\Log
 ⁣
(
1
−
(
𝜇
𝑗
/
𝜆
)
𝑞
)
,
𝑔
𝐴
(
𝜃
)
=
−
\Log
𝐹
𝐴
(
𝑒
𝑖
𝜃
)
.
Ψ
q
	​

(A)=−
j=2
∑
d
	​

\Log(1−(μ
j
	​

/λ)
q
),g
A
	​

(θ)=−\LogF
A
	​

(e
iθ
).

This removes an unnecessary analytic ambiguity.

M4. Add a genuinely complex-character test case

A short 
𝐶
3
C
3
	​

 example would suffice. Let 
𝐺
=
𝐶
3
=
{
1
,
𝑎
,
𝑎
2
}
G=C
3
	​

={1,a,a
2
} and 
𝜒
(
𝑎
)
=
𝜔
χ(a)=ω. Then

1
{
𝑎
}
(
𝑔
)
=
1
3
∑
𝜓
∈
𝐺
^
𝜓
(
𝑎
)
‾
 
𝜓
(
𝑔
)
,
1
{a}
	​

(g)=
3
1
	​

ψ∈
G
∑
	​

ψ(a)
	​

ψ(g),

whereas

1
3
∑
𝜓
∈
𝐺
^
𝜓
(
𝑎
)
𝜓
(
𝑔
)
=
1
{
𝑎
−
1
}
(
𝑔
)
.
3
1
	​

ψ∈
G
∑
	​

ψ(a)ψ(g)=1
{a
−1
}
	​

(g).

This immediately validates the corrected convention and would have exposed the present error. The 
𝑆
3
S
3
	​

 example can then remain as the Adams-obstruction example, which is where it is genuinely useful.

In short, the paper has a potentially publishable core, but the current draft needs a mathematically serious revision before it can be assessed positively.