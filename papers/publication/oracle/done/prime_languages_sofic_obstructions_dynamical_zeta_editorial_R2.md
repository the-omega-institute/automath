<!-- oracle metadata: {"timestamp": "2026-04-05T08:43:42.520890", "model": "o3-mini-high", "response_length": 17515} -->

1. Overall assessment

Reject.

The submission is not journal-ready in its present form. I do not see a fatal correctness defect in the elementary matrix argument behind Theorem 2.2 or in the transfer-matrix proof of Theorem 3.1. The decisive problems are different: the paper has no usable bibliography, several central claims are only proof sketches rather than publication-level arguments, the title and scope overstate what is actually established, and the theorem-level contribution is too slight for a research article. As written, the manuscript reads as three loosely connected short notes: a DFA density lemma, a Zeckendorf counting lemma, and two analytic observations. That is not enough for acceptance in a standard journal venue. 

main

2. Novelty rating for each theorem
Theorem	Rating	One-line justification
Theorem 2.2	LOW	This is a direct finite-state Markov chain / stochastic matrix decomposition for 
𝑎
𝑚
(
𝐴
)
/
2
𝑚
a
m
	​

(A)/2
m
.
Theorem 3.1	MEDIUM	The Zeckendorf-specific formulation is neat, but the proof is a standard Perron-Frobenius transfer-matrix argument once regularity is known.
Theorem 3.5	LOW	Once Proposition 3.4 and (
Theorem 4.1	LOW	This is a classical Pólya-Carlson / rationality argument dressed for the Euler product at hand.

A further observation. Proposition 4.2 is also LOW novelty and is too slight to support the title’s “dynamical 
𝜁
ζ-functions” framing. 

main

3. Issue table

The following issues arise directly from the title, abstract, §§1 to 4, and the theorem statements/proofs. 

main

ID	Section	Severity	Description	Suggested fix
B1	§1.2, throughout	BLOCKER	The bibliography is unusable. Placeholder citations remain unresolved, so novelty, dependence on standard results, and priority claims cannot be assessed.	Add a full bibliography and replace every placeholder with specific sources and theorem-level citations.
B2	Paper-wide	BLOCKER	The contribution is below research-journal threshold as written. Theorems 2.2, 3.1, 3.5, and 4.1 are short consequences of standard finite-state, transfer-matrix, and Pólya-Carlson machinery.	Either recast as a short note, or add a substantially stronger theorem that genuinely generalizes beyond the Fibonacci/prime special case.
M1	§2.2	MEDIUM	The proof of Theorem 2.2 is too compressed. The constants 
𝑐
𝑟
c
r
	​

 are not constructed explicitly, and their non-negativity is asserted without proof.	Replace the Markov-chain appeal by an explicit spectral decomposition of 
𝑃
=
𝐵
/
2
P=B/2 on recurrent classes.
M2	§3.1 to §3.5	MEDIUM	Theorem 3.5 uses an unstated lemma about residue-class asymptotics of exponential-polynomial sequences.	Insert a precise lemma and proof for the asymptotic form of 
𝑎
𝑞
𝑘
+
𝑟
a
qk+r
	​

 on residue classes.
M3	§4.1	MEDIUM	Theorem 4.1 suppresses two substantive steps: the exact Pólya-Carlson input, and the eventual periodicity of bounded integer linear-recurrence sequences.	State these ingredients explicitly and either prove them or cite them precisely.
M4	Title, §1.2, §4.2	MEDIUM	“Dynamical 
𝜁
ζ-functions” is misleading. Proposition 4.2 is merely a finite-determinant periodicity observation and is not presented in genuine Artin-Mazur/Ruelle form.	Either change the title, or rewrite §4.2 in an actual dynamical-
𝜁
ζ framework.
M5	Abstract, §1, Cor. 2.4	MEDIUM	Several claims are broader than the proved statements. The paper rules out fixed-DFA approximation and exact regular/sofic realizations, not “finite-state models” in any broad sense.	Narrow the abstract/introduction and isolate the exact contradiction proved for fixed DFAs and sofic shifts.
M6	§3.1	MEDIUM	Theorem 3.1 is underformulated. The exponent 
𝛼
α is not identified explicitly in the statement, and sharpness examples are absent.	State 
𝛼
=
log
⁡
𝜆
/
log
⁡
𝜑
α=logλ/logφ explicitly and add examples showing endpoint cases 
𝛼
=
0
α=0 and 
𝛼
=
1
α=1.
L1	§2 to §4	LOW	Standard inputs are used without citation: finite Markov chain periodic decomposition, Perron-Frobenius asymptotics, sofic block counts, Pólya-Carlson, and the prime number theorem.	Add precise theorem references.
L2	Title/organization	LOW	The paper reads as three separate notes rather than a unified argument.	Separate the sections more honestly, or unify them with one principal theorem.
4. Missing references

At minimum, the paper should cite the following.

For automata and automatic/recognizable sets:

Cobham, foundational papers on base dependence and recognizable sets.

Allouche and Shallit, Automatic Sequences.

For primes and digital restrictions:

Mauduit and Rivat on primes in digit-restricted settings.

Drmota, Mauduit, and Rivat on primes in automatic/digital frameworks.

For Zeckendorf and Parry numeration:

Frougny on linear/Parry numeration systems.

A standard reference on Zeckendorf expansions and admissible regular syntax.

For symbolic dynamics and sofic shifts:

Lind and Marcus, An Introduction to Symbolic Dynamics and Coding.

For rational generating functions and recurrences:

Flajolet and Sedgewick, Analytic Combinatorics.

Or a standard transfer-matrix / linear-recurrence reference.

For analytic number theory:

A standard prime number theorem reference.

Pólya and Carlson for the Pólya-Carlson theorem.

Estermann or another classical reference on Euler products and natural boundaries.

If the title keeps “dynamical 
𝜁
ζ-functions”, then also:

Artin-Mazur and/or Ruelle.

A standard modern reference such as Lind and Ward on dynamical zeta functions.

5. Specific improvements needed to reach acceptance

The paper needs five substantive changes.

First, the references and scholarly positioning must be rebuilt completely.

Second, the authors must decide what kind of paper this is. In its current form it is closer to a short note than to a journal research article.

Third, Theorem 2.2, Theorem 3.5, and Theorem 4.1 must be written at publication-level rigor rather than as compressed sketches.

Fourth, the title and abstract must be narrowed so that they match the precise scope of the proofs.

Fifth, the Zeckendorf section should either be generalized substantially or presented much more modestly. As it stands, it is a clean but routine transfer-matrix application. 

main

6. Concrete fixes
B1. Repair the bibliography and the scholarly apparatus

This is non-optional.

A workable repair is:

add a full references section;

replace every placeholder in §1.2, §2, §3, and §4;

cite theorem numbers, not only books or chapters.

A minimal citation plan would be:

after Theorem 2.2: a finite Markov chain periodic decomposition reference;

after the prime-count asymptotics in Corollaries 2.3 and 2.4: a PNT reference;

after Theorem 3.1 and Proposition 3.4: transfer-matrix / sofic-count references;

after Theorem 4.1: Pólya-Carlson and Estermann;

after Proposition 4.2, if retained: a genuine dynamical-
𝜁
ζ reference.

The last paragraph of §1.2 should also be rewritten. The present language still overstates novelty. A more accurate version is:

“The finite-state, transfer-matrix, and analytic tools used here are classical. The contribution of the present note is to place three elementary obstructions side by side for prime-supported binary and Zeckendorf languages.”

That would align the exposition with the actual mathematical content.

B2. Raise the theoremic substance, or recast as a short note

This is the central editorial problem.

A mathematically meaningful path to journal acceptance would be to replace the Fibonacci-specific result by a genuine Parry numeration theorem. For example:

Proposed strengthened theorem. Let 
𝛽
>
1
β>1 be a Parry number with greedy admissible language 
𝑍
𝛽
Z
β
	​

, and let 
𝑈
𝑛
=
𝐶
𝛽
𝑛
+
𝑂
(
𝜏
𝑛
)
U
n
	​

=Cβ
n
+O(τ
n
) be the associated place values with 
𝜏
<
𝛽
τ<β. If 
𝐿
⊆
𝑍
𝛽
L⊆Z
β
	​

 is regular, then

𝑁
𝐿
(
𝑇
)
=
𝑇
𝛼
+
𝑜
(
1
)
,
𝛼
=
log
⁡
𝜌
log
⁡
𝛽
,
N
L
	​

(T)=T
α+o(1)
,α=
logβ
logρ
	​

,

where 
𝜌
ρ is the maximal spectral radius of an accessible/coaccessible strongly connected component of the recognizing automaton. Moreover, if an arithmetic family of length slices 
𝐴
𝑛
A
n
	​

 satisfies 
∣
𝐴
𝑛
∣
≍
𝛽
𝑛
/
𝑛
∣A
n
	​

∣≍β
n
/n, then 
𝐴
𝑛
A
n
	​

 cannot be eventually realized by a sofic shift.

This is not difficult given the current proof strategy. The proof is the same transfer-matrix argument already used in §3, with 
𝜑
φ replaced by 
𝛽
β, plus the standard exponential-polynomial form for sofic counts.

If the authors do not want to generalize beyond Fibonacci, then the correct editorial solution is to shorten the paper and submit it as a brief note. In that case, Section 4.2 should probably be removed, and the title should no longer promise “dynamical 
𝜁
ζ-functions”.

M1. Make Theorem 2.2 explicit and rigorous

The current proof appeals to “finite-state Markov-chain theory” in a way that is too compressed.

A publication-level replacement is:

Let

𝑃
:
=
𝐵
2
.
P:=
2
B
	​

.

After permuting states, write 
𝑃
P in block upper-triangular form with transient block 
𝑇
T and irreducible recurrent-class blocks 
𝑃
1
,
…
,
𝑃
𝑠
P
1
	​

,…,P
s
	​

. If 
𝑃
𝑖
P
i
	​

 has period 
𝑑
𝑖
d
i
	​

, then standard periodic Perron-Frobenius theory gives

𝑃
𝑖
𝑚
=
∑
ℓ
=
0
𝑑
𝑖
−
1
𝜔
𝑑
𝑖
ℓ
𝑚
𝐸
𝑖
,
ℓ
+
𝑅
𝑖
𝑚
,
∥
𝑅
𝑖
𝑚
∥
≤
𝐶
𝑖
𝜃
𝑖
𝑚
,
P
i
m
	​

=
ℓ=0
∑
d
i
	​

−1
	​

ω
d
i
	​

ℓm
	​

E
i,ℓ
	​

+R
i
m
	​

,∥R
i
m
	​

∥≤C
i
	​

θ
i
m
	​

,

where 
𝜔
𝑑
𝑖
=
𝑒
2
𝜋
𝑖
/
𝑑
𝑖
ω
d
i
	​

	​

=e
2πi/d
i
	​

, 
𝐸
𝑖
,
ℓ
E
i,ℓ
	​

 are the spectral projectors for the peripheral eigenvalues, and 
0
<
𝜃
𝑖
<
1
0<θ
i
	​

<1.

Now let

𝑝
=
l
c
m
(
𝑑
1
,
…
,
𝑑
𝑠
)
,
𝜃
=
max
⁡
(
𝜃
1
,
…
,
𝜃
𝑠
,
𝜃
𝑇
)
.
p=lcm(d
1
	​

,…,d
s
	​

),θ=max(θ
1
	​

,…,θ
s
	​

,θ
T
	​

).

Grouping the peripheral terms by residue class mod 
𝑝
p gives

𝑢
𝑇
𝑃
𝑚
𝑣
=
𝑐
𝑚
 
m
o
d
 
𝑝
+
𝑂
(
𝜃
𝑚
)
.
u
T
P
m
v=c
mmodp
	​

+O(θ
m
).

One may define

𝑐
𝑟
:
=
lim
⁡
𝑘
→
∞
𝑢
𝑇
𝑃
𝑘
𝑝
+
𝑟
𝑣
,
c
r
	​

:=
k→∞
lim
	​

u
T
P
kp+r
v,

which exists by the previous formula and satisfies 
𝑐
𝑟
≥
0
c
r
	​

≥0 because every term 
𝑢
𝑇
𝑃
𝑘
𝑝
+
𝑟
𝑣
u
T
P
kp+r
v is nonnegative.

This proves exactly the stated asymptotic and also repairs the missing justification for non-negativity of the 
𝑐
𝑟
c
r
	​

.

M2. Insert the missing residue-class lemma needed in Theorem 3.5

The proof of Theorem 3.5 currently jumps too fast from Proposition 3.4 to the contradiction with 
𝜑
𝑚
/
𝑚
φ
m
/m.

What is needed is the following lemma.

Lemma. Let

𝑎
𝑚
=
∑
𝑗
=
1
𝐽
𝑄
𝑗
(
𝑚
)
𝜆
𝑗
𝑚
,
a
m
	​

=
j=1
∑
J
	​

Q
j
	​

(m)λ
j
m
	​

,

where the 
𝑄
𝑗
Q
j
	​

 are polynomials and 
𝜆
𝑗
∈
𝐶
λ
j
	​

∈C. Let

Λ
:
=
max
⁡
𝑗
∣
𝜆
𝑗
∣
.
Λ:=
j
max
	​

∣λ
j
	​

∣.

Then there exists 
𝑞
≥
1
q≥1 such that for every residue class 
𝑟
(
m
o
d
𝑞
)
r(modq),

𝑎
𝑞
𝑘
+
𝑟
=
Λ
𝑞
𝑘
+
𝑟
(
𝑅
𝑟
(
𝑘
)
+
𝑜
(
𝑘
𝑑
𝑟
)
)
,
a
qk+r
	​

=Λ
qk+r
(R
r
	​

(k)+o(k
d
r
	​

)),

where 
𝑅
𝑟
R
r
	​

 is either the zero polynomial or has positive leading coefficient and degree 
𝑑
𝑟
∈
𝑍
≥
0
d
r
	​

∈Z
≥0
	​

, provided 
𝑎
𝑚
≥
0
a
m
	​

≥0 eventually.

Proof sketch. Write each dominant root as 
𝜆
𝑗
=
Λ
𝜁
𝑗
λ
j
	​

=Λζ
j
	​

 with 
∣
𝜁
𝑗
∣
=
1
∣ζ
j
	​

∣=1. For matrices coming from sofic shifts, each 
𝜁
𝑗
ζ
j
	​

 is a root of unity. Let 
𝑞
q annihilate all 
𝜁
𝑗
ζ
j
	​

. Then on the subsequence 
𝑚
=
𝑞
𝑘
+
𝑟
m=qk+r,

𝑎
𝑞
𝑘
+
𝑟
=
Λ
𝑞
𝑘
+
𝑟
(
∑
∣
𝜆
𝑗
∣
=
Λ
𝜁
𝑗
𝑟
𝑄
𝑗
(
𝑞
𝑘
+
𝑟
)
)
+
𝑂
(
(
Λ
−
𝛿
)
𝑞
𝑘
)
,
a
qk+r
	​

=Λ
qk+r
	​

∣λ
j
	​

∣=Λ
∑
	​

ζ
j
r
	​

Q
j
	​

(qk+r)
	​

+O((Λ−δ)
qk
),

and the bracket is a polynomial in 
𝑘
k. Since 
𝑎
𝑞
𝑘
+
𝑟
≥
0
a
qk+r
	​

≥0 eventually, this polynomial cannot oscillate in sign indefinitely; hence either it is identically zero or it has positive leading coefficient.

Apply this lemma to

𝑎
𝑚
=
∣
𝑃
𝑚
(
𝑍
)
∣
.
a
m
	​

=∣P
m
(Z)
	​

∣.

Because 
𝑎
𝑚
≍
𝜑
𝑚
/
𝑚
a
m
	​

≍φ
m
/m for all large 
𝑚
m, every residue subsequence is positive and has size 
𝜑
𝑞
𝑘
+
𝑟
/
𝑘
φ
qk+r
/k. But the lemma shows that every nonzero residue subsequence of an exponential polynomial has asymptotic size

𝑐
𝑟
𝑘
𝑑
𝑟
Λ
𝑞
𝑘
+
𝑟
(
1
+
𝑜
(
1
)
)
c
r
	​

k
d
r
	​

Λ
qk+r
(1+o(1))

with 
𝑑
𝑟
≥
0
d
r
	​

≥0. A 
𝑘
−
1
k
−1
 factor is impossible. This yields a complete proof.

M3. Make Theorem 4.1 fully rigorous

The current argument is close to correct, but two steps need to be formalized.

Let

𝑅
(
𝑧
)
:
=
−
𝑧
𝑍
𝑏
′
(
𝑧
)
𝑍
𝑏
(
𝑧
)
=
∑
𝑚
≥
1
𝑐
𝑚
𝑧
𝑚
.
R(z):=−
Z
b
	​

(z)
zZ
b
′
	​

(z)
	​

=
m≥1
∑
	​

c
m
	​

z
m
.

If 
𝑍
𝑏
Z
b
	​

 extends across an arc, Pólya-Carlson implies that 
𝑍
𝑏
Z
b
	​

 is rational. Because 
𝑍
𝑏
(
0
)
=
1
Z
b
	​

(0)=1 and each partial Euler product is zero-free on 
∣
𝑧
∣
<
1
∣z∣<1, Hurwitz implies 
𝑍
𝑏
Z
b
	​

 is zero-free on 
∣
𝑧
∣
<
1
∣z∣<1. Therefore 
𝑅
(
𝑧
)
R(z) is rational and holomorphic on 
∣
𝑧
∣
<
1
∣z∣<1.

Now write the partial-fraction decomposition of 
𝑅
R:

𝑅
(
𝑧
)
=
𝐻
(
𝑧
)
+
∑
𝑗
=
1
𝐽
𝛼
𝑗
1
−
𝑧
/
𝜌
𝑗
,
R(z)=H(z)+
j=1
∑
J
	​

1−z/ρ
j
	​

α
j
	​

	​

,

where 
𝐻
H is a polynomial and 
∣
𝜌
𝑗
∣
≥
1
∣ρ
j
	​

∣≥1. Since 
𝑅
R is a logarithmic derivative of a rational function, every pole is simple. Hence

𝑐
𝑚
=
[
𝑧
𝑚
]
𝑅
(
𝑧
)
=
∑
∣
𝜌
𝑗
∣
=
1
𝛼
𝑗
𝜌
𝑗
−
𝑚
+
𝑂
(
𝜃
𝑚
)
c
m
	​

=[z
m
]R(z)=
∣ρ
j
	​

∣=1
∑
	​

α
j
	​

ρ
j
−m
	​

+O(θ
m
)

for some 
𝜃
<
1
θ<1. In particular, 
(
𝑐
𝑚
)
(c
m
	​

) is bounded.

Next, because 
𝑅
(
𝑧
)
R(z) is rational, 
(
𝑐
𝑚
)
(c
m
	​

) satisfies a linear recurrence. After clearing denominators, one may take that recurrence to have integer coefficients. Since the 
𝑐
𝑚
c
m
	​

 are bounded integers, the state vector

(
𝑐
𝑚
,
𝑐
𝑚
+
1
,
…
,
𝑐
𝑚
+
𝑑
−
1
)
(c
m
	​

,c
m+1
	​

,…,c
m+d−1
	​

)

ranges over a finite set and evolves deterministically. Therefore 
(
𝑐
𝑚
)
(c
m
	​

) is eventually periodic.

Now use

𝑐
𝑝
=
𝑐
1
+
𝑝
𝑏
𝑝
c
p
	​

=c
1
	​

+pb
p
	​


for primes 
𝑝
p. If 
𝑏
𝑝
>
0
b
p
	​

>0 for infinitely many primes, then 
𝑐
𝑝
c
p
	​

 is unbounded along primes, contradicting eventual periodicity. This closes the proof.

That argument is self-contained and stronger than the current sketch.

M4. Either remove the 
𝜁
ζ-language from the title, or make it genuine

As written, Section 4.2 does not justify the title. A mathematically correct upgrade would be:

Proposed replacement for Proposition 4.2. If 
𝑋
X is a shift of finite type with adjacency matrix 
𝐴
A, then its Artin-Mazur zeta function satisfies

𝜁
𝑋
(
𝑧
)
=
1
det
⁡
(
𝐼
−
𝑧
𝐴
)
.
ζ
X
	​

(z)=
det(I−zA)
1
	​

.

Therefore

𝜁
𝑋
(
𝑒
−
𝑠
)
=
1
det
⁡
(
𝐼
−
𝑒
−
𝑠
𝐴
)
ζ
X
	​

(e
−s
)=
det(I−e
−s
A)
1
	​


is 
2
𝜋
𝑖
2πi-periodic in 
𝑠
s. Hence no Dirichlet series

𝐹
(
𝑠
)
=
∑
𝑛
≥
1
𝑎
𝑛
𝑛
−
𝑠
F(s)=
n≥1
∑
	​

a
n
	​

n
−s

with a non-periodic first nonzero exponential term can agree with 
𝜁
𝑋
(
𝑒
−
𝑠
)
ζ
X
	​

(e
−s
) on a nonempty open subset of its half-plane of convergence.

The proof is immediate. If 
𝑛
0
>
1
n
0
	​

>1 is the smallest index with 
𝑎
𝑛
0
≠
0
a
n
0
	​

	​


=0, then for large real 
𝜎
σ,

𝐹
(
𝜎
+
2
𝜋
𝑖
)
−
𝐹
(
𝜎
)
=
𝑎
𝑛
0
𝑛
0
−
𝜎
(
𝑒
−
2
𝜋
𝑖
log
⁡
𝑛
0
−
1
)
+
𝑂
(
(
𝑛
0
+
1
)
−
𝜎
)
,
F(σ+2πi)−F(σ)=a
n
0
	​

	​

n
0
−σ
	​

(e
−2πilogn
0
	​

−1)+O((n
0
	​

+1)
−σ
),

and the leading coefficient is nonzero because 
log
⁡
𝑛
0
∉
𝑍
logn
0
	​

∈
/
Z.

If the authors do not want to introduce genuine Artin-Mazur/Ruelle zeta functions, then the title should be changed. In its current form it overpromises.

M5. Narrow the scope claims and state the exact quantitative contradiction

The current prose suggests a broad “finite-state obstruction”, but the proved approximation theorem is only for a fixed DFA.

A clean repair is to add the following proposition.

Proposition. Let 
𝐴
A be a fixed DFA and suppose there exists 
𝛿
>
0
δ>0 and infinitely many 
𝑚
m such that

R
e
c
𝑚
≥
𝛿
,
P
r
e
c
𝑚
≥
𝛿
.
Rec
m
	​

≥δ,Prec
m
	​

≥δ.

Then

𝛿
∣
𝑃
𝑚
(
2
)
∣
≤
∣
𝐿
𝑚
∩
𝑃
𝑚
(
2
)
∣
≤
∣
𝐿
𝑚
∣
≤
𝛿
−
1
∣
𝐿
𝑚
∩
𝑃
𝑚
(
2
)
∣
≤
𝛿
−
1
∣
𝑃
𝑚
(
2
)
∣
.
δ∣P
m
(2)
	​

∣≤∣L
m
	​

∩P
m
(2)
	​

∣≤∣L
m
	​

∣≤δ
−1
∣L
m
	​

∩P
m
(2)
	​

∣≤δ
−1
∣P
m
(2)
	​

∣.

Therefore

∣
𝐿
𝑚
∣
≍
2
𝑚
𝑚
∣L
m
	​

∣≍
m
2
m
	​


on infinitely many 
𝑚
m, contradicting Theorem 2.2.

This is the exact contradiction being used. Once it is stated directly, the introduction can be narrowed accordingly:

fixed DFA approximation for binary primes;

exact regular-language obstruction for prime Zeckendorf representations;

exact sofic-slice obstruction for prime Zeckendorf length slices.

That is much more accurate than the current broad rhetoric.

M6. State Theorem 3.1 sharply and add examples

The theorem should state the exponent explicitly.

A better statement is:

Let 
𝐿
⊆
𝑍
L⊆Z be regular, and let 
𝜌
ρ be the maximal spectral radius of an accessible/coaccessible strongly connected component of the transfer matrix recognizing 
𝐿
L. Then

𝑁
𝐿
(
𝑇
)
=
𝑇
𝛼
+
𝑜
(
1
)
,
𝛼
=
{
0
,
	
𝜌
≤
1
,


log
⁡
𝜌
log
⁡
𝜑
,
	
𝜌
>
1.
N
L
	​

(T)=T
α+o(1)
,α=
⎩
⎨
⎧
	​

0,
logφ
logρ
	​

,
	​

ρ≤1,
ρ>1.
	​


This is already proved implicitly in the manuscript. It should be stated explicitly.

The exposition also needs examples:

𝐿
=
𝑍
L=Z, giving 
𝜌
=
𝜑
ρ=φ and 
𝛼
=
1
α=1;

𝐿
L finite, giving 
𝛼
=
0
α=0;

a simple infinite sparse regular sublanguage with 
𝜌
=
1
ρ=1, giving 
𝑁
𝐿
(
𝑇
)
=
𝑇
𝑜
(
1
)
N
L
	​

(T)=T
o(1)
.

Without those examples, the theorem is harder to calibrate than it should be.

In summary, the paper is not fundamentally unsound, but it is not currently a publishable journal article. The main obstacles are lack of depth, missing references, compressed proofs, and overclaiming. The most plausible path forward is either a substantial generalization of the Zeckendorf section, or a major contraction into a carefully written short note. 

main