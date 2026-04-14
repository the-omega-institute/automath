<!-- oracle metadata: {"timestamp": "2026-04-09T17:59:44.260263", "model": "chatgpt-5.4-pro-extended", "response_length": 9559} -->

I reviewed the manuscript 

main

.

1. Overall assessment

Major revision

The paper has an interesting explicit example, and the determinant computation plus most of the geometric package look potentially publishable as a short note. In its current form, however, I would not recommend acceptance. The biggest problem is that the proof of the asymptotic theorem is not valid as written: Lemma 3.11 contains both a sign mistake and a substantive gap in the root-separation argument. In addition, the bibliography is incomplete, with multiple unresolved placeholders in Section 1.2, and the paper needs a stronger explanation of why this particular example is of independent interest beyond being a worked computation.

2. Novelty rating for each theorem
Theorem	Rating	One-line justification
Theorem 1.1	MEDIUM	The determinant formulas themselves are mostly explicit computation, but the genus 6 curve, genus 3 quotient, and generic 
𝑆
6
S
6
	​

 Galois group make the example structurally nontrivial.
Theorem 1.2	MEDIUM	The degree law and 
𝑚
=
2
m=2 case are routine once the setup is in place, but the explicit large-
𝑚
m Perron-root expansion is a meaningful calculation for this concrete family, assuming the proof is repaired.

A finer breakdown would be: 1.1(i), 1.1(ii), 1.2(i), and 1.2(ii) are LOW novelty individually, while 1.1(iii) and especially 1.2(iii) are MEDIUM.

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	1.2, References	BLOCKER	Multiple unresolved citations remain as [?]. This makes the literature review incomplete and publication-ready references impossible.	Replace all placeholders with full bibliographic entries and verify that every citation compiles correctly.
B2	3.4, Lemma 3.11 Step 1	BLOCKER	The sign logic is wrong. From 
𝑤
′
(
2
)
=
−
11
/
153
w
′
(2)=−11/153 and 
𝑠
=
2
−
𝛿
s=2−δ, one gets 
𝑤
∗
(
2
−
𝛿
)
>
1
/
3
w
∗
	​

(2−δ)>1/3, not 
<
1
/
3
<1/3.	Rewrite the local monotonicity argument with the correct inequality direction.
B3	3.4, Lemma 3.11 Step 3 and Theorem 3.12	BLOCKER	The root-separation argument is false as stated. Other conjugates such as 
2
cos
⁡
(
3
𝜋
/
𝑚
)
2cos(3π/m) also approach 
2
2 as 
𝑚
→
∞
m→∞, so the fixed-
𝜀
ε compactness argument does not isolate 
±
𝑠
𝑚
±s
m
	​

.	Give a new proof comparing all near-endpoint conjugates 
2
cos
⁡
(
𝑎
𝜋
/
𝑚
)
2cos(aπ/m) using monotonicity or asymptotic comparison of the endpoint branch.
M1	Introduction, overall framing	MEDIUM	The paper presents itself as a “modest” case study with no new general method. As written, the broader significance is under-motivated.	State clearly what structural lesson this example gives about self-dual kernels, or reframe the paper explicitly as a short computational note.
M2	3.2, Lemma 3.4	MEDIUM	Irreducibility is proved only by appealing forward to Proposition 3.7. This is fixable but awkward and obscures logical flow.	Reorder the section so the Galois-group result precedes irreducibility, or add a direct irreducibility proof.
M3	3.2, curve notation	MEDIUM	The base field 
𝑘
k is not defined in the genus and function-field statements.	Specify the field explicitly, for example over 
𝑄
‾
Q
	​

 or characteristic 0, and define 
𝑋
X as the normalization of the projective closure of the irreducible affine curve.
M4	Appendix A, reproducibility	MEDIUM	Several key claims are delegated to “computer algebra” without code or detailed certificates.	Provide Sage/Mathematica scripts or a supplementary repository, and include exact outputs for the decisive computations.
M5	2.2, example presentation	MEDIUM	Because the paper is example-driven, the origin of the 10-state kernel is not explained enough. The state labels feel ad hoc.	Add a figure of the digraph and a short derivation from the synchronization/path-comparison construction.
L1	3.3	LOW	The nonstandard notation 
Φ
𝑚
+
Φ
m
+
	​

 and the exceptional case 
𝑚
=
3
m=3 are only partly explained.	Add a short remark with the first few 
Φ
𝑚
+
Φ
m
+
	​

 and what happens for 
𝑚
=
2
,
3
m=2,3.
L2	3.1	LOW	It is surprising that a 
10
×
10
10×10 matrix yields a determinant of degree 6, but the paper does not explain why.	Add one sentence explaining the rank reduction or the four persistent zero eigenvalues.
L3	Abstract, 1.1, 3.12	LOW	“Full asymptotic expansion” is stronger than what is explicitly displayed.	Either state existence to all orders and list the first six terms, or weaken the phrasing to “through order 
𝑚
−
12
m
−12
”.
4. Missing references

At minimum, the unresolved placeholders in Section 1.2 should be replaced by the standard references the text is clearly aiming at: Hashimoto’s 1989 paper on zeta functions of finite graphs and 
𝑝
p-adic groups, Stark and Terras on zeta functions of finite graphs and coverings, Kotani and Sunada on zeta functions of finite graphs, Terras’s graph-zeta monograph, Adler-Kitchens-Marcus on finite group actions on shifts of finite type, Fiebig on periodic points and finite group actions on SFTs, and Boyle-Schmieding on finite group extensions of SFTs. The exact Pollicott-Sharp paper alluded to should also be supplied explicitly. 
Cambridge University Press & Assessment
+7
Project Euclid
+7
ScienceDirect
+7

5. Specific improvements needed to reach acceptance

Repair the proof of the main arithmetic statement, namely Lemma 3.11 and therefore Theorem 3.12.

Complete the bibliography and fix every unresolved citation.

Strengthen the introduction so the reader understands why this kernel is canonical or instructive, rather than merely computable.

Tighten the formal setup: define the base field, clean up the irreducibility argument, and clarify the exceptional cyclotomic cases.

Make the computer algebra verifiable by a reader.

6. Concrete fixes

B1. References and placeholders.
Run a full bibliography audit. Replace every [?] in Section 1.2 by an actual citation, add the missing BibTeX entries, and recompile until there are no unresolved references. Because Section 1.2 makes several literature claims, each named thread of prior work should have a concrete, checkable citation.

B2. Sign error in Lemma 3.11.
Rewrite Step 1 using the local expansion

𝑤
∗
(
2
−
𝛿
)
=
1
3
+
11
153
𝛿
+
𝑂
(
𝛿
2
)
,
w
∗
	​

(2−δ)=
3
1
	​

+
153
11
	​

δ+O(δ
2
),

which follows immediately from 
𝑤
′
(
2
)
=
−
11
/
153
w
′
(2)=−11/153. Then state the correct conclusion: for 
𝑠
<
2
s<2 near 2, the relevant root satisfies 
𝑤
∗
(
𝑠
)
>
1
/
3
w
∗
	​

(s)>1/3, while it still remains the unique root in the chosen disk and stays below the next root-modulus threshold.

B3. New proof of root separation.
The present compactness argument cannot work because for fixed odd 
𝑎
a, 
2
cos
⁡
(
𝑎
𝜋
/
𝑚
)
→
2
2cos(aπ/m)→2 as 
𝑚
→
∞
m→∞. A viable repair is:

first prove there is 
𝜂
>
0
η>0 such that for 
𝑠
∈
[
2
−
𝜂
,
2
]
s∈[2−η,2], the branch 
𝑤
∗
(
𝑠
)
w
∗
	​

(s) is the unique smallest-modulus root of 
Δ
^
(
 
⋅
 
,
𝑠
)
Δ
(⋅,s);

use 
𝜌
′
(
2
)
=
11
/
17
>
0
ρ
′
(2)=11/17>0 to deduce that 
𝜌
(
𝑠
)
=
1
/
𝑤
∗
(
𝑠
)
ρ(s)=1/w
∗
	​

(s) is strictly increasing in 
𝑠
s on that interval;

for conjugates 
𝛼
𝑎
=
2
cos
⁡
(
𝑎
𝜋
/
𝑚
)
α
a
	​

=2cos(aπ/m) near 
2
2, compare them by

2
−
𝛼
𝑎
=
𝑎
2
𝜋
2
𝑚
2
+
𝑂
(
𝑚
−
4
)
,
2−α
a
	​

=
m
2
a
2
π
2
	​

+O(m
−4
),

so 
𝑎
=
1
a=1 gives the largest 
𝜌
(
𝛼
𝑎
)
ρ(α
a
	​

), hence the smallest 
∣
𝑤
∗
(
𝛼
𝑎
)
∣
∣w
∗
	​

(α
a
	​

)∣;

handle the conjugates away from 
±
2
±2 by a genuine compactness bound;

use the symmetry 
Δ
^
(
−
𝑤
,
𝑠
)
=
Δ
^
(
𝑤
,
−
𝑠
)
Δ
(−w,s)=
Δ
(w,−s) to treat the negative endpoint.

That would make Theorem 3.12 supportable.

M1. Framing and significance.
Add one paragraph near the end of the introduction saying exactly what general phenomenon this example illustrates. For instance: self-duality can force a two-parameter determinant to collapse to a completed polynomial, whose quotient geometry and cyclotomic specializations become tractable. Without that statement, the contribution reads as an isolated computation.

M2. Irreducibility proof.
Either move Proposition 3.7 before Lemma 3.4, or replace Lemma 3.4 by a direct argument. A simple direct route is to show one specialization 
Δ
^
(
𝑤
,
𝑠
0
)
Δ
(w,s
0
	​

) is irreducible over 
𝑄
[
𝑤
]
Q[w], which already implies irreducibility over 
𝑄
(
𝑠
)
[
𝑤
]
Q(s)[w] for the generic polynomial.

M3. Base field and curve definitions.
State explicitly, for example: “All curves are considered over 
𝑄
‾
Q
	​

. Let 
𝑋
X be the normalization of the projective closure of the irreducible affine curve 
Δ
^
(
𝑤
,
𝑠
)
=
0
Δ
(w,s)=0.” This will make the genus statements and the quadratic-extension ramification argument fully precise.

M4. Computational reproducibility.
Add a supplementary file containing the exact Sage/Mathematica code for:

the determinant of 
𝐼
−
𝑧
𝐵
(
𝑢
)
I−zB(u),

the Gröbner basis computation for 
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

⟩,

the discriminant in 
𝑠
s,

the mod-
𝑝
p factorization checks,

the recursive jet computation at 
(
1
/
3
,
2
)
(1/3,2).

Even a one-page appendix with code snippets or a repository link would materially improve confidence.

M5. Explain the kernel itself.
Insert a figure of the 10-state digraph with the five dual pairs marked, and add a short paragraph explaining how the states arise from the synchronization mismatch construction. Since the paper’s value is example-specific, the example itself should be easier to parse.

My bottom line is that the paper is close enough in spirit that I would not reject it outright, but the main arithmetic argument must be repaired before it can be considered for acceptance.