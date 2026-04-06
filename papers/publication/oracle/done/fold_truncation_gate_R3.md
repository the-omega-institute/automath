<!-- oracle metadata: {"timestamp": "2026-04-06T19:35:41.666382", "model": "o3-mini-high", "response_length": 15113} -->

1. Overall assessment

Reject.

I reviewed the attached manuscript. 

main

The algebraic recursion behind Theorem 4.1 appears essentially correct, and some of the deterministic material could likely be salvaged as a short note. But the paper is not journal-ready in its present form. The bibliography is unresolved with placeholder citations throughout, so originality claims cannot be checked. The main deterministic theorem is largely formal once the adjacent defect is defined, several later results are immediate corollaries, and Section 7 is explicitly presented as a standard conditional criterion that is not established for the Fold tower itself. In addition, Theorem 7.1 has a statement-level well-definedness problem: characters on 
𝐻
𝑚
H
m
	​

 are evaluated on increments taking values in the ambient group 
(
𝑍
/
2
𝑍
)
𝑚
(Z/2Z)
m
 without a specified extension or reachable-state restriction. 

main

 

main

 

main

2. Novelty rating for each named result

I rate all named formal results, not only the two items labeled “Theorem”.

Result	Novelty	One-line justification
Proposition 2.1	MEDIUM	The residue reformulation is neat and useful, but it is a direct repackaging of Zeckendorf normalization plus truncation.
Theorem 4.1	MEDIUM	The observable may be specific to this manuscript, but the identity is essentially the telescoping of an adjacent discrepancy defined precisely to telescope.
Corollary 4.4	LOW	This is bounded-difference plus union bound once Theorem 4.1 is available.
Corollary 5.1	LOW	Immediate from Hamming-Lipschitz control and subadditivity of Hamming weight under xor.
Proposition 5.2	LOW	Direct split of the telescoping sum at an intermediate scale.
Proposition 6.1	LOW	Summability of nonnegative integers implies eventual vanishing, after which inverse-limit compatibility is automatic.
Theorem 7.1	LOW	Standard Fourier/spectral mixing criterion for finite-state additive Markov models, and the paper itself presents it as a general conditional template.
Corollary 7.4	LOW	Standard character consequence of Theorem 7.1 plus the trivial fact that Haar on 
(
𝑍
/
2
𝑍
)
𝑚
(Z/2Z)
m
 gives iid Bernoulli
(
1
/
2
)
(1/2) coordinates.
3. Issue table

The issues below are grounded in the manuscript’s own description of the contribution, the unresolved placeholders in the introduction, the deterministic core around Proposition 2.1 and Theorem 4.1, and the conditional status of Section 7. 

main

 

main

 

main

ID	Section	Severity	Description	Suggested fix
B1	Introduction / bibliography	BLOCKER	The paper contains unresolved placeholders [?, ?] throughout. Foundational background, overlap with the “core folding paper”, and novelty claims are therefore impossible to assess.	Supply a complete bibliography, cite the prior Fold manuscript explicitly, and add a paragraph stating exact overlap and non-overlap.
B2	Whole paper	BLOCKER	The journal-level contribution is too thin in present form. Theorem 4.1 is largely formal, Corollaries 4.4 and 5.1 and Proposition 5.2 are immediate, and Proposition 6.1 is nearly tautological.	Either recast as a very short note with modest claims or add genuinely new structural/probabilistic theorems.
B3	Section 7.1	BLOCKER	Theorem 7.1 is not formally well-defined as written: 
𝜒
∈
𝐻
^
𝑚
χ∈
H
m
	​

 is evaluated on 
Γ
𝑚
(
𝑎
,
𝑏
)
∈
(
𝑍
/
2
𝑍
)
𝑚
Γ
m
	​

(a,b)∈(Z/2Z)
m
 without specifying an extension of 
𝜒
χ to the ambient group or restricting to reachable transitions.	Reformulate the theorem using ambient characters 
𝜒
𝑢
(
𝑣
)
=
(
−
1
)
⟨
𝑢
,
𝑣
⟩
χ
u
	​

(v)=(−1)
⟨u,v⟩
 on 
𝐺
=
(
𝑍
/
2
𝑍
)
𝑚
G=(Z/2Z)
m
, or restrict to reachable states and prove all accessible increments lie in 
𝐻
𝑚
H
m
	​

.
M1	Section 2.1 / Proposition 2.1	MEDIUM	Fold_m is not fully self-contained: 
𝑍
(
𝑁
)
Z(N) is not defined as a zero-padded infinite sequence, and the proof uses the unproved claim 
𝑁
(
𝑥
)
<
𝐹
𝑚
+
2
N(x)<F
m+2
	​

 for 
𝑥
∈
𝑋
𝑚
x∈X
m
	​

.	Add explicit conventions for 
𝑍
(
0
)
Z(0) and zero-padding, and prove 
max
⁡
𝑥
∈
𝑋
𝑚
𝑁
(
𝑥
)
=
𝐹
𝑚
+
2
−
1
max
x∈X
m
	​

	​

N(x)=F
m+2
	​

−1.
M2	Sections 3 to 5	MEDIUM	The manuscript never characterizes the local defect. Without an explicit criterion for 
𝐾
𝑚
+
1
→
𝑚
K
m+1→m
	​

, the telescoping identity has little explanatory content.	Add a theorem classifying when the adjacent defect is nonzero, in terms of a threshold crossing for the prefix value.
M3	Sections 4.2 to 5	MEDIUM	The “probability bound” and “budget” are formally correct but mathematically weak because no natural input law is analyzed.	Choose a canonical law on raw words and compute or estimate 
𝑃
(
𝐾
𝑗
+
1
→
𝑗
=
1
)
P(K
j+1→j
	​

=1), (E
M4	Section 7	MEDIUM	Section 7 is explicitly not verified for the Fold tower, so it currently reads as a detached appendix theorem rather than part of the paper’s contribution.	Either remove it from the title/abstract/introduction and move it to an appendix, or instantiate 
(
𝑆
𝑚
,
𝑃
𝑚
,
Γ
𝑚
)
(S
m
	​

,P
m
	​

,Γ
m
	​

) for Fold.
M5	Section 4.1	MEDIUM	The proof of Theorem 4.1 hides the key recursion inside an inline calculation; the descent across changing cube dimensions is harder to audit than necessary.	State the recursion as a separate lemma and prove the theorem by explicit descending induction.
M6	Section 6.1	MEDIUM	Proposition 6.1 uses a summability assumption much stronger than the real content. Since (	\delta_m
L1	Section 4.1	LOW	“Stokes” terminology oversells what is essentially a telescoping/coboundary identity.	Rename as telescoping or cocycle identity, or formalize the cochain language.
L2	Throughout	LOW	“Auditable” is nonstandard mathematical prose and substitutes rhetoric for sharper content.	Replace with precise statistical or combinatorial formulations.
4. Missing references

At minimum, the paper should cite the following bodies of work.

Classical Zeckendorf uniqueness and representation theory: Lekkerkerker (1951/52) and Zeckendorf (1972). These are the obvious foundational citations for any paper whose basic object is Zeckendorf normalization. 
Numdam
+1

Fibonacci numeration and automata/normalization: Christiane Frougny’s work on Fibonacci representations and finite automata, together with earlier linear numeration-system work. This is directly relevant to the Fold map as a normalization mechanism. 
ADS
+1

Broader Fibonacci numeration survey background: Berstel’s survey on Fibonacci words and arithmetic/normalization in the Fibonacci system. 
Springer Link

Symbolic-dynamics background for the golden-mean shift and intrinsic Markov structure: Parry’s Intrinsic Markov Chains and Lind-Marcus. 
JSTOR
+1

Finite-group Fourier methods for Section 7: Diaconis, Group Representations in Probability and Statistics. 
Persi Diaconis

The “core folding paper” itself: the current manuscript repeatedly refers to a core Fold paper and a larger manuscript, but does not identify them. Those must be cited explicitly, with overlap stated theorem by theorem. 

main

5. Specific improvements needed to reach acceptance

First, the manuscript must become a real scholarly object: complete bibliography, explicit dependence map, and a self-contained statement of what is assumed from earlier Fold work and what is proved here.

Second, the deterministic core needs one genuinely substantive theorem beyond the formal telescoping identity. The natural candidate is an explicit classification of the adjacent defect, followed by a nontrivial computation under a natural probability law.

Third, Section 7 must be repaired or demoted. As written, it is both standard and disconnected from the Fold problem. Either instantiate the model for Fold, or move the section to an appendix and remove it from the abstract and contribution claims.

Fourth, the paper must be reframed at the right scale. In its current state it is closer to a short technical note than to a full journal article.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Complete the bibliography and dependency map

Add a short subsection, ideally at the end of the introduction, of the form:

External inputs. The only external results used in Sections 2 to 6 are:
(i) uniqueness/existence of Zeckendorf expansions;
(ii) standard facts about finite shifts of finite type.
No theorem from the prior Fold manuscript is used except Definition X / Proposition Y.

If earlier Fold work is genuinely used, cite it by theorem number. If it is not used, delete references to the “core folding paper” and “larger manuscript” from the abstract and introduction.

B2. Add a genuinely new structural theorem

The easiest way to make the paper nontrivial is to classify the adjacent defect explicitly.

Let 
𝜂
=
𝑝
 
𝑏
∈
Ω
𝑚
+
1
η=pb∈Ω
m+1
	​

 with 
𝑝
∈
Ω
𝑚
p∈Ω
m
	​

, 
𝑏
∈
{
0
,
1
}
b∈{0,1}, and let 
𝑠
:
=
𝑁
(
𝑝
)
s:=N(p). Then the following proposition should be proved.

𝐾
𝑚
+
1
→
𝑚
(
𝑝
,
𝑏
)
=
𝑏
⋅
1
{
𝑠
≥
𝐹
𝑚
+
1
}
.
K
m+1→m
	​

(p,b)=b⋅1
{s≥F
m+1
	​

}
	​

.

More precisely:

if 
𝑏
=
0
b=0, then 
𝜅
𝑚
+
1
→
𝑚
(
𝑝
,
0
)
=
0
κ
m+1→m
	​

(p,0)=0;

if 
𝑏
=
1
b=1 and 
𝑠
<
𝐹
𝑚
+
1
s<F
m+1
	​

, then 
𝜅
𝑚
+
1
→
𝑚
(
𝑝
,
1
)
=
0
κ
m+1→m
	​

(p,1)=0;

if 
𝑏
=
1
b=1 and 
𝑠
=
𝐹
𝑚
+
1
+
𝑡
s=F
m+1
	​

+t with 
0
≤
𝑡
<
𝐹
𝑚
+
2
0≤t<F
m+2
	​

, then

𝜋
𝑚
+
1
→
𝑚
 ⁣
(
𝐹
𝑜
𝑙
𝑑
𝑚
+
1
(
𝑝
,
1
)
)
=
𝜋
∞
→
𝑚
(
𝑍
(
𝑡
)
)
,
π
m+1→m
	​

(Fold
m+1
	​

(p,1))=π
∞→m
	​

(Z(t)),

so

𝜅
𝑚
+
1
→
𝑚
(
𝑝
,
1
)
=
𝐹
𝑜
𝑙
𝑑
𝑚
(
𝑝
)
⊕
𝜋
∞
→
𝑚
(
𝑍
(
𝑡
)
)
.
κ
m+1→m
	​

(p,1)=Fold
m
	​

(p)⊕π
∞→m
	​

(Z(t)).

This follows directly from Proposition 2.1 applied at levels 
𝑚
m and 
𝑚
+
1
m+1. It would convert the current formal identity into an actual structural statement: local defects occur exactly when the added 
(
𝑚
+
1
)
(m+1)-st bit pushes the prefix value across the Zeckendorf threshold 
𝐹
𝑚
+
1
F
m+1
	​

.

B3. Repair Theorem 7.1 so it is well-defined

The clean fix is to formulate Section 7 on the ambient group 
𝐺
=
(
𝑍
/
2
𝑍
)
𝑚
G=(Z/2Z)
m
, not on 
𝐻
^
𝑚
H
m
	​

.

For 
𝑢
∈
𝐺
u∈G, define

𝜒
𝑢
(
𝑣
)
:
=
(
−
1
)
⟨
𝑢
,
𝑣
⟩
,
𝑣
∈
𝐺
,
χ
u
	​

(v):=(−1)
⟨u,v⟩
,v∈G,

and define the twisted matrices by

𝑃
𝑚
,
𝑢
(
𝑎
,
𝑏
)
:
=
𝑝
𝑎
𝑏
𝜒
𝑢
(
Γ
𝑚
(
𝑎
,
𝑏
)
)
.
P
m,u
	​

(a,b):=p
ab
	​

χ
u
	​

(Γ
m
	​

(a,b)).

Let

𝐻
𝑚
⊥
:
=
{
𝑢
∈
𝐺
:
𝜒
𝑢
∣
𝐻
𝑚
≡
1
}
.
H
m
⊥
	​

:={u∈G:χ
u
	​

∣
H
m
	​

	​

≡1}.

Then state the criterion as:

If 
𝜌
(
𝑃
𝑚
,
𝑢
)
<
1
ρ(P
m,u
	​

)<1 for every 
𝑢
∉
𝐻
𝑚
⊥
u∈
/
H
m
⊥
	​

, then

∥
\Law
(
𝐷
𝑛
→
𝑚
)
−
\Haar
(
𝐻
𝑚
)
∥
𝑇
𝑉
≤
𝐶
𝑚
𝜌
𝑚
 
𝑛
−
𝑚
.
∥\Law(D
n→m
	​

)−\Haar(H
m
	​

)∥
TV
	​

≤C
m
	​

ρ
m
n−m
	​

.

The proof then runs by Fourier inversion on the full cube 
𝐺
G. Under Haar measure on 
𝐻
𝑚
H
m
	​

, the ambient Fourier transform is exactly 
1
𝑢
∈
𝐻
𝑚
⊥
1
u∈H
m
⊥
	​

	​

, so the bookkeeping is cleaner and no extension ambiguity remains.

M1. Make Proposition 2.1 self-contained

Define 
𝑍
(
𝑁
)
Z(N) explicitly as the unique infinite binary sequence 
𝑧
=
(
𝑧
𝑘
)
𝑘
≥
1
z=(z
k
	​

)
k≥1
	​

 with finite support, no adjacent 1s, and

𝑁
=
∑
𝑘
≥
1
𝑧
𝑘
𝐹
𝑘
+
1
.
N=
k≥1
∑
	​

z
k
	​

F
k+1
	​

.

Set 
𝑍
(
0
)
=
0
∞
Z(0)=0
∞
.

Then add the missing lemma:

𝑀
𝑚
:
=
max
⁡
𝑥
∈
𝑋
𝑚
𝑁
(
𝑥
)
=
𝐹
𝑚
+
2
−
1.
M
m
	​

:=
x∈X
m
	​

max
	​

N(x)=F
m+2
	​

−1.

A short proof is:

𝑀
𝑚
=
max
⁡
{
𝑀
𝑚
−
1
,
 
𝐹
𝑚
+
1
+
𝑀
𝑚
−
2
}
,
M
m
	​

=max{M
m−1
	​

,F
m+1
	​

+M
m−2
	​

},

because either 
𝑥
𝑚
=
0
x
m
	​

=0, or 
𝑥
𝑚
=
1
x
m
	​

=1 and then 
𝑥
𝑚
−
1
=
0
x
m−1
	​

=0. With 
𝑀
0
=
0
M
0
	​

=0 and 
𝑀
1
=
1
M
1
	​

=1, induction gives 
𝑀
𝑚
=
𝐹
𝑚
+
2
−
1
M
m
	​

=F
m+2
	​

−1. This justifies the line 
𝑁
(
𝑥
)
<
𝐹
𝑚
+
2
N(x)<F
m+2
	​

 used in Proposition 2.1.

M2. Use the local-defect classification to strengthen the deterministic core

Once the threshold criterion above is proved, rewrite Corollary 4.4 as

{
𝐷
𝑛
→
𝑚
≠
0
}
⊆
⋃
𝑗
=
𝑚
𝑛
−
1
{
𝜔
𝑗
+
1
=
1
,
 
𝑁
(
𝑟
𝑛
→
𝑗
(
𝜔
)
)
≥
𝐹
𝑗
+
1
}
.
{D
n→m
	​


=0}⊆
j=m
⋃
n−1
	​

{ω
j+1
	​

=1, N(r
n→j
	​

(ω))≥F
j+1
	​

}.

This is far more informative than the present abstract union bound over undefined-looking defect events. It exposes the defect as a precise carry-threshold phenomenon.

M3. Turn the probability bounds into actual theorems

Fix a natural law, for example the uniform law on 
Ω
𝑛
Ω
n
	​

 or iid Bernoulli
(
1
/
2
)
(1/2) bits on 
{
0
,
1
}
𝑁
{0,1}
N
. Then define

𝐴
𝑗
(
𝑡
)
:
=
#
{
𝑝
∈
{
0
,
1
}
𝑗
:
𝑁
(
𝑝
)
=
𝑡
}
.
A
j
	​

(t):=#{p∈{0,1}
j
:N(p)=t}.

These satisfy the dynamic-programming recursion

𝐴
𝑗
+
1
(
𝑡
)
=
𝐴
𝑗
(
𝑡
)
+
𝐴
𝑗
(
𝑡
−
𝐹
𝑗
+
2
)
,
A
j+1
	​

(t)=A
j
	​

(t)+A
j
	​

(t−F
j+2
	​

),

with the obvious convention 
𝐴
𝑗
(
𝑠
)
=
0
A
j
	​

(s)=0 for 
𝑠
<
0
s<0.

Then

𝑃
(
𝐾
𝑗
+
1
→
𝑗
=
1
)
=
2
−
(
𝑗
+
1
)
∑
𝑡
≥
𝐹
𝑗
+
1
𝐴
𝑗
(
𝑡
)
P(K
j+1→j
	​

=1)=2
−(j+1)
t≥F
j+1
	​

∑
	​

A
j
	​

(t)

under the uniform law on 
Ω
𝑗
+
1
Ω
j+1
	​

.

This gives explicit quantities to insert into Corollaries 4.4 and 5.1. Without something of this form, the current “probability bound” remains mathematically correct but nearly empty.

M4. Either instantiate Section 7 for Fold or demote it

If Section 7 is to stay in the main body, build the actual finite-state model. For fixed 
𝑚
m, take a finite normalization transducer for Zeckendorf conversion, let the state record the transducer state together with the current 
𝑚
m-prefix of the normalized output, and define the increment in 
𝐺
=
(
𝑍
/
2
𝑍
)
𝑚
G=(Z/2Z)
m
 to be the change in the defect coordinate after one transition. This yields a concrete candidate 
(
𝑆
𝑚
,
𝑃
𝑚
,
Γ
𝑚
)
(S
m
	​

,P
m
	​

,Γ
m
	​

).

If the author cannot carry out that construction and verify the twisted spectral-radius condition, Section 7 should be moved to an appendix and removed from the abstract and stated contributions.

M5. Rewrite Theorem 4.1 as an induction, not an inline telescoping trick

State first the recursive lemma

Δ
𝑗
−
1
(
𝜔
)
=
𝜅
𝑗
→
𝑗
−
1
(
𝑟
𝑛
→
𝑗
(
𝜔
)
)
⊕
𝜏
𝑗
→
𝑗
−
1
(
Δ
𝑗
(
𝜔
)
)
,
𝑚
<
𝑗
≤
𝑛
.
Δ
j−1
	​

(ω)=κ
j→j−1
	​

(r
n→j
	​

(ω))⊕τ
j→j−1
	​

(Δ
j
	​

(ω)),m<j≤n.

Then prove by descending induction on 
𝑗
j that

Δ
𝑚
(
𝜔
)
=
𝜏
𝑗
→
𝑚
Δ
𝑗
(
𝜔
)
⊕
⨁
𝑡
=
𝑚
𝑗
−
1
𝜏
𝑡
→
𝑚
(
𝜅
𝑡
+
1
→
𝑡
(
𝑟
𝑛
→
𝑡
+
1
(
𝜔
)
)
)
.
Δ
m
	​

(ω)=τ
j→m
	​

Δ
j
	​

(ω)⊕
t=m
⨁
j−1
	​

τ
t→m
	​

(κ
t+1→t
	​

(r
n→t+1
	​

(ω))).

Setting 
𝑗
=
𝑛
j=n and using 
Δ
𝑛
=
0
Δ
n
	​

=0 gives Theorem 4.1. This is more transparent and fully auditable.

M6. Replace Proposition 6.1 by the exact compatibility criterion

The real statement is:

∃
 
𝑥
∞
∈
𝑋
∞
 with 
𝜋
∞
→
𝑚
(
𝑥
∞
)
=
𝑥
𝑚
 for all 
𝑚
≥
𝑀
  
⟺
  
𝛿
𝑚
=
0
 for all 
𝑚
≥
𝑀
.
∃x
∞
∈X
∞
	​

 with π
∞→m
	​

(x
∞
)=x
m
	​

 for all m≥M⟺δ
m
	​

=0 for all m≥M.

That is the exact inverse-limit compatibility criterion. The current summability hypothesis is only a sufficient condition for the left-hand side, and because 
∣
𝛿
𝑚
∣
0
∈
𝑁
∣δ
m
	​

∣
0
	​

∈N, it is equivalent to eventual vanishing anyway. The present proposition should therefore be sharpened, with the summability statement relegated to a one-line corollary.

In short, I would reject this version, but I do think there is a potentially publishable short note hiding inside it if the author supplies the missing bibliography, fixes Section 7 formally, and adds one substantive theorem about the actual structure of the local defect.