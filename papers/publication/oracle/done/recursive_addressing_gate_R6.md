<!-- oracle metadata: {"timestamp": "2026-04-12T01:22:45.780346", "model": "chatgpt-5.4-pro-extended", "response_length": 13406} -->

1. Overall assessment

Reject.

The manuscript is readable and reasonably organized, and the authors are commendably candid that much of it is expository. However, as a research-journal submission it does not yet meet the bar. The main reasons are: most numbered results are standard or immediate reformulations; the bridge from the measurable setup to the later prefix-site formalism is not valid in the stated generality; Proposition 5.1 contains a serious gap and is not justified as stated; and the only nontrivial cocycle computation is prescribed ad hoc on a nerve rather than derived from the advertised readout semantics. In its current form, this is closer to an expository note with one toy computation than to a publishable research article. 

main

For an explicitly expository venue, a major rewrite could make it useful. For a standard research journal, I would not recommend acceptance.

2. Novelty rating for each numbered result

I interpret “each theorem” as each numbered theorem-like statement.

Result	Novelty	One-line justification
Proposition 2.1	LOW	Standard measurability of finite cylinder events generated from previous observable data.
Corollary 2.2	LOW	Immediate consequence of Proposition 2.1 and shift-invariance of the generated σ-algebra.
Proposition 2.4	LOW	Direct unpacking of the coding map and symbolic cylinder pullback identity.
Proposition 3.3	LOW	Standard fact that finite covers in a poset/category of cylinder objects generate a Grothendieck topology.
Proposition 4.1	LOW	Merely restates “readout exists at 
𝑎
a” as 
𝑅
(
𝑎
)
≠
∅
R(a)

=∅.
Corollary 4.2	LOW	Standard presheaf failure trichotomy: emptiness, descent failure, non-separatedness.
Lemma 4.4	LOW	Standard normalized Čech complex of a finite ordered nerve.
Proposition 4.6	LOW	Standard obstruction logic: a coherent global object forces the defect class to vanish.
Proposition 5.1	MEDIUM	Mildly new packaging, but mathematically routine in intent and currently not correct in full stated generality.
Lemma 5.3	LOW	Elementary cardinality/fiber-counting argument once a quotient 
𝐴
→
𝐴
v
i
s
A→A
vis
	​

 is fixed.
Proposition 5.5	LOW	Dual reformulation of factorization through a quotient; conceptually straightforward.
Proposition 6.1	LOW	Elementary combinatorial description of a four-set cover.
Proposition 6.3	MEDIUM	Explicit toy cocycle computation on a tetrahedral nerve is the most concrete original part of the paper, though still limited in scope.
Proposition 7.1	LOW	Standard inverse-limit and ultrametric facts.
Theorem 7.4	LOW	Standard stalk/germ injectivity reformulated in the paper’s terminology.
3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	1, 5, 6, 8	BLOCKER	The contribution is below research-journal novelty level. The paper itself presents most results as standard/background, while the “new” part is either routine packaging or a toy computation.	Either retarget as an expository article, or add a genuinely new theorem derived from actual recursive-addressing models.
B2	2 to 3	BLOCKER	The transition from measurable coding to the prefix-site setup is not justified in the stated generality. In particular, the standing axioms (especially CA3) need not hold for a general admissible language coming from 
𝜅
𝐿
+
κ
L
+
	​

.	Redefine the site on admissible trace cylinders inside the image shift 
𝑋
a
d
m
:
=
i
m
(
𝜅
𝐿
+
)
X
adm
	​

:=im(κ
L
+
	​

), or impose and prove precise closure assumptions.
B3	5	BLOCKER	Proposition 5.1 has a serious proof gap. From 
Φ
∗
[
𝛼
]
=
0
Φ
∗
	​

[α]=0 in 
𝐻
2
(
𝑈
,
∏
𝐴
/
𝑁
𝑟
)
H
2
(U,∏A/N
r
	​

), it does not follow that 
𝑞
∗
[
𝛼
]
=
0
q
∗
	​

[α]=0 in 
𝐻
2
(
𝑈
,
i
m
 
Φ
)
H
2
(U,imΦ) unless injectivity on cohomology is proved. As written, the “visible quotient” construction is unsupported, and Lemma 5.3 and Proposition 5.5 inherit that problem.	Add hypotheses under which the argument is valid, or replace Proposition 5.1 by a weaker correct statement.
B4	6	BLOCKER	The only nontrivial obstruction example is not derived from the readout presheaf/measurable semantics. The manuscript explicitly prescribes comparison torsors and cocycle values on the nerve.	Supply a semantically derived example from an actual 
𝑅
R, or clearly relegate Section 6 to an isolated combinatorial appendix.
M1	4.3	MEDIUM	Definition 4.5 is under-specified. “
𝐴
A-equivariant composition” is not enough to justify the change-of-trivialization formula 
𝛼
′
=
𝛼
+
𝛿
𝛽
α
′
=α+δβ.	State the exact torsor compatibility axiom, then prove the representative-change lemma separately.
M2	1, 4, 6, 8	MEDIUM	There are placeholder citations “[?, ?]” and incomplete literature positioning. This is not publication-ready.	Replace all placeholders, add missing conceptual neighbors, and support all nonstandard claims.
M3	Throughout	MEDIUM	Cross-reference and nomenclature errors remain. Examples include “Theorem 5.1” for Proposition 5.1, “Theorem 6.3” for Proposition 6.3, and inconsistent labeling of 7.4.	Do a full editorial pass with automated labels/refs and notation cleanup.
M4	5, 8	MEDIUM	The “intrinsic” language in Section 5 is too strong. 
𝐴
v
i
s
A
vis
	​

 is only attached to a fixed cover/class, and no refinement invariance or functoriality is established.	Either prove refinement invariance, or explicitly state the cover dependence and weaken the rhetoric.
L1	1, Table 1	LOW	The terminology table adds little mathematically and slightly obscures the standard sheaf language.	Compress or remove Table 1.
L2	6	LOW	The tetrahedral computation would be much easier to follow with a figure of the nerve and overlaps.	Add one simple schematic figure.
4. Missing references

These are the most important conceptual omissions I would flag.

Abramsky and Brandenburger, The Sheaf-Theoretic Structure of Non-Locality and Contextuality (2011). This is highly relevant because it systematically frames compatibility data and failure of global sections in sheaf-theoretic terms, which is very close in spirit to Sections 3 and 4. 
arXiv

Abramsky, Mansfield, and Barbosa, The Cohomology of Non-Locality and Contextuality (2012). This is especially important here. It uses Čech cohomology to build cohomological obstructions from compatible local data, which is precisely the conceptual neighborhood of the manuscript’s Section 4. 
arXiv

Justin Curry, Sheaves, Cosheaves and Applications (2014 thesis; circulated earlier on arXiv). Relevant for the manuscript’s combinatorial/poset viewpoint on local-to-global structure over finite bases. 
Math Department
+1

Dowling, Kalies, and Vandervorst, Continuation Sheaves in Dynamics: Sheaf Cohomology and Bifurcation (2023). If the authors want to claim a modern sheaf-theoretic dynamical-systems perspective, this is a natural reference point. 
arXiv
+1

5. Specific improvements needed to reach acceptance

The manuscript would need all of the following.

Correct the mathematical foundation of Sections 3 and 5. Right now the general setup is too broad for the proofs actually given.

Produce at least one real example where the comparison torsors and cocycle arise canonically from the stated readout semantics, rather than being imposed externally on a chosen nerve.

Sharpen the claim of originality. Either make this a genuinely expository paper, or add a theorem that is unmistakably new and nontrivial.

Repair the bibliography and literature discussion. The current placeholders and omissions are not acceptable.

Clean up notation, theorem numbering, and rhetoric about what is “intrinsic.”

The single most important mathematical change is Section 5. The single most important conceptual change is Section 6.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Contribution below the research-journal bar

Two viable paths.

First path: reframe the paper as an expository note. In that case, remove any suggestion of a new general theory, cut Section 5 down to a carefully labeled observation under explicit hypotheses, and present Section 6 as an illustration only.

Second path: turn it into a research paper. Then add at least one substantial theorem of the following sort:

a canonical construction of the comparison torsors from a natural class of readout presheaves,

an invariance theorem under cover refinement,

or a nontrivial application to a genuine symbolic/measurable model such as a sofic shift or factor map.

Without one of those, the paper does not have enough original mathematics.

B2. Gap between measurable coding and the site-theoretic setup

The clean repair is to work on the actual image shift

𝑋
a
d
m
:
=
i
m
(
𝜅
𝐿
+
)
⊆
Σ
𝐿
𝑁
,
X
adm
	​

:=im(κ
L
+
	​

)⊆Σ
L
N
	​

,

and define objects to be finite unions of trace cylinders

(
𝐶
𝑎
∩
𝑋
a
d
m
)
.
(C
a
	​

∩X
adm
	​

).

Then the site lives on the admissible symbolic system, not on the full shift. This makes the connection to Proposition 2.4 honest and avoids the false impression that Boolean operations on admissible cylinders inside 
Σ
𝑁
Σ
N
 remain unions of admissible cylinders.

If the authors prefer the current presentation, they must instead state explicit hypotheses such as prefix closure and a Boolean-closure property, and prove that those hypotheses hold in the class of models they want to cover.

B3. Proposition 5.1 is not justified as stated

The current proof uses:

Φ
∗
[
𝛼
]
=
0
  
⟹
  
𝑞
∗
[
𝛼
]
=
0
,
Φ
∗
	​

[α]=0⟹q
∗
	​

[α]=0,

where 
𝑞
:
𝐴
→
i
m
 
Φ
q:A→imΦ and 
Φ
=
𝑖
∘
𝑞
Φ=i∘q with 
𝑖
:
i
m
 
Φ
↪
∏
𝑟
𝐴
/
𝑁
𝑟
i:imΦ↪∏
r
	​

A/N
r
	​

.

That implication is not automatic. It would follow if the induced map

𝑖
∗
:
𝐻
2
(
𝑈
,
i
m
 
Φ
)
→
𝐻
2
 ⁣
(
𝑈
,
∏
𝑟
𝐴
/
𝑁
𝑟
)
i
∗
	​

:H
2
(U,imΦ)→H
2
(U,
r
∏
	​

A/N
r
	​

)

were injective, but no such injectivity is proved, and it fails in general because 
𝐻
2
(
𝑈
,
−
)
H
2
(U,−) may contain an 
E
x
t
(
𝐻
1
(
𝑁
(
𝑈
)
)
,
−
)
Ext(H
1
	​

(N(U)),−) contribution.

A repair is possible if the authors impose a hypothesis such as

𝐻
1
(
𝑁
(
𝑈
)
;
𝑍
)
=
0
H
1
	​

(N(U);Z)=0

or at least torsion-free, so that 
𝐻
2
(
𝑈
,
−
)
H
2
(U,−) behaves like 
H
o
m
(
𝐻
2
(
𝑁
(
𝑈
)
)
,
−
)
Hom(H
2
	​

(N(U)),−) on coefficients. Under such a hypothesis, the inclusion on coefficients does induce an injection on 
𝐻
2
H
2
, and the argument can be salvaged.

If the authors do not want extra hypotheses, they should withdraw the general claim and replace Section 5 by a weaker statement that is actually proved.

B4. Section 6 is not a genuine model of the advertised semantics

The manuscript itself says the comparison data are prescribed directly on the nerve. That makes Section 6 a combinatorial cocycle exercise, not a demonstration that the readout-presheaf formalism captures a real obstruction in recursive addressing.

A proper fix would be:

choose an explicit presheaf 
𝑅
R over a concrete symbolic system,

define 
𝐶
𝑜
𝑚
𝑝
𝑖
𝑗
Comp
ij
	​

 as actual comparison torsors between local objects,

define the composition maps 
𝑚
𝑖
𝑗
𝑘
m
ijk
	​

 canonically,

and then compute the resulting defect class.

If the authors cannot do that, Section 6 should be labeled explicitly as an ad hoc toy model and should not be used as evidence for the broader program.

M1. Definition 4.5 needs precise axioms

Replace “
𝐴
A-equivariant composition” by an explicit rule such as

𝑚
𝑖
𝑗
𝑘
(
𝑎
⋅
𝜉
,
  
𝑏
⋅
𝜂
)
=
(
𝑎
+
𝑏
)
⋅
𝑚
𝑖
𝑗
𝑘
(
𝜉
,
𝜂
)
,
m
ijk
	​

(a⋅ξ,b⋅η)=(a+b)⋅m
ijk
	​

(ξ,η),

for all 
𝑎
,
𝑏
∈
𝐴
a,b∈A, together with associativity on quadruple overlaps.

Then isolate the representative-change calculation as a short lemma:
if 
𝛾
𝑖
𝑗
′
=
𝛽
𝑖
𝑗
⋅
𝛾
𝑖
𝑗
γ
ij
′
	​

=β
ij
	​

⋅γ
ij
	​

, prove directly that

𝛼
′
=
𝛼
+
𝛿
𝛽
.
α
′
=α+δβ.

This will make the defect class construction mathematically precise rather than implicit.

M2. Replace placeholders and broaden literature positioning

Every “[?, ?]” must be removed. Add at least the four works listed above, with a sentence in the introduction explaining how this paper differs from each of them:

classic topos/descent references,

global-section obstruction literature,

Čech-cohomological obstruction literature,

and modern sheaf-theoretic work in dynamics/combinatorics. 
arXiv
+3
arXiv
+3
arXiv
+3

M3. Editorial and cross-reference cleanup

Use \label and \ref consistently and do a theorem-number pass. Specifically:

fix Proposition/Theorem mismatches,

standardize the label of 7.4,

define the dual notation for 
𝐴
v
i
s
A
vis
	​

 unambiguously,

and check every internal forward/backward reference after recompilation.

This is easy to fix but currently distracting.

M4. Clarify dependence on the chosen cover and data

Right now Section 5 speaks as if 
𝐴
v
i
s
A
vis
	​

 is intrinsically attached to the phenomenon. In fact it is attached to a fixed cover 
𝑈
U, a fixed comparison datum, and the resulting class 
[
𝛼
]
[α].

There are two acceptable ways to fix this.

One is to prove a refinement theorem: if 
𝑈
′
U
′
 refines 
𝑈
U, compare the pulled-back defect classes and show how 
𝐴
v
i
s
A
vis
	​

 behaves functorially.

The other is to weaken the prose everywhere and say explicitly: “for a fixed finite cover and fixed comparison datum, one obtains a quotient 
𝐴
v
i
s
(
𝑈
,
𝛼
)
A
vis
	​

(U,α).”

That would make the claims accurate.

Overall, I would encourage the authors to decide what paper they want this to be. Right now it sits awkwardly between a careful expository note and a research article, and that ambiguity hurts both the presentation and the contribution.