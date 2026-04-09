<!-- oracle metadata: {"timestamp": "2026-04-02T12:13:39.336330", "model": "o3-mini-high", "response_length": 22077} -->

Overall assessment: REJECT. The manuscript is ambitious and contains a substantial amount of formal scaffolding, but it is not publishable in its present form. The main problems are not merely expository. Several central claims are either under-justified, dependent on undefined or unstable placeholders, or stated at a level of generality far beyond what is actually proved. In particular, the paper repeatedly invokes standard results with placeholder citations “[? ]”, unresolved cross-references “(??)”, and undeclared hypotheses at exactly the points where the logical burden is highest. As a result, the current version does not provide a verifiable proof chain for Theorems A, B, and C. 

main

 

main

A second major issue is conceptual compression. The paper tries to combine: forcing semantics, site-theoretic sheafification, stacks and gerbes, banded gerbe obstruction theory, the universal coefficient sequence, character-theoretic visibility, multi-branch comparison theorems, refinement dynamics, and contextuality. That could work only if each interface were proved with extreme care. Instead, several transitions are asserted too quickly: from presheaf semantics to realization prestacks, from component stacks to gerbes, from Čech cocycles to derived 
𝐻
2
H
2
, from class-admissible characters to intrinsic visibility quotients, and from unique-branch semantics to Abramsky-Brandenburger contextuality. The result is a manuscript with potentially interesting ideas, but without the level of mathematical closure required for journal publication. 

main

 

main

 

main

Novelty rating for each theorem

Theorem 4.6 / Theorem A component “sheafification characterizes compatible local sectionability”: MEDIUM. The formulation is natural and useful in the paper’s semantics, but it is close to the standard description of sheafification by matching families; the novelty lies mainly in packaging it into the paper’s semantic layer language. 

main

Theorem 4.29 / Theorem A “forcing necessity”: MEDIUM. The separation idea is interesting, but the proof currently relies on a very tailored automorphism construction and does not yet establish the strongest possible undefinability claim with full precision. 

main

Theorem 4.31 / 4.35 / Theorem B “branched gerbe semantics”: MEDIUM-HIGH. The component-gerbe viewpoint is potentially original and conceptually promising, but the current proof architecture is incomplete because the passage from realization prestack to obstruction-theoretic gerbe semantics depends on strong hidden assumptions and unresolved references. 

main

Theorem 4.37 / 4.38 / 4.41 on strict visible quotients and strictification budgets: MEDIUM. These are mathematically clean quotient-universal-property arguments, but they are elementary once the subgroup 
𝐻
𝛼
H
α
	​

 is defined. 

main

Theorem 4.47 / 4.49 / 4.56 / Theorem C “homological visibility”: HIGH. This is the strongest and most original part of the manuscript. The use of the universal coefficient sequence to distinguish 
𝐻
2
H
2
-visible and Ext-type blind parts is conceptually strong. However, the present exposition still leaves gaps at the Čech/simplicial/derived interface and in the semantic interpretation of the algebraic quotient. 

main

Theorems 4.67-4.77 on multi-branch aggregation: MEDIUM. The lattice-theoretic quotient comparisons are neat, but once branchwise subgroups 
𝐾
𝑣
K
v
	​

 are available, the proofs are straightforward group theory. 

main

Theorem 4.80 on comparison with Abramsky-Brandenburger: MEDIUM. Potentially significant as an interpretive bridge, but not yet rigorous enough because the contextuality specialization is imposed at the level of assumptions rather than derived with adequate care. 

main

Theorem A.1 on complexity upper bounds: LOW. Routine once the finite encoding is assumed. 

main

Issue table
ID	Section	Severity	Description	Suggested fix
B1	Throughout	BLOCKER	The manuscript contains unresolved citations “[? ]” and unresolved internal references “(??)” in theorem statements, proofs, and the introduction. This makes the logical chain unverifiable.	Replace every placeholder with precise theorem/section references and bibliographic entries before submission.
B2	4.3-4.7	BLOCKER	The realization-prestack to branched-gerbe pipeline is not fully justified. The paper shows a split prestack exists, but the later obstruction theory needs a gluing-sensitive lift with global conservativity and branch obstruction classes. This existence/interface is not proved.	State and prove a separate existence theorem for gluing-sensitive realization prestacks under explicit hypotheses, or weaken later claims to conditional propositions.
B3	4.7 / Theorem 4.35	BLOCKER	The equivalence between gluing-level absence and “every component gerbe is non-neutral” relies on global conservativity plus component-gerbe neutrality, but the bridge from global sections of 
𝐹
𝑝
,
𝑠
F
p,s
	​

 to neutrality of some 
𝐺
𝑣
G
v
	​

 is only conditional on assumptions that are too strong and insufficiently motivated.	Make the theorem conditional in the statement title, isolate the exact hypotheses used, and prove necessity and sufficiency separately with no hidden dependence on stackification artifacts.
B4	4.10 / Theorem 4.47, 4.49, 4.54	BLOCKER	The homological visibility theorem mixes Čech cochains on a cover, simplicial cochains on the nerve, and universal coefficient maps for 
𝐻
2
(
𝑁
(
𝑈
)
,
𝐴
)
H
2
(N(U),A), but the comparison maps are not stated carefully enough.	Add a formal setup section fixing one cohomology model and proving the identifications used.
B5	4.12 / Theorem 4.80	BLOCKER	The connection to Abramsky-Brandenburger contextuality is asserted at a very high level. The support presheaf identification, measurement-cover site, and realization-prestack assumptions are not enough by themselves to justify the claimed equivalence without more explicit translation.	Add a dedicated proposition translating each contextuality notion into the paper’s semantic language, then derive Theorem 4.80 from those propositions.
M1	2	MEDIUM	The conservative-extension formalism is clean, but too abstractly detached from the later constructions. The paper never fully instantiates the data 
𝑒
𝑚
,
𝑛
e
m,n
	​

, 
𝑈
𝑛
,
𝑚
U
n,m
	​

, and 
𝜋
𝑛
,
𝑚
π
n,m
	​

 for all layers 
𝐿
0
⪯
⋯
⪯
𝐿
4
L
0
	​

⪯⋯⪯L
4
	​

.	Add a proposition explicitly defining the embeddings, forgetful maps, and state projections for each adjacent pair of layers.
M2	4.2 / Theorem 4.6	MEDIUM	The proof appeals to “standard site-theoretic description of sheafification” but does not verify that the local families defined in 4.4(ii) match the exact matching-family equivalence relation used by sheafification.	Expand the proof with an explicit bijection between compatible local families modulo refinement and elements of 
𝑎
𝑝
,
𝑠
𝐹
𝑝
,
𝑠
(
𝑎
)
a
p,s
	​

F
p,s
	​

(a).
M3	4.6 / Theorem 4.29	MEDIUM	The undefinability theorem proves indistinguishability only for a constrained class of Form1-formulas and within a custom-built model. As written, the “in particular” conclusion is stronger than what the proof transparently establishes.	Reformulate as non-definability under automorphism-invariant pointwise semantics, or strengthen the statement by a genuine back-and-forth argument.
M4	4.7 / Theorem 4.34	MEDIUM	The Čech gerbe obstruction theorem assumes 
𝐻
1
(
𝑈
𝑖
,
𝐴
)
=
𝐻
1
(
𝑈
𝑖
𝑗
,
𝐴
)
=
0
H
1
(U
i
	​

,A)=H
1
(U
ij
	​

,A)=0, but the dependence on this hypothesis and the cofinality condition is not cleanly organized.	Separate the theorem into: existence of local objects, existence of transition isomorphisms, cocycle construction, independence of choices, and neutrality criterion.
M5	4.8-4.10	MEDIUM	The paper introduces two quotient theories: strict visible quotient 
𝐴
/
𝐻
𝛼
A/H
α
	​

 and intrinsic visible quotient 
𝐴
/
𝐾
𝜔
A/K
ω
	​

. The semantic meaning of the difference is not explained sharply enough before the algebra develops.	Insert a proposition explicitly stating that 
𝐻
𝛼
H
α
	​

 is presentation-level chain visibility and 
𝐾
𝜔
K
ω
	​

 is cycle-level class visibility.
M6	4.10 / Proposition 4.54	MEDIUM	The sentence “evaluation of a cocycle on cycles is precisely the map in the universal coefficient theorem associated with that class” is too compressed to serve as proof.	Provide an explicit derivation via the cochain-level universal coefficient pairing.
M7	5	MEDIUM	The refinement-dynamics section is under-integrated with the earlier obstruction theory. Many definitions are given, but only one substantive theorem, 5.12, connects refinement to branch visibility.	Either cut Section 5 substantially or add concrete propositions showing how refinement changes 
𝑉
𝑖
𝑠
𝑝
,
𝑠
(
𝑟
)
Vis
p,s
	​

(r), 
𝐾
𝑣
K
v
	​

, and 
𝐴
𝑣
𝑣
𝑖
𝑠
A
v
vis
	​

 in nontrivial examples.
L1	1, 6	LOW	The introduction and conclusion overstate what has been proved.	Tone down claims of complete answers and emphasize conditionality.
L2	4.4	LOW	“typed readout” is semantically motivated but mathematically thin.	Shorten or move to a semantic remarks section.
L3	Appendix	LOW	Complexity claims are detached from the rest of the paper and likely belong in a separate note unless used centrally.	Compress to a remark or move to supplementary material.
Missing references

The reference apparatus is currently incomplete because many citations are placeholders. At minimum, the following bodies of work must be cited precisely, with theorem-level references where used:

Kripke semantics / Beth / Fitting / Goldblatt / Tierney / Johnstone for the forcing and topos-semantics background explicitly invoked in the introduction and conclusion. 

main

 

main

Stacks Project, Tag 02ZP and Tag 06NY, already mentioned informally, but the exact role must be cited precisely for stackification and gerbe facts. 

main

 

main

Giraud, non-abelian cohomology / gerbes, for the banded-gerbe classification and the neutrality-versus-
𝐻
2
H
2
 correspondence.

SGA 4 or standard sheaf-theory references for sheafification via matching families and Čech-to-derived comparison.

Universal coefficient theorem references at the exact level used for finite nerves and coefficients in finite abelian groups.

Finite abelian Pontryagin duality / character separation for the repeated annihilator arguments. These are used centrally in Theorems 4.47, 4.48, and 4.68. 

main

 

main

Abramsky-Brandenburger contextuality and subsequent cohomological-obstruction literature, including the “blind cases” attributed to Carù, with exact citations. 

main

 

main

Papadimitriou-Yannakakis for DP in the appendix. 

main

Specific improvements needed to reach acceptance

The paper needs a major structural revision.

First, it must choose one primary theorem. At present, Theorems A, B, and C are presented as co-equal pillars, but the strongest and most original mathematics is in Theorem C. The forcing-layer and branched-gerbe layers should be streamlined to serve that result. The current text spends too much space on formal semantic infrastructure whose later use is only partial.

Second, the paper needs a strict separation between proved unconditional results and results conditional on chosen realization prestacks, cofinal gerbe-adapted covers, global conservativity, branch constancy, and finite nerve presentations. Right now those hypotheses are scattered and easy to miss. The reader cannot tell which statements are formal, which are existential, and which are conditional on auxiliary models. 

main

 

main

Third, the cohomological model must be fixed rigorously. The manuscript currently alternates among:

presheaf/sheaf semantics on a site,

stackification on a slice site,

Čech cohomology on covers,

simplicial cohomology on finite nerves,

derived 
𝐻
2
H
2
,

universal coefficient exact sequence,

character duality on finite abelian coefficient groups.

That is workable only with a dedicated technical subsection specifying comparison isomorphisms and assumptions under which they hold. Without that, the heart of Theorem C remains too implicit. 

main

Fourth, the contextuality comparison should be reduced in ambition unless the translation is made fully explicit. The current theorem reads more like a research program statement than a finished theorem.

Fifth, the unresolved cross-references and placeholder citations must be completely eliminated. In the current state, the paper is not refereable in a normal sense because too many dependencies are hidden behind “??” and “[?]”. That alone is sufficient for rejection.

Concrete fixes
B1. Unresolved citations and cross-references

Problem. Placeholder citations and “??” references appear inside theorem statements and proofs.

Concrete fix.
Before any resubmission, every theorem/proposition/corollary must be renumbered and all references resolved. For example, the introduction currently says:

𝐿
0
⪯
𝐿
1
⪯
𝐿
2
⪯
𝐿
3
⪯
𝐿
4
L
0
	​

⪯L
1
	​

⪯L
2
	​

⪯L
3
	​

⪯L
4
	​


and refers to preservations by “(??)”. Replace this by explicit references to Proposition 2.3 and Corollary 2.4, and do the same everywhere else. Likewise, every “[? ]” must become a precise bibliographic citation with theorem or section number where possible. Until this is done, the paper is not in reviewable form. 

main

B2. Existence of gluing-sensitive realization prestacks

Problem. Proposition 4.10 gives a canonical split prestack, but later theorems need much more: global conservativity at 
𝑎
a, meaningful component gerbes, and branch obstruction classes.

Concrete fix.
Insert a new theorem after Proposition 4.10 of the following form:

Theorem. Let 
𝐹
𝑝
,
𝑠
∣
𝐶
𝑎
F
p,s
	​

∣
C
a
	​

	​

 be a sheaf of sets on 
𝐶
𝑎
C
a
	​

, and let 
𝐴
A be an abelian sheaf on 
𝐶
𝑎
C
a
	​

. Suppose there exists an 
𝐴
A-banded stack 
𝐿
𝑟
L
r
	​

 on 
𝐶
𝑎
C
a
	​

 together with an isomorphism 
𝜋
0
(
𝐿
𝑟
)
≅
𝑎
(
𝐹
𝑝
,
𝑠
∣
𝐶
𝑎
)
π
0
	​

(L
r
	​

)≅a(F
p,s
	​

∣
C
a
	​

	​

) and a functor 
𝑃
𝑟
→
𝐿
𝑟
P
r
	​

→L
r
	​

 from a prestack 
𝑃
𝑟
P
r
	​

 satisfying 
𝜋
0
𝑝
𝑟
𝑒
(
𝑃
𝑟
)
≅
𝐹
𝑝
,
𝑠
∣
𝐶
𝑎
π
0
pre
	​

(P
r
	​

)≅F
p,s
	​

∣
C
a
	​

	​

 and essential surjectivity on the terminal fiber 
𝑎
a. Then the conclusions of Theorems 4.31 and 4.35 hold.

This does two things. It removes any implicit claim that the split prestack suffices, and it makes the later branch-obstruction theory honestly conditional on the additional structure actually needed.

B3. Repair Theorem 4.35

Problem. The current theorem bundles several equivalences at once.

Concrete fix.
Split it into three propositions.

Compatible local sections versus visible branches

𝑀
,
𝑝
⊩
C
o
m
p
S
e
c
s
𝑠
(
𝑟
)
  
⟺
  
𝑉
𝑖
𝑠
𝑝
,
𝑠
(
𝑟
)
≠
∅
.
M,p⊩CompSecs
s
	​

(r)⟺Vis
p,s
	​

(r)

=∅.

Proof: combine Theorem 4.6 with Theorem 4.16.

Global sections versus neutral component gerbes, conditional on global conservativity:

𝑀
,
𝑝
⊩
S
e
c
s
(
𝑟
)
  
⟺
  
∃
𝑣
∈
𝑉
𝑖
𝑠
𝑝
,
𝑠
(
𝑟
)
 with 
𝐺
𝑣
(
𝑎
)
≠
∅
.
M,p⊩Secs(r)⟺∃v∈Vis
p,s
	​

(r) with G
v
	​

(a)

=∅.

Then add a lemma:

𝐺
𝑣
(
𝑎
)
≠
∅
  
⟺
  
𝐺
𝑣
 is neutral
.
G
v
	​

(a)

=∅⟺G
v
	​

 is neutral.

The nontrivial direction needs the definition of neutrality used in this paper.

Then conclude:

N
u
l
l
g
l
u
e
𝑠
(
𝑟
)
  
⟺
  
𝑉
𝑖
𝑠
𝑝
,
𝑠
(
𝑟
)
≠
∅
 
&
 
∀
𝑣
,
 
𝐺
𝑣
 non-neutral
.
Nullglue
s
	​

(r)⟺Vis
p,s
	​

(r)

=∅ & ∀v, G
v
	​

 non-neutral.

This avoids hiding multiple logical steps inside one theorem.

B4. Fix the cohomology model behind Theorem C

Problem. The paper moves too quickly from a Čech obstruction presentation to a simplicial class on the nerve and then to the universal coefficient exact sequence.

Concrete fix.
Add a subsection titled “Cohomological conventions for finite nerve presentations” containing:

If 
𝑈
=
{
𝑎
𝑖
→
𝑎
}
𝑖
∈
𝐼
U={a
i
	​

→a}
i∈I
	​

 is a finite cover whose nerve 
𝑁
(
𝑈
)
N(U) is finite and if the band 
𝐴
A is trivialized on 
𝑈
U, then there is a canonical identification

𝐶
ˇ
𝑛
(
𝑈
,
𝐴
)
≅
𝐶
𝑛
(
𝑁
(
𝑈
)
,
𝐴
)
C
ˇ
n
(U,A)≅C
n
(N(U),A)

between Čech cochains and simplicial cochains.

Under this identification, the branch obstruction cocycle 
𝑔
=
(
𝑔
𝑖
𝑗
𝑘
)
g=(g
ijk
	​

) defines a class

𝜔
∈
𝐻
2
(
𝑁
(
𝑈
)
,
𝐴
)
.
ω∈H
2
(N(U),A).

The universal coefficient exact sequence is

0
→
E
x
t
1
(
𝐻
1
(
𝑁
(
𝑈
)
,
𝑍
)
,
𝐴
)
→
𝐻
2
(
𝑁
(
𝑈
)
,
𝐴
)
→
𝜂
𝐴
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
,
𝑍
)
,
𝐴
)
→
0.
0→Ext
1
(H
1
	​

(N(U),Z),A)→H
2
(N(U),A)
η
A
	​

	​

Hom(H
2
	​

(N(U),Z),A)→0.

Define

𝑒
𝑣
𝜔
:
=
𝜂
𝐴
(
𝜔
)
.
ev
ω
	​

:=η
A
	​

(ω).

Then, in Proposition 4.54, explicitly prove that for a cocycle representative 
𝛼
α,

𝛼
♯
(
𝑧
)
=
∑
𝜎
𝑛
𝜎
𝛼
(
𝜎
)
,
𝑧
=
∑
𝜎
𝑛
𝜎
𝜎
∈
𝑍
2
(
𝑁
(
𝑈
)
,
𝑍
)
α
♯
(z)=
σ
∑
	​

n
σ
	​

α(σ),z=
σ
∑
	​

n
σ
	​

σ∈Z
2
	​

(N(U),Z)

depends only on the homology class of 
𝑧
z because 
𝛿
𝛼
=
0
δα=0, and that the induced map 
𝐻
2
→
𝐴
H
2
	​

→A is exactly 
𝑒
𝑣
𝜔
ev
ω
	​

. That proof should not be compressed into a single sentence.

B5. Strengthen or weaken Theorem 4.80

Problem. The contextuality bridge is currently too broad.

Concrete fix.
Add an intermediate proposition:

Proposition. In a finite Abramsky-Brandenburger scenario with support presheaf 
𝑆
𝑒
S
e
	​

, for the site 
𝐶
𝑎
C
a
	​

 arising from the measurement cover, compatible families of 
𝑆
𝑒
S
e
	​

 are exactly the objects interpreted by 
C
o
m
p
S
e
c
s
𝑠
(
𝑟
)
CompSecs
s
	​

(r), and global sections of 
𝑆
𝑒
S
e
	​

 are exactly the objects interpreted by 
S
e
c
s
(
𝑟
)
Secs(r).

Then Theorem 4.80(i)-(iii) becomes immediate. For (iv)-(v), explicitly state that these are consequences of the unique-branch assumption together with Theorems 4.47 and 4.56. Without this intermediate proposition, the theorem reads as an analogy rather than a derived result.

M1. Instantiate the conservative-extension chain

Problem. Section 2 defines conservative extension abstractly, but the later layers are never fully instantiated.

Concrete fix.
Add a theorem in Section 2 or 3:

Proposition. For each adjacent pair 
𝐿
𝑖
⪯
𝐿
𝑖
+
1
L
i
	​

⪯L
i+1
	​

, define the language embedding 
𝑒
𝑖
,
𝑖
+
1
e
i,i+1
	​

, forgetful functor 
𝑈
𝑖
+
1
,
𝑖
U
i+1,i
	​

, and state projection 
𝜋
𝑖
+
1
,
𝑖
π
i+1,i
	​

. Then condition (1) of Definition 2.2 holds.

Even a schematic proof is needed. Otherwise the four-layer chain is more announced than proved. 

main

M2. Expand Theorem 4.6

Problem. The proof is too short for such a foundational interface theorem.

Concrete fix.
Write the bijection explicitly. Let 
𝑎
=
[
𝑟
]
𝑝
a=[r]
p
	​

. Show:

a section of 
𝑎
𝑝
,
𝑠
𝐹
𝑝
,
𝑠
a
p,s
	​

F
p,s
	​

 over 
𝑎
a is represented by a pair 
(
{
𝑎
𝑖
→
𝑎
}
,
𝜎
𝑖
)
({a
i
	​

→a},σ
i
	​

) where 
𝜎
𝑖
∈
𝐹
𝑝
,
𝑠
(
𝑎
𝑖
)
σ
i
	​

∈F
p,s
	​

(a
i
	​

) is a matching family,

two such families are equivalent iff they agree on a common refinement,

this matches Definition 4.4(ii) exactly.

That gives a complete proof rather than an appeal to sheaf folklore.

M3. Repair the strength of Theorem 4.29

Problem. The proof only treats formulas invariant under a chosen automorphism and excluding local-object predicates.

Concrete fix.
Restate the conclusion precisely as:

“No formula of the Form1-language, interpreted pointwise and invariant under automorphisms of the Form1-reduct, can define 
C
o
m
p
S
e
c
s
𝑠
CompSecs
s
	​

, 
S
e
c
s
Secs, or 
N
u
l
l
g
l
u
e
𝑠
Nullglue
s
	​

.”

If the stronger undefinability claim is intended, then prove a proper back-and-forth theorem between two pointed structures with the same Form1-theory but different 
𝐿
2
L
2
	​

-behavior.

M4. Clean up Theorem 4.34

Problem. Too many logically distinct steps are merged.

Concrete fix.
Rewrite the proof in this sequence:

𝐺
𝑣
G
v
	​

 locally nonempty on 
𝑈
𝑖
U
i
	​

, choose 
𝑥
𝑖
∈
𝐺
𝑣
(
𝑈
𝑖
)
x
i
	​

∈G
v
	​

(U
i
	​

).

I
s
o
m
(
𝑥
𝑖
∣
𝑈
𝑖
𝑗
,
𝑥
𝑗
∣
𝑈
𝑖
𝑗
)
Isom(x
i
	​

∣
U
ij
	​

	​

,x
j
	​

∣
U
ij
	​

	​

) is an 
𝐴
∣
𝑈
𝑖
𝑗
A∣
U
ij
	​

	​

-torsor.

Since 
𝐻
1
(
𝑈
𝑖
𝑗
,
𝐴
)
=
0
H
1
(U
ij
	​

,A)=0, choose 
𝜑
𝑖
𝑗
φ
ij
	​

.

Define

𝑔
𝑖
𝑗
𝑘
=
𝜑
𝑖
𝑘
−
1
𝜑
𝑗
𝑘
𝜑
𝑖
𝑗
∈
𝐴
(
𝑈
𝑖
𝑗
𝑘
)
.
g
ijk
	​

=φ
ik
−1
	​

φ
jk
	​

φ
ij
	​

∈A(U
ijk
	​

).

Verify 
𝛿
𝑔
=
0
δg=0 on quadruple overlaps.

Show changes of 
𝜑
𝑖
𝑗
φ
ij
	​

 alter 
𝑔
g by a coboundary.

Show changes of 
𝑥
𝑖
x
i
	​

 alter 
𝑔
g by a coboundary using 
𝐻
1
(
𝑈
𝑖
,
𝐴
)
=
0
H
1
(U
i
	​

,A)=0.

Prove neutrality iff 
[
𝑔
]
=
0
[g]=0.

This will make the proof readable and checkable.

M5. Explain the meaning of 
𝐻
𝛼
H
α
	​

 versus 
𝐾
𝜔
K
ω
	​


Problem. The distinction is important but under-motivated before the algebra begins.

Concrete fix.
Add a short proposition before Definition 4.44:

𝐻
𝛼
=
Im
⁡
(
𝛼
~
:
𝐶
2
(
𝑁
(
𝑈
)
,
𝑍
)
→
𝐴
)
,
𝐾
𝜔
=
Im
⁡
(
𝑒
𝑣
𝜔
:
𝐻
2
(
𝑁
(
𝑈
)
,
𝑍
)
→
𝐴
)
.
H
α
	​

=Im(
α
~
:C
2
	​

(N(U),Z)→A),K
ω
	​

=Im(ev
ω
	​

:H
2
	​

(N(U),Z)→A).

Then explain in prose:

𝐻
𝛼
H
α
	​

 records values seen by the chosen presentation on all 2-chains.

𝐾
𝜔
K
ω
	​

 records values that survive homology and hence belong intrinsically to the class.

This would greatly clarify the later comparison theorems. 

main

 

main

M6. Shorten or integrate Section 5

Problem. Section 5 is currently more of a framework extension than a tightly used part of the paper.

Concrete fix.
Either:

remove most of 5.1-5.2 and keep only Theorem 5.12 plus one interpretive remark, or

add a worked example showing a refinement 
𝑞
≤
𝑝
q≤p with explicit branch pullback and strict inequality

𝐾
𝑤
⊊
𝐾
𝑣
,
𝐴
𝑤
𝑣
𝑖
𝑠
↠
𝐴
𝑣
𝑣
𝑖
𝑠
.
K
w
	​

⊊K
v
	​

,A
w
vis
	​

↠A
v
vis
	​

.

As written, the refinement section dilutes the paper’s focus.

Recommendation

The paper should be rejected in its current form, but there is a potentially publishable core. The strongest route to a viable revision is:

center the paper on Theorem C and the intrinsic visible quotient 
𝐴
𝜔
𝑣
𝑖
𝑠
A
ω
vis
	​

,

retain only the minimum semantic and gerbe machinery needed to make that theorem meaningful,

make every auxiliary assumption explicit and local,

fully repair the cohomological foundations and all citations.

That version could become a serious paper. The present version is not yet mathematically closed enough for acceptance.