<!-- oracle metadata: {"timestamp": "2026-04-12T01:48:45.752389", "model": "chatgpt-5.4-pro-extended", "response_length": 14905} -->

Referee report
1. Overall assessment

Recommendation: Reject

The manuscript has an interesting core idea. In particular, the fixed-presentation algebra around the evaluation map 
𝑒
𝑣
𝜔
ev
ω
	​

, the hidden subgroup 
𝐾
𝜔
K
ω
	​

, the quotient 
𝐴
v
i
s
𝜔
A
vis
ω
	​

, and the branch-sensitive versus branch-uniform comparison is potentially publishable. But in its current form I would not recommend acceptance. Two of the headline claims are not at publication standard. First, Theorem 4.30 is false as stated. Even without parameters, formulas using equality between free variables distinguish tuples with different equality patterns. With parameters, a formula like 
𝑥
=
𝑏
x=b distinguishes the fixed witnesses 
𝑎
𝑖
a
i
	​

. Second, Theorem 4.52 is not actually verified, and its proof appears to rely on an incorrect statement about the GHZ measurement-cover nerve being 
𝑆
2
S
2
. Proposition 4.56 also does not justify the claimed refinement-invariance of 
𝐾
𝜔
K
ω
	​

 and 
𝐴
v
i
s
𝜔
A
vis
ω
	​

. These are central defects, not local polishing issues. 

main

My editorial reading is that the paper currently overclaims. What seems solid is a conditional framework plus a promising algebraic quotient construction. What is not yet solid is the paper’s advertised strengthened undefinability theorem, the “first worked natural example,” and the claim that the visibility quotient is intrinsic under refinement. 

main

2. Novelty rating for each theorem

The theorem-numbered results in the manuscript are Theorems 4.28, 4.30, 4.52, and 4.70. The paper’s headline “Theorems A, B, C” are aggregates built from these and several propositions. 

main

Theorem	Novelty	One-line justification
Theorem 4.28	LOW	This is essentially a formal consequence of the preceding definitions and propositions on null modes and refinement.
Theorem 4.30	MEDIUM	The intended semantic non-definability statement is interesting, but the mechanism is a standard symmetry-orbit argument, and the claimed strengthening to tuples and parameters is not presently valid.
Theorem 4.52	HIGH	A correct GHZ/Mermin realization of the full gerbe layer would be the manuscript’s strongest genuinely new contribution, but the current proof does not establish it.
Theorem 4.70	MEDIUM	The “pure Ext equals character-blindness” message is conceptually nice, but mathematically it is a fairly direct universal-coefficient consequence once the setup is granted.

A fair summary at the headline level is this. Theorem A would be medium novelty if repaired. Theorem B is high novelty only if Theorem 4.52 is actually proved. Theorem C is medium novelty because its algebraic backbone is standard, while the semantic interpretation is the new part.

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Section 4.6, Theorem 4.30	BLOCKER	Theorem 4.30 is false as stated. For 
𝑚
≥
2
m≥2, equality formulas such as 
𝑥
1
=
𝑥
2
x
1
	​

=x
2
	​

 distinguish tuples with different equality patterns. With parameters, 
𝑥
=
𝑏
x=b distinguishes 
𝑎
1
a
1
	​

 from 
𝑎
2
a
2
	​

. The proof’s orbit argument only works within a single orbit type and fails for arbitrary tuples/parameters.	Rewrite the theorem. The cleanest repair is to retreat to one free variable and no parameters, or else restrict tuples to a fixed equality pattern and choose fresh witnesses outside parameter support.
B2	Section 4.10, Theorem 4.52(iv), Example 4.54	BLOCKER	The GHZ cover listed in the paper has pairwise nonempty intersections but all triple intersections are empty, so its Čech nerve is the graph 
𝐾
4
K
4
	​

, not 
∂
Δ
3
≃
𝑆
2
∂Δ
3
≃S
2
. The 
𝑆
2
S
2
-based 
𝐻
2
H
2
	​

 and fundamental-class calculations do not follow.	Recompute the nerve for the actual cover. If the intended object is not the Čech nerve but a flag complex or another refinement, define it explicitly and prove the comparison theorem.
B3	Section 4.10, Theorem 4.52(ii)-(iii)	BLOCKER	The GHZ/Mermin “verification theorem” does not verify the required hypotheses H1-H4 item by item. The construction of 
𝑃
G
H
Z
P
GHZ
	​

, the band, global conservativity, the singleton branch set, and the obstruction class are asserted in a few lines rather than proved.	Turn Section 4.10 into a real construction. Define objects, morphisms, band action, stackification map, and then prove each required hypothesis in separate lemmas.
B4	Section 4.11, Proposition 4.56	BLOCKER	The refinement-invariance proof is incomplete. From 
𝑒
𝑣
𝜔
′
=
𝑒
𝑣
𝜔
∘
𝑓
∗
ev
ω
′
	​

=ev
ω
	​

∘f
∗
	​

 one gets only 
I
m
(
𝑒
𝑣
𝜔
′
)
⊆
I
m
(
𝑒
𝑣
𝜔
)
Im(ev
ω
′
	​

)⊆Im(ev
ω
	​

), not equality, unless extra hypotheses on 
𝑓
∗
f
∗
	​

 are added.	Strengthen the hypotheses to require homology isomorphisms under refinement, or redefine 
𝐾
𝜔
K
ω
	​

 directly in a derived, presentation-independent way and prove invariance there.
B5	Whole manuscript	BLOCKER	Without B1, B2, and B3, the paper’s main advertised advances are not established. The current manuscript is therefore mostly a conditional packaging of standard tools plus a promising but not fully secured algebraic quotient story.	Re-scope the paper. Either prove the flagship claims completely, or retitle and shorten it as a conditional framework with a smaller proven core.
M1	Introduction and Section 4.6	MEDIUM	The comparison class is not stated cleanly. The text first emphasizes one free reference variable, then Theorem 4.30 jumps to finitely many free variables and parameters.	Give one formal definition of the lower comparison class and state all non-definability results relative to that exact class.
M2	Sections 4.3-4.7	MEDIUM	The key notion “gluing-sensitive realization prestack” is scattered across several definitions and hypotheses, making it hard to separate assumptions from proved results.	Consolidate the requirements into one boxed definition and rewrite the later results to refer back to it explicitly.
M3	Sections 4.11-4.12	MEDIUM	The paper does not clearly separate routine algebraic lemmas from the genuinely new semantic content. This makes the manuscript longer and the main contribution harder to evaluate.	Compress routine universal-coefficient and Pontryagin-duality consequences, and isolate the genuinely new semantic statements as theorems.
M4	Section 4.13	MEDIUM	The bridge to the standard Abramsky-Brandenburger cohomological obstruction is not made precise. The paper speaks of a formal comparison, but the relation between the usual contextuality obstruction and the paper’s 
𝐻
2
H
2
 gerbe class is not explicitly derived.	Add a comparison theorem showing exactly what data are translated, in what degree, and under which assumptions the two obstruction pictures coincide or differ.
M5	Section 5 and Appendix A	MEDIUM	The dynamics/support/complexity material is largely disconnected from the core obstruction theory and weakens the paper’s focus.	Move most of Section 5 to an appendix or separate note. Keep only what is used in the main proofs.
M6	Abstract, Introduction, Conclusion	MEDIUM	The rhetoric is too strong for the proved content. Phrases like “journal readiness repairs,” “first worked natural example,” and “intrinsic” are not yet justified.	Tone down claims until the proofs are complete, or prove the missing statements in full.
L1	Introduction	LOW	There is a visible placeholder “??” in the plan-of-paper paragraph.	Fix all unresolved placeholders.
L2	Throughout	LOW	There are encoding and typography problems that materially hurt readability.	Perform a full source cleanup and copy-edit.
L3	References	LOW	Some items are preprints or bibliographically incomplete.	Update to final versions where available and standardize citation format.
L4	Throughout	LOW	The manuscript is longer than the proved content requires.	Compress routine propositions and move secondary material out of the main line.
4. Missing references

Important omissions, especially if the GHZ/Mermin section remains central:

Greenberger, Horne, Zeilinger, original GHZ paper(s). The manuscript relies heavily on a GHZ example but only cites later sheaf-theoretic descendants.

N. D. Mermin, original GHZ/Mermin all-versus-nothing contextuality papers.

Kochen and Specker (1967). If the paper continues to situate itself in the contextuality tradition and discusses Kochen-Specker style extendability, the original source should be cited.

Brylinski, Loop Spaces, Characteristic Classes and Geometric Quantization. If the gerbe layer is retained as a core part of the paper, this is a standard gerbe reference worth adding.

The authors should also check whether the preprints cited as [12] and [23] now have final journal versions, and cite those if they exist.

5. Specific improvements needed to reach acceptance

The paper could become publishable, but only after a substantial redesign.

First, the authors need to decide what the real paper is. Right now it tries to be four papers at once: a forcing paper, a local-to-global semantics paper, a gerbe/contextuality paper, and a dynamic-support paper. For acceptance, it needs one central theorem line.

Second, Theorem 4.30 must be replaced by a correct theorem. As written, it cannot stand.

Third, the paper needs one completely verified, natural example. If the GHZ/Mermin example is kept, it must be proved from first principles, with the correct nerve and exact comparison maps. If that cannot be done, the paper should not claim an end-to-end natural realization.

Fourth, the “intrinsic” visibility quotient needs a genuinely presentation-independent proof. Until then, that terminology is premature.

Fifth, the paper should be shortened and refocused. The strongest salvageable core is the quotient theory around 
𝑒
𝑣
𝜔
ev
ω
	​

, 
𝐾
𝜔
K
ω
	​

, class-admissible characters, and branch aggregation.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Repair Theorem 4.30

A workable repair is this. Define the lower comparison class once and for all as the parameter-free, constant-free 
Σ
1
Σ
1
	​

-fragment with one free variable of sort Refs. Then prove non-definability for 
L
o
c
S
e
c
s
LocSecs, 
C
o
m
p
S
e
c
s
CompSecs, 
S
e
c
s
Secs, and 
N
u
l
l
g
l
u
e
Nullglue in that class.

If the authors insist on tuples, the theorem must be stated orbitwise. Tuples can only be compared when they have the same equality pattern. If the authors insist on parameters, they cannot use one fixed set of witnesses 
𝑎
1
,
…
,
𝑎
4
a
1
	​

,…,a
4
	​

. They need a theorem of the form: for each finite parameter set 
𝐵
B, one can choose fresh witnesses outside 
𝐵
B lying in the relevant 
𝐵
B-orbits.

B2. Repair the GHZ nerve computation

The authors should explicitly compute the intersections of the four stated contexts. On the standard GHZ cover, all triple intersections are empty. So the Čech nerve is 
𝐾
4
K
4
	​

, not 
𝑆
2
S
2
.

There are only three honest options. Use the actual nerve and redo the cohomology. Or switch to a different cover/refinement and prove that it computes the same obstruction. Or, if the intended object is really the clique complex of the overlap graph rather than the Čech nerve, define that object explicitly and justify why it is the correct one here.

B3. Make Theorem 4.52 a real theorem

Section 4.10 needs to become a full verification section. Define the slice site 
𝐶
𝑎
C
a
	​

. Define the prestack 
𝑃
G
H
Z
P
GHZ
	​

 on each object of that site. Define its morphisms and band action. Prove 
𝜋
0
p
r
e
(
𝑃
G
H
Z
)
≅
𝑆
G
H
Z
π
0
pre
	​

(P
GHZ
	​

)≅S
GHZ
	​

. Prove global conservativity as essential surjectivity of the terminal-fibre functor, not merely nonemptiness. Then compute 
V
i
s
𝑝
,
𝑠
(
𝑟
)
Vis
p,s
	​

(r) directly.

Without those steps, the GHZ theorem is only a sketch, not a theorem.

B4. Repair the “intrinsic” invariance claim

The current proof of Proposition 4.56 is not enough. The authors need one of two stronger routes.

One route is to strengthen the hypothesis on refinement so that every refinement map induces an isomorphism on the relevant 
𝐻
2
H
2
	​

. Then equality of images follows.

The other route is more conceptual. Define 
𝐾
𝜔
K
ω
	​

 directly from a presentation-independent derived object, rather than via one chosen finite nerve presentation, and prove invariance by naturality at that level. If neither route is completed, the paper should stop calling the quotient “intrinsic.”

B5. Re-scope the paper

If B1 through B4 are not all repaired, the present title and abstract are too strong. The paper should be rewritten around the part that is actually solid. A shorter paper centered on the quotient 
𝐴
v
i
s
𝜔
A
vis
ω
	​

, class-admissible characters, and branch aggregation could be viable.

M1. Clarify the lower comparison class

The paper needs one formal definition that says exactly what formulas are allowed. Equality. Parameters. Repeated variables. Free reference variables. Invariance condition. All of this should be fixed before Theorem 4.30 is stated.

M2. Consolidate the realization hypotheses

Introduce one definition, for example “gluing-sensitive realization prestack,” containing all required assumptions currently spread across Definition 4.9, Proposition 4.11, Definition 4.13, and H1-H4. Then state later theorems as “Assume a gluing-sensitive realization prestack in the sense of Definition X.”

M3. Separate routine algebra from new semantics

Sections 4.11 and 4.12 should be reorganized. Put routine algebraic lemmas in a preliminary subsection or appendix. Then elevate the genuine semantic conclusions, such as the interpretation of 
𝐾
𝜔
K
ω
	​

, the quotient detected by class-admissible characters, and the branch-sensitive/uniform comparison, into the main theorem statements.

M4. Add a precise bridge to contextuality literature

The authors should spell out how the standard support-presheaf obstruction is converted into their 
𝐻
2
H
2
 gerbe obstruction. Right now the comparison is too informal. A reader needs a theorem that says exactly what object on the Abramsky-Brandenburger side maps to what object on the present side, and in which degree.

M5. Move the dynamics section out of the main line

Unless Section 5 is used later in a substantive theorem, it should not remain in the main body. It currently reads as a separate project. Moving it to an appendix would sharpen the paper considerably.

M6. Tone down claims and rewrite the abstract

The abstract and introduction should be rewritten after the mathematics is stabilized. Claims like “first worked natural example,” “journal readiness repairs,” and “intrinsic” should appear only when the corresponding statements are fully proved.

Bottom line

I would reject this version. The paper has a potentially interesting and publishable core, but the current manuscript does not yet support its main advertised results. A substantially revised version focused on a correct theorem set, a real example, and a repaired invariance argument could be worth reconsidering.