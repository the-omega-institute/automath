<!-- oracle metadata: {"timestamp": "2026-04-08T09:43:42.951014", "model": "chatgpt-5.4-pro-extended", "response_length": 11731} -->

Overall assessment

Major revision

There is a potentially strong paper here, but not yet a publishable one. The finite-state Markov-hole core, especially the exact killed-matrix formula for depth-
𝑚
m Bayes error and its identification with the escape exponent, is interesting and plausibly new in the specific “finite observation detects open-system invariants” sense. However, the current version has two serious problems: one headline formula has the wrong sign, and the Hölder/block-recoding extension is not established at the same level of rigor as the finite-state part. In addition, the manuscript is materially overextended relative to what the paper itself says is its true center of gravity, namely Section 6. 

main

 

main

Most importantly, Theorem 1.3/6.4 states the dominant pole as 
𝑧
𝐻
=
𝜌
𝐻
−
1
=
𝑒
𝑃
𝑌
𝐻
(
𝜙
)
−
𝑃
𝑌
(
𝜙
)
z
H
	​

=ρ
H
−1
	​

=e
P
Y
H
	​

	​

(ϕ)−P
Y
	​

(ϕ)
. But Theorem 6.1 gives 
−
log
⁡
𝜌
𝐻
=
𝑃
𝑌
(
𝜙
)
−
𝑃
𝑌
𝐻
(
𝜙
)
−logρ
H
	​

=P
Y
	​

(ϕ)−P
Y
H
	​

	​

(ϕ), hence 
𝜌
𝐻
=
𝑒
𝑃
𝑌
𝐻
(
𝜙
)
−
𝑃
𝑌
(
𝜙
)
ρ
H
	​

=e
P
Y
H
	​

	​

(ϕ)−P
Y
	​

(ϕ)
 and therefore 
𝜌
𝐻
−
1
=
𝑒
𝑃
𝑌
(
𝜙
)
−
𝑃
𝑌
𝐻
(
𝜙
)
ρ
H
−1
	​

=e
P
Y
	​

(ϕ)−P
Y
H
	​

	​

(ϕ)
. The displayed pole formula has the exponent reversed. Since this is a headline theorem and tied to the phrase “reciprocal escape factor,” it is a blocker. 

main

 

main

Novelty rating for each theorem

I rate the substantive theorem statements once. Theorems 1.1, 1.2, and 1.3 are summary versions of later detailed statements, so their ratings are inherited from Theorems 6.3, 7.1, and 6.4/6.5 respectively. 

main

Theorem	Rating	One-line justification
4.6	LOW	Standard sliding-block/factor-collapse machinery, useful but not conceptually new.
4.9	LOW	Standard inverse-limit and ultrametric singleton-intersection argument.
4.11	LOW	Classical complete inverse-limit reconstruction/homeomorphism statement in this notation.
5.4	LOW	Discrete Tanaka decomposition applied to a conditional-probability martingale.
5.8	LOW	Straight boundary-mass estimate once cylinder weights are controlled.
5.9	MEDIUM	A useful weighted product-automaton formulation, but the mechanism is standard finite-state/Markov technology.
6.1	HIGH	This is the real contribution: finite-depth Bayes error is linked explicitly to killed dynamics and recovers escape rate.
6.3	MEDIUM	A meaningful refinement of 6.1, but obtained by standard Perron-Frobenius/quasistationary asymptotics once the formula is known.
6.4	MEDIUM	The cyclotomic lift is neat, but after writing the residue lift the spectral statement is mostly linear algebra.
6.5	LOW	As stated, it reads as a standard Hölder/block-recoding extension of the finite-state result, and the novelty is not isolated from the proof burden.
7.1	MEDIUM	Natural thermodynamic consequence of the killed-matrix partition sum, with a useful conditioned-law interpretation.
7.3	LOW	Standard Chen-Stein/occupancy argument, not a new dynamical theorem.
7.5	LOW	Standard entropy bookkeeping via relative entropy and conditional entropy identities.
7.7	LOW	Essentially convexity plus injective lifting, with limited dynamical novelty.
Issue table
ID	Section	Severity	Description	Suggested fix
B1	1.3, 6.4	BLOCKER	Dominant pole formula has the wrong sign. This is a headline mathematical error.	Correct all occurrences of the pole formula and audit every downstream statement using it.
B2	6.5	BLOCKER	The Hölder/block-recoding extension is not proved at publication level. Several key operator-theoretic steps are asserted too quickly.	Either fully prove it with precise Banach spaces and theorem-level citations, or remove/demote it from the main results.
M1	Introduction, references	MEDIUM	Literature positioning is incomplete, especially relative to prior work on subsystems of finite type, pressure-gap asymptotics, and Poisson limits.	Add a comparison paragraph explaining exactly what is new here and what is inherited from earlier open-system/hitting-time work.
M2	Title, abstract, Introduction	MEDIUM	The manuscript overpromises breadth. Secondary themes are presented as coequal with the core theorem.	Reframe title/abstract around the Markov-hole Bayes-error/escape-rate theorem, and clearly demote secondary consequences.
M3	Overall organization	MEDIUM	Theorem hierarchy is not sharp. The strongest result is 6.1, then 6.3. Several later results are consequences, not coequal main theorems.	Reorganize theorem numbering and introduction around one main theorem plus refinements/corollaries.
M4	Section 4	MEDIUM	Long supplementary structural material is disproportionate to its role in the paper.	Move most of Section 4 to an appendix, or compress it radically.
M5	Section 7.3	MEDIUM	Hidden-information/injective-refinement material is weakly connected to the ETDS core and mathematically elementary relative to Sections 6 and 7.1.	Remove it, or move it to an appendix/companion note.
M6	6.1	MEDIUM	The residue non-degeneracy hypothesis is central but not operationally packaged for the reader.	State verifiable sufficient conditions, plus an example where the hypothesis fails.
L1	3.3	LOW	The Sturmian illustration is peripheral to the main open-system/Markov story.	Shorten to a remark or remove.
L2	Throughout	LOW	The paper front-loads notation and machinery before reaching the main theorem.	Delay nonessential notation and add a brief notation roadmap.

The focus-related medium issues are not merely stylistic. The introduction explicitly says Section 6 is the “center of gravity,” and describes the resolvent material, Section 4 background, and the final subsection of Section 7 as supplementary. That strongly supports substantial cutting or relocation of those parts. 

main

Missing references

The most important omission is the Chazottes-Coelho-Collet line of work. They already study subsystems of finite type, higher-block reduction, pressure-difference asymptotics, and marked Poisson processes. That does not make the present Bayes-error observable redundant, but it narrows the novelty zone and must be confronted directly. 
University of York
+2
arXiv
+2

At minimum, I would add the following.

Chazottes, Coelho, Collet, Poisson processes for subsystems of finite type in symbolic dynamics, Stochastics and Dynamics 9 (2009), 393–422. Very close context for subsystems of finite type, higher-block reduction, pressure-gap scaling, and Poisson asymptotics. 
University of York
+1

Chazottes, Coelho, Collet, On the asymptotic measure of periodic subsystems of finite type in symbolic dynamics (2008, arXiv:0804.2551). Relevant for asymptotics of 
𝜇
(
Δ
𝑛
)
μ(Δ
n
	​

) versus restricted pressure, especially periodic versus aperiodic survivor subsystems. 
arXiv

Bruin, Demers, Todd, Hitting and escaping statistics: mixing, targets and holes (2018). Useful modern context for the relation between hitting statistics and escape statistics. 
St Andrews Research Repository

Freitas, Freitas, Todd, Speed of convergence for laws of rare events and escape rates (2015). Relevant context for convergence-rate issues in rare-event and escape laws. 
IDEAS/RePEc

Haydn, Yang, Local escape rates for 
𝜙
ϕ-mixing dynamical systems (2020). Relevant modern context for escape-rate asymptotics beyond the finite-state setting. 
Cambridge University Press & Assessment

Specific improvements needed to reach acceptance

Fix the mathematical error in Theorem 1.3/6.4. This must be done before anything else.

Decide what the paper actually is. Either it is a finite-state Markov-hole paper, in which case it can be shorter and stronger, or it is a finite-state plus Hölder/open-Ruelle paper, in which case Section 6.5 needs a real proof.

Reposition the novelty. The genuine novelty seems concentrated in the finite-observation/Bayes-error link to escape rates and quasistationary amplitudes, not in the supplementary structural sections or the Chen-Stein appendix-level material.

Rewrite the introduction and abstract. The current title and framing make the paper look broader and deeper than the proven core.

Trim or relocate supplementary material. Section 4 and Section 7.3 should not occupy this much space in an ETDS submission unless they are indispensable, and they are not presented that way by the manuscript itself. 

main

Make the main assumptions reader-checkable. In particular, residue non-degeneracy needs concrete criteria and examples.

Concrete fixes for each BLOCKER and MEDIUM issue

B1. Wrong sign in dominant pole formula.
Action: replace every occurrence of

𝑧
𝐻
=
𝜌
𝐻
−
1
=
𝑒
𝑃
𝑌
𝐻
(
𝜙
)
−
𝑃
𝑌
(
𝜙
)
z
H
	​

=ρ
H
−1
	​

=e
P
Y
H
	​

	​

(ϕ)−P
Y
	​

(ϕ)

by

𝑧
𝐻
=
𝜌
𝐻
−
1
=
𝑒
𝑃
𝑌
(
𝜙
)
−
𝑃
𝑌
𝐻
(
𝜙
)
=
𝑒
𝛾
𝐻
(
𝜙
)
.
z
H
	​

=ρ
H
−1
	​

=e
P
Y
	​

(ϕ)−P
Y
H
	​

	​

(ϕ)
=e
γ
H
	​

(ϕ)
.

Then add a one-line consistency check in the proof: since 
𝜌
𝐻
=
𝑒
−
𝛾
𝐻
(
𝜙
)
<
1
ρ
H
	​

=e
−γ
H
	​

(ϕ)
<1, the smallest positive real pole of the resolvent must be 
𝑒
𝛾
𝐻
(
𝜙
)
>
1
e
γ
H
	​

(ϕ)
>1, not 
𝑒
−
𝛾
𝐻
(
𝜙
)
e
−γ
H
	​

(ϕ)
. Recheck the abstract, introduction, theorem statements, and final remarks. 

main

 

main

B2. Theorem 6.5 not at publication-level rigor.
Action: choose one of two paths.

Path A, recommended. Remove Theorem 6.5 from the headline results, keep only the exact finite-state theory, and relegate the Hölder extension to a short conjectural remark or “expected extension” paragraph.

Path B. Keep Theorem 6.5, but add a full subsection that precisely defines the function spaces, the backward operator, the open operator, the pairing on the natural extension, the spectral-gap assumptions, and the exact theorem used to identify the isolated spectrum with that of the forward open Ruelle operator. Also prove, not just assert, the Hölder regularity of the residue-hit probability functions 
𝑝
𝑟
−
p
r
−
	​

.

M1. Literature positioning incomplete.
Action: add a dedicated introduction paragraph comparing the paper to Chazottes-Coelho-Collet on subsystems of finite type and to the later hitting/escape literature. Explicitly say: “our new observable is Bayes error under finite observation,” then explain why that is not already contained in existing pressure-gap and Poisson-process results. 
Cambridge University Press & Assessment
+5
www-users.york.ac.uk
+5
arXiv
+5

M2. Title/abstract overpromise.
Action: retitle around the core result. For example: Finite Observation and Escape Rates for Markov Holes in Mixing Shifts of Finite Type. In the abstract, keep the exact finite-state theorem first, state the amplitude refinement second, and either drop the Hölder extension or present it as conditional/supplementary.

M3. Theorem hierarchy unclear.
Action: make 6.1 the main theorem in the introduction. Present 6.3 as the main refinement. Present 6.4 as an exact algebraic corollary. Present 7.1 and 7.3 as secondary consequences.

M4. Section 4 too long.
Action: compress Section 4 to a 1 to 2 page appendix, or replace it by one proposition stating the only fact later used, with proof deferred or referenced.

M5. Section 7.3 off-focus.
Action: remove it from the main text, or move it to a very short appendix. If retained, explain in one paragraph why ETDS readers need it for the dynamical story.

M6. Residue non-degeneracy too abstract.
Action: add a lemma giving graph-theoretic sufficient conditions, for example in terms of safe-state accessibility to hole states with two different residue classes. Then add one short worked example where the condition holds and one where it fails.

My bottom line is this: the paper should be revised around Sections 6.1 and 6.3. If the authors fix the sign error, either fully prove or substantially demote the Hölder extension, and trim the non-core material, the manuscript could become a serious submission.