<!-- oracle metadata: {"timestamp": "2026-04-11T09:49:44.263699", "model": "chatgpt-5.4-pro-extended", "response_length": 9935} -->

1. Overall assessment

Reject

The manuscript is readable and Section 2 is conceptually clean, but in its current form it does not meet the threshold for a journal research article. The paper itself says that Theorem 1.1 is classical, Theorem 1.4 is known background, and that the only new mathematics is the fixed-DFA obstruction in Section 2 and its two consequences. That leaves a very small original core, and that core is essentially an immediate application of a standard density dichotomy plus the prime number theorem. More importantly, the Zeckendorf part contains a real logical problem: Corollary 3.4 is not established by Theorem 3.1 as stated, because 
𝜋
(
𝑇
)
∼
𝑇
/
log
⁡
𝑇
π(T)∼T/logT is compatible with 
𝑇
1
+
𝑜
(
1
)
T
1+o(1)
. 

main

I do not see a fundamental correctness problem in Section 2. My negative recommendation is driven by contribution level, positioning, and the unsupported Section 3 deduction. 

main

2. Novelty rating for each theorem

Theorem 1.1: LOW. This is a restatement of a classical density dichotomy, and the authors explicitly say so. 

main

Theorem 2.2: LOW. Same content as Theorem 1.1, now proved in the body. It is standard transfer-matrix / Perron-Frobenius material. 

main

Theorem 1.4: LOW. Explicitly labeled “Known” and presented as contextual background only. 

main

Theorem 3.1: LOW. Same known Zeckendorf growth statement as Theorem 1.4, restated in the body. 

main

For completeness, the genuinely new numbered claims appear to be Proposition 2.4 and Corollaries 2.5 and 2.6. I would still rate all three LOW in novelty. They are neat observations, but they are very short corollaries of Theorem 2.2 plus 
∣
𝑃
𝑚
(
𝑏
)
∣
≍
𝑏
𝑚
/
𝑚
∣P
m
(b)
	​

∣≍b
m
/m. 

main

3. Issue table

The table below is based on the manuscript’s current framing of novelty in Sections 1 to 3, and on the proof chain around Theorem 3.1, Corollary 3.4, and Remark 3.5. 

main

ID	Section	Severity	Description	Suggested fix
B1	Sections 1 to 2	BLOCKER	The original contribution is too slight for a journal article. All theorem-labeled results are known/restatements, and the new content is basically Proposition 2.4 plus two direct corollaries.	Either add a substantially stronger theorem, or radically compress and reposition this as a brief note for a lower-threshold venue.
B2	Section 3, Cor. 3.4 and Rem. 3.5	BLOCKER	Corollary 3.4 is not implied by Theorem 3.1. The case 
𝛼
=
1
α=1 in 
𝑇
𝛼
+
𝑜
(
1
)
T
α+o(1)
 still allows 
𝑇
/
log
⁡
𝑇
T/logT. Remark 3.5 therefore also lacks support.	Delete Section 3, or replace it with a correct proof or a correct citation to prior work.
M1	Abstract, Cor. 1.2, Cor. 2.5	MEDIUM	The constant 
𝑐
𝑏
c
b
	​

 is ambiguous. The notation suggests dependence only on 
𝑏
b, but the proof uses automaton-dependent constants 
𝑐
𝑟
c
r
	​

.	Rename it 
𝑐
𝐴
,
𝑏
c
A,b
	​

, or rewrite the proof so the constant really depends only on 
𝑏
b.
M2	Introduction and Section 3	MEDIUM	Too much space is devoted to known material, and the known material is duplicated between the introduction and body. This inflates the paper and obscures what is actually new.	Compress Theorem 1.1/2.2 and Theorem 1.4/3.1, and remove or move Section 3 to an appendix.
M3	Section 1.2	MEDIUM	Literature positioning is incomplete. Important prior work on primes and S-recognizability, density of automatic sets, and primes along automatic sequences is missing.	Add the missing references and explain exactly what the paper adds beyond them.
M4	Section 2	MEDIUM	The paper does not discuss sharpness. The 
Ω
(
𝑏
𝑚
/
𝑚
)
Ω(b
m
/m) lower bound is optimal up to constants, and the proof of Cor. 2.6 actually yields more quantitative information than the statement advertises.	Add a sharpness remark and explicit examples showing optimality of both types of bounds.
L1	Proof of Cor. 2.6	LOW	The jump from residue-wise exponential decay to global exponential decay is compressed too much.	Add one sentence selecting a uniform 
𝜃
<
1
θ<1 over the finitely many residue classes.
L2	Overall scope	LOW	The Zeckendorf section is thematically disconnected from the core base-
𝑏
b result.	Remove it, or unify the paper around a genuine regular-numeration-systems theorem.
4. Missing references

The most important omissions are these:

Michel Rigo, Generalization of automatic sequences for numeration systems on a regular language, Theoret. Comput. Sci. 244 (2000), 271 to 281. This is the single most important missing citation. The abstract states that for any numeration system 
𝑆
S, the set of primes is never 
𝑆
S-recognizable, which directly bears on the Zeckendorf discussion and likely subsumes the manuscript’s Corollary 3.4. 
dblp
+1

Jason P. Bell, The upper density of an automatic set is rational, J. Théor. Nombres Bordeaux 32 (2020), 585 to 604. This is a modern density reference closely related to the manuscript’s density theme. 
Numdam

Clemens Müllner, Automatic sequences fulfill the Sarnak conjecture, Duke Math. J. 166 (2017), no. 17, 3219 to 3290. This is directly relevant to the manuscript’s discussion of primes in automatic settings, and its abstract explicitly mentions a prime number theorem for a broad class of automatic sequences. 
Project Euclid
+1

Boris Adamczewski, Michael Drmota, Clemens Müllner, (Logarithmic) densities for automatic sequences along primes and squares, Trans. Amer. Math. Soc. 375 (2022). This is highly relevant to any discussion of densities of automatic sequences along primes. 
American Mathematical Society
+1

Jason P. Bell, Thomas F. Lidbetter, Jeffrey Shallit, Additive Number Theory via Approximation by Regular Languages, Int. J. Found. Comput. Sci. 31 (2020), 667 to 687. This is thematically close to the paper’s regular-approximation viewpoint in a number-theoretic setting. 
dblp
+1

5. Specific improvements needed to reach acceptance

First, Section 3 must be removed or corrected. As written, that part is not mathematically supported.

Second, the manuscript needs a much stronger originality claim than it currently has. For a standard journal, cosmetic tightening is not enough. The authors need either a materially stronger theorem beyond fixed DFA, or a serious extension to a broader numeration/automata setting.

Third, the paper must be repositioned honestly against prior work. At present it under-cites the literature most directly adjacent to its claims, especially on S-recognizability of primes and on primes along automatic sequences.

Fourth, Section 2 should explicitly discuss sharpness and clean up the constant dependence in Corollary 2.5.

6. Concrete fixes for each BLOCKER and MEDIUM issue

B1. Insufficient novelty

Actionable fix: choose one of these two routes.

Short-note route. Delete Section 3 entirely. Compress the classical material to one preliminary proposition with references. Present Proposition 2.4 and Corollaries 2.5 to 2.6 as a short observation of 4 to 5 pages.

Research-article route. Add a genuinely stronger theorem. Plausible directions would be fixed NFA, bounded-ambiguity automata, automata families with controlled state growth in 
𝑚
m, or extension to regular numeration systems beyond full base-
𝑏
b shifts.

For a standard journal, only the second route is likely sufficient.

B2. Invalid deduction in Section 3

Actionable fix: do not deduce non-regularity of the prime Zeckendorf language from Theorem 3.1 as currently stated.

The easiest repair is:

Replace Corollary 3.4 by a literature statement citing Rigo 2000.

Reword the section as “known background”.

Make Remark 3.5 depend on that external result instead of on Theorem 3.1. 
dblp
+1

If the authors insist on a self-contained Section 3, they must prove a stronger theorem than 3.1. The current exponent-only statement is too weak to exclude 
𝑇
/
log
⁡
𝑇
T/logT.

M1. Ambiguous constant 
𝑐
𝑏
c
b
	​


Actionable fix:

Either change every occurrence of 
𝑐
𝑏
c
b
	​

 to 
𝑐
𝐴
,
𝑏
c
A,b
	​

, and add one sentence stating dependence on the automaton.

Or keep 
𝑐
𝑏
c
b
	​

 and make the proof genuinely uniform in 
𝐴
A. In the 
𝑐
𝑟
>
0
c
r
	​

>0 case, once 
𝑚
m is large enough, 
(
𝑐
𝑟
/
4
)
𝑏
𝑚
≥
(
𝐴
/
2
)
𝑏
𝑚
/
𝑚
(c
r
	​

/4)b
m
≥(A/2)b
m
/m, so the same base-dependent lower-bound constant can be used after increasing the threshold.

M2. Overdeveloped known material

Actionable fix:

In the introduction, state Theorem 1.1 and Theorem 1.4 informally and cite the literature.

In the body, keep only the minimum needed proof skeleton for Theorem 2.2.

Delete Section 3, or move it to an appendix labeled explicitly as non-original background.

M3. Incomplete literature positioning

Actionable fix:

Add a paragraph separating four strands: classical density of regular languages, approximation by regular languages, primes along automatic sequences, and S-recognizable sets.

Cite Rigo 2000 for “primes are never S-recognizable”. Cite Bell 2020 for modern density behavior of automatic sets. Cite Müllner 2017 and Adamczewski-Drmota-Müllner 2022 for primes/densities along automatic sequences. Cite Bell-Lidbetter-Shallit 2020 for number theory via regular approximation. 
dblp
+6
DBLP
+6
arXiv
+6

M4. No sharpness discussion

Actionable fix:

Add a remark immediately after Corollary 2.5 saying the 
Ω
(
𝑏
𝑚
/
𝑚
)
Ω(b
m
/m) bound is optimal up to constants, because 
𝐿
=
∅
L=∅ gives 
∣
𝐿
𝑚
△
𝑃
𝑚
(
𝑏
)
∣
=
∣
𝑃
𝑚
(
𝑏
)
∣
≍
𝑏
𝑚
/
𝑚
∣L
m
	​

△P
m
(b)
	​

∣=∣P
m
(b)
	​

∣≍b
m
/m.

Add a positive-density example, such as words ending in 0, to show why an 
Ω
(
𝑏
𝑚
)
Ω(b
m
) bound naturally appears on arithmetic progressions.

Strengthen Corollary 2.6 by stating the quantitative estimate already proved in the text, namely 
P
r
e
c
𝑚
=
𝑂
(
1
/
𝑚
)
Prec
m
	​

=O(1/m) on positive-density progressions.

My bottom line is this: Section 2 has the seed of a publishable short observation, but the current manuscript is padded by known material, under-positioned in the literature, and weakened by an unsupported Section 3.