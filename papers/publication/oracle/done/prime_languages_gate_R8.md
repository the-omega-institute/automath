<!-- oracle metadata: {"timestamp": "2026-04-10T12:41:44.218920", "model": "chatgpt-5.4-pro-extended", "response_length": 10180} -->

Referee report on the attached manuscript. 

main

1. Overall assessment

Reject

The note is readable and the Section 2 argument looks essentially correct, but in its present form I do not think it is strong enough for journal publication. The manuscript itself says that Theorem 1.1 is a specialized reproof, Theorem 1.4 is known, and the genuinely new content is the fixed-DFA approximation obstruction in Section 2. That leaves the paper resting almost entirely on a very short corollary package from a classical density dichotomy plus the prime number theorem. In addition, the literature positioning is incomplete, and one central headline sentence overstates the logic by calling two different consequences “equivalent.” 

main

 
Springer
+2
ResearchGate
+2

2. Novelty rating for each main result

I include the proposition and corollaries, because they carry the substantive claims. These ratings reflect both the manuscript’s own prior-work section and the surrounding literature. 

main

 
Springer
+2
ResearchGate
+2

Result	Novelty	One-line justification
Theorem 1.1 / 2.2 (density dichotomy for DFA languages)	LOW	The manuscript itself labels this a specialized reproof of classical transfer-matrix / regular-language density behavior.
Proposition 2.3 (quantitative recall/precision obstruction)	LOW	This is a direct inequality chase from the definitions of recall and precision once (
Corollary 1.2 / 2.4 (symmetric-difference lower bound)	MEDIUM	The exact 
Ω
(
2
𝑚
/
𝑚
)
Ω(2
m
/m) formulation may be new in this wording, but it is a very short consequence of the classical dichotomy and prime-slice asymptotics.
Corollary 1.3 / 2.5 (no simultaneous recall and precision)	MEDIUM	The recall/precision phrasing is likely the most publishable point, but mathematically it is still a near-immediate corollary once Theorem 2.2 is available.
Theorem 1.4 / 3.1 (regular Zeckendorf languages have power-law growth)	LOW	The manuscript explicitly marks this as known, and it sits inside the broader S-recognizable growth literature.
Corollary 1.5 / 3.4 (prime Zeckendorf language is not regular)	LOW	This is an immediate consequence of the known growth theorem plus the prime number theorem.
Remark 3.5 (eventual sofic realization excluded)	LOW	This is an immediate finite-symmetric-difference argument once Corollary 3.4 is in place.
3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Whole paper, especially §1.2 and Section 2	BLOCKER	The publishable novelty is too thin for a journal article. By the paper’s own account, Theorem 1.1 is classical, Theorem 1.4 is known, and only the Section 2 obstruction is new.	Either substantially strengthen the main theorem, or recast the paper as a much shorter note with a much narrower claim.
B2	Abstract and Introduction	BLOCKER	The manuscript says the recall/precision obstruction and the symmetric-difference lower bound are “equivalent.” As stated, they are not equivalent. Large symmetric difference alone does not rule out recall and precision both being bounded away from zero.	Rewrite this as two separate consequences of the density dichotomy.
M1	Section 3, title, abstract	MEDIUM	Too much of the paper is explicitly known supporting context, which makes the manuscript feel padded and broadens the title beyond the actual new content.	Compress Section 3 to a remark or appendix, or add a genuinely new Zeckendorf result.
M2	§1.2 and bibliography	MEDIUM	Important related work on densities of regular languages and regular approximations is missing or underemphasized.	Add the missing references and explain precisely what is and is not new here.
M3	Bibliography, ref. [5]	MEDIUM	The Sin’ya entry is incorrect. The manuscript points to arXiv:1509.06823, but the actual paper is arXiv:2008.01413 / SOFSEM 2021, and arXiv:1509.06823 is unrelated.	Replace the bibliography entry with the correct paper and identifier.
M4	§1 and §3 notation	MEDIUM	The Zeckendorf digit order is nonstandard and not stated clearly. This is especially confusing because the binary section uses leading-digit language.	State the digit order explicitly on first use, or rewrite Section 3 in standard most-significant-digit order.
M5	§1.2 prior-work discussion	MEDIUM	The sentence saying prime Zeckendorf nonregularity is “a special case of Rigo’s theorem” is too vague to be useful editorially or mathematically.	Cite the exact theorem that implies it, or remove the attribution and keep only the self-contained proof.
M6	Section 2 scope	MEDIUM	The restriction to base 2 looks artificial. The argument appears to extend with minimal changes to any fixed base.	Generalize to base 
𝑏
b, or explain clearly why the paper intentionally stays binary.
L1	Section 2	LOW	There is no brief sharpness discussion or concrete example showing the two extremal behaviors in the dichotomy.	Add one short remark with examples.
L2	Title and framing	LOW	The title sounds broader than the actual new contribution.	Retitle to focus on fixed-DFA approximation of binary primes.
4. Missing references

The most important omissions are:

Jean Berstel, Sur la densité asymptotique de langages formels (1973).

Manuel Bodirsky, Tobias Gärtner, Timo von Oertzen, Jan Schwinghammer, Efficiently Computing the Density of Regular Languages (LATIN 2004).

Brendan Cordy and Kai Salomaa, On the existence of regular approximations (TCS 2007).

Pierre Lecomte and Michel Rigo, Numeration systems on a regular language (foundational for the abstract-numeration framing).

The correct Sin’ya paper: Asymptotic Approximation by Regular Languages, arXiv:2008.01413, later at SOFSEM 2021. 
ACM Digital Library
+5
Numdam
+5
Springer
+5

5. Specific improvements needed to reach acceptance

The paper needs one of two paths.

First, substantially stronger new mathematics. The cleanest path would be to extend the obstruction beyond the current binary-DFA setting, for example to arbitrary fixed bases, or to a broader finite-state/numeration framework, or to a sharper optimal statement that is not essentially a one-page corollary of a classical density theorem.

Second, much tighter and more modest presentation. If the authors do not add stronger results, then the paper should be reduced to a short note centered only on the genuinely new Section 2 consequence, with the classical density theorem cited rather than reproved in full, and the Zeckendorf material compressed to a brief contextual remark. In its current article-length form, the ratio of new mathematics to known material is too low. 

main

Independently of that choice, the abstract and introduction must be made logically exact, the bibliography must be repaired, and the prior-work section must situate the result against the existing density and approximation literature. 
Springer
+2
ResearchGate
+2

6. Concrete fixes for each BLOCKER and MEDIUM issue

B1. Novelty too thin

Actionable solution: either

add a genuinely stronger theorem, or

cut the paper to a short note of about 4 to 6 pages and present the new contribution honestly as a concise corollary-style observation.

A good strengthening target would be: prove the same obstruction for every fixed base, or for a natural class of regular numeration systems, or for a stronger approximation metric.

B2. False “equivalently” claim

Actionable solution: replace the abstract sentence by something like:

“From the density dichotomy we derive two consequences: first, no fixed DFA can have recall and precision both bounded away from zero on infinitely many lengths; second, every fixed DFA language has symmetric difference at least 
𝑐
 
2
𝑚
/
𝑚
c2
m
/m from the binary prime slice for all sufficiently large 
𝑚
m.”

That wording is correct and preserves the actual content.

M1. Section 3 is too large relative to new content

Actionable solution: move Theorem 3.1 and its proof to an appendix, and reduce the main-text Zeckendorf discussion to a short paragraph. If the authors want Section 3 in the main body, then Section 3 needs a new result, not only known context.

M2. Missing literature

Actionable solution: add a dedicated prior-work paragraph separating three strands:

density / accumulation-point results for regular languages,

regular approximation frameworks,

abstract numeration / S-recognizable growth results.

Then explain in one or two sentences what the present paper adds beyond each strand. 
arXiv
+3
Springer
+3
ResearchGate
+3

M3. Incorrect Sin’ya bibliography entry

Actionable solution: replace the current item with the correct entry for Ryoma Sin’ya, “Asymptotic Approximation by Regular Languages,” arXiv:2008.01413, and preferably cite the SOFSEM 2021 version as well. Remove arXiv:1509.06823 from this entry, because that identifier belongs to an unrelated paper, Davide Fusi, “On rational varieties of small degree.” 

main

 
arXiv
+2
ACM Digital Library
+2

M4. Zeckendorf notation is unclear

Actionable solution: add an explicit sentence at first use, for example:

“We write Zeckendorf words least-significant digit first, so 
𝑤
=
𝑥
1
⋯
𝑥
𝑚
w=x
1
	​

⋯x
m
	​

 represents 
∑
𝑘
=
1
𝑚
𝑥
𝑘
𝐹
𝑘
+
1
∑
k=1
m
	​

x
k
	​

F
k+1
	​

, and the condition 
𝑥
𝑚
=
1
x
m
	​

=1 means that the most significant nonzero digit is 1.”

Or else rewrite the notation in standard most-significant-digit order.

M5. Vague Rigo attribution

Actionable solution: either give the exact theorem number and exact statement from the cited source that implies the claim about primes in the Zeckendorf / abstract-numeration setting, or delete that sentence and let the self-contained proof stand on its own.

M6. Binary restriction looks artificial

Actionable solution: rewrite Theorem 2.2 and its consequences for an alphabet of size 
𝑏
b, normalize by 
𝑏
𝑚
b
m
, and state the prime-language corollary for base-
𝑏
b expansions. If the authors intentionally want only base 2, they need one sentence in the introduction explaining why the binary case is singled out.

My bottom line is simple: the paper contains a neat observation, but it is currently framed as more substantial than it is. To become publishable, it needs either significantly stronger mathematics or a much leaner and more honest short-note presentation.