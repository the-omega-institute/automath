<!-- oracle metadata: {"timestamp": "2026-04-12T04:26:45.761012", "model": "chatgpt-5.4-pro-extended", "response_length": 11896} -->

1. Overall assessment

Reject.

The manuscript is admirably candid that almost all of the paper is expository and that the only genuinely new claim is the hidden-Markov/sofic theorem in Section 5.3. Unfortunately, that is exactly where the manuscript currently fails. The main formal class in Definition 5.6 does not match the flagship even-shift example, the counting formula in Theorem 5.7(3) is incorrect as written, and Example 6.3 collapses under the stated fair Bernoulli measure because the even-shift event has measure zero. With Section 5.3 in its current form, the paper is not publishable. Without Section 5.3, what remains is mostly a clean repackaging of standard identities and straightforward corollaries. 

main

There is a readable core here, and Example 6.4 is a nice construction, but the central theorem needs a substantial reworking before the paper can be considered again.

2. Novelty rating for each theorem-level claim

I am rating each numbered proposition/corollary/theorem.

Claim	Novelty	One-line justification
Proposition 2.2	LOW	Standard characterization of partition-measurable sets as unions of atoms/clopen cylinders.
Proposition 3.1	LOW	Classical Bayes risk decomposition on a finite partition.
Proposition 3.2	LOW	Standard threshold/Bayes-optimal classifier statement.
Corollary 3.3	LOW	Immediate consequence of partition refinement and Bayes optimality.
Proposition 4.1	LOW	A clean reformulation, but essentially a discrete convexity identity plus martingale orthogonality.
Proposition 5.2	LOW	Tautological factorization 
𝜀
𝑚
=
𝐴
𝑚
𝜃
𝑚
ε
m
	​

=A
m
	​

θ
m
	​

.
Proposition 5.3	LOW	Direct corollary of Proposition 5.2 under uniform cylinder upper bounds.
Proposition 5.4	LOW	Straightforward two-sided estimate once thickness and comparability are assumed.
Proposition 5.5	LOW	Simple rearrangement of Proposition 5.3.
Theorem 5.7	MEDIUM	This is the only potentially new bridge from finite-state ambiguous-state graphs to scan-error decay, but the graph-counting and Perron-Frobenius ingredients are classical and the present statement is not yet correct.
Proposition 5.9	LOW	Same argument as Proposition 5.4 with polynomial distortion factors.
3. Issue table

The issues below refer to the manuscript as written, especially Definition 5.6, Theorem 5.7, and Examples 6.2-6.7. 

main

ID	Section	Severity	Description	Suggested fix
B1	5.3, 6.3	BLOCKER	Definition 5.6 does not match Example 6.3. The definition sets 
𝑃
=
⋃
𝑤
∈
𝐿
(
𝑀
)
[
𝑤
]
P=⋃
w∈L(M)
	​

[w], so 
𝑃
P is a prefix-accepted cylinder union, hence an open event. The even shift in Example 6.3 is an infinite-word safety property, not of this form.	Either narrow the theorem to absorbing prefix-decision automata and delete Example 6.3, or replace Definition 5.6 by a correct automata-on-infinite-words or finite-state posterior-state formalism.
B2	5.7(3), 6.3	BLOCKER	The count formula is wrong. 
𝑁
𝑚
(
∂
𝑃
)
=
1
⊤
𝐵
∂
𝑚
1
N
m
	​

(∂P)=1
⊤
B
∂
m
	​

1 ignores the initial state and accessible component. At 
𝑚
=
0
m=0 it gives (	H
B3	6.3	BLOCKER	Example 6.3 is invalid under the stated measure. Under fair Bernoulli measure on 
{
0
,
1
}
𝑁
{0,1}
N
, the even-shift event has measure 
0
0: the gaps between successive 1s are a.s. infinitely many, and each gap is even with probability 
2
/
3
2/3, so the probability all are even is 
0
0. Thus 
∂
𝑚
𝑃
∂
m
	​

P is empty measure-theoretically and 
𝜀
𝑚
=
0
ε
m
	​

=0.	Remove this example or replace it with a genuine positive-measure hidden-Markov factor example.
B4	5.7(2)	BLOCKER	The automatic-thickness proof is not established. Primitivity of 
𝐵
∂
B
∂
	​

 does not by itself imply a uniform length 
𝐿
L from each ambiguous state to both decision outcomes, and in the current setup “reaching 
𝐹
F” is not the right notion for infinite-word events anyway.	Prove a separate bounded-reachability lemma under the corrected model, then derive thickness from Parry cylinder lower bounds.
M1	1.2, 5.3	MEDIUM	Related work is incomplete for the main theorem. The current citations cover symbolic dynamics and probabilistic automata on finite words, but not the classical “functions/probabilistic functions of Markov chains” literature or automata on infinite words, both directly relevant here.	Add foundational references and explain precisely what is new beyond them.
M2	Intro, 3-5.2	MEDIUM	The paper is too long relative to the genuinely new content. Since almost everything before Section 5.3 is standard, the manuscript reads more like an expository synthesis than a research note.	Compress Sections 2-5.2 substantially, or move routine material to a short preliminaries section or appendix.
M3	5.3	MEDIUM	The symbolic setup is not precise enough. The paper overloads 
𝐴
A for alphabet and adjacency matrix, does not clearly specify the path/cylinder model, and the proof of Theorem 5.7(1) only shows dependence on terminal state, not the stated iff criterion.	Clean up notation, define the product-state process explicitly, and prove 
0
<
𝜇
(
𝑃
∣
[
𝑤
]
)
<
1
0<μ(P∣[w])<1 iff the terminal state is ambiguous.
M4	6, 7	MEDIUM	Measure-theoretic boundary and topological possibility are conflated. This is harmless in some examples but fatal in Example 6.3.	Insert a warning that “boundary” always means positive mass on both sides, then re-audit every example under that convention.
L1	4	LOW	“Local time” language in Proposition 4.1 is heavier than the proof warrants.	Recast it as a Tanaka-style identity rather than a local-time theorem.
L2	Throughout	LOW	Notation is crowded, especially 
𝐴
A versus 
𝐴
𝑚
(
𝑃
;
𝜇
)
A
m
	​

(P;μ).	Rename the alphabet or adjacency matrix.
L3	6	LOW	The examples section is larger than the theorem support currently justifies.	Keep the best examples, especially 6.4 and 6.6, and shorten the rest after repairing Section 5.3.
4. Missing references

Two strands are importantly missing.

First, if Section 5.3 is meant to sit inside the classical hidden-Markov / probabilistic-function-of-Markov-chain literature, then at least Blackwell (1957), Heller (1965), and Baum-Petrie (1966) should be cited and discussed. These are foundational references for processes and probabilistic functions derived from finite-state Markov chains. 
MathNet
+2
Project Euclid
+2

Second, if the intended event class is really an automata class on infinite words rather than a prefix-hitting class on finite words, then standard references such as Thomas, “Automata on Infinite Objects” (1990) and Perrin-Pin, Infinite Words (2004) are essential. Kitchens (1998) would also be a useful standard symbolic-dynamics reference for topological Markov shifts and factor maps. 
ScienceDirect
+2
Cambridge University Press & Assessment
+2

5. Specific improvements needed to reach acceptance

Repair Section 5.3 completely. The paper stands or falls with a correct version of Theorem 5.7. Right now the main theorem is not stated for the class used by the main example, and one of its key formulas is false.

Replace Example 6.3 with a valid positive-measure example. This is not a cosmetic correction. The current example directly contradicts the paper’s own measure-theoretic boundary definition.

Sharpen the contribution. If the only original result is one finite-state theorem, then the rest of the manuscript should be compressed aggressively. A publishable version should make the new theorem, its exact assumptions, and its nontrivial consequences the clear center of gravity.

Clarify the formal model. The paper needs to decide whether it is about:

prefix-decided events generated by absorbing automata on finite words, or

genuine infinite-word events recognized by omega-automata / finite-state filters.

At present it mixes these two viewpoints.

Reposition the paper in the literature. The authors need a precise paragraph saying how their corrected theorem differs from classical hidden-Markov, symbolic-dynamics, and automata-on-infinite-words frameworks.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1

Choose one of two salvage paths.

Narrow path. Restrict Definition 5.6 to an absorbing prefix-decision automaton. Define disjoint absorbing yes/no sets 
𝑅
+
R
+
	​

, 
𝑅
−
R
−
	​

, let 
𝑃
P be the event that the run hits 
𝑅
+
R
+
	​

, and define the ambiguous state set by

𝐻
=
{
𝑠
:
𝑃
𝑠
(
𝑃
)
∈
(
0
,
1
)
}
.
H={s:P
s
	​

(P)∈(0,1)}.

Then drop Example 6.3.

Broader path. If the authors want examples like the even shift, replace Definition 5.6 by a genuine automaton/filter on infinite words, with the acceptance condition stated explicitly. Then rewrite Theorem 5.7 accordingly.

B2

Introduce an initial vector 
𝑢
u for the accessible ambiguous product states, and replace

𝑁
𝑚
(
∂
𝑃
)
=
1
⊤
𝐵
∂
𝑚
1
N
m
	​

(∂P)=1
⊤
B
∂
m
	​

1

by

𝑁
𝑚
(
∂
𝑃
)
=
𝑢
⊤
𝐵
∂
𝑚
1
N
m
	​

(∂P)=u
⊤
B
∂
m
	​

1

or the equivalent accessible-subgraph count. Under primitivity of the accessible ambiguous component and 
𝑢
≠
0
u

=0, Perron-Frobenius then gives

𝑢
⊤
𝐵
∂
𝑚
1
=
𝜅
𝜌
∂
𝑚
+
𝑂
(
𝜂
𝑚
)
.
u
⊤
B
∂
m
	​

1=κρ
∂
m
	​

+O(η
m
).

This also fixes the Fibonacci example: starting from the “even” state gives 
𝐹
𝑚
+
2
F
m+2
	​

, not 
1
⊤
𝐵
𝑚
1
1
⊤
B
m
1.

B3

Delete Example 6.3 in its current form. Replace it by one of the following.

A bona fide positive-measure hidden-Markov factor example coming from a finite-state Markov chain with a deterministic output map and a nontrivial ambiguous component.

A narrower absorbing-prefix example if the theorem is restricted as above.

If the authors want to keep a Fibonacci-growth example, they should build it inside a model where the event has positive conditional mass on boundary cylinders.

B4

Prove a separate lemma of the following type.

For each ambiguous state 
𝑠
s, there exist witness words 
𝑢
𝑠
,
𝑣
𝑠
u
s
	​

,v
s
	​

 of lengths bounded by a common 
𝐿
L such that continuing by 
𝑢
𝑠
u
s
	​

 forces or guarantees a yes-outcome with probability at least 
𝛿
δ, and continuing by 
𝑣
𝑠
v
s
	​

 forces or guarantees a no-outcome with probability at least 
𝛿
δ. Because the ambiguous state set is finite, 
𝐿
L and 
𝛿
δ can be chosen uniformly. Then combine this with Parry lower bounds on admissible cylinders to derive uniform thickness.

That is the right place to use finiteness and Parry comparability. It should not be hidden inside one sentence about primitivity.

M1

Add a brief but explicit literature paragraph with the missing references above. The paragraph should answer: what do Blackwell/Heller/Baum-Petrie already provide, what do Thomas/Perrin-Pin already provide if the event class is omega-regular, and what exactly is new in the corrected theorem.

M2

Compress the standard material. A good target would be:

one short preliminaries section for Propositions 3.1-3.2 and Corollary 3.3,

one short identity section for Proposition 4.1,

then move immediately to the corrected main theorem.

As written, too much space is spent proving or restating facts that are completely standard.

M3

Clean up the symbolic notation in Section 5.3.

Use 
𝐴
A for the alphabet and 
𝐴
A for the adjacency matrix.

State clearly whether cylinders are vertex-labeled or edge-labeled.

Define the product state after a word 
𝑤
w explicitly.

Define the ambiguity function 
𝑔
(
𝑠
)
g(s) and show that 
0
<
𝑔
(
𝑠
)
<
1
0<g(s)<1 exactly on the ambiguous states.

That will also make the proof of Theorem 5.7(1) precise.

M4

Add a one-paragraph warning before the examples:

𝐶
∈
∂
𝑚
𝑃
  
⟺
  
𝜇
(
𝑃
∩
𝐶
)
>
0
 and 
𝜇
(
𝐶
∖
𝑃
)
>
0.
C∈∂
m
	​

P⟺μ(P∩C)>0 and μ(C∖P)>0.

Then re-check every example under that definition. In particular, any event of measure zero cannot produce nontrivial measure-theoretic boundary cylinders.

My editorial bottom line is this: the paper is not currently publishable, but there is a potentially salvageable result hidden in Section 5.3 if the authors rebuild the formalism, replace the invalid example, and sharply reduce the expository ballast.