<!-- oracle metadata: {"timestamp": "2026-04-11T14:53:44.211574", "model": "chatgpt-5.4-pro-extended", "response_length": 9980} -->

I reviewed the attached manuscript, An Explicit Self-Dual Synchronisation Kernel and Its Completed Determinant. The comments below refer to the paper’s own numbering and claims. 

main

1. Overall assessment

Major revision

The paper contains a potentially interesting explicit case study. The most substantial part is the geometric and Galois analysis of the completed curve. However, the manuscript is not ready for acceptance in its current form. There is one serious proof gap, namely the irreducibility argument in Lemma 3.5, and one later proof contains an incorrect numerical statement in Lemma 3.13. In addition, the paper does not yet make a strong conceptual case for significance beyond a single carefully chosen example. Even after repair, this reads more like a short specialized note than a broad conceptual paper.

2. Novelty rating for each theorem

Because Theorems 1.1 and 1.2 bundle quite different claims, I rate the main numbered parts separately.

Claim	Novelty	One-line justification
Theorem 1.1(i)	LOW	This is largely a direct symbolic determinant computation for one fixed 10-state matrix.
Theorem 1.1(ii)	LOW	The completed determinant and sign symmetry are formal consequences of the explicit determinant plus the self-dual change of variables.
Theorem 1.1(iii)	MEDIUM	The genus-6 normalization, genus-3 quartic quotient, and generic 
𝑆
6
S
6
	​

 computation make the example genuinely more interesting, though still very example-specific.
Theorem 1.2(i)	LOW	The degree law and evenness are straightforward from the resultant product formula and the symmetry 
Δ
^
(
𝑤
,
−
𝑠
)
=
Δ
^
(
−
𝑤
,
𝑠
)
Δ
(w,−s)=
Δ
(−w,s).
Theorem 1.2(ii)	LOW	The 
𝑚
=
2
m=2 case is a direct substitution and factorization.
Theorem 1.2(iii)	MEDIUM	The explicit asymptotic expansion through 
𝑚
−
12
m
−12
 is technically nontrivial and likely new for this kernel, but the method is standard once root separation is in place.

The later Theorems 3.10 and 3.14 are essentially internal restatements of Theorem 1.2(i) and 1.2(iii), so I would not rate them separately.

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	§3.2, Lemma 3.5; downstream Lemma 3.7 and Prop. 3.8	BLOCKER	The irreducibility proof is not valid as written. Irreducibility of 
Δ
^
(
𝑤
,
3
)
Δ
(w,3) does not by itself imply irreducibility of 
Δ
^
(
𝑤
,
𝑠
)
Δ
(w,s) in 
𝑄
[
𝑠
,
𝑤
]
Q[s,w], because a factor can specialize to a nonzero constant. This undermines the integrality and function-field setup used later.	Replace Lemma 3.5 with a rigorous proof, or prove Proposition 3.9 first and deduce irreducibility from transitivity of the generic Galois group.
M1	§3.4, Lemma 3.13, Step 1	MEDIUM	The statement “the next smallest modulus among the roots is 1” for 
Δ
^
(
𝑤
,
2
)
=
0
Δ
(w,2)=0 is false. The cubic factor 
𝑤
3
−
𝑤
2
+
𝑤
+
1
w
3
−w
2
+w+1 has a real root near 
−
0.543689
−0.543689.	Replace this by a correct root-gap computation or a rigorous bound showing every non-Perron root has modulus 
>
1
/
2
>1/2.
M2	Introduction; Definition 2.2	MEDIUM	The manuscript says the matrix comes from a “two-track comparison automaton,” but the underlying labelled graph/automaton is never actually specified. As written, the synchronization provenance is not independently reconstructible.	Either add the source labelled system and derive the 10-state recurrent core, or present the paper simply as the study of an explicit weighted 10-state digraph.
M3	Introduction; §4	MEDIUM	The paper overstates generality. It proves a detailed analysis of one ad hoc example, but phrases such as “the completed determinant of a self-dual kernel is the correct unit to study” go beyond what is established.	Narrow the claims, or add at least one genuine general proposition about self-dual kernels and completion.
M4	Throughout; Appendix A	MEDIUM	Several central steps are computer-assisted, but that status is not clearly flagged in the main text. The appendix is helpful, but editorially the proof architecture still needs a clearer audit trail.	Add a short “computer-assisted verification” paragraph, state software/versions, and provide a single supplementary code bundle.
L1	Remark 3.4; §3.3	LOW	“Completed determinant” and 
Φ
𝑚
+
Φ
m
+
	​

 are nonstandard terminology/notation and are only partially contextualized.	Introduce them earlier and compare explicitly with standard terminology.
L2	Proposition 3.9, Step 1	LOW	The phrase “discriminant of the degree-six resolvent” is inaccurate here.	Say “discriminant of 
Δ
^
(
𝑤
,
𝑠
)
Δ
(w,s) as a polynomial in 
𝑤
w.”
L3	Remark 3.15	LOW	The numerical table is useful, but the manuscript does not say clearly how the displayed 
𝜌
𝑚
ρ
m
	​

 values were computed.	Add one sentence explaining whether they come from 
𝑅
𝑚
R
m
	​

 or from the specialized factor 
Δ
^
(
𝑤
,
𝑠
𝑚
)
Δ
(w,s
m
	​

), and point to code.
4. Missing references

The clearest omission is:

H. Bass, The Ihara-Selberg zeta function of a tree lattice (1992). This is a foundational determinant-formula reference in graph-zeta theory and belongs in §1.2.

A second, more conditional gap is this: if the authors want to keep the “comparison automaton / synchronization kernel” origin as a central theme, they should cite a direct reference from the labelled-graph / fibre-product side of symbolic dynamics. Right now the citations to Lind-Marcus and Kitchens are general background, not a direct source for that construction.

I do not see many other major bibliographic omissions.

5. Specific improvements needed to reach acceptance

Repair the irreducibility and geometry chain. This is the main technical requirement.

Correct Lemma 3.13 and recheck the asymptotic argument. The current proof contains a false numerical statement.

Make the model self-contained. Either derive the 10-state kernel from an explicit source system, or stop claiming that derivation as part of the core contribution.

Reframe the paper honestly as an explicit case study. Separate what is truly general from what is special to this example.

Clarify the computer-assisted components and improve reproducibility.

Add Bass and, if needed, a direct synchronization/fibre-product reference.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Invalid irreducibility proof

Best fix: reorder the paper.

Prove Proposition 3.9 before Lemma 3.5. Once you show the generic Galois group contains a 6-cycle, the action is transitive, hence 
Δ
^
(
𝑤
,
𝑠
)
Δ
(w,s) is irreducible over 
𝑄
(
𝑠
)
Q(s). Then use Gauss’s lemma to deduce irreducibility in 
𝑄
[
𝑠
,
𝑤
]
Q[s,w]. After that, Lemma 3.7 and Proposition 3.8 become valid.

A clean rewrite would be:

Proposition 3.9: generic Galois group is 
𝑆
6
S
6
	​

.

Corollary: 
Δ
^
(
𝑤
,
𝑠
)
Δ
(w,s) is irreducible in 
𝑄
(
𝑠
)
[
𝑤
]
Q(s)[w], hence in 
𝑄
[
𝑠
,
𝑤
]
Q[s,w].

Then proceed to integrality, quotient field, and Hurwitz.

If the authors prefer a direct proof, they need a genuinely valid irreducibility argument over 
𝑄
(
𝑠
)
Q(s) or 
𝑄
[
𝑠
,
𝑤
]
Q[s,w]. The current one-specialization argument is not enough.

M1. Incorrect root-gap statement in Lemma 3.13

At 
𝑠
=
2
s=2,

Δ
^
(
𝑤
,
2
)
=
(
𝑤
−
1
)
(
𝑤
+
1
)
(
3
𝑤
−
1
)
(
𝑤
3
−
𝑤
2
+
𝑤
+
1
)
.
Δ
(w,2)=(w−1)(w+1)(3w−1)(w
3
−w
2
+w+1).

The cubic has a real root near 
−
0.543689
−0.543689, so “the next smallest modulus is 1” is false. The proof can still be saved.

A robust repair is:

show the cubic has one real root in a rational interval such as 
(
−
11
/
20
,
−
27
/
50
)
(−11/20,−27/50);

deduce that every root of the cubic has modulus 
>
0.54
>0.54;

then choose 
1
/
2
1/2 as the isolation radius for the Perron branch near 
𝑤
=
1
/
3
w=1/3.

This keeps the implicit-function argument intact, but makes it correct.

M2. Unclear provenance of the 10-state kernel

There are two acceptable fixes.

The stronger fix is to add a short subsection before Definition 2.2 that gives:

the underlying labelled graph or automaton,

the two-track comparison construction,

the transient states that are discarded,

and the derivation of the ten recurrent states shown in Figure 1.

The weaker fix is editorial but acceptable: define 
𝐵
(
𝑢
)
B(u) directly from the transition table and remove unverifiable language suggesting that the paper has already derived it from a standard synchronization construction.

M3. Overstated conceptual scope

The introduction should distinguish sharply between:

general facts, such as the formal self-dual compression 
𝑢
=
𝑒
𝑖
𝜃
↦
𝑠
=
2
cos
⁡
𝜃
u=e
iθ
↦s=2cosθ,

and example-specific facts, such as degree 
6
6, genus 
6
6, quartic quotient, and generic 
𝑆
6
S
6
	​

.

A good way to improve the paper is to add one short general lemma of the form:

If 
𝐵
(
𝑢
)
=
𝐵
0
+
𝑢
𝐵
1
B(u)=B
0
	​

+uB
1
	​

 satisfies 
Π
−
1
𝐵
0
Π
=
𝐵
1
Π
−1
B
0
	​

Π=B
1
	​

, then 
Δ
(
𝑧
,
𝑢
)
=
Δ
(
𝑢
𝑧
,
𝑢
−
1
)
Δ(z,u)=Δ(uz,u
−1
), and after 
𝑢
=
𝑟
2
u=r
2
, 
𝑧
=
𝑤
/
𝑟
z=w/r, the determinant rewrites as a polynomial in 
𝑤
w and 
𝑠
=
𝑟
+
𝑟
−
1
s=r+r
−1
 with the parity symmetry 
Δ
^
(
𝑤
,
−
𝑠
)
=
Δ
^
(
−
𝑤
,
𝑠
)
Δ
(w,−s)=
Δ
(−w,s).

Then present the rest of the paper explicitly as one worked 10-state example where this general mechanism becomes completely calculable.

M4. Computer-assisted proof architecture

Add a brief paragraph, either at the end of the introduction or at the start of Appendix A, saying explicitly which results rely on CAS verification. At minimum, identify:

Proposition 3.1, determinant expansion,

Proposition 3.6, Gröbner-basis smoothness certificate,

Proposition 3.9, discriminant and finite-field factorization data,

Proposition 3.12 / Theorem 3.14, jet recursion and high-order series.

Also state the software and version numbers, and provide one supplementary script or notebook instead of scattered commands only.

My recommendation remains Major revision. The paper is not yet acceptably rigorous in its current form, but the main claims look repairable, and the example may be publishable as a concise specialized note after substantial revision.