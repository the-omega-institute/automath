<!-- oracle metadata: {"timestamp": "2026-04-10T22:58:44.231638", "model": "chatgpt-5.4-pro-extended", "response_length": 12307} -->

1. Overall assessment: Major revision

The manuscript has a potentially publishable core idea: using a Bayes-error observable for first-entry residue events and showing that, in the finite-state Markov-hole setting, it is exactly a killed-matrix path sum whose exponential decay matches the usual escape rate. That part is interesting. However, in its current form I would not recommend acceptance. Two problems are serious. First, the paper’s general setup in Sections 2 to 5 is built around a binary visible process, while the main theorem in Section 6 is actually proved for observation of the full symbolic alphabet. Second, the novelty claims are not positioned carefully enough relative to recent symbolic-hole/Markov-measure escape-rate work and to classical quasi-stationary theory. Section 7 also overstates the “birthday threshold” consequence unless an additional third-moment condition is either proved from the pressure formalism or explicitly retained in the statement. 

main

My editorial reading is: the paper may become acceptable after a substantial rewrite that narrows and clarifies the true contribution. As written, it overpackages a finite-state Markov calculation as a broader general visible-factor theorem, and it does not sufficiently separate what is genuinely new from what is standard.

2. Novelty rating for each theorem

I rate the unique theorem statements only. Theorems 1.1 and 6.1 are duplicates, as are 1.2 and 6.6.

Theorem	Novelty	One-line justification
Theorem 4.1	LOW	Standard composition of sliding-block codes. Useful, but not new in substance.
Theorem 5.4	LOW	The Bayes-risk martingale identity is a routine convexity/Tanaka-type calculation.
Theorem 5.8	LOW	A straightforward boundary-mass estimate from cylinder-size bounds.
Theorem 5.9	MEDIUM	The weighted-automaton packaging of boundary mass is neat and useful, but assembled from standard weighted automata and Perron-Frobenius machinery.
Theorem 6.1 / 1.1	MEDIUM	The Bayes-error observable seems new, but the spectral-radius/pressure-gap escape mechanism is standard and closely overlaps with recent exact escape-rate formulae for Markov-measure SFT holes. 
arXiv
+1

Theorem 6.6 / 1.2	MEDIUM	The residue-dependent amplitude attached to Bayes error is a nice reformulation, but the asymptotic mechanism is classical quasi-stationary/Perron-Frobenius theory for killed finite Markov chains. 
Cambridge University Press & Assessment
+1

I do not see a HIGH-novelty theorem in the current version. The new ingredient is the observable and its residue-weighted interpretation, not the underlying escape-rate or quasi-stationary machinery.

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	§§2 to 6	BLOCKER	Structural mismatch. Sections 2 to 5 define observation through a binary readout, but Section 6 proves the main formula using full A-valued symbolic cylinders. As written, Theorem 6.1 is not literally a specialization of Theorem 5.9.	Rewrite the general framework for an arbitrary finite observation alphabet, or explicitly state that Section 6 switches to full-symbol observation and remove the claim that it is a direct specialization of the earlier binary setup.
B2	Introduction, §§6 to 8	BLOCKER	Novelty/literature positioning is inadequate. The paper omits directly relevant symbolic-hole work on escape rates for SFTs with Markov measure and relevant quasi-stationary references, so the novelty of the escape-rate and amplitude claims is overstated.	Add the missing references, rewrite the introduction, and isolate the truly new part: Bayes-error weighting and residue-resolved amplitudes.
M1	Corollary 1.4, §7	MEDIUM	The “birthday threshold” is stated too strongly. The Poisson statement needs the extra condition 
𝑁
𝑚
3
𝑆
3
𝐻
(
𝑚
)
→
0
N
m
3
	​

S
3
H
	​

(m)→0, but the headline summary reads as if the 
ℎ
2
,
𝐻
h
2,H
	​

 scale alone were sufficient.	Either prove the required 
𝑆
3
S
3
	​

-control from the survivor pressure formalism, or weaken the corollary and abstract to a conditional statement.
M2	Remark 1.5, Remark 6.8	MEDIUM	Too much conjectural/operator-theoretic material is presented in theorem-like form. Some relevant countable-state/open-transfer-operator literature already exists.	Shorten the remark, move most of it to a final outlook section, and cite the existing countable-state/open-hole literature.
M3	§§2 to 5	MEDIUM	The paper is overbuilt. The generic visible-factor and recursive-refinement machinery obscures the actual finite-state symbolic result and is only weakly connected to the core theorem.	Compress §§2 to 5 substantially or move the general machinery to an appendix. Lead with the symbolic killed-matrix statement.
M4	Theorem 6.1	MEDIUM	The residue non-degeneracy hypothesis is used for lower bounds and asymptotic comparison, but not for the exact identity 
𝜀
𝑚
=
𝑢
𝑇
𝐵
𝐻
𝑚
−
1
𝑏
𝑚
−
1
ε
m
	​

=u
T
B
H
m−1
	​

b
m−1
	​

. The theorem bundles these together imprecisely.	Split the theorem into an unconditional exact formula and a separate asymptotic theorem under non-degeneracy.
L1	Bibliography	LOW	Reference [6] is incomplete and some bibliography entries are dated or not fully informative for the actual claims used in the paper.	Complete all bibliographic data and add the more relevant recent references.
L2	Notation/organization	LOW	Repeated theorem statements and shifting notation between binary and nonbinary alphabets create avoidable confusion.	Add a notation paragraph at the start of §6 and state clearly when the observation alphabet changes.
4. Missing references

These are the most important omitted works I would expect the authors to address.

Agarwal, Cheriyath, Tikekar, On Escape rate for subshift with Markov measure (2024 preprint).
Very relevant. It already gives an exact spectral-radius formula for escape rate into holes for SFTs with Markov measure, plus a pole/rational-function description. The current manuscript must explain precisely what is new beyond that. 
arXiv
+1

Cheriyath and Agarwal, Subshifts of Finite Type with a Hole, J. Aust. Math. Soc. 115 (2023).
Direct symbolic-hole context, especially if the introduction discusses escape rates in SFTs and comparison across holes. 
Cambridge University Press & Assessment

Darroch and Seneta, On Quasi-Stationary Distributions in Absorbing Discrete-Time Finite Markov Chains (1965).
Theorem 6.6 is, at heart, a quasi-stationary asymptotic statement for a killed finite Markov chain with a new terminal observable. This classical reference should be cited. 
Cambridge University Press & Assessment
+1

Collet, Martínez, San Martín, Quasi-Stationary Distributions: Markov Chains, Diffusions and Dynamical Systems (2013).
Useful umbrella reference for the quasi-stationary language used in §6.2. 
Springer

Demers, Ianzano, Mayer, Morfe, Yoo, Limiting distributions for countable state topological Markov chains with holes, DCDS 37 (2017).
Important for the countable-state/open-hole direction mentioned in Remark 6.8. 
AIM Sciences

Tanaka, Quasi-compactness of transfer operators for topological Markov shifts with holes, DCDS 44 (2024).
Directly relevant to the operator-theoretic extension discussed in Remark 6.8. As written, the remark reads as if this territory were entirely future work. It is not. 
AIM Sciences
+1

5. Specific improvements needed to reach acceptance

The paper needs a sharper contract with the reader.

First, decide what the observation model actually is. If the paper is about Bayes error from the first 
𝑚
m symbols of the original SFT, then Sections 2 to 5 should be rewritten in that general finite-alphabet language from the start. If it is really about a binary visible factor, then the current Section 6 is proving a different problem and must be replaced or substantially extended.

Second, rewrite the introduction so the novelty claim is precise. The paper should say something close to this: “The new contribution is the Bayes-error observable and its residue-dependent terminal weighting. The escape-rate, pressure-gap, and quasi-stationary asymptotics are standard once the observable is written as a killed-matrix path sum.” That would be a much more credible positioning.

Third, either strengthen or weaken Section 7. At present it reads more definitive than what is actually proved. The survivor Rényi-pressure identity is fine, but the birthday-threshold language should not suppress the extra 
𝑆
3
S
3
	​

 hypothesis unless the authors prove it follows automatically in their setting.

Fourth, reduce the bulk. The paper is prepared as if it were proving a broad visible-factor theorem, but the real core is a finite-state symbolic calculation. ETDS readers will respond better to a shorter, more direct paper with a precise main theorem and sharper comparison to existing open-system work.

Fifth, handle the conjectural extension more responsibly. Remark 6.8 is currently too long, too theorem-like, and insufficiently connected to the literature that already exists.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Observation-model mismatch

Actionable fix:

Replace the standing binary alphabet 
Σ
=
{
0
,
1
}
Σ={0,1} in §§2 to 5 by a generic finite observation alphabet 
𝑉
V.

Restate Propositions 5.2 to 5.8 and Theorem 5.9 for cylinders in 
𝑉
𝑚
V
m
. None of the proofs fundamentally need the alphabet to be binary.

At the start of §6, explicitly say that the observation alphabet is now the original symbolic alphabet 
𝐴
A, so the Bayes classifier sees the full length-
𝑚
m word 
𝑎
0
…
𝑎
𝑚
−
1
a
0
	​

…a
m−1
	​

.

If the authors want to keep the binary-readout narrative, then they must add a separate theorem for the actual hole-indicator process. That theorem will not have the current simple terminal-state formula.

B2. Novelty and literature positioning

Actionable fix:

Add the six missing references listed above.

Revise the introduction and abstract so that the uncited escape-rate formula and rational-function/pole literature are acknowledged.

Replace broad claims like “the finite-observation exponent recovers the escape rate” with more precise language: “for this new Bayes-error observable, the exponent is controlled by the same killed spectral radius.”

In §6.2, explicitly say that the amplitude theorem is a quasi-stationary asymptotic for a killed finite Markov chain with a new terminal observable.

M1. Overstated birthday-threshold claim

Actionable fix:

Rewrite Corollary 1.4 and the abstract so the Poisson conclusion is conditional on the third-moment hypothesis.

Alternatively, prove a pressure inequality implying 
𝑁
𝑚
3
𝑆
3
𝐻
(
𝑚
)
→
0
N
m
3
	​

S
3
H
	​

(m)→0 whenever 
(
𝑁
𝑚
2
)
𝑆
2
𝐻
(
𝑚
)
→
𝜏
(
2
N
m
	​

	​

)S
2
H
	​

(m)→τ in the present Markov-survivor setting.

If such a proof is unavailable, downgrade the wording to “heuristic scale” or “conditional threshold.”

M2. Conjectural extension too prominent

Actionable fix:

Move most of Remark 6.8 to the final section as an outlook paragraph.

Cite Demers et al. 2017 and Tanaka 2024 when discussing countable-state and open-transfer-operator results. 
AIM Sciences
+1

Reduce the remark to one concise statement of what remains open for this specific Bayes-error observable.

M3. Overbuilt general machinery

Actionable fix:

Start the paper with the symbolic setting and state Theorem 6.1 immediately after preliminaries on SFTs and equilibrium Markov measures.

Move Theorem 4.1 and most of the “recursive visible refinements” discussion to an appendix, unless it is used in an essential later argument.

Keep only the minimum from §5 needed to prove the main theorem. The rest can be presented as a general appendix or a separate note.

M4. Theorem 6.1 bundles exact identity with non-degeneracy-dependent asymptotics

Actionable fix:

State a proposition first: for every 
𝑚
≥
1
m≥1, 
𝜀
𝑚
(
𝑃
𝑅
;
𝜈
𝜙
)
=
𝑢
𝑇
𝐵
𝐻
𝑚
−
1
𝑏
𝑚
−
1
 
m
o
d
 
𝑞
ε
m
	​

(P
R
	​

;ν
ϕ
	​

)=u
T
B
H
m−1
	​

b
m−1modq
	​

, without non-degeneracy.

Then state the exponent theorem under the residue non-degeneracy hypothesis.

Add one sentence explaining what fails when some 
𝛽
𝑖
,
𝑟
=
0
β
i,r
	​

=0. The exact identity survives, but the comparison with survivor mass can break down.

My bottom line: the paper has a workable core, but it needs a serious conceptual and editorial rewrite before it is ready.