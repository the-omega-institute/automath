<!-- oracle metadata: {"timestamp": "2026-04-08T12:08:42.929657", "model": "chatgpt-5.4-pro-extended", "response_length": 12778} -->

Review of the attached manuscript. This review is based on the main PDF as supplied. 

main

1. Overall assessment

Major revision

This is an interesting paper with a genuinely nonstandard viewpoint. The strongest idea is to use full sampled click-record statistics, especially a Parry-law threshold in the ideal dead-time model and an exact 1-dependence threshold in the finite-recovery model, rather than only the mean detector rate. That conceptual move is potentially publishable. However, in its current form the manuscript has two central problems that prevent acceptance: first, the detector protocol in Section 3.1 is inconsistent with the hidden-state/reset logic used later in Section 3.4; second, the direct proof of exact 1-dependence is invalid as written. In addition, the main PDF sends many key derivations to supplementary material, and the attachment here does not include that supplementary file, so the central claims cannot be fully checked from the submission as provided. Several quantitative claims in Sections 3.7 and 4.1 are also presented more strongly than the supporting argument warrants. 

main

My editorial view is: the paper is not acceptable in its present form, but it looks salvageable if the authors repair the stochastic model, replace the broken proof, and sharply tighten the scope and novelty claims. If they cannot repair the Section 3 issues, rejection would follow. 

main

2. Novelty rating for each theorem

Editorial note: the most original material is not in the theorem-labeled statements, but in the Section 3 stochastic-process analysis, especially Proposition 3.2. The named theorems are mostly downstream geometric consequences. 

main

Theorem	Novelty	One-line justification
Theorem 4.1	MEDIUM	Useful geometric lift, but once the Section 3 thresholds and the response formula are granted, the shell equations are largely substitutions into the Planck-type rate law.
Theorem 5.1	MEDIUM	The exact common-amplitude cancellation is neat and operationally relevant, but algebraically it follows by dividing the two shell equations under the homogeneous spectral-weight assumption.
Theorem 5.3	MEDIUM	The near-horizon ratio law is a nice application, but it is essentially Theorem 5.1 plus the standard nonextremal horizon expansion of the lapse.
Theorem 5.5	LOW	The local inverse statement is mathematically routine once the shell-ratio equations are set up, because it is an implicit-function-theorem argument.
3. Issue table

Main issues, based on Sections 3 to 5, the discussion, and the data-availability statement. 

main

ID	Section	Severity	Description	Suggested fix
B1	3.1 and 3.4	BLOCKER	Model inconsistency. Section 3.1 says the detector is read out and then reset to (	g\rangle) for the next interval, but Section 3.4 builds the renewal structure from the claim that every click resets the hidden state to the refractory state. Those are different models, and the renewal law, hazard, covariance, and shell thresholds depend on which one is intended.
B2	3.4	BLOCKER	Broken proof of exact 1-dependence. The proof claims that 
𝐴
𝑛
A
n
	​

 is a deterministic function of 
(
𝐻
𝑛
,
𝐻
𝑛
+
1
)
(H
n
	​

,H
n+1
	​

), but the displayed kernels allow both click and no-click transitions from the refractory state back to the refractory state. So the determinism claim is false, and the proof does not establish exact 1-dependence.	Replace the proof with a correct factorization argument using output-labeled kernels, or enlarge the hidden state so that the emission becomes deterministic from the augmented state.
B3	Whole paper, especially intro and data availability	BLOCKER	Core derivations are not verifiable from the attached submission. The manuscript explicitly says that detailed proofs are in Supplementary Material and that scripts are supplied separately, but they are not available in the attachment reviewed here.	Supply the supplement and scripts, and move the most important derivations into a main-text appendix.
M1	3.7	MEDIUM	Finite-sample observability claims are too strong for the evidence shown. The asymptotic variance formula, CLT-based detection percentages, and “consistent with photon-counting experiments” claim are asserted without proof, simulation, or citation.	Either prove these claims under explicit assumptions, or relabel them as heuristics and support them with Monte Carlo experiments.
M2	4.1 and 5.5	MEDIUM	Unproved quantitative error bounds outside the homogeneous regime. The 
𝑂
(
𝜀
0
)
O(ε
0
	​

) shell-ratio correction and shell-shift statements are presented as concrete bounds, but no theorem or assumptions are given.	State and prove a perturbative theorem with explicit hypotheses, or delete the bound and leave only the qualitative statement.
M3	Abstract, Sections 4 to 5, Discussion	MEDIUM	Novelty is overstated at the theorem level. The paper itself admits that both thresholds are functions of the same local rate. The real novelty is the record-level thresholding, not the later shell algebra, cancellation law, or IFT inversion.	Recenter the paper around the Section 3 process results. Present Sections 4 to 5 as applications/corollaries, not as the main source of novelty.
M4	Title, Abstract, 3.1, Discussion	MEDIUM	The physics framing is too broad. The paper explicitly uses a phenomenological rate-driven counter model and does not derive it from first-principles AQFT. Some of the wording still reads as if the results were direct UDW detector theorems.	Tighten the title, abstract, and conclusion so they consistently say “phenomenological counter model driven by the stationary UDW excitation rate.”
M5	5.4	MEDIUM	The worked example is an internal consistency check, not a validation study. Feeding exact model-generated shell radii back into exact inverse formulas and recovering the same parameters is expected. It does not test robustness to noise or model mismatch.	Add a noisy synthetic inversion test, or a perturbative numerical study, showing actual recovery performance under shell-location errors.

The evidence for B1 through B3 is especially clear in Section 3.1, the displayed kernels and proof text in Section 3.4, and the statements that full proofs and scripts are in supplementary material. The paper also openly characterizes the model as phenomenological, and later acknowledges that the results are conditional on this model class. 

main

4. Missing references

I do not see a single omission that destroys the paper’s core claim, but the bibliography should be strengthened in three places.

First, for static spherical detector-response literature, add Ng, Hodgkinson, Louko, Mann, and Martín-Martínez, Unruh-DeWitt detector response along static and circular geodesic trajectories for Schwarzschild-AdS black holes, Phys. Rev. D 90, 064003 (2014). This is directly relevant to the paper’s positioning in Sections 4 and 5. 
arXiv

Second, add Tjoa and Mann, Unruh-DeWitt detector in dimensionally-reduced static spherically symmetric spacetimes, JHEP 2022, 14 (2022). This is very relevant background for the manuscript’s discussion of static spherically symmetric response theory. 
arXiv

Third, for the probability side of finite dependence, add Holroyd and Liggett, Finitely dependent coloring, Forum of Mathematics, Pi 4:e9 (2016). It is not a QFT paper, but it would strengthen the finite-dependence context beyond the older classical references already cited. 
University of Bristol

5. Specific improvements needed to reach acceptance

The paper needs five concrete upgrades.

First, the authors must make the detector model internally coherent. Right now the protocol, hidden-state interpretation, and output kernels do not line up.

Second, the proof of exact 1-dependence must be replaced by a correct proof. Since this threshold is one of the two pillars of the paper, this is not a cosmetic fix.

Third, the submission must be self-contained enough for refereeing. At minimum, the full supplement must be provided. Preferably, the derivations behind Proposition 3.2, the sub-Poissonian result, the near-horizon law, and the local inversion theorem should be moved into an appendix.

Fourth, the authors need to separate theorem-level statements from heuristic numerical commentary. Section 3.7 and the 
𝑂
(
𝜀
0
)
O(ε
0
	​

) discussion should either become properly supported propositions or be clearly labeled as heuristic guidance.

Fifth, the novelty and scope need sharpening. The core contribution is a record-statistics thresholding idea inside a phenomenological detector model. The later shell geometry and inverse content are model-conditional consequences. The current exposition sometimes suggests a stronger claim than the manuscript itself supports. 

main

6. Concrete fixes for each BLOCKER and MEDIUM issue

B1. Fix the model definition

Add a one-page timing appendix with a state diagram:

state immediately after readout,

state during the interval,

state immediately before the next readout,

what happens after a click and after a no-click.

Then choose one of two models, and only one:

Model A: a click leaves the detector in a refractory state for the next interval. Then the current renewal logic may survive, but Section 3.1 must be rewritten.

Model B: every readout resets the detector to ready. Then finite-recovery memory across intervals disappears, and 
𝑇
0
,
𝑇
1
T
0
	​

,T
1
	​

, the renewal law, and all shell results must be rederived.

B2. Replace the invalid 1-dependence proof

Do not argue that 
𝐴
𝑛
A
n
	​

 is determined by 
(
𝐻
𝑛
,
𝐻
𝑛
+
1
)
(H
n
	​

,H
n+1
	​

). It is not. Use the output-labeled kernels directly. If 
𝑇
𝑢
T
u
	​

 and 
𝑇
𝑣
T
v
	​

 denote the products of 
𝑇
0
,
𝑇
1
T
0
	​

,T
1
	​

 associated with two visible words separated by at least one time step, then at the critical line one has 
𝑃
=
𝑇
0
+
𝑇
1
=
1
𝜋
P=T
0
	​

+T
1
	​

=1π. The required factorization should be proved from

𝜋
 
𝑇
𝑢
 
𝑃
 
𝑇
𝑣
 
1
=
(
𝜋
𝑇
𝑢
1
)
(
𝜋
𝑇
𝑣
1
)
,
πT
u
	​

PT
v
	​

1=(πT
u
	​

1)(πT
v
	​

1),

or an equivalent cylinder-probability identity. That directly establishes 1-dependence. If this route becomes awkward, enlarge the hidden state so the emission label is part of the state.

B3. Make the submission referee-checkable

Upload the supplementary PDF and scripts. Also move the following into the main manuscript or a formal appendix:

the derivation of the zero-run law and hazard monotonicity,

the covariance formula and exact 1-dependence proof,

the spectral density/Fano-factor derivation,

the near-horizon expansion details,

the local inverse theorem proof.

M1. Support Section 3.7 properly

A good repair is:

state an asymptotic-normality proposition for the lag-2 covariance estimator using a regenerative CLT for the renewal process,

provide a short Monte Carlo appendix showing sign-detection rates versus 
𝑁
N,

remove the experimental-feasibility sentence unless it is tied to a citation or to explicit count-rate assumptions.

M2. Prove or remove the 
𝑂
(
𝜀
0
)
O(ε
0
	​

) claim

If the authors want a perturbative shell-shift bound, they should assume:

𝑆
𝑥
(
Ω
)
=
𝑆
(
Ω
)
(
1
+
𝜀
(
𝑥
)
)
S
x
	​

(Ω)=S(Ω)(1+ε(x)) with 
∣
𝜀
∣
≤
𝜀
0
∣ε∣≤ε
0
	​

,

differentiability of the shell-defining map,

a nonvanishing derivative with respect to lapse at the shell.

Then a direct implicit-function-theorem estimate can yield an actual bound. Without this, the current sentence should be softened to a qualitative remark.

M3. Reframe the contribution

Restructure the paper so that the central theorem is the Section 3 record-statistics result. Then present:

shell equations as corollaries of the threshold formulas plus the local rate law,

the amplitude-cancellation law as an application,

near-horizon and inverse statements as tertiary consequences.

This would make the novelty claim much more convincing.

M4. Tighten the physics language

Revise the title and abstract so the reader immediately understands that the object is a phenomenological sampled counter model fed by a stationary UDW excitation rate, not a first-principles theorem about a continuously measured UDW detector. This change would materially improve accuracy.

M5. Upgrade the worked example

Keep Table 2, but add one of the following:

a noisy synthetic inversion experiment with perturbed shell radii,

a contour plot of parameter-recovery error versus shell-separation error,

or a short Monte Carlo study showing how the conditioning estimate translates into actual reconstruction error.

That would turn the example from algebraic back-substitution into real evidence of practical inverse content.

Final recommendation to the editor: major revision, not acceptable as currently written, but potentially worthwhile if the Section 3 model/proof issues are fully repaired. 

main