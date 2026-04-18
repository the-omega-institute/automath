<!-- oracle metadata: {"timestamp": "2026-04-13T19:24:45.735139", "model": "chatgpt-5.4-pro-extended", "response_length": 13231} -->

1. Overall assessment

Major revision

The paper has a real core, but it is narrower than the manuscript currently suggests. The strongest part is the sampled-counter analysis in Section 3, especially the finite-recovery renewal law, the closed covariance formula, and the exact 1-dependence transition. In contrast, much of Sections 4 and 5 consists of algebraic consequences of plugging those thresholds into a response formula. My main concern is that the manuscript does not yet justify, at a sufficiently consistent microscopic level, why this should be read as a standard Unruh-DeWitt detector result rather than as a phenomenological dead-time/recovery counter driven by a stationary rate. A second concern is that the shell and inverse claims rest on a spectral decomposition and on homogeneity/shared-hardware assumptions whose scope is narrower than the prose implies. I would not accept the paper in its present form, but I would reconsider after a substantial rewrite. 

main

2. Novelty rating for theorem-level results

I am rating all numbered theorem-level statements, including propositions and corollaries, because that is how the manuscript structures its main claims. I do not currently see a HIGH-novelty theorem.

Result	Novelty	One-line justification
Proposition 3.1	LOW	Matching a one-parameter golden-mean Markov chain to the Parry measure is elementary; the novelty is mainly interpretive.
Proposition 3.2	MEDIUM	This is the paper’s strongest result: explicit renewal/covariance formulas and an exact 1-dependence threshold for the specific sampled counter model.
Corollary 3.3	LOW	This is essentially immediate once the finite-recovery process has full support, or equivalently positive reclick probability.
Proposition 3.5	LOW	The quadratic suppression and fixed-window concentration are straightforward small-
Δ
𝜏
Δτ asymptotics.
Proposition 3.6	MEDIUM	Exact spectral-density and Fano-factor formulas are useful, but antibunching/sub-Poisson behavior of refractory renewal models is qualitatively well known.
Theorem 4.1	LOW	The shell equations are direct substitutions of record-defined threshold rates into the assumed KMS response formula.
Corollary 4.3	LOW	Homogeneous spectral weight gives a direct lapse-level-set specialization.
Proposition 4.4	LOW	Shell ordering is a simple monotonicity consequence of the threshold rates.
Theorem 5.1	LOW	Common-amplitude cancellation follows immediately by dividing two shell equations.
Corollary 5.2	LOW	The spectral-transport identity is useful but algebraically direct.
Proposition 5.3	LOW	The perturbative bound is an elementary multiplicative estimate.
Theorem 5.4	MEDIUM	The near-horizon hierarchy is physically interesting, even though mathematically it is a straightforward expansion.
Proposition 5.5	LOW	This is a direct algebraic inversion in the homogeneous Schwarzschild toy model.
Theorem 5.6	LOW	Local identifiability by the implicit function theorem is standard once the ratio equations are set up.
3. Issue table

The issues below are based on the attached manuscript, especially Sections 3 to 5 and Appendix B. 

main

ID	Section	Severity	Description	Suggested fix
B1	3.1, Appendix B	BLOCKER	The microscopic link to a standard UDW detector is not yet consistent. The manuscript mixes endpoint projective readout with an interval click/no-click observable, introduces a refractory recovery channel 
𝜅
𝑟
κ
r
	​

 alongside standard UDW transition language, and states conflicting scale assumptions about 
Γ
Δ
𝜏
ΓΔτ.	Either reframe the paper explicitly as a phenomenological sampled counter driven by a UDW rate, or provide a full microscopic instrument/unraveling derivation with a consistent regime of validity.
B2	Remark 3.4, Section 4	BLOCKER	Equation (19) is load-bearing, but the definition of 
𝑆
𝑥
(
Ω
)
S
x
	​

(Ω) is not given in standard KMS spectral terms and appears technically inaccurate as written.	Replace this with a precise Wightman/KMS spectral definition and derive Eq. (19) carefully, including positivity and state-dependence statements.
M1	3.7, 5.6	MEDIUM	Finite-sample “observability” is mostly heuristic. The paper gives simulations, but no regenerative CLT, asymptotic variance formula, or confidence analysis for the key estimators.	Either prove asymptotic normality for the empirical hazard/covariance statistics, or clearly demote these sections to numerical illustrations.
M2	4 to 5	MEDIUM	The physical scope is narrower than the prose suggests. The shell/inverse program is exact mainly in the homogeneous spectral-weight toy model and under shared-hardware assumptions.	State these restrictions prominently in the abstract, theorem statements, and discussion.
M3	5.2 to 5.3	MEDIUM	Proposition 5.3 only controls the ratio observable, not the shell locations. That does not fully support the current “stability” rhetoric.	Either derive an actual shell-displacement bound under derivative assumptions, or rewrite the claim as ratio-level stability only.
M4	5.1	MEDIUM	Exact amplitude cancellation assumes the blanking mode and free-recovery mode keep the same effective prefactor 
𝜆
𝑐
2
𝑆
𝑥
(
Ω
)
λ
c
2
	​

S
x
	​

(Ω). This is physically nontrivial and not justified.	Model the mode dependence explicitly, or state equal amplitude as an assumption and discuss when it is realistic.
M5	whole submission	MEDIUM	The manuscript repeatedly defers details to Supplementary Material, but no supplement is available in the attached submission.	Supply the supplement, or move all load-bearing derivations into the main paper/appendices.
M6	Introduction, 4, 5, 6	MEDIUM	The paper overweights algebraic downstream corollaries relative to the genuinely new stochastic content.	Reorganize so Section 3 is the clear centerpiece and Sections 4 to 5 are explicitly applications.
M7	3.2 to 3.3, 6	MEDIUM	Terms like “exact-clock,” “zero-jitter,” and record-level “thermality” are misleading for the Parry/golden-mean benchmark.	Rename the object as a Parry or grammar benchmark shell and tone down the thermodynamic language.
L1	Introduction, Discussion	LOW	The manuscript is repetitive. Several claims are restated multiple times with little added precision.	Cut the introduction and discussion substantially.
4. Missing references

The most important omissions are these.

Fukuma, Sakatani, Sugishita (2014), Master equation for the Unruh-DeWitt detector and the universal relaxation time in de Sitter space. This is the most obvious missing citation for Appendix B, because it derives a master equation for UDW detectors and is directly relevant to your attempt to motivate a GKLS reduction. 
arXiv
+1

Costa and Piazza (2009), Modeling a particle detector in field theory. This matters because your detector model is explicitly phenomenological, and this paper discusses the status and stability of particle-detector models beyond the textbook UDW idealization. 
arXiv
+1

Marzen and Crutchfield (2015), Informational and Causal Architecture of Discrete-Time Renewal Processes, and Pitman and You (2021), Stationary 1-dependent Counting Processes. These are directly relevant to the renewal and 1-dependent counting-process claims in Section 3. Marzen and Crutchfield study discrete-time stationary renewal processes with binary alphabets and i.i.d. interevent counts; Pitman and You develop formulas for stationary 1-dependent counting processes. 
MDPI
+2
MDPI
+2

Bednorz (2023), General quantum measurements in relativistic quantum field theory, and Papageorgiou, de Ramón, Anastopoulos (2024), Particle-field duality in QFT measurements. These are relevant because your framing turns on what a time-resolved detector record means in QFT, and both works address that question more directly than the current bibliography does. 
APS Link
+3
arXiv
+3
APS Link
+3

Rapp et al. (2019), Dead Time Compensation for High-Flux Ranging. This is not curved-spacetime work, but it is relevant modern dead-time literature with Markov and inverse-statistics aspects that overlap with your detector-counter framing. 
arXiv
+1

Sanders (2013), Thermal equilibrium states of a linear scalar quantum field in stationary spacetimes. This would strengthen the KMS background of Section 4. 
arXiv
+1

5. Specific improvements needed to reach acceptance

Choose the paper’s true level of description. Right now it oscillates between a microscopic UDW measurement paper and a phenomenological counter paper. Pick one and rewrite consistently. 

main

Repair the response-theory foundation. Equation (19) and the definition of 
𝑆
𝑥
(
Ω
)
S
x
	​

(Ω) must be made precise before any shell geometry or inversion claims can be trusted. 

main

Re-scope Sections 4 and 5. In the present form they read as if they carry equal scientific weight to Section 3, but most of that material is direct algebra once the threshold rates are fixed. 

main

Upgrade or demote the finite-sample claims. Either prove statistical asymptotics for the proposed diagnostics or explicitly present those sections as exploratory numerics only. 

main

Add omitted literature and sharpen attribution. The manuscript needs a clearer statement of what is actually new relative to UDW master-equation work, QFT measurement theory, renewal-process theory, and classical dead-time inverse problems. 
arXiv
+7
arXiv
+7
arXiv
+7

6. Concrete fixes for each BLOCKER and MEDIUM issue

B1. Microscopic detector model

Minimal salvage path: remove the claim that Appendix B derives the model from a standard sampled UDW detector, and instead state plainly that the paper studies a phenomenological two-state counter whose click intensity is driven by the stationary UDW excitation rate.

Stronger path: define an explicit detector Hilbert space, a no-click/click interval instrument, and a quantum-jump or POVM description for “at least one excitation during 
[
𝑛
Δ
𝜏
,
(
𝑛
+
1
)
Δ
𝜏
]
[nΔτ,(n+1)Δτ].”

In either path, clarify the roles of 
Γ
+
Γ
+
	​

, 
Γ
−
Γ
−
	​

, and 
𝜅
𝑟
κ
r
	​

, and state one consistent parameter hierarchy.

B2. Spectral weight and Eq. (19)

Define the stationary pullback Wightman spectrum 
𝑊
^
𝑥
(
𝜔
)
W
x
	​

(ω) precisely.

State the KMS relation in the standard form 
𝑊
^
𝑥
(
−
𝜔
)
=
𝑒
−
𝛽
l
o
c
𝜔
𝑊
^
𝑥
(
𝜔
)
W
x
	​

(−ω)=e
−β
loc
	​

ω
W
x
	​

(ω).

Then define the positive spectral density you actually use, and derive the factorization of 
Γ
+
(
𝑥
,
Ω
)
Γ
+
	​

(x,Ω) from that relation.

If the clean factorization into “spectral weight times Planck denominator” does not hold in the intended generality, rewrite the shell equations in terms of 
𝑊
^
𝑥
(
Ω
)
W
x
	​

(Ω) directly.

M1. Finite-sample observability

Prove a regenerative CLT for empirical run counts and a delta-method limit for 
ℎ
^
𝑘
h
k
	​

.

For the covariance sign test, derive an asymptotic variance for 
𝛾
^
2
γ
	​

2
	​

, or else present the Monte Carlo evidence only as heuristic calibration.

Report confidence intervals and required sample sizes derived from the asymptotics, not only simulation frequencies.

M2. Scope of Sections 4 to 5

Rewrite the abstract so that the core result is clearly the Section 3 stochastic analysis.

Move phrases like “inverse content” and “identifiability” behind explicit qualifiers such as “in the homogeneous spectral-weight toy model.”

In theorem statements, separate “exact in the homogeneous model” from “identity valid in the inhomogeneous case.”

M3. Stability under spectral inhomogeneity

Add a theorem of the following form: if 
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

(Ω)=S(Ω)(1+ε(x)), 
∣
𝜀
∣
≤
𝜀
0
∣ε∣≤ε
0
	​

, and the derivative of the shell-defining function with respect to the lapse is bounded away from zero, then the shell lapse shifts by 
𝑂
(
𝜀
0
)
O(ε
0
	​

).

Translate that lapse shift into a geometric displacement using 
∣
∇
𝑁
∣
∣∇N∣.

If you do not prove this, remove “stability bound” language for shell positions.

M4. Shared-hardware amplitude cancellation

Introduce a possible mode-dependent prefactor 
𝐴
𝑚
𝜆
𝑐
2
𝑆
𝑥
(
Ω
)
A
m
	​

λ
c
2
	​

S
x
	​

(Ω) in the shell equations.

Show by model or experiment when 
𝐴
blanking
=
𝐴
recovery
A
blanking
	​

=A
recovery
	​

 is justified.

If equality cannot be justified, carry 
𝐴
blanking
/
𝐴
recovery
A
blanking
	​

/A
recovery
	​

 as a nuisance parameter and explain what remains identifiable.

M5. Missing supplementary material

Provide the supplement.

If a supplement is not allowed, move every load-bearing derivation into the appendices, especially those for the renewal law, hazard monotonicity, spectral density/Fano factor, and the shell identities.

M6. Theorem hierarchy and novelty inflation

Collapse Sections 4 and 5 into a shorter “Applications” section.

Keep one main theorem for the finite-recovery record and one proposition for the ideal dead-time benchmark.

Convert trivial algebraic consequences into remarks or corollaries, not headline theorems.

M7. Terminology

Rename “exact-clock shell” to something like Parry shell or grammar benchmark shell.

Remove “zero-jitter” language.

Keep “Parry-law benchmark” if you want, but do not present it as a thermality notion parallel to Gibbs thermality unless you sharply emphasize that it is only a record-level entropy benchmark.

My editorial recommendation remains Major revision.