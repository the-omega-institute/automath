<!-- oracle metadata: {"timestamp": "2026-04-07T10:15:41.688817", "model": "o3-mini-high", "response_length": 13118} -->

1. Overall assessment

Major revision

There is a publishable core here. The paper’s central idea, that record-level statistics of a sampled Unruh–DeWitt detector can define two detector-selected thresholds and then lift them to shell loci in static KMS backgrounds, is interesting and plausibly original. The manuscript is strongest in section 3, especially the finite-recovery renewal analysis. However, in its present form I would not recommend acceptance in Journal of Physics Communications. My concerns are mainly about technical soundness and physical framing, not lack of interesting ideas: essential derivations are deferred to supplementary material not present in the attached file, the key notion of “exact symbolic thermality” is not yet physically justified well enough, and the click/recovery model is not clearly derived from a concrete UDW measurement protocol. For this journal, the important threshold is whether the work is original and technically sound with strong methodology. On the current record, it is not yet there. 

main

 
IOPscience - Publishing Support
+1

A practical nuance: if the supplementary proofs were in fact supplied separately to the journal but not included in the file I reviewed, my strongest procedural objection weakens. Even then, the main text still needs more self-contained justification.

2. Novelty rating for each theorem
Theorem	Novelty	One-line justification
Theorem 4.1	MEDIUM	The lift from record thresholds to detector-defined KMS shell loci appears new in this setting, but technically it is mostly direct substitution of the rate formula into previously identified thresholds.
Theorem 5.1	MEDIUM	Exact common-amplitude cancellation for a matched shell pair is operationally useful and likely new, but algebraically straightforward once the two shell equations are written down.
Theorem 5.3	HIGH	The near-horizon shell-ratio hierarchy is the paper’s most distinctive geometric claim and goes beyond a trivial rewriting of Tolman scaling.
Theorem 5.5	LOW	The local uniqueness statement is mainly a standard implicit-function-theorem application after the shell-ratio setup is in place.

The strongest original content is actually not in the formal theorems of sections 4 and 5, but in propositions 3.1 to 3.5, especially the finite-recovery renewal law, the strictly increasing hazard, the exact 1-dependence threshold, and the antibunching/Fano-factor analysis. 

main

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	1; 3 to 5	BLOCKER	Core derivations are said to be in supplementary material, but that material is not in the attached review file. From the main text alone, the reader cannot independently verify exact 1-dependence, hazard monotonicity, the Fano-factor claim, or the near-horizon asymptotics.	Supply full proofs and add short proof sketches in the main text with explicit appendix cross-references.
B2	3.1; 4.1; 6	BLOCKER	“Exact symbolic thermality” is defined via equality to the Parry measure on the golden-mean shift, but the physical reason this should count as thermality is under-argued. The exact-clock shell rests entirely on this choice.	Either justify this benchmark from a detector thermodynamic principle, or rename/reframe it as a Parry-law or maximum-entropy grammar threshold rather than thermality.
B3	2 to 3	BLOCKER	The dead-time and finite-recovery click laws are introduced phenomenologically, not derived from a concrete repeated-measurement or open-system UDW protocol. It is unclear which conclusions are genuinely about sampled UDW detectors and which come from an appended counter model.	Derive the discrete click model from an explicit measurement/reset scheme, or narrow the claims to a phenomenological counter driven by the UDW excitation rate.
M1	4 to 5	MEDIUM	The paper speaks of detector-defined “shell hypersurfaces,” but existence, regularity, and uniqueness conditions are not stated. In addition, the strongest inverse claims rely on the homogeneous spectral-weight regime without quantitative control of deviations.	State regular-value/existence assumptions explicitly and add a correction analysis or worked example with nonconstant 
𝑆
𝑥
(
Ω
)
S
x
	​

(Ω).
M2	1; 4; 6	MEDIUM	The claim that the full record carries geometric information “beyond rate thermometry” is overstated. Once the detector model is fixed, the shell equations are still rate level sets. The new content is the operational selection of special thresholds from the full record.	Clarify this distinction and moderate the wording in the abstract, introduction, and discussion.
M3	3; 5	MEDIUM	There is no finite-sample inference layer. The paper claims operational detectability of the shells from hazards, covariances, and Fano factors, but gives no estimator, error bar, or sample-size analysis.	Add explicit estimators and at least a Monte Carlo or asymptotic uncertainty study showing how many clicks are needed to detect each shell.
M4	3.2	MEDIUM	Technical edge cases are not handled cleanly. Formulas are written mainly for 
𝜅
𝑟
≠
Γ
κ
r
	​


=Γ, yet the critical point may occur at 
Γ
𝑐
=
𝜅
𝑟
Γ
c
	​

=κ
r
	​

 when 
𝜅
𝑟
Δ
𝜏
=
1
κ
r
	​

Δτ=1. The closed form for 
Γ
𝑐
Γ
c
	​

 is also left implicit.	Add the equal-rate limit, branch structure, and a Lambert-
𝑊
W expression for 
Γ
𝑐
Γ
c
	​

, plus precise definitions of 
𝑆
𝑥
(
Ω
)
S
x
	​

(Ω) and positivity assumptions.
M5	6	MEDIUM	The discussion generalizes the memory-shell mechanism to arbitrary recovery kernels and monotone-hazard renewal detectors, but no theorem or even sketch is given for that extension.	Either prove the generalization, or explicitly downgrade it to conjecture/outlook.
M6	1; 6	MEDIUM	Literature positioning is incomplete in several directly relevant directions: detector-based measurement theory, detector thermalization, detector-based geometry/topology probing, and waiting-time/inverse counting statistics.	Expand the introduction and discussion with the missing references and explain precisely what is new relative to them.
L1	5.4	LOW	The worked example uses two modes with the same 
𝐶
=
Δ
𝜏
Γ
𝑐
/
log
⁡
𝜙
C=ΔτΓ
c
	​

/logϕ, so it does not actually illustrate the two-mode local inversion logic of theorem 5.5.	Replace one mode so 
𝐶
1
≠
𝐶
2
C
1
	​


=C
2
	​

 and compute the Jacobian numerically.
L2	Throughout	LOW	Notation and claim calibration need tightening. In particular, 
Γ
Γ and 
Γ
+
Γ
+
	​

 are alternated, and “thermality” is sometimes used where “record benchmark” would be safer.	Clean up notation and soften rhetoric where the result is conditional on the detector model.
4. Missing references

At minimum, I would expect the manuscript to discuss the following related work.

Operational detector-measurement foundations: Polo-Gómez, Garay and Martín-Martínez, A detector-based measurement theory for quantum field theory; Tjoa, López Gutiérrez, Sachs and Martín-Martínez, What makes a particle detector click; and Perche et al., Particle Detectors from Localized Quantum Field Theories. These are directly relevant to the measurement/reset interpretation of the click model. 
arXiv
+2
arXiv
+2

Detector thermality and stationary asymptotic states: Fewster, Juárez-Aubry and Louko, Waiting for Unruh; Garay, Martín-Martínez and de Ramón, Thermalization of particle detectors: The Unruh effect and its reverse; Juárez-Aubry and Moustos, Asymptotic states for stationary Unruh-DeWitt detectors; and Perche, General features of the thermalization of particle detectors and the Unruh effect. These would materially strengthen the paper’s framing of KMS thermality and stationary detector behavior. 
arXiv
+3
arXiv
+3
arXiv
+3

Detector-based geometry and topology probing: Ng, Mann and Martín-Martínez on the hollow-shell problem and on distinguishing the 
𝑅
𝑃
3
RP
3
 geon from Schwarzschild; also Tjoa and Mann on UDW detectors in static spherically symmetric spacetimes. These are important prior examples of extracting geometric or nonlocal information with detectors. 
arXiv
+2
arXiv
+2

Waiting-time and inverse counting-statistics methodology: Brandes, Waiting Times and Noise in Single Particle Transport, and Bruderer et al., Inverse counting statistics for stochastic and open quantum systems. These are not UDW papers, but they are directly relevant methodological precedents for the renewal, hazard, spectral-density, Fano-factor, and inverse-statistics aspects of this manuscript. 
arXiv
+1

5. Specific improvements needed to reach acceptance

First, the submission must become self-contained enough for a referee to verify the core claims.

Second, the paper must sharpen the physical meaning of its central benchmark. Right now the Parry-measure condition is mathematically neat, but it is not yet convincingly established as a notion of detector thermality.

Third, the click-record model needs a clearer microscopic bridge to an actual sampled UDW detector. At present the paper reads partly as UDW response theory fed into a phenomenological counter model.

Fourth, the strongest geometric claims need tighter conditions. The manuscript should either quantify when the homogeneous spectral-weight approximation is valid, or restrict the inverse claims more sharply.

Fifth, the operational side needs to be strengthened. A paper about extracting geometry from full click records should show how those observables would actually be estimated from finite data.

6. Concrete fixes for each BLOCKER and MEDIUM issue

B1. Missing derivations / supplement
Add a supplement or appendix containing full proofs of propositions 3.2 to 3.5 and theorems 5.3 and 5.5. In the main text, insert short proof roadmaps of 3 to 6 lines for each major result. If the supplement already exists, resubmit it with the manuscript and cite exact appendix numbers from the statements.

B2. Under-justified “symbolic thermality”
Add a dedicated subsection that compares three notions: detailed-balance thermality, Gibbs thermalization, and the Parry/max-entropy symbolic law on the golden-mean grammar. Then either justify why the last should be called thermality, or rename the whole construction. My recommendation is to rename it unless the authors can derive a genuine thermodynamic principle behind it.

B3. No microscopic bridge from UDW detector to click model
Specify an explicit protocol: readout every 
Δ
𝜏
Δτ, post-click reset, hidden refractory state, and exponential recovery generated by a two-state master equation. Then derive 
𝑇
0
T
0
	​

 and 
𝑇
1
T
1
	​

 from that protocol. If the authors do not want to do this, they should narrow the claim to “a phenomenological dead-time/recovery counter driven by the stationary UDW excitation rate,” and cite the detector-measurement foundation papers above. 
arXiv
+2
arXiv
+2

M1. Shell regularity and homogeneous spectral-weight assumptions
State explicitly that the shell loci are regular level sets under appropriate nonvanishing-gradient conditions, otherwise call them “loci” rather than “hypersurfaces.” Then add either one nonhomogeneous example, or an error bound of the form 
𝑆
𝑥
𝜙
/
𝑆
𝑥
m
e
m
=
1
+
𝑂
(
𝜀
)
S
x
ϕ
	​

	​

/S
x
mem
	​

	​

=1+O(ε) to quantify the correction to the ratio law.

M2. “Beyond rate thermometry” overclaim
Revise the abstract, introduction, and discussion so the claim becomes precise: the full record does not create a new geometry observable independent of the rate, but it selects special operational thresholds not visible from a rate-only summary of the same data. That is still a good claim, and it is more defensible.

M3. No finite-sample observability analysis
Introduce explicit estimators for the hazard, covariance ratio, and Fano factor from a finite binary record. Then add a numerical section with simulated click records showing detection power for 
Σ
𝜙
Σ
ϕ
	​

 and 
Σ
m
e
m
Σ
mem
	​

 as a function of record length.

M4. Technical edge cases omitted
Add a short appendix handling the 
𝜅
𝑟
=
Γ
κ
r
	​

=Γ limit and the special case 
𝜅
𝑟
Δ
𝜏
=
1
κ
r
	​

Δτ=1. Give 
Γ
𝑐
Γ
c
	​

 explicitly via Lambert 
𝑊
W, with the branch choice stated. Also define 
𝑆
𝑥
(
Ω
)
S
x
	​

(Ω) precisely from the response or commutator spectrum and state the assumptions under which it is positive.

M5. Unsupported generalization beyond exponential recovery
Either prove a general theorem for nonexponential recovery kernels, or rewrite the discussion to say that this is a conjectural extension suggested by the exponential model. Right now it reads stronger than the paper demonstrates.

M6. Incomplete literature positioning
Expand the introduction by one substantial paragraph and the discussion by one short paragraph. Distinguish clearly between prior work on detector thermality, prior work on operational detector measurement theory, prior work on detector-based geometry/topology probing, and the general counting-statistics literature. Then explain, in one sentence each, what this paper adds beyond those lines. 
arXiv
+7
arXiv
+7
arXiv
+7

In one sentence: this is an interesting manuscript with a real idea in it, but it needs substantial reframing and technical strengthening before it is ready for acceptance.