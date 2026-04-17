import Mathlib.Tactic

namespace Omega.Discussion

/-- Scalar packaging of the KL decomposition term
`I(ω;τ | y) + D_KL(L(τ | y) || S_y)`. -/
def epsZkConditionalRelativeEntropy (mutualInfo residual : ℝ) : ℝ :=
  mutualInfo + residual

/-- Pinsker envelope controlling transcript total variation from an `ε`-relative-entropy bound. -/
noncomputable def epsZkPinskerEnvelope (ε : ℝ) : ℝ :=
  Real.sqrt (ε / 2)

/-- Bayes-risk improvement from giving the learner the transcript in addition to the public readout.
-/
def epsZkBayesRiskImprovement (riskFromReadout riskFromTranscript : ℝ) : ℝ :=
  riskFromReadout - riskFromTranscript

/-- Paper-facing scalar form of the `ε`-zero-knowledge argument: the conditional mutual
information is the nonnegative part of the conditional relative entropy, Pinsker bounds the
transcript total variation by `√(ε / 2)`, and any Bayes-risk improvement controlled by that total
variation inherits the same upper bound.
    thm:discussion-epszk-cmi-and-risk-improvement-bound -/
theorem paper_discussion_epszk_cmi_and_risk_improvement_bound
    (ε mutualInfo residual riskFromReadout riskFromTranscript tv : ℝ)
    (hDecomp : epsZkConditionalRelativeEntropy mutualInfo residual = ε)
    (hResidual : 0 ≤ residual)
    (hPinsker : tv ≤ epsZkPinskerEnvelope ε)
    (hTransfer :
      epsZkBayesRiskImprovement riskFromReadout riskFromTranscript ≤ tv) :
    mutualInfo ≤ ε ∧
      epsZkBayesRiskImprovement riskFromReadout riskFromTranscript ≤ epsZkPinskerEnvelope ε := by
  have hCmi : mutualInfo ≤ ε := by
    unfold epsZkConditionalRelativeEntropy at hDecomp
    linarith
  exact ⟨hCmi, le_trans hTransfer hPinsker⟩

end Omega.Discussion
