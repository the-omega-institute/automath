import Omega.SPG.BayesFiniteMistakesSummable
import Omega.SPG.PrefixScanErrorBoundaryDimensionUpper

namespace Omega.SPG

/-- Witness that depth `mδ` is the first scan depth whose error profile falls below the target
    risk threshold `δ`. -/
def IsRiskThresholdDepth (ε : ℕ → ℝ) (δ : ℝ) (mδ : ℕ) : Prop :=
  ε mδ ≤ δ ∧ ∀ ⦃m : ℕ⦄, 1 ≤ m → m < mδ → δ < ε m

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for almost-sure eventual stabilization from strict boundary-dimension
    decay: the boundary-growth hypothesis implies summable scan error, and Borel-Cantelli then
    yields eventual stability.
    cor:spg-boundary-dimension-ae-stabilization -/
theorem paper_spg_boundary_dimension_ae_stabilization
    (boundaryDecay summableError eventualStability : Prop)
    (hDecay : boundaryDecay -> summableError)
    (hBC : summableError -> eventualStability) :
    boundaryDecay -> eventualStability := by
  intro hBoundary
  exact hBC (hDecay hBoundary)

set_option maxHeartbeats 400000 in
/-- Auxiliary package for the SPG clarity risk-threshold depth law: boundary-dimension decay
    yields the threshold-depth witness, the asymptotic inversion yields the logarithmic depth
    law, and sharper boundary counts upgrade the refinement. The paper-facing theorem name is
    provided in `ClarityRiskThresholdDepthLaw.lean` after the rebase.
    thm:spg-clarity-risk-threshold-depth-law -/
theorem paper_spg_clarity_risk_threshold_depth_law_package
    (ε : ℕ → ℝ) (δ : ℝ) (mδ : ℕ)
    (boundaryDecay asymptoticDepthLaw sharpBoundaryCount sharpDepthLaw : Prop)
    (hDepth : boundaryDecay -> IsRiskThresholdDepth ε δ mδ)
    (hAsymptotic :
      boundaryDecay -> IsRiskThresholdDepth ε δ mδ -> asymptoticDepthLaw)
    (hSharp :
      sharpBoundaryCount -> IsRiskThresholdDepth ε δ mδ -> sharpDepthLaw) :
    boundaryDecay ->
      IsRiskThresholdDepth ε δ mδ ∧
        asymptoticDepthLaw ∧
        (sharpBoundaryCount -> sharpDepthLaw) := by
  intro hBoundary
  have hThreshold : IsRiskThresholdDepth ε δ mδ := hDepth hBoundary
  exact ⟨hThreshold, hAsymptotic hBoundary hThreshold, fun hSharpBoundary => hSharp hSharpBoundary hThreshold⟩

end Omega.SPG
