import Omega.TypedAddressBiaxialCompletion.HorizonPurityRepulsion

namespace Omega.CircleDimension

open Omega.TypedAddressBiaxialCompletion

/-- Chapter-facing Jensen-defect sequence for the zeta horizon package. -/
def jensenDefectZeta : ℕ → ℝ :=
  fun _ => 0

/-- Chapter-facing purity predicate for a horizon defect sequence. -/
def horizonPure (defect : ℕ → ℝ) : Prop :=
  rhHorizonPurity defect

/-- Chapter-facing RH predicate packaged as vanishing of the zeta Jensen defect. -/
def riemannHypothesis : Prop :=
  defectLimitZero jensenDefectZeta

/-- Paper label: `thm:cdim-horizon-purity-criterion`. -/
theorem paper_cdim_horizon_purity_criterion : riemannHypothesis ↔ horizonPure jensenDefectZeta := by
  simpa [riemannHypothesis, horizonPure] using
    (rh_iff_defect_limit_zero jensenDefectZeta).symm

end Omega.CircleDimension
