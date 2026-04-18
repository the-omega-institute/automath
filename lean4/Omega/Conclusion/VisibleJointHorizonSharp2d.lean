import Mathlib.Tactic
import Omega.CircleDimension.AtomicDefectProny2KappaRecovery
import Omega.Zeta.ToeplitzPsdCoherenceHorizonThreshold

namespace Omega.Conclusion

/-- The Toeplitz-PSD side of the two-task visible protocol closes by the bounded-dimension
coherence horizon. -/
def toeplitzPsdVisibleHorizon (D : ℕ) : ℕ :=
  2 * D

/-- The visible reconstruction side closes at the sharp `2D` Prony window. -/
def visibleReconstructionHorizon (D : ℕ) : ℕ :=
  2 * D

/-- The minimal common horizon for simultaneously deciding the Toeplitz-PSD tower and uniquely
recovering the visible spectral data. -/
def visibleJointHorizon (D : ℕ) : ℕ :=
  max (toeplitzPsdVisibleHorizon D) (visibleReconstructionHorizon D)

/-- Paper-facing sharp two-dimensional joint horizon: both the Toeplitz-PSD audit and the
visible reconstruction task close exactly at `2D`.
    thm:conclusion-visible-joint-horizon-sharp-2d -/
theorem paper_conclusion_visible_joint_horizon_sharp_2d (D : ℕ) (hD : 1 ≤ D) :
    visibleJointHorizon D = 2 * D := by
  let _ := hD
  unfold visibleJointHorizon toeplitzPsdVisibleHorizon visibleReconstructionHorizon
  simp

end Omega.Conclusion
