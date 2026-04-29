import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- The diagonal ellipsoid volume ratio attached to the prime-weight profile `M`. -/
def godelEllipsoidVolumeRatio (M : Fin m → ℕ) : ℝ :=
  ∏ i : Fin m, ((M i : ℝ) + 1)

/-- The Gödel register is the squared Jacobian factor of the diagonal prime-weight map. -/
def godelRegister (M : Fin m → ℕ) : ℝ :=
  (godelEllipsoidVolumeRatio M) ^ 2

/-- Paper label: `prop:fold-gauge-anomaly-godel-ellipsoid-volume`. -/
theorem paper_fold_gauge_anomaly_godel_ellipsoid_volume (m : ℕ) (M : Fin m → ℕ) :
    godelEllipsoidVolumeRatio M = Real.sqrt (godelRegister M) := by
  rw [godelRegister, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  unfold godelEllipsoidVolumeRatio
  exact Finset.prod_nonneg fun i _ => by
    positivity

end

end Omega.Folding
