import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Under the determinant and trace scaling laws, the visibility complexity acquires exactly one
copy of `log m`.
    cor:xi-toeplitz-visibility-complexity-anomaly -/
theorem paper_xi_toeplitz_visibility_complexity_anomaly (k : Real) (S V : Real -> Real)
    (hS : ∀ m : Real, S m = S 1 + k * Real.log m)
    (hV : ∀ m : Real, V m = V 1 - Real.log m) :
    ∀ m : Real, S m + (k - 1) * V m = (S 1 + (k - 1) * V 1) + Real.log m := by
  intro m
  rw [hS m, hV m]
  ring

end Omega.Zeta
