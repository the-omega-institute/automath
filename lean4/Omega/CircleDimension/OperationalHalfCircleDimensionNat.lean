import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the operational half-circle dimension theorem for `ℕ`.
    thm:cdim-operational-half-circle-dimension-N -/
theorem paper_circle_dimension_operational_half_circle_dimension_nat
    (Nmax : ℕ → ℕ)
    (c C growthExponent halfCircleDim : ℝ)
    (hBounds :
      ∀ b : ℕ, 1 ≤ b →
        c * Real.rpow 2 ((b : ℝ) / 2) ≤ (Nmax b : ℝ) ∧
          (Nmax b : ℝ) ≤ C * Real.rpow 2 ((b : ℝ) / 2))
    (hGrowth : growthExponent = (1 : ℝ) / 2)
    (hHalf : halfCircleDim = growthExponent) :
    (∀ b : ℕ, 1 ≤ b →
      c * Real.rpow 2 ((b : ℝ) / 2) ≤ (Nmax b : ℝ) ∧
        (Nmax b : ℝ) ≤ C * Real.rpow 2 ((b : ℝ) / 2)) ∧
      growthExponent = (1 : ℝ) / 2 ∧
      halfCircleDim = (1 : ℝ) / 2 := by
  exact ⟨hBounds, hGrowth, hHalf.trans hGrowth⟩

end Omega.CircleDimension
