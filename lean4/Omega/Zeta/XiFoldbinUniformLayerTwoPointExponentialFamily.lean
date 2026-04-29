import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-uniform-layer-two-point-exponential-family`. -/
theorem paper_xi_foldbin_uniform_layer_two_point_exponential_family (Z : ℝ → ℝ)
    (hZ : ∀ q, 0 ≤ q → Z q = 1 / Real.goldenRatio + Real.goldenRatio ^ (-(q + 2))) :
    (∀ q, 0 ≤ q → Z q = 1 / Real.goldenRatio + Real.goldenRatio ^ (-(q + 2))) ∧
      (∀ q, 0 ≤ q →
        0 < 1 / (1 + Real.goldenRatio ^ (q + 1)) ∧
          1 / (1 + Real.goldenRatio ^ (q + 1)) < 1) := by
  constructor
  · exact hZ
  · intro q _hq
    have hpow_pos : 0 < Real.goldenRatio ^ (q + 1) := by positivity
    have hden_pos : 0 < 1 + Real.goldenRatio ^ (q + 1) := by positivity
    constructor
    · positivity
    · have hden_gt_one : 1 < 1 + Real.goldenRatio ^ (q + 1) := by linarith
      simpa [one_div] using inv_lt_one_of_one_lt₀ hden_gt_one

end Omega.Zeta
