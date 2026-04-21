import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The central Poisson slice expanded through the sixth centered moment. -/
noncomputable def poissonCenterMomentSlice (μ₂ μ₄ μ₆ t : ℝ) : ℝ :=
  1 - μ₂ / t ^ 2 + μ₄ / t ^ 4 - μ₆ / t ^ 6

/-- Recover the second centered moment after subtracting the fourth- and sixth-order corrections. -/
noncomputable def poissonSecondMomentRecovery (Φ μ₄ μ₆ t : ℝ) : ℝ :=
  t ^ 2 * (1 - Φ) + μ₄ / t ^ 2 - μ₆ / t ^ 4

/-- Recover the fourth centered moment after subtracting the sixth-order correction. -/
noncomputable def poissonFourthMomentRecovery (Φ μ₂ μ₆ t : ℝ) : ℝ :=
  t ^ 4 * (Φ - 1 + μ₂ / t ^ 2) + μ₆ / t ^ 2

/-- Paper label: `prop:cdim-poisson-center-moment-spectrum`.

The center slice is the alternating even-moment expansion of `(1 + (Δ / t)^2)⁻¹`, and the
second and fourth centered moments are recovered recursively by clearing the lower-order terms. -/
theorem paper_cdim_poisson_center_moment_spectrum
    (μ₂ μ₄ μ₆ t : ℝ) (ht : t ≠ 0) :
    poissonCenterMomentSlice μ₂ μ₄ μ₆ t = 1 - μ₂ / t ^ 2 + μ₄ / t ^ 4 - μ₆ / t ^ 6 ∧
      poissonSecondMomentRecovery (poissonCenterMomentSlice μ₂ μ₄ μ₆ t) μ₄ μ₆ t = μ₂ ∧
      poissonFourthMomentRecovery (poissonCenterMomentSlice μ₂ μ₄ μ₆ t) μ₂ μ₆ t = μ₄ := by
  constructor
  · rfl
  constructor
  · unfold poissonSecondMomentRecovery poissonCenterMomentSlice
    field_simp [ht]
    ring
  · unfold poissonFourthMomentRecovery poissonCenterMomentSlice
    field_simp [ht]
    ring

end Omega.CircleDimension
