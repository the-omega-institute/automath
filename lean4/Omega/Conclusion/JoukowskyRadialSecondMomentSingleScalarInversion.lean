import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete scalar datum for the radial Joukowsky second-moment inversion. -/
structure conclusion_joukowsky_radial_second_moment_single_scalar_inversion_data where
  radius : ℝ
  radius_ge_one : 1 ≤ radius

namespace conclusion_joukowsky_radial_second_moment_single_scalar_inversion_data

/-- The second-moment limit supplied by radial identifiability. -/
def secondMomentLimit
    (D : conclusion_joukowsky_radial_second_moment_single_scalar_inversion_data) : ℝ :=
  D.radius ^ 2 + (D.radius⁻¹) ^ 2

/-- The quadratic scalar `r^2 + r^{-2}`. -/
def radiusSquaredPlusInverse
    (D : conclusion_joukowsky_radial_second_moment_single_scalar_inversion_data) : ℝ :=
  D.radius ^ 2 + (D.radius⁻¹) ^ 2

/-- The displayed square-root reconstruction from the single scalar channel. -/
def reconstructionValue
    (D : conclusion_joukowsky_radial_second_moment_single_scalar_inversion_data) : ℝ :=
  Real.sqrt
    ((D.secondMomentLimit +
      Real.sqrt (D.secondMomentLimit ^ 2 - 4)) / 2)

end conclusion_joukowsky_radial_second_moment_single_scalar_inversion_data

/-- Paper label:
`prop:conclusion-joukowsky-radial-second-moment-single-scalar-inversion`.  For `r ≥ 1`,
the scalar `r^2 + r^{-2}` determines `r` through the positive square-root branch. -/
theorem paper_conclusion_joukowsky_radial_second_moment_single_scalar_inversion
    (D : conclusion_joukowsky_radial_second_moment_single_scalar_inversion_data) :
    D.secondMomentLimit = D.radiusSquaredPlusInverse ∧
      D.reconstructionValue = D.radius := by
  refine ⟨rfl, ?_⟩
  let r : ℝ := D.radius
  have hr1 : 1 ≤ r := D.radius_ge_one
  have hr0 : 0 ≤ r := by linarith
  have hrpos : 0 < r := by linarith
  have hne : r ≠ 0 := ne_of_gt hrpos
  have hinv_sq_le : r⁻¹ ^ 2 ≤ r ^ 2 := by
    rw [sq_le_sq]
    rw [abs_of_nonneg (inv_nonneg.mpr hr0), abs_of_nonneg hr0]
    have hinv_le_one : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
    linarith
  have hsqrt_disc :
      Real.sqrt ((r ^ 2 + r⁻¹ ^ 2) ^ 2 - 4) = r ^ 2 - r⁻¹ ^ 2 := by
    have hdisc : (r ^ 2 + r⁻¹ ^ 2) ^ 2 - 4 = (r ^ 2 - r⁻¹ ^ 2) ^ 2 := by
      field_simp [hne]
      ring
    rw [hdisc, Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (sub_nonneg.mpr hinv_sq_le)
  have hinner :
      ((r ^ 2 + r⁻¹ ^ 2) + Real.sqrt ((r ^ 2 + r⁻¹ ^ 2) ^ 2 - 4)) / 2 = r ^ 2 := by
    rw [hsqrt_disc]
    ring
  dsimp [conclusion_joukowsky_radial_second_moment_single_scalar_inversion_data.reconstructionValue,
    conclusion_joukowsky_radial_second_moment_single_scalar_inversion_data.secondMomentLimit,
    r]
  rw [hinner, Real.sqrt_sq_eq_abs, abs_of_nonneg hr0]

end

end Omega.Conclusion
