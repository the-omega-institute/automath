import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The Joukowsky boundary parameterization written in real coordinates. -/
def conclusion_analytic_holography_inversion_rigidity_joukowsky_modsquare (r θ : ℝ) : ℝ :=
  (r * Real.cos θ + (1 / r) * Real.cos θ) ^ 2 +
    (r * Real.sin θ - (1 / r) * Real.sin θ) ^ 2

/-- The symbolic second radial moment of the Haar pushforward on the corresponding ellipse. -/
def conclusion_analytic_holography_inversion_rigidity_second_radial_moment (r : ℝ) : ℝ :=
  r ^ 2 + (1 / r) ^ 2

private lemma conclusion_analytic_holography_inversion_rigidity_modsquare_formula
    {r : ℝ} (hr : 1 ≤ r) (θ : ℝ) :
    conclusion_analytic_holography_inversion_rigidity_joukowsky_modsquare r θ =
      conclusion_analytic_holography_inversion_rigidity_second_radial_moment r +
        2 * Real.cos (2 * θ) := by
  have hrne : r ≠ 0 := by
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    linarith
  unfold conclusion_analytic_holography_inversion_rigidity_joukowsky_modsquare
    conclusion_analytic_holography_inversion_rigidity_second_radial_moment
  have hcos : Real.cos θ ^ 2 - Real.sin θ ^ 2 = Real.cos (2 * θ) := by
    nlinarith [Real.cos_two_mul θ, Real.sin_sq_add_cos_sq θ]
  have hsum : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    (r * Real.cos θ + (1 / r) * Real.cos θ) ^ 2 + (r * Real.sin θ - (1 / r) * Real.sin θ) ^ 2 =
        (r ^ 2 + (1 / r) ^ 2) * (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
          2 * (r * (1 / r)) * (Real.cos θ ^ 2 - Real.sin θ ^ 2) := by
            ring
    _ = r ^ 2 + (1 / r) ^ 2 + 2 * (r * (1 / r)) * (Real.cos θ ^ 2 - Real.sin θ ^ 2) := by
          rw [hsum]
          ring
    _ = r ^ 2 + (1 / r) ^ 2 + 2 * Real.cos (2 * θ) := by
          have hrinv : r * (1 / r) = 1 := by field_simp [hrne]
          rw [hrinv, hcos]
          ring

private lemma conclusion_analytic_holography_inversion_rigidity_discriminant
    {r : ℝ} (hr : 1 ≤ r) :
    (conclusion_analytic_holography_inversion_rigidity_second_radial_moment r) ^ 2 - 4 =
      (r ^ 2 - (1 / r) ^ 2) ^ 2 := by
  have hrne : r ≠ 0 := by
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    linarith
  unfold conclusion_analytic_holography_inversion_rigidity_second_radial_moment
  field_simp [hrne]
  ring

private lemma conclusion_analytic_holography_inversion_rigidity_difference_nonneg
    {r : ℝ} (hr : 1 ≤ r) : 0 ≤ r ^ 2 - (1 / r) ^ 2 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsq : 1 ≤ r ^ 2 := by nlinarith
  have hinv : (1 / r) ≤ 1 := by
    simpa [one_div] using inv_le_one_of_one_le₀ hr
  have hsqinv : (1 / r) ^ 2 ≤ 1 := by
    nlinarith [hinv, one_div_nonneg.mpr (le_of_lt hrpos)]
  nlinarith

private lemma conclusion_analytic_holography_inversion_rigidity_sqrt_discriminant
    {r : ℝ} (hr : 1 ≤ r) :
    Real.sqrt
        ((conclusion_analytic_holography_inversion_rigidity_second_radial_moment r) ^ 2 - 4) =
      r ^ 2 - (1 / r) ^ 2 := by
  rw [conclusion_analytic_holography_inversion_rigidity_discriminant hr]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (conclusion_analytic_holography_inversion_rigidity_difference_nonneg hr)

private lemma conclusion_analytic_holography_inversion_rigidity_recover_square
    {r : ℝ} (hr : 1 ≤ r) :
    (conclusion_analytic_holography_inversion_rigidity_second_radial_moment r +
        Real.sqrt
          ((conclusion_analytic_holography_inversion_rigidity_second_radial_moment r) ^ 2 - 4)) /
      2 =
      r ^ 2 := by
  have hrne : r ≠ 0 := by
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    linarith
  rw [conclusion_analytic_holography_inversion_rigidity_sqrt_discriminant hr]
  unfold conclusion_analytic_holography_inversion_rigidity_second_radial_moment
  field_simp [hrne]
  ring

private lemma conclusion_analytic_holography_inversion_rigidity_recover_radius
    {r : ℝ} (hr : 1 ≤ r) :
    Real.sqrt
        ((conclusion_analytic_holography_inversion_rigidity_second_radial_moment r +
            Real.sqrt
              ((conclusion_analytic_holography_inversion_rigidity_second_radial_moment r) ^ 2 -
                4)) /
          2) =
      r := by
  rw [conclusion_analytic_holography_inversion_rigidity_recover_square hr]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (le_trans zero_le_one hr)

private lemma conclusion_analytic_holography_inversion_rigidity_moment_injective
    {r s : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (h : conclusion_analytic_holography_inversion_rigidity_second_radial_moment s =
      conclusion_analytic_holography_inversion_rigidity_second_radial_moment r) :
    s = r := by
  have hsq : s ^ 2 = r ^ 2 := by
    calc
      s ^ 2 =
          (conclusion_analytic_holography_inversion_rigidity_second_radial_moment s +
              Real.sqrt
                ((conclusion_analytic_holography_inversion_rigidity_second_radial_moment s) ^ 2 -
                  4)) /
            2 := by
              symm
              exact conclusion_analytic_holography_inversion_rigidity_recover_square hs
      _ =
          (conclusion_analytic_holography_inversion_rigidity_second_radial_moment r +
              Real.sqrt
                ((conclusion_analytic_holography_inversion_rigidity_second_radial_moment r) ^ 2 -
                  4)) /
            2 := by rw [h]
      _ = r ^ 2 := conclusion_analytic_holography_inversion_rigidity_recover_square hr
  nlinarith [hr, hs]

/-- Paper label: `thm:conclusion-analytic-holography-inversion-rigidity`. The concrete Lean
surrogate packages the Joukowsky boundary formula, the second radial moment, the quadratic recovery
of `r²`, the recovery of `r`, and the injectivity of the moment map on `[1, ∞)`. -/
theorem paper_conclusion_analytic_holography_inversion_rigidity
    {r s : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (∀ θ : ℝ,
      conclusion_analytic_holography_inversion_rigidity_joukowsky_modsquare r θ =
        conclusion_analytic_holography_inversion_rigidity_second_radial_moment r +
          2 * Real.cos (2 * θ)) ∧
      (conclusion_analytic_holography_inversion_rigidity_second_radial_moment r +
          Real.sqrt
            ((conclusion_analytic_holography_inversion_rigidity_second_radial_moment r) ^ 2 - 4)) /
        2 =
        r ^ 2 ∧
      Real.sqrt
          ((conclusion_analytic_holography_inversion_rigidity_second_radial_moment r +
              Real.sqrt
                ((conclusion_analytic_holography_inversion_rigidity_second_radial_moment r) ^ 2 -
                  4)) /
            2) =
        r ∧
      (conclusion_analytic_holography_inversion_rigidity_second_radial_moment s =
          conclusion_analytic_holography_inversion_rigidity_second_radial_moment r ↔
        s = r) := by
  refine ⟨conclusion_analytic_holography_inversion_rigidity_modsquare_formula hr, ?_, ?_, ?_⟩
  · exact conclusion_analytic_holography_inversion_rigidity_recover_square hr
  · exact conclusion_analytic_holography_inversion_rigidity_recover_radius hr
  · constructor
    · exact conclusion_analytic_holography_inversion_rigidity_moment_injective hr hs
    · intro hsr
      simp [hsr]

end

end Omega.Conclusion
