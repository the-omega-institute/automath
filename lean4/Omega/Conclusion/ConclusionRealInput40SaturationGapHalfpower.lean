import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInput40PressureFreezing

namespace Omega.Conclusion

/-- Concrete data for the real-input-40 saturation-gap half-power law.  The pressure-freezing
package supplies the zero-temperature half-slope, while the remaining fields record the audited
Puiseux leading constant and the rewrite between `u` and `theta` coordinates. -/
structure conclusion_realinput40_saturation_gap_halfpower_data where
  conclusion_realinput40_saturation_gap_halfpower_freezingData :
    Omega.SyncKernelRealInput.real_input_40_pressure_freezing_data
  conclusion_realinput40_saturation_gap_halfpower_c : ℝ
  conclusion_realinput40_saturation_gap_halfpower_d : ℝ
  conclusion_realinput40_saturation_gap_halfpower_alpha : ℝ → ℝ
  conclusion_realinput40_saturation_gap_halfpower_pressureThetaDerivative : ℝ → ℝ
  conclusion_realinput40_saturation_gap_halfpower_uHalfPower : ℝ → ℝ
  conclusion_realinput40_saturation_gap_halfpower_thetaHalfPower : ℝ → ℝ
  conclusion_realinput40_saturation_gap_halfpower_alpha_eq_pressure_derivative_exp :
    ∀ θ : ℝ,
      conclusion_realinput40_saturation_gap_halfpower_alpha (Real.exp θ) =
        conclusion_realinput40_saturation_gap_halfpower_pressureThetaDerivative θ
  conclusion_realinput40_saturation_gap_halfpower_theta_rewrite :
    ∀ θ : ℝ,
      conclusion_realinput40_saturation_gap_halfpower_thetaHalfPower θ =
        conclusion_realinput40_saturation_gap_halfpower_uHalfPower (Real.exp θ)
  conclusion_realinput40_saturation_gap_halfpower_u_gap_law :
    ∀ u : ℝ,
      (1 / 2 : ℝ) - conclusion_realinput40_saturation_gap_halfpower_alpha u =
        (conclusion_realinput40_saturation_gap_halfpower_d /
            (2 * conclusion_realinput40_saturation_gap_halfpower_c)) *
          conclusion_realinput40_saturation_gap_halfpower_uHalfPower u

/-- The leading half-power gap constant `d/(2c)`. -/
noncomputable def conclusion_realinput40_saturation_gap_halfpower_leading_constant
    (D : conclusion_realinput40_saturation_gap_halfpower_data) : ℝ :=
  D.conclusion_realinput40_saturation_gap_halfpower_d /
    (2 * D.conclusion_realinput40_saturation_gap_halfpower_c)

/-- The exact half-power gap law in `u` and in the logarithmic coordinate `u = exp theta`,
together with the already packaged right-endpoint square-root scaling. -/
def conclusion_realinput40_saturation_gap_halfpower_statement
    (D : conclusion_realinput40_saturation_gap_halfpower_data) : Prop :=
  D.conclusion_realinput40_saturation_gap_halfpower_freezingData.right_sqrt_scaling ∧
    (∀ u : ℝ,
      (1 / 2 : ℝ) - D.conclusion_realinput40_saturation_gap_halfpower_alpha u =
        conclusion_realinput40_saturation_gap_halfpower_leading_constant D *
          D.conclusion_realinput40_saturation_gap_halfpower_uHalfPower u) ∧
      ∀ θ : ℝ,
        (1 / 2 : ℝ) -
            D.conclusion_realinput40_saturation_gap_halfpower_pressureThetaDerivative θ =
          conclusion_realinput40_saturation_gap_halfpower_leading_constant D *
            D.conclusion_realinput40_saturation_gap_halfpower_thetaHalfPower θ

/-- Paper label: `thm:conclusion-realinput40-saturation-gap-halfpower`. -/
theorem paper_conclusion_realinput40_saturation_gap_halfpower
    (D : conclusion_realinput40_saturation_gap_halfpower_data) :
    conclusion_realinput40_saturation_gap_halfpower_statement D := by
  have hfreezing :=
    Omega.SyncKernelRealInput.paper_real_input_40_pressure_freezing
      D.conclusion_realinput40_saturation_gap_halfpower_freezingData
  refine ⟨hfreezing.2.1, ?_, ?_⟩
  · intro u
    simpa [conclusion_realinput40_saturation_gap_halfpower_leading_constant] using
      D.conclusion_realinput40_saturation_gap_halfpower_u_gap_law u
  · intro θ
    calc
      (1 / 2 : ℝ) -
          D.conclusion_realinput40_saturation_gap_halfpower_pressureThetaDerivative θ =
          (1 / 2 : ℝ) -
            D.conclusion_realinput40_saturation_gap_halfpower_alpha (Real.exp θ) := by
            rw [D.conclusion_realinput40_saturation_gap_halfpower_alpha_eq_pressure_derivative_exp θ]
      _ =
          conclusion_realinput40_saturation_gap_halfpower_leading_constant D *
            D.conclusion_realinput40_saturation_gap_halfpower_uHalfPower (Real.exp θ) := by
            simpa [conclusion_realinput40_saturation_gap_halfpower_leading_constant] using
              D.conclusion_realinput40_saturation_gap_halfpower_u_gap_law (Real.exp θ)
      _ =
          conclusion_realinput40_saturation_gap_halfpower_leading_constant D *
            D.conclusion_realinput40_saturation_gap_halfpower_thetaHalfPower θ := by
            rw [D.conclusion_realinput40_saturation_gap_halfpower_theta_rewrite θ]

end Omega.Conclusion
