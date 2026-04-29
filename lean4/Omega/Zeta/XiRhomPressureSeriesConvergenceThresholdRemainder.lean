import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Omega.Zeta

noncomputable section

/-- The root-of-unity angle used in the local pressure expansion. -/
def xi_rhom_pressure_series_convergence_threshold_remainder_angle (m : ℕ) : ℝ :=
  2 * Real.pi / (m : ℝ)

/-- The Cauchy comparison ratio `|t_m| / r`. -/
def xi_rhom_pressure_series_convergence_threshold_remainder_ratio (m : ℕ) (r : ℝ) : ℝ :=
  |xi_rhom_pressure_series_convergence_threshold_remainder_angle m| / r

/-- Concrete convergence-in-the-disc predicate for the local pressure series at `t_m`. -/
def xi_rhom_pressure_series_convergence_threshold_remainder_localSeriesConverges
    (m : ℕ) (r : ℝ) : Prop :=
  |xi_rhom_pressure_series_convergence_threshold_remainder_angle m| < r

/-- The geometric Cauchy tail majorant for the even Taylor tail after order `2K`. -/
def xi_rhom_pressure_series_convergence_threshold_remainder_envelope
    (m K : ℕ) (r M : ℝ) : ℝ :=
  M *
    (xi_rhom_pressure_series_convergence_threshold_remainder_ratio m r) ^ (2 * K + 2) /
      (1 - (xi_rhom_pressure_series_convergence_threshold_remainder_ratio m r) ^ 2)

/-- Additive Taylor-remainder bound by the Cauchy geometric envelope. -/
def xi_rhom_pressure_series_convergence_threshold_remainder_remainderBound
    (m K : ℕ) (r M additiveRemainder : ℝ) : Prop :=
  |additiveRemainder| ≤
    xi_rhom_pressure_series_convergence_threshold_remainder_envelope m K r M

/-- Exponential relative-error bound obtained from the additive logarithmic remainder. -/
def xi_rhom_pressure_series_convergence_threshold_remainder_relativeErrorBound
    (m K : ℕ) (r M additiveRemainder : ℝ) : Prop :=
  Real.exp |additiveRemainder| - 1 ≤
    Real.exp (xi_rhom_pressure_series_convergence_threshold_remainder_envelope m K r M) - 1

/-- Paper label:
`thm:xi-rhom-pressure-series-convergence-threshold-remainder`.

The external analytic input is the radius certificate
`|t_m| < r` and the Cauchy coefficient audit giving the additive tail bound. The final clause is
then the monotonicity of the exponential map applied to that additive remainder. -/
theorem paper_xi_rhom_pressure_series_convergence_threshold_remainder
    (m K : ℕ) (r M additiveRemainder : ℝ)
    (_hm : 6 ≤ m)
    (hRadius :
      xi_rhom_pressure_series_convergence_threshold_remainder_localSeriesConverges m r)
    (hRemainder :
      xi_rhom_pressure_series_convergence_threshold_remainder_remainderBound
        m K r M additiveRemainder) :
    xi_rhom_pressure_series_convergence_threshold_remainder_localSeriesConverges m r ∧
      xi_rhom_pressure_series_convergence_threshold_remainder_remainderBound
        m K r M additiveRemainder ∧
        xi_rhom_pressure_series_convergence_threshold_remainder_relativeErrorBound
          m K r M additiveRemainder := by
  refine ⟨hRadius, hRemainder, ?_⟩
  unfold xi_rhom_pressure_series_convergence_threshold_remainder_relativeErrorBound
  unfold xi_rhom_pressure_series_convergence_threshold_remainder_remainderBound at hRemainder
  exact sub_le_sub_right (Real.exp_le_exp.mpr hRemainder) 1

end

end Omega.Zeta
