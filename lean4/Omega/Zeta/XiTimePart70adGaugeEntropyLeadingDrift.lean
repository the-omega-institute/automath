import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiFoldKappaGaugeFirstOrderConstants

namespace Omega.Zeta

noncomputable section

/-- Concrete seed parameter for the gauge-entropy leading-drift wrapper: the window depth. -/
abbrev xi_time_part70ad_gauge_entropy_leading_drift_data : Type :=
  ℕ

namespace xi_time_part70ad_gauge_entropy_leading_drift_data

/-- The Renyi/hidden-logmultiplicity leading constant written in the thermodynamic denominator. -/
def xi_time_part70ad_gauge_entropy_leading_drift_kappa_constant : ℝ :=
  -Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2)

/-- The same leading constant in the Fibonacci closed form. -/
def xi_time_part70ad_gauge_entropy_leading_drift_fibonacci_constant : ℝ :=
  -Real.log Real.goldenRatio / (Real.goldenRatio * Real.sqrt 5)

/-- The certified main term inherited from the gauge-density thermodynamic constant. -/
def xi_time_part70ad_gauge_entropy_leading_drift_gauge_main
    (D : xi_time_part70ad_gauge_entropy_leading_drift_data) : ℝ :=
  xiFoldbinGaugeDensityThermodynamicMain D

/-- The matching Renyi/hidden-logmultiplicity affine main term. -/
def xi_time_part70ad_gauge_entropy_leading_drift_kappa_main
    (D : xi_time_part70ad_gauge_entropy_leading_drift_data) : ℝ :=
  (D : ℝ) * Real.log (2 / Real.goldenRatio) +
    xi_time_part70ad_gauge_entropy_leading_drift_fibonacci_constant

/-- Concrete paper-facing statement for the leading drift and its one-nat gauge shift. -/
def xi_time_part70ad_gauge_entropy_leading_drift_statement
    (D : xi_time_part70ad_gauge_entropy_leading_drift_data) : Prop :=
  xi_time_part70ad_gauge_entropy_leading_drift_kappa_constant =
      xi_time_part70ad_gauge_entropy_leading_drift_fibonacci_constant ∧
    xi_time_part70ad_gauge_entropy_leading_drift_gauge_main D =
      (D : ℝ) * Real.log (2 / Real.goldenRatio) - 1 +
        xi_time_part70ad_gauge_entropy_leading_drift_fibonacci_constant ∧
    xi_time_part70ad_gauge_entropy_leading_drift_gauge_main D =
      xi_time_part70ad_gauge_entropy_leading_drift_kappa_main D - 1

end xi_time_part70ad_gauge_entropy_leading_drift_data

open xi_time_part70ad_gauge_entropy_leading_drift_data

lemma xi_time_part70ad_gauge_entropy_leading_drift_golden_denominator_eq :
    1 + Real.goldenRatio ^ 2 = Real.goldenRatio * Real.sqrt 5 := by
  rw [Real.goldenRatio_sq]
  unfold Real.goldenRatio
  have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
    norm_num [Real.sq_sqrt]
  nlinarith

lemma xi_time_part70ad_gauge_entropy_leading_drift_golden_denominator :
    (1 : ℝ) / (1 + Real.goldenRatio ^ 2) =
      1 / (Real.goldenRatio * Real.sqrt 5) := by
  rw [xi_time_part70ad_gauge_entropy_leading_drift_golden_denominator_eq]

/-- Paper label: `thm:xi-time-part70ad-gauge-entropy-leading-drift`. -/
theorem paper_xi_time_part70ad_gauge_entropy_leading_drift
    (D : xi_time_part70ad_gauge_entropy_leading_drift_data) :
    D.xi_time_part70ad_gauge_entropy_leading_drift_statement := by
  have hconstants :
      xi_time_part70ad_gauge_entropy_leading_drift_kappa_constant =
        xi_time_part70ad_gauge_entropy_leading_drift_fibonacci_constant := by
    unfold xi_time_part70ad_gauge_entropy_leading_drift_kappa_constant
      xi_time_part70ad_gauge_entropy_leading_drift_fibonacci_constant
    rw [xi_time_part70ad_gauge_entropy_leading_drift_golden_denominator_eq]
  have hverified := paper_xi_fold_kappa_gauge_first_order_constants D
  dsimp at hverified
  rcases hverified with ⟨_hkappa, hgauge, hgauge_shift⟩
  refine ⟨hconstants, ?_, ?_⟩
  · unfold xi_time_part70ad_gauge_entropy_leading_drift_gauge_main
      xi_time_part70ad_gauge_entropy_leading_drift_fibonacci_constant
    have hrewrite :
        -Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2) =
          -Real.log Real.goldenRatio / (Real.goldenRatio * Real.sqrt 5) := by
      rw [xi_time_part70ad_gauge_entropy_leading_drift_golden_denominator_eq]
    rw [← hrewrite]
    linarith
  · unfold xi_time_part70ad_gauge_entropy_leading_drift_gauge_main
      xi_time_part70ad_gauge_entropy_leading_drift_kappa_main
      xi_time_part70ad_gauge_entropy_leading_drift_fibonacci_constant
    have hrewrite :
        -Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2) =
          -Real.log Real.goldenRatio / (Real.goldenRatio * Real.sqrt 5) := by
      rw [xi_time_part70ad_gauge_entropy_leading_drift_golden_denominator_eq]
    rw [← hrewrite]
    linarith

end

end Omega.Zeta
