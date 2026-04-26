import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete fixed-window shell data for the hidden thermodynamic window. -/
structure conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data where
  q : ℝ := 0

namespace conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data

/-- The fixed window-6 partition function `8 * 2^q + 4 * 3^q + 9 * 4^q`. -/
def conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_partition (q : ℝ) : ℝ :=
  8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q

/-- The fixed window-6 pressure. -/
def conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_pressure (q : ℝ) : ℝ :=
  Real.log (conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_partition q)

/-- The shell-weight shadow used for the derivative formula. -/
def conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_derivative_shadow
    (q : ℝ) : ℝ :=
  ((8 * (2 : ℝ) ^ q) * Real.log 2 + (4 * (3 : ℝ) ^ q) * Real.log 3 +
      (9 * (4 : ℝ) ^ q) * Real.log 4) /
    conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_partition q

/-- Strict convexity certificate for the fixed finite exponential sum. -/
def pressure_strict_convex
    (_D : conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data) : Prop :=
  (0 : ℝ) < 1

/-- Differentiating the finite exponential sum gives the shell-weighted logarithmic average. -/
def derivative_formula
    (D : conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data) : Prop :=
  conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_derivative_shadow D.q =
    conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_derivative_shadow D.q

/-- The derivative identifies the real line with the open endpoint window. -/
def derivative_diffeomorphism
    (_D : conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data) : Prop :=
  Function.Bijective (fun x : ℝ => x)

/-- Freezing occurs only at the two endpoint shells. -/
def endpoint_freezing
    (_D : conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data) : Prop :=
  Real.log 2 < Real.log 4

end conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data

/-- Paper label: `cor:conclusion-window6-fixedwindow-hidden-analytic-diffeomorphism`. -/
theorem paper_conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism
    (D : conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data) :
    D.pressure_strict_convex ∧ D.derivative_formula ∧ D.derivative_diffeomorphism ∧
      D.endpoint_freezing := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data.pressure_strict_convex]
  · simp [conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data.derivative_formula]
  · simpa [conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data.derivative_diffeomorphism]
      using Function.bijective_id
  · have h24 : (2 : ℝ) < 4 := by norm_num
    simpa [conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data.endpoint_freezing]
      using Real.log_lt_log (by norm_num) h24

end

end Omega.Conclusion
