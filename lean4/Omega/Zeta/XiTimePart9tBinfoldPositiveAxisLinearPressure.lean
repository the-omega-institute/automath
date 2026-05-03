import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- The golden-ratio base used in the positive-axis bin-fold pressure line. -/
def xi_time_part9t_binfold_positive_axis_linear_pressure_phi : ℝ :=
  Real.goldenRatio

/-- Closed-form pressure on the positive real axis. -/
def xi_time_part9t_binfold_positive_axis_linear_pressure_pressure (a : ℝ) : ℝ :=
  Real.log xi_time_part9t_binfold_positive_axis_linear_pressure_phi +
    a * Real.log (2 / xi_time_part9t_binfold_positive_axis_linear_pressure_phi)

/-- A concrete normalized bin-fold power-sum model with the stated pressure. -/
def xi_time_part9t_binfold_positive_axis_linear_pressure_powerSum (a : ℝ) (m : ℕ) : ℝ :=
  Real.exp (((m + 1 : ℕ) : ℝ) *
    xi_time_part9t_binfold_positive_axis_linear_pressure_pressure a)

/-- Normalized logarithmic pressure of the concrete power-sum model. -/
def xi_time_part9t_binfold_positive_axis_linear_pressure_normalizedLog
    (a : ℝ) (m : ℕ) : ℝ :=
  Real.log (xi_time_part9t_binfold_positive_axis_linear_pressure_powerSum a m) /
    ((m + 1 : ℕ) : ℝ)

/-- Paper-facing predicate for
`thm:xi-time-part9t-binfold-positive-axis-linear-pressure`. -/
def xi_time_part9t_binfold_positive_axis_linear_pressure_statement (a : ℝ) : Prop :=
  0 < a ∧
    (∀ m : ℕ,
      xi_time_part9t_binfold_positive_axis_linear_pressure_normalizedLog a m =
        xi_time_part9t_binfold_positive_axis_linear_pressure_pressure a) ∧
    Tendsto (xi_time_part9t_binfold_positive_axis_linear_pressure_normalizedLog a)
      atTop (nhds (xi_time_part9t_binfold_positive_axis_linear_pressure_pressure a)) ∧
    ∀ b c : ℝ,
      xi_time_part9t_binfold_positive_axis_linear_pressure_pressure (b + c) =
        xi_time_part9t_binfold_positive_axis_linear_pressure_pressure b +
          c * Real.log (2 / xi_time_part9t_binfold_positive_axis_linear_pressure_phi)

lemma xi_time_part9t_binfold_positive_axis_linear_pressure_normalizedLog_eq
    (a : ℝ) (m : ℕ) :
    xi_time_part9t_binfold_positive_axis_linear_pressure_normalizedLog a m =
      xi_time_part9t_binfold_positive_axis_linear_pressure_pressure a := by
  have hne : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold xi_time_part9t_binfold_positive_axis_linear_pressure_normalizedLog
    xi_time_part9t_binfold_positive_axis_linear_pressure_powerSum
  rw [Real.log_exp]
  field_simp [hne]

/-- Paper label: `thm:xi-time-part9t-binfold-positive-axis-linear-pressure`. -/
theorem paper_xi_time_part9t_binfold_positive_axis_linear_pressure (a : ℝ) (ha : 0 < a) :
    xi_time_part9t_binfold_positive_axis_linear_pressure_statement a := by
  refine ⟨ha, ?_, ?_, ?_⟩
  · exact xi_time_part9t_binfold_positive_axis_linear_pressure_normalizedLog_eq a
  · have hconst :
        xi_time_part9t_binfold_positive_axis_linear_pressure_normalizedLog a =
          fun _ : ℕ => xi_time_part9t_binfold_positive_axis_linear_pressure_pressure a := by
      funext m
      exact xi_time_part9t_binfold_positive_axis_linear_pressure_normalizedLog_eq a m
    rw [hconst]
    exact tendsto_const_nhds
  · intro b c
    unfold xi_time_part9t_binfold_positive_axis_linear_pressure_pressure
    ring

end

end Omega.Zeta
