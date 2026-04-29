import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9xfGoldenMetallicLogcostMinimizer

namespace Omega.Zeta

open Omega.Folding

noncomputable section

/-- The metallic scalarization threshold, specialized to the golden branch. -/
def xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c : ℝ :=
  metallicPerronRoot (1 : ℝ)

/-- The left Pareto envelope branch at the metallic transition. -/
def xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_value (β : ℝ) : ℝ :=
  Real.log xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c +
    (β - xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c) +
      (β - xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c) ^ (2 : ℕ) / 2

/-- The right Pareto envelope branch at the metallic transition. -/
def xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_value (β : ℝ) : ℝ :=
  Real.log xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c +
    (β - xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c) +
      (β - xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c) ^ (2 : ℕ)

/-- The split envelope selecting the left branch up to the metallic threshold. -/
def xi_time_part9xfa_metallic_value_c1_nonc2_transition_envelope (β : ℝ) : ℝ :=
  if β ≤ xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c then
    xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_value β
  else
    xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_value β

/-- First derivative of the left quadratic branch. -/
def xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_slope (β : ℝ) : ℝ :=
  1 + (β - xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c)

/-- First derivative of the right quadratic branch. -/
def xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_slope (β : ℝ) : ℝ :=
  1 + 2 * (β - xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c)

/-- One-sided second derivative of the left quadratic branch. -/
def xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_curvature (_β : ℝ) : ℝ :=
  1

/-- One-sided second derivative of the right quadratic branch. -/
def xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_curvature (_β : ℝ) : ℝ :=
  2

/-- Paper label: `thm:xi-time-part9xfa-metallic-value-c1-nonc2-transition`.
The golden metallic threshold supplies a two-branch quadratic value envelope.  The branch values
and first slopes match at the transition, while the one-sided curvatures jump. -/
theorem paper_xi_time_part9xfa_metallic_value_c1_nonc2_transition (A : ℕ) (hA : 2 ≤ A) :
    xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c = Real.goldenRatio ∧
      (1 : ℝ) / Real.log Real.goldenRatio <
        (A : ℝ) / Real.log (metallicPerronRoot (A : ℝ)) ∧
      metallicEntropyRate A < metallicEntropyRate 1 ∧
      (∀ β : ℝ, β ≤ xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c →
        xi_time_part9xfa_metallic_value_c1_nonc2_transition_envelope β =
          xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_value β) ∧
      (∀ β : ℝ, xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c < β →
        xi_time_part9xfa_metallic_value_c1_nonc2_transition_envelope β =
          xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_value β) ∧
      xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_value
          xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c =
        xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_value
          xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c ∧
      xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_slope
          xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c =
        xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_slope
          xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c ∧
      xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_curvature
          xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c -
        xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_curvature
          xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c =
          1 ∧
      xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_curvature
          xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c ≠
        xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_curvature
          xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c := by
  have hmetallic := paper_xi_time_part9xf_golden_metallic_logcost_minimizer A hA
  refine ⟨?_, hmetallic.1, hmetallic.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [xi_time_part9xfa_metallic_value_c1_nonc2_transition_beta_c, metallicPerronRoot,
      Real.goldenRatio]
    norm_num
  · intro β hβ
    simp [xi_time_part9xfa_metallic_value_c1_nonc2_transition_envelope, hβ]
  · intro β hβ
    simp [xi_time_part9xfa_metallic_value_c1_nonc2_transition_envelope, not_le.mpr hβ]
  · simp [xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_value,
      xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_value]
  · simp [xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_slope,
      xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_slope]
  · norm_num [xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_curvature,
      xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_curvature]
  · norm_num [xi_time_part9xfa_metallic_value_c1_nonc2_transition_left_curvature,
      xi_time_part9xfa_metallic_value_c1_nonc2_transition_right_curvature]

end

end Omega.Zeta
