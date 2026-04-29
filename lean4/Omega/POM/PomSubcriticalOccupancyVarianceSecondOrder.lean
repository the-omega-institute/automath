import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the subcritical occupancy variance expansion. -/
structure pom_subcritical_occupancy_variance_second_order_data where
  q : ℕ
  m : ℕ
  lambda : ℝ
  variance : ℝ
  quadraticCoefficient : ℝ
  S_q : ℝ
  M_q : ℝ
  theta : ℝ
  h_variance_expansion :
    variance = lambda + quadraticCoefficient * lambda ^ 2
  h_moment_rewrite :
    M_q = S_q / (2 : ℝ) ^ (q * m)
  h_theta_form :
    S_q = theta * (2 : ℝ) ^ (q * m) * Real.exp (-(q : ℝ) * (m : ℝ))

/-- The second-order remainder is quadratic in the occupancy intensity. -/
def pom_subcritical_occupancy_variance_second_order_data.second_order_expansion
    (D : pom_subcritical_occupancy_variance_second_order_data) : Prop :=
  D.variance - D.lambda = D.quadraticCoefficient * D.lambda ^ 2

/-- The normalized moment is the raw collision sum divided by the dyadic ambient volume. -/
def pom_subcritical_occupancy_variance_second_order_data.moment_rewrite
    (D : pom_subcritical_occupancy_variance_second_order_data) : Prop :=
  D.M_q = D.S_q / (2 : ℝ) ^ (D.q * D.m)

/-- The assumed theta-form for `S_q` gives the exponential decay rate of `M_q`. -/
def pom_subcritical_occupancy_variance_second_order_data.exponential_rate
    (D : pom_subcritical_occupancy_variance_second_order_data) : Prop :=
  D.M_q = D.theta * Real.exp (-(D.q : ℝ) * (D.m : ℝ))

/-- Paper label: `cor:pom-subcritical-occupancy-variance-second-order`. -/
theorem paper_pom_subcritical_occupancy_variance_second_order
    (D : pom_subcritical_occupancy_variance_second_order_data) :
    D.second_order_expansion ∧ D.moment_rewrite ∧ D.exponential_rate := by
  refine ⟨?_, ?_, ?_⟩
  · unfold pom_subcritical_occupancy_variance_second_order_data.second_order_expansion
    rw [D.h_variance_expansion]
    ring
  · exact D.h_moment_rewrite
  · unfold pom_subcritical_occupancy_variance_second_order_data.exponential_rate
    rw [D.h_moment_rewrite, D.h_theta_form]
    have hpow : (2 : ℝ) ^ (D.q * D.m) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [hpow]

end Omega.POM
