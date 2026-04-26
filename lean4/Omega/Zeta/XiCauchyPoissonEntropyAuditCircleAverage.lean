import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete audit package for the Cauchy--Poisson circle average.  The projection identity records
the timefiber Poisson projection principle applied to `log h`, while the Jensen field records the
normalization inequality. -/
structure xi_cauchy_poisson_entropy_audit_circle_average_data where
  xi_cauchy_poisson_entropy_audit_circle_average_rho : ℝ
  xi_cauchy_poisson_entropy_audit_circle_average_h : ℝ → ℝ
  xi_cauchy_poisson_entropy_audit_circle_average_audit_functional : ℝ
  xi_cauchy_poisson_entropy_audit_circle_average_cauchy_log_average : ℝ
  xi_cauchy_poisson_entropy_audit_circle_average_circle_average : ℝ
  xi_cauchy_poisson_entropy_audit_circle_average_rho_pos :
    0 < xi_cauchy_poisson_entropy_audit_circle_average_rho
  xi_cauchy_poisson_entropy_audit_circle_average_rho_lt_one :
    xi_cauchy_poisson_entropy_audit_circle_average_rho < 1
  xi_cauchy_poisson_entropy_audit_circle_average_audit_eq_neg_cauchy_average :
    xi_cauchy_poisson_entropy_audit_circle_average_audit_functional =
      -xi_cauchy_poisson_entropy_audit_circle_average_cauchy_log_average
  xi_cauchy_poisson_entropy_audit_circle_average_projection_identity :
    xi_cauchy_poisson_entropy_audit_circle_average_circle_average =
      xi_cauchy_poisson_entropy_audit_circle_average_cauchy_log_average
  xi_cauchy_poisson_entropy_audit_circle_average_jensen_normalization :
    xi_cauchy_poisson_entropy_audit_circle_average_cauchy_log_average ≤ 0

/-- Paper-facing statement: the entropy audit is nonnegative and is the negative circle average. -/
def xi_cauchy_poisson_entropy_audit_circle_average_statement
    (D : xi_cauchy_poisson_entropy_audit_circle_average_data) : Prop :=
  0 ≤ D.xi_cauchy_poisson_entropy_audit_circle_average_audit_functional ∧
    D.xi_cauchy_poisson_entropy_audit_circle_average_audit_functional =
      -D.xi_cauchy_poisson_entropy_audit_circle_average_circle_average

/-- Paper label: `prop:xi-cauchy-poisson-entropy-audit-circle-average`. -/
theorem paper_xi_cauchy_poisson_entropy_audit_circle_average
    (D : xi_cauchy_poisson_entropy_audit_circle_average_data) :
    xi_cauchy_poisson_entropy_audit_circle_average_statement D := by
  refine ⟨?_, ?_⟩
  · rw [D.xi_cauchy_poisson_entropy_audit_circle_average_audit_eq_neg_cauchy_average]
    linarith [D.xi_cauchy_poisson_entropy_audit_circle_average_jensen_normalization]
  · rw [D.xi_cauchy_poisson_entropy_audit_circle_average_audit_eq_neg_cauchy_average,
      D.xi_cauchy_poisson_entropy_audit_circle_average_projection_identity]

end Omega.Zeta
