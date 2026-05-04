import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-poisson-two-parameter-sixth-rigidity-complex-third`. -/
theorem paper_xi_poisson_two_parameter_sixth_rigidity_complex_third (varGap cov : ℝ)
    (third : ℂ) (hquad : varGap ^ 2 / 8 + cov ^ 2 / 2 = 0)
    (hsix : (3 : ℝ) / 32 * Complex.normSq third = 0) :
    varGap = 0 ∧ cov = 0 ∧ third = 0 := by
  have hvar_nonneg : 0 ≤ varGap ^ 2 / 8 := by positivity
  have hcov_nonneg : 0 ≤ cov ^ 2 / 2 := by positivity
  have hvar_term : varGap ^ 2 / 8 = 0 := by nlinarith
  have hcov_term : cov ^ 2 / 2 = 0 := by nlinarith
  have hvar_sq : varGap ^ 2 = 0 := by nlinarith
  have hcov_sq : cov ^ 2 = 0 := by nlinarith
  have hthird_norm : Complex.normSq third = 0 := by
    exact Or.resolve_left (mul_eq_zero.mp hsix) (by norm_num)
  exact ⟨sq_eq_zero_iff.mp hvar_sq, sq_eq_zero_iff.mp hcov_sq,
    Complex.normSq_eq_zero.mp hthird_norm⟩

end Omega.Zeta
