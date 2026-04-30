import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-poisson-defect-measure-superquartic-iff-m2zero`. -/
theorem paper_xi_poisson_defect_measure_superquartic_iff_m2zero (varGap cov : ℝ) :
    varGap ^ 2 + 4 * cov ^ 2 = 0 ↔ varGap = 0 ∧ cov = 0 := by
  constructor
  · intro h
    have hvar_nonneg : 0 ≤ varGap ^ 2 := sq_nonneg varGap
    have hcov_nonneg : 0 ≤ 4 * cov ^ 2 := by positivity
    have hvar_sq : varGap ^ 2 = 0 := by nlinarith
    have hcov_sq : cov ^ 2 = 0 := by nlinarith
    exact ⟨sq_eq_zero_iff.mp hvar_sq, sq_eq_zero_iff.mp hcov_sq⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

end Omega.Zeta
