import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-poisson-cauchy-endpoint-arcsine-common-parameter`. -/
theorem paper_conclusion_poisson_cauchy_endpoint_arcsine_common_parameter {r Γ : ℝ}
    (hr1 : r ≠ 1) (hrm1 : r ≠ -1) (hΓ : Γ = (1 + r) / (1 - r)) :
    1 / Γ = (1 - r) / (1 + r) ∧ 1 - r ^ 2 = 4 * Γ / (1 + Γ) ^ 2 := by
  have hden1 : 1 - r ≠ 0 := by
    intro h
    apply hr1
    linarith
  have hden2 : 1 + r ≠ 0 := by
    intro h
    apply hrm1
    linarith
  subst Γ
  constructor
  · field_simp [hden1, hden2]
  · field_simp [hden1, hden2]
    ring

end Omega.Conclusion
