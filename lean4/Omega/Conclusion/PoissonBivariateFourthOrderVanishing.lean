import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-poisson-bivariate-fourth-order-vanishing`. -/
theorem paper_conclusion_poisson_bivariate_fourth_order_vanishing (A B : ℝ) :
    A ^ 2 / (8 : ℝ) + B ^ 2 / (2 : ℝ) = 0 ↔ A = 0 ∧ B = 0 := by
  constructor
  · intro h
    have hA_nonneg : 0 ≤ A ^ 2 := sq_nonneg A
    have hB_nonneg : 0 ≤ B ^ 2 := sq_nonneg B
    have hA_sq : A ^ 2 = 0 := by nlinarith
    have hB_sq : B ^ 2 = 0 := by nlinarith
    exact ⟨sq_eq_zero_iff.mp hA_sq, sq_eq_zero_iff.mp hB_sq⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

end Omega.Conclusion
