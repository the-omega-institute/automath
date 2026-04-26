import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-poisson-bivariate-quartic-null-cone-fdiv-universal`. -/
theorem paper_conclusion_poisson_bivariate_quartic_null_cone_fdiv_universal
    (A B c : ℝ) (hc : c ≠ 0) :
    c * (A ^ 2 + 4 * B ^ 2) = 0 ↔ A = 0 ∧ B = 0 := by
  constructor
  · intro h
    have hsum : A ^ 2 + 4 * B ^ 2 = 0 := by
      exact (mul_eq_zero.mp h).resolve_left hc
    have hA2_nonneg : 0 ≤ A ^ 2 := sq_nonneg A
    have hB2_nonneg : 0 ≤ 4 * B ^ 2 := by positivity
    have hA2 : A ^ 2 = 0 := by nlinarith
    have hB2 : B ^ 2 = 0 := by nlinarith
    exact ⟨sq_eq_zero_iff.mp hA2, sq_eq_zero_iff.mp hB2⟩
  · rintro ⟨rfl, rfl⟩
    ring

end Omega.Conclusion
