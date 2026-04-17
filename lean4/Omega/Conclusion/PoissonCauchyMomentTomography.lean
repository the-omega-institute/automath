import Mathlib.Tactic

namespace Omega.Conclusion

/-- Solving the three asymptotic constants `(T₃, K₄, K₆)` recovers `μ₂`, `|μ₃|`, and `μ₄`.
    thm:conclusion-poisson-cauchy-three-constant-moment-tomography -/
theorem paper_conclusion_poisson_cauchy_three_constant_moment_tomography
    {T3 K4 K6 mu2 mu3 mu4 : Real} (hmu2 : 0 < mu2) (hT3 : T3 = |mu3| / Real.pi)
    (hK4 : K4 = mu2 ^ 2 / 8)
    (hK6 : K6 = mu2 ^ 3 / 64 - mu2 * mu4 / 8 + 3 * mu3 ^ 2 / 32) :
    mu2 = Real.sqrt (8 * K4) ∧
      |mu3| = Real.pi * T3 ∧
      mu4 =
        (3 * Real.pi ^ 2 * T3 ^ 2) / (4 * mu2) + mu2 ^ 2 / 8 - (8 * K6) / mu2 := by
  have hpi : (Real.pi : Real) ≠ 0 := by positivity
  have hmu2_ne : mu2 ≠ 0 := ne_of_gt hmu2
  have hden : (8 * mu2 : Real) ≠ 0 := by
    exact mul_ne_zero (show (8 : Real) ≠ 0 by norm_num) hmu2_ne
  have hmu2_eq : mu2 = Real.sqrt (8 * K4) := by
    rw [hK4]
    have hsq : 8 * (mu2 ^ 2 / 8) = mu2 ^ 2 := by ring
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hmu2]
  have habs_mu3 : |mu3| = Real.pi * T3 := by
    calc
      |mu3| = Real.pi * (|mu3| / Real.pi) := by
        field_simp [hpi]
      _ = Real.pi * T3 := by rw [← hT3]
  have hmu3_sq : mu3 ^ 2 = Real.pi ^ 2 * T3 ^ 2 := by
    calc
      mu3 ^ 2 = |mu3| ^ 2 := by rw [sq_abs]
      _ = (Real.pi * T3) ^ 2 := by rw [habs_mu3]
      _ = Real.pi ^ 2 * T3 ^ 2 := by ring
  have hmu4_raw : mu4 = (mu2 ^ 3 + 6 * mu3 ^ 2 - 64 * K6) / (8 * mu2) := by
    apply (eq_div_iff hden).2
    nlinarith [hK6]
  have hmu4_eq :
      mu4 =
        (3 * Real.pi ^ 2 * T3 ^ 2) / (4 * mu2) + mu2 ^ 2 / 8 - (8 * K6) / mu2 := by
    rw [hmu4_raw, hmu3_sq]
    field_simp [hmu2_ne]
    ring
  exact ⟨hmu2_eq, habs_mu3, hmu4_eq⟩

end Omega.Conclusion
